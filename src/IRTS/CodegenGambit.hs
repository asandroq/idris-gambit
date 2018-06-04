module IRTS.CodegenGambit (codegenGambit) where

import Control.Exception
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Data.Foldable

import Idris.Core.TT
import IRTS.CodegenCommon
import IRTS.Lang hiding (lift)

import System.IO

import qualified Data.Map.Strict as Map

data Gen = Gen
         { genTag :: Int
         , genCtx :: Map.Map Name LDecl
         , genOut :: Handle
         } deriving (Eq, Show)


type GenState = StateT Gen IO

codegenGambit :: CodeGenerator
codegenGambit ci = bracket (openFile (outputFile ci) WriteMode)
                           (hClose)
                           (\h -> evalStateT (codegenST ci) (Gen 0 Map.empty h))

codegenST :: CodegenInfo -> GenState ()
codegenST ci = do decls <- genInitialState $ liftDecls ci
                  genPrint preamble
                  traverse_ (uncurry codegen) decls
                  genPrint start

genInitialState :: [(Name, LDecl)] -> GenState [(Name, LDecl)]
genInitialState = traverse (uncurry go)
    where
      go name f@(LFun _ _ _ _) = do gen <- get
                                    put $ gen { genCtx = Map.insert name f (genCtx gen) }
                                    pure (name, f)
      go name (LConstructor _ _ ary) = do gen <- get
                                          let tag = genTag gen
                                          let cnt = LConstructor name tag ary
                                          put $ gen { genTag = tag + 1
                                                    , genCtx = Map.insert name cnt (genCtx gen)
                                                    }
                                          pure (name, cnt)

codegen :: Name -> LDecl -> GenState ()
codegen name (LFun _ _ args expr) = do let name' = quoteSym name
                                       let args' = genArgs args
                                       expr' <- genExpr expr
                                       genPrint $ "(define (" ++ name' ++ args' ++ ") " ++ expr' ++ ")\n\n"
codegen _ _ = pure ()

genExpr :: LExp -> GenState String
genExpr (LV name) = pure $ quoteSym name
genExpr (LApp _ (LV fn) args) = do ctx <- gets genCtx
                                   case Map.lookup fn ctx of
                                     Just (LConstructor _ _ ary) -> genApply fn ary args
                                     Just (LFun _ _ as _) -> genApply fn (length as) args
                                     Nothing -> genApply fn (length args) args
genExpr (LApp _ f _) = do f' <- genExpr f
                          pure $ "(error \"Impossible application of expression " ++ f' ++ ")"
genExpr (LLazyApp fn args) = do expr <- genExpr (LApp False (LV fn) args)
                                pure $ "(delay "++ expr ++ ")"
genExpr (LLazyExp expr) = do expr' <- genExpr expr
                             pure $ "(delay " ++ expr' ++ ")"
genExpr (LForce (LLazyApp n args)) = genExpr (LApp False (LV n) args)
genExpr (LForce expr) = do expr' <- genExpr expr
                           pure $ "(force " ++ expr' ++ ")"
genExpr (LLet name expr body) = do let name' = quoteSym name
                                   expr' <- genExpr expr
                                   body' <- genExpr body
                                   pure $ "(let ((" ++ name' ++ " " ++ expr' ++ ")) " ++ body' ++ ")"
genExpr (LLam args body) = do let args' = genArgs args
                              body' <- genExpr body
                              pure $ "(lambda (" ++ args' ++ ") " ++ body' ++ ")"
genExpr (LProj expr fld) = do expr' <- genExpr expr
                              let fld' = show (fld + 1)
                              pure $ "(##vector-ref " ++ expr' ++ " " ++ fld' ++ ")"
genExpr (LCon _ _ name args) = do let name' = quoteSym name
                                  args' <- genExprs args
                                  pure $ "(vector '" ++ name' ++ args' ++ ")"
genExpr (LCase _ expr alts) = do expr' <- genExpr expr
                                 alts' <- concat <$> traverse (genAlt expr) alts
                                 let test = if any isConCase alts
                                            then "(##vector-ref " ++ expr' ++ " 0)"
                                            else expr'
                                 pure $ "(case " ++ test ++ alts' ++ ")"
    where
      isConCase (LConCase _ _ _ _) = True
      isConCase _ = False
genExpr (LConst cnt) = pure $ genConst cnt
genExpr (LForeign _ t _) = do let name = case t of
                                           FStr s -> s
                                           _ -> show t
                              pure $ "(error \"Foreign call to '" ++ name ++ "' not implemented\")"
genExpr (LOp fn args) = genOp fn args
genExpr LNothing = pure "(##void)"
genExpr (LError msg) = pure $ "(error \"" ++ msg ++ "\")"

genExprs :: [LExp] -> GenState String
genExprs exprs = concat . map (" " ++) <$> traverse genExpr exprs

genApply :: Name -> Int -> [LExp] -> GenState String
genApply fn ary args = case compare ary (length args) of
                         LT -> do outer <- genApply fn ary (take ary args)
                                  rest <- genExprs (drop ary args)
                                  pure $ "(" ++ outer ++ rest ++ ")"
                         EQ -> do args' <- genExprs args
                                  pure $ "(" ++ quoteSym fn ++ args' ++ ")"
                         GT -> do extraArgs <- replicateM (ary - length args) genVar
                                  inner <- genApply fn ary (args ++ (LV <$> extraArgs))
                                  pure $ "(lambda (" ++ genArgs extraArgs ++ ") " ++ inner ++ ")"

genArgs :: [Name] -> String
genArgs = concatMap ((" " ++) . quoteSym)

genAlt :: LExp -> LAlt -> GenState String
genAlt cnt (LConCase _ name args expr) = do cnt' <- genExpr cnt
                                            expr' <- genExpr expr
                                            let body = if length args > 0
                                                       then "(let (" ++ bindings cnt' ++ ") " ++ expr' ++ ")"
                                                       else expr'
                                            pure $ "((" ++ quoteSym name ++ ") " ++ body ++ ")"
    where
      bindings c = concatMap (binding c) (zip args [1::Int ..])
      binding c (a, i) = "(" ++ quoteSym a ++ " (##vector-ref " ++ c ++ " " ++ show i ++ "))"
genAlt _ (LConstCase cnt expr) = do expr' <- genExpr expr
                                    pure $ "((" ++ genConst cnt ++ ") " ++ expr' ++ ")"
genAlt _ (LDefaultCase expr) = do expr' <- genExpr expr
                                  pure $ "(else " ++ expr' ++ ")"

genConst :: Const -> String
genConst (I i) = show i
genConst (BI i) = show i
genConst (Fl d) = show d
genConst (Ch c) = "#\\" ++ [c]
genConst (Str s) = "\"" ++ s ++ "\""
genConst (B8 b) = show b
genConst (B16 b) = show b
genConst (B32 b) = show b
genConst (B64 b) = show b
genConst _ = "(error \"Constant type not implemented\")"

genOp :: PrimFn -> [LExp] -> GenState String
genOp (LPlus (ATInt ITNative)) args = do args' <- genExprs args
                                         pure $ "(##fx+" ++ args' ++ ")"
genOp (LMinus (ATInt ITNative)) args = do args' <- genExprs args
                                          pure $ "(##fx-" ++ args' ++ ")"
genOp (LMinus (ATInt ITBig)) args = do args' <- genExprs args
                                       pure $ "(-" ++ args' ++ ")"
genOp (LTimes (ATInt ITNative)) args = do args' <- genExprs args
                                          pure $ "(##fx*" ++ args' ++ ")"
genOp (LEq aty) [l, r] = let op = case aty of
                                    ATInt (ITFixed _) -> "##fx="
                                    ATInt ITNative -> "##fx="
                                    ATInt ITBig -> "="
                                    ATInt ITChar -> "##char=?"
                                    ATFloat -> "##fl="
                         in genCompOp op l r
genOp (LLt ity) [l, r] = genOp (LSLt (ATInt ity)) [l, r]
genOp (LGt ity) [l, r] = genOp (LSGt (ATInt ity)) [l, r]
genOp (LSLt aty) [l, r] = let op = case aty of
                                    ATInt (ITFixed _) -> "##fx<"
                                    ATInt ITNative -> "##fx<"
                                    ATInt ITBig -> "<"
                                    ATInt ITChar -> "##char<?"
                                    ATFloat -> "##fl<"
                         in genCompOp op l r
genOp (LSGt aty) [l, r] = let op = case aty of
                                    ATInt (ITFixed _) -> "##fx>"
                                    ATInt ITNative -> "##fx>"
                                    ATInt ITBig -> ">"
                                    ATInt ITChar -> "##char>?"
                                    ATFloat -> "##fl>"
                         in genCompOp op l r
genOp (LSExt _ _) [x] = genExpr x
genOp (LIntStr ITChar) [x] = do x' <- genExpr x
                                pure $ "(make-string 1 " ++ x' ++ ")"
genOp (LIntStr _) [x] = do x' <- genExpr x
                           pure $ "(##number->string " ++ x' ++ ")"
genOp LStrConcat args = do args' <- genExprs args
                           pure $  "(##string-append" ++ args' ++ ")"
genOp LWriteStr [_, s] = do s' <- genExpr s
                            pure $ "(display " ++ s' ++ ")"
genOp fn _ = pure $ "(error \"Primitive operation " ++ show fn ++ " not implemented yet\")"

-- Idris's backend encodes booleans as integers
genCompOp :: String -> LExp -> LExp -> GenState String
genCompOp op lhs rhs = do lhs' <- genExpr lhs
                          rhs' <- genExpr rhs
                          pure $ "(if (" ++ op ++ " " ++ lhs' ++ " " ++ rhs' ++ ") 1 0)"

quoteSym :: Name -> String
quoteSym name = case name of
                  MN _ _ -> "|" ++ cleanup name ++ "|"
                  _ -> "|[Idris] " ++ cleanup name ++ "|"
    where
      cleanup = concatMap (\c -> if c == '|' then "\\|" else [c]) . showCG

genPrint :: String -> GenState ()
genPrint s = do out <- gets genOut
                lift $ hPutStr out s

genVar :: GenState Name
genVar = do tag <- gets genTag
            modify (\g -> g {genTag = tag + 1})
            pure $ MN tag "gensym"

preamble :: String
preamble = "(declare\n \
\ (block)\n \
\ (standard-bindings)\n \
\ (extended-bindings)\n \
\ (not run-time-bindings))\n\n"

start :: String
start = "(" ++ quoteSym (sMN 0 "runMain") ++ ")\n\n"
