module IRTS.CodegenGambit (codegenGambit) where

import Control.Exception
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Data.Foldable
import Data.List

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
codegenST ci = do let decls = sortBy declOrder $ liftDecls ci
                  ndecls <- genInitialState decls
                  genPrint preamble
                  traverse_ (uncurry codegen) ndecls
                  genPrint start
    where
      declOrder (_, (LConstructor _ _ _)) (_, (LFun _ _ _ _)) = LT
      declOrder (_, (LFun _ _ _ _)) (_, (LConstructor _ _ _)) = GT
      declOrder _ _ = EQ

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
codegen name (LFun _ _ args expr) = do genPrint "(define ("
                                       genPrint $ quoteSym name
                                       genArgs args
                                       genPrint ") "
                                       genExpr expr
                                       genPrint ")\n\n"
codegen name (LConstructor _ tag _) = do  genPrint ";; "
                                          genPrint $ quoteSym name
                                          genPrint " -> "
                                          genPrint $ show tag
                                          genPrint "\n"

genExpr :: LExp -> GenState ()
genExpr (LV name) = genPrint $ quoteSym name
genExpr (LApp _ (LV fn) args) = do ctx <- gets genCtx
                                   case Map.lookup fn ctx of
                                     Just (LConstructor _ _ ary) -> genApply fn ary args
                                     Just (LFun _ _ as _) -> genApply fn (length as) args
                                     Nothing -> genApply fn (length args) args
genExpr (LApp _ f _) = do genPrint "(error \"Impossible application of expression \""
                          genExpr f
                          genPrint "\")"
genExpr (LLazyApp fn args) = do genPrint "(delay "
                                genExpr (LApp False (LV fn) args)
                                genPrint ")"
genExpr (LLazyExp expr) = do genPrint "(delay "
                             genExpr expr
                             genPrint ")"
genExpr (LForce (LLazyApp n args)) = genExpr (LApp False (LV n) args)
genExpr (LForce expr) = do genPrint "(force "
                           genExpr expr
                           genPrint ")"
genExpr (LLet name expr body) = do genPrint "(let (("
                                   genPrint $ quoteSym name
                                   genPrint " "
                                   genExpr expr
                                   genPrint ")) "
                                   genExpr body
                                   genPrint ")"
genExpr (LLam args body) = do genPrint "(lambda ("
                              genArgs args
                              genPrint ") "
                              genExpr body
                              genPrint ")"
genExpr (LProj expr fld) = do genPrint "(##vector-ref "
                              genExpr expr
                              genPrint " "
                              genPrint $ show (fld + 1)
                              genPrint ")"
genExpr (LCon _ _ name args) = do genPrint "(vector '"
                                  genPrint $ quoteSym name
                                  traverse_ (\a -> genPrint " " >> genExpr a) args
                                  genPrint ")"
genExpr (LCase _ expr alts) = do genPrint "(case "
                                 if any isConCase alts
                                    then do genPrint "(##vector-ref "
                                            genExpr expr
                                            genPrint " 0)"
                                    else genExpr expr
                                 traverse_ (\a -> genPrint " " >> genAlt expr a) alts
                                 genPrint ")"
    where
      isConCase (LConCase _ _ _ _) = True
      isConCase _ = False
genExpr (LConst cnt) = genPrint $ genConst cnt
genExpr (LForeign r t _) = do genPrint "(error \"Foreign call to '"
                              case t of
                                FStr s -> genPrint s
                                _ -> genPrint $ show t
                              genPrint " ("
                              genPrint $ show r
                              genPrint ")"
                              genPrint "' not implemented\")"
genExpr (LOp fn args) = genOp fn args
genExpr LNothing = genPrint "(##void)"
genExpr (LError msg) = do genPrint "(error \""
                          genPrint msg
                          genPrint "\")"

genApply :: Name -> Int -> [LExp] -> GenState ()
genApply fn ary args = case compare ary (length args) of
                         LT -> do genPrint "("
                                  genApply fn ary (take ary args)
                                  traverse_ (\a -> genPrint " " >> genExpr a) (drop ary args)
                                  genPrint ")"
                         EQ -> do genPrint "("
                                  genPrint $ quoteSym fn
                                  traverse_ (\a -> genPrint " " >> genExpr a) args
                                  genPrint ")"
                         GT -> do tag <- gets genTag
                                  let newTag = tag + ary - length args
                                  let extraArgs = (flip sMN) "extraArg" <$> [tag .. newTag - 1]
                                  modify (\g -> g { genTag = newTag })
                                  genPrint "(lambda ("
                                  genArgs extraArgs
                                  genPrint ") "
                                  genApply fn ary (args ++ (LV <$> extraArgs))
                                  genPrint ")"

genArgs :: [Name] -> GenState ()
genArgs = traverse_ (\a -> genPrint (" " ++ quoteSym a))

genAlt :: LExp -> LAlt -> GenState ()
genAlt cnt (LConCase _ name args expr) = do genPrint "(("
                                            genPrint $ quoteSym name
                                            genPrint ") "
                                            when (length args > 0) $ do
                                              genPrint "(let ("
                                              forM_ (zip args [1::Int ..]) $ \(a, i) -> do
                                                genPrint "("
                                                genPrint $ quoteSym a
                                                genPrint " (##vector-ref "
                                                genExpr cnt
                                                genPrint " "
                                                genPrint $ show i
                                                genPrint "))"
                                              genPrint ") "
                                            genExpr expr
                                            when (length args > 0) $ genPrint ")"
                                            genPrint ")"
genAlt _ (LConstCase cnt expr) = do genPrint "(("
                                    genPrint $ genConst cnt
                                    genPrint ") "
                                    genExpr expr
                                    genPrint ")"
genAlt _ (LDefaultCase expr) = do genPrint "(else "
                                  genExpr expr
                                  genPrint ")"

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

genOp :: PrimFn -> [LExp] -> GenState ()
genOp (LPlus (ATInt ITNative)) [l, r] = do genPrint "(##fx+ "
                                           genExpr l
                                           genPrint " "
                                           genExpr r
                                           genPrint ")"
genOp (LMinus (ATInt ITNative)) [l, r] = do genPrint "(##fx- "
                                            genExpr l
                                            genPrint " "
                                            genExpr r
                                            genPrint ")"
genOp (LMinus (ATInt ITBig)) [l, r] = do genPrint "(- "
                                         genExpr l
                                         genPrint " "
                                         genExpr r
                                         genPrint ")"
genOp (LTimes (ATInt ITNative)) [l, r] = do genPrint "(##fx* "
                                            genExpr l
                                            genPrint " "
                                            genExpr r
                                            genPrint ")"
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
genOp (LIntStr ITChar) [x] = do genPrint "(make-string 1 "
                                genExpr x
                                genPrint ")"
genOp (LIntStr _) [x] = do genPrint "(##number->string "
                           genExpr x
                           genPrint ")"
genOp LStrConcat [l, r] = do genPrint "(##string-append "
                             genExpr l
                             genPrint " "
                             genExpr r
                             genPrint ")"
genOp LWriteStr [_, s] = do genPrint "(display "
                            genExpr s
                            genPrint ")"
genOp fn _ = do genPrint "(error \"Primitive operation "
                genPrint $ show fn
                genPrint " not implemented yet\")"

genCompOp :: String -> LExp -> LExp -> GenState ()
genCompOp op lhs rhs = do genPrint "(if ("
                          genPrint op
                          genPrint " "
                          genExpr lhs
                          genPrint " "
                          genExpr rhs
                          genPrint ") 1 0)"

quoteSym :: Name -> String
quoteSym name = case name of
                  MN _ _ -> "|" ++ cleanup name ++ "|"
                  _ -> "|[Idris] " ++ cleanup name ++ "|"
    where
      cleanup = concatMap (\c -> if c == '|' then "\\|" else [c]) . showCG

genPrint :: String -> GenState ()
genPrint s = do out <- gets genOut
                lift $ hPutStr out s

preamble :: String
preamble = "(declare\n \
\ (block)\n \
\ (standard-bindings)\n \
\ (extended-bindings)\n \
\ (not run-time-bindings))\n\n"

start :: String
start = "(" ++ quoteSym (sMN 0 "runMain") ++ ")\n\n"
