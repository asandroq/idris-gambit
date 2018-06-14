module IRTS.CodegenGambit (codegenGambit) where

import Control.Exception
import Control.Monad.Trans.Reader
import Data.Foldable

import Idris.Core.TT
import IRTS.CodegenCommon
import IRTS.Defunctionalise hiding (genArgs, lift)

import System.IO

import qualified Data.Map.Strict as Map


type Generator = Reader (Map.Map Name DDecl)

codegenGambit :: CodeGenerator
codegenGambit ci = bracket (openFile (outputFile ci) WriteMode)
                           (hClose)
                           (\h -> codegen h (defunDecls ci))

codegen :: Handle -> [(Name, DDecl)] -> IO ()
codegen h decls = do hPutStr h preamble
                     traverse_ go decls
                     hPutStr h start
    where
      go (name, (DFun _ args expr)) = do let name' = quoteSym name
                                         let args' = genArgs args
                                         let expr' = runReader (genExpr expr) ctx
                                         hPutStr h $ "(define (" ++ name' ++ args' ++ ") " ++ expr' ++ ")\n\n"
      go _ = pure ()

      ctx = Map.fromList decls

genExpr :: DExp -> Generator String
genExpr (DV name) = pure $ quoteSym name
genExpr (DApp _ fn args) = do ctx <- ask
                              let fn' = quoteSym fn
                              args' <- genExprs args
                              case Map.lookup fn ctx of
                                Just (DConstructor _ _ _) -> genExpr (DC Nothing 0 fn args)
                                Just (DFun _ _ _) -> pure $ "(" ++ fn' ++ args' ++ ")"
                                Nothing -> pure $ "(error \"No such variable " ++ fn' ++ "\")"
genExpr (DLet name expr body) = do let name' = quoteSym name
                                   expr' <- genExpr expr
                                   body' <- genExpr body
                                   pure $ "(let ((" ++ name' ++ " " ++ expr' ++ ")) " ++ body' ++ ")"
genExpr (DUpdate name expr) = do let name' = quoteSym name
                                 expr' <- genExpr expr
                                 pure $ "(begin (set! " ++ name' ++ " " ++ expr' ++ ") " ++ name' ++ ")"
genExpr (DProj expr fld) = do expr' <- genExpr expr
                              let fld' = show (fld + 1)
                              pure $ "(##vector-ref " ++ expr' ++ " " ++ fld' ++ ")"
genExpr (DC _ _ name args) = do let name' = quoteSym name
                                args' <- genExprs args
                                pure $ "(vector '" ++ name' ++ args' ++ ")"
genExpr (DCase _ expr alts) = genCase expr alts
genExpr (DChkCase expr alts) = genCase expr alts
genExpr (DConst cnt) = pure $ genConst cnt
genExpr (DForeign _ t _) = do let name = case t of
                                           FStr s -> s
                                           _ -> show t
                              pure $ "(error \"Foreign call to '" ++ name ++ "' not implemented\")"
genExpr (DOp fn args) = genOp fn args
genExpr DNothing = pure "(##void)"
genExpr (DError msg) = pure $ "(error \"" ++ msg ++ "\")"

genExprs :: [DExp] -> Generator String
genExprs exprs = concat . map (" " ++) <$> traverse genExpr exprs

genCase :: DExp -> [DAlt] -> Generator String
genCase expr alts =  do expr' <- genExpr expr
                        alts' <- concat <$> traverse (genAlt expr) alts
                        let test = if any isConCase alts
                                   then "(##vector-ref " ++ expr' ++ " 0)"
                                   else expr'
                        pure $ "(case " ++ test ++ alts' ++ ")"
    where
      isConCase (DConCase _ _ _ _) = True
      isConCase _ = False

genAlt :: DExp -> DAlt -> Generator String
genAlt cnt (DConCase _ name args expr) = do cnt' <- genExpr cnt
                                            expr' <- genExpr expr
                                            let body = if length args > 0
                                                       then "(let (" ++ bindings cnt' ++ ") " ++ expr' ++ ")"
                                                       else expr'
                                            pure $ "((" ++ quoteSym name ++ ") " ++ body ++ ")"
    where
      bindings c = concatMap (binding c) (zip args [1::Int ..])
      binding c (a, i) = "(" ++ quoteSym a ++ " (##vector-ref " ++ c ++ " " ++ show i ++ "))"
genAlt _ (DConstCase cnt expr) = do expr' <- genExpr expr
                                    pure $ "((" ++ genConst cnt ++ ") " ++ expr' ++ ")"
genAlt _ (DDefaultCase expr) = do expr' <- genExpr expr
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

genOp :: PrimFn -> [DExp] -> Generator String
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
genOp LFloatStr [x] = do x' <- genExpr x
                         pure $ "(##flonum->string " ++ x' ++ " 10 #f)"
genOp LStrConcat args = do args' <- genExprs args
                           pure $  "(##string-append" ++ args' ++ ")"
genOp LWriteStr [_, s] = do s' <- genExpr s
                            pure $ "(display " ++ s' ++ ")"
genOp fn _ = pure $ "(error \"Primitive operation " ++ show fn ++ " not implemented yet\")"

-- Idris's backend encodes booleans as integers
genCompOp :: String -> DExp -> DExp -> Generator String
genCompOp op lhs rhs = do lhs' <- genExpr lhs
                          rhs' <- genExpr rhs
                          pure $ "(if (" ++ op ++ " " ++ lhs' ++ " " ++ rhs' ++ ") 1 0)"

genArgs :: [Name] -> String
genArgs = concatMap ((" " ++) . quoteSym)

quoteSym :: Name -> String
quoteSym name = case name of
                  MN _ _ -> "|" ++ cleanup name ++ "|"
                  _ -> "|[Idris] " ++ cleanup name ++ "|"
    where
      cleanup = concatMap (\c -> if c == '|' then "\\|" else [c]) . showCG

preamble :: String
preamble = "(declare\n \
\ (block)\n \
\ (standard-bindings)\n \
\ (extended-bindings)\n \
\ (not run-time-bindings))\n\n"

start :: String
start = "(" ++ quoteSym (sMN 0 "runMain") ++ ")\n\n"
