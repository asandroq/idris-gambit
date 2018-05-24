module Main where

import Idris.AbsSyntax
import Idris.ElabDecls
import Idris.Main
import Idris.Options

import IRTS.Compiler
import IRTS.CodegenGambit

import System.Environment
import System.Exit

data Opts = Opts
          { inputs :: [FilePath]
          , output :: FilePath
          }

getOpts :: IO Opts
getOpts = do xs <- getArgs
             pure $ process (Opts [] "a.scm") xs
   where
     process opts ("-o" : o : xs) = process (opts {output = o}) xs
     process opts (x : xs) = process (opts {inputs = x : inputs opts}) xs
     process opts [] = opts

showUsage :: IO ()
showUsage = do putStrLn "Usage: idris-gambit <ibc files> [-o <output file>]"
               exitWith ExitSuccess

compileMain :: Opts -> Idris ()
compileMain opts = do elabPrims
                      _ <- loadInputs (inputs opts) Nothing
                      mainProg <- elabMain
                      ir <- compile (Via IBCFormat "scm") (output opts) (Just mainProg)
                      runIO $ codegenGambit ir

main :: IO ()
main = do opts <- getOpts
          if null (inputs opts)
             then showUsage
             else runMain $ compileMain opts
