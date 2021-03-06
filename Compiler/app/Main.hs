{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Lens
import Control.Monad.State
import Control.Monad

import Text.Parsec (parse)

import System.IO (hPutStrLn, stderr)
import System.Exit

import AST
import Compiler
import Env
import Parser
import Phase
import Preprocessor
import Transform
import Typechecker

import Config

main :: IO ()
main = compileFile =<< getArgs

putError = hPutStrLn stderr

compileFile :: Config -> IO ()
compileFile config = do
    content <- obtainContent config
    case parse parseProgram "" content of
        Left err -> error $ show err
        Right prog -> do
            debugPretty config "Parsed program:" prog

            let (compiled, env) = runState (preprocess prog) (newEnv Preprocessor) >>> typecheck >>> compileProg

            if not $ null $ env^.errors then do
                putError "Compilation failed!"
                putError "-------------------"
                putError $ prettyStr $ env^.errors
                exitFailure
            else do
                if config^.debug > 0 then do
                    putStrLn "Compiled program:"
                else pure ()

                putStrLn $ prettyStr compiled

            if config^.debug > 1 then print env
            else pure ()

    exitSuccess

obtainContent :: Config -> IO String
obtainContent config =
    case config^.srcName of
        Just "-" -> getContents
        Nothing -> getContents
        Just path -> readFile path

debugPretty :: PrettyPrint a => Config -> String -> a -> IO a
debugPretty config message x = do
    if config^.debug > 0 then do
        putStrLn message
        putStrLn $ prettyStr x
        putStrLn "========================================================"
        putStrLn "========================================================"
    else pure ()

    pure x

