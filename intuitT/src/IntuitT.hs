{-# LANGUAGE TypeOperators, QuasiQuotes #-}
{- quasi quotation
String are enclosed between   [r| and  |]
-}

module Main where


import Text.RawString.QQ
import Data.Maybe
import Data.IORef
import System.IO
import System.Environment -- getArgs
import MiniSat
-- import qualified Data.Map as Map
-- import qualified Data.Set as Set
-- import Data.List
import Control.Monad ( when )
-- import Control.Monad.State

-- import System.TimeIt
import Types
import ParseProblem 
import Clausify
import Prover
import Utility

import Text.Printf
import Control.Exception
import System.CPUTime
import System.Directory
-- import System.FilePath.Posix
import System.FilePath

-- import G4Prover
import WriteLatex 

-- type LClause = [Lit] :=> [Lit]
-- type LImplClause = (Lit :-> Lit) :-> Lit

-- https://hackage.haskell.org/package/minisat-0.1.2/docs/MiniSat.html


--------------------------------------------------------------------------------
-- main

main :: IO ()
main =
  do argss <- getArgs
     case argss of
       ["-t",file]  ->   withParseFile file (processTrace TraceLevel_high_with_latex) -- prove with trace
       ["-t0",file]  ->  withParseFile file (processTrace TraceLevel_low) 
       ["-t1",file]  ->  withParseFile file (processTrace TraceLevel_medium)
       ["-t2",file]  ->  withParseFile file (processTrace TraceLevel_high) 
       _ -> putStrLn help


-- IntuitT, implementation of intuit with trace and construction of derivations/countermodles

help :: String
help = [r|
Usage: intuitT OPTION FILE

FILE
  text file containing the input formula in TPTP syntax
  (see http://tptp.cs.miami.edu/TPTP/QuickGuide/Problems.html)

OPTIONS
 -t     trace (maximum level) and generate output files
 -t0    minimum trace level, no output files 
 -t1    medium  trace level, no output files
 -t2    maximum trace level, no output files|]  -- end string


withParseFile :: FilePath -> (FilePath -> [Input Form] -> IO ()) -> IO ()
withParseFile file process =
  do putStrLn ("+++ Reading file '" ++ show file ++ "'...")
     mForms <- readProblem file
     case mForms of
       Nothing -> do return ()
       Just inputForms -> do process file inputForms


-- prover with trace
processTrace :: TraceLevel -> FilePath -> [Input Form] -> IO ()
processTrace traceLev file inputForms = 
  do 
     putStrLn ("+++ Clausification...")
     start1 <- getCPUTime
     (cs,ics,mainGoal,countImplReductions) <- clausify inputForms
      --  cs:   flat clauses
      --  ics:  implication clauses
      --  mainGoal: atom (standard name: "$goal")
     end1 <- getCPUTime 
     let  (countCs,countIcs) = (length cs, length ics )
     when( traceLev >=  TraceLevel_high)(
       sequence_[
           putStrLn ("+++ Created " ++ show countCs ++ " flat clauses and "
                              ++ show countIcs ++ " implication clauses"),
           -- putStrLn $ "+++ Number of reduced implication clauses: " ++ show countImplReductions,
           putStrLn $ "==== FLAT CLAUSES (" ++ show countCs ++  ") ====" ,
           putStr $ unlines $ map printClause cs ,
           putStrLn $ "==== IMPLICATION CLAUSES (" ++ show countIcs ++  ") ====" ,
           putStr $ unlines $ map printImplClause ics 
           ]) -- end when
     putStrLn ("+++ Proving (intuitT)")
     hFlush stdout
     start2 <- getCPUTime
     proveProblem  traceLev file cs ics mainGoal
     end2 <- getCPUTime
     let time_clausify =(fromIntegral (end1 - start1)) / (10^12)
         time_prover =  (fromIntegral (end2 - start2)) / (10^12)
     putStrLn $  concatN 80 "*"  
     printf "Clausification time: %0.3f sec\n" (time_clausify :: Double)
     printf "Prover time: %0.3f sec\n" (time_prover :: Double)
  
