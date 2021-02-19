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
import Control.Monad ( when )
import Text.Printf
import System.CPUTime

--------
import Types
import ParseProblem 
import Clausify
import Prover
import Utility
import WriteLatex 





--------------------------------------------------------------------------------
-- main

main :: IO ()
main =
  do argss <- getArgs
     case argss of
       [file] -> withParseFile  file processPlain  
       ["-t",file]  ->  withParseFile  file (processTrace TraceLevel_high_with_latex) -- prove with trace
       ["-t0",file]  ->  withParseFile  file (processTrace TraceLevel_low) 
       ["-t1",file]  ->  withParseFile  file (processTrace TraceLevel_medium)
       ["-t2",file]  ->  withParseFile  file (processTrace TraceLevel_high)
       ["-h"] -> putStrLn help
-- ---  HIDDEN OPTIONS ---
       ["-fCube",file]    -> withParseFile'  file (putStrLn . showFCubeProblem)  --  only translate problem 
       ["-IntHistGC",file] -> withParseFile'  file (putStrLn . showIntHistGCProblem) -- only translate problem
-- -----------------------
       _ -> putStrLn help

-- IntuitR, a SAT-based prover for Intuitionistic Propositional Logic.

help :: String
help = [r|
Usage: intuitR [OPTION] FILE

FILE
  text file containing the input formula in TPTP syntax
  (see http://tptp.cs.miami.edu/TPTP/QuickGuide/Problems.html)

OPTIONS
 -t     trace (maximum level) and generate output files 
 -t0    minimum trace level, no output files 
 -t1    medium  trace level, no output files
 -t2    maximum trace level, no output files|]  -- end string


withParseFile ::  FilePath -> (FilePath -> [Input Form] -> IO ()) -> IO ()
withParseFile file process =
  do putStrLn ("+++ Reading file '" ++ show file ++ "'...")
     mForms <- readProblem file
     case mForms of
       Nothing -> do return ()
       Just inputForms -> do process file inputForms

withParseFile' ::  String -> ([Input Form] -> IO ()) -> IO ()
withParseFile' file h =
  do  mfs <- readProblem file
      case mfs of
        Nothing -> do return ()
        Just fs -> do h fs

  

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
     putStrLn ("+++ Proving (intuitR)")
     hFlush stdout
     start2 <- getCPUTime
     proveProblem  traceLev file cs ics mainGoal
     end2 <- getCPUTime
     let time_clausify =(fromIntegral (end1 - start1)) / (10^12)
         time_prover =  (fromIntegral (end2 - start2)) / (10^12)
     putStrLn $  concatN 60 "*"  
     printf "Clausification time: %0.3f sec\n" (time_clausify :: Double)
     printf "Prover time: %0.3f sec\n" (time_prover :: Double)
   
       
-- prover without trace 
processPlain :: FilePath -> [Input Form] -> IO ()
processPlain file inputForms =
  do putStrLn ("+++ Clausification...")
     start1 <- getCPUTime
     (cs,ics, mainGoal,_) <- clausify inputForms
     --  cs:  flat clauses
     -- ics:  implication clauses
    --  mainGoal  = atom (standard name: "$goal")
     end1 <- getCPUTime 
     putStrLn ("+++ Created " ++ show (length cs) ++ " flat clauses and "
                              ++ show (length ics) ++ " implication clauses")
     putStrLn ("+++ Proving (intuitR)")
     hFlush stdout   
     start2 <- getCPUTime
     proveProblemPlain file cs ics  mainGoal
     end2 <- getCPUTime
     let time_clausify =(fromIntegral (end1 - start1)) / (10^12)
         time_prover = (fromIntegral (end2 - start2)) / (10^12)
     printf "============================\n"    
     printf "Clausification time: %0.3f sec\n" (time_clausify :: Double)
     printf "Prover time: %0.3f sec\n" (time_prover :: Double)
      





