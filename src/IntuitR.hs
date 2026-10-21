{-# LANGUAGE TypeOperators, QuasiQuotes #-}
{- quasi quotation
String are enclosed between   [r| and  |]
-}


module Main where

import Data.List
import Text.RawString.QQ
import Data.Maybe
import Data.IORef
import System.IO
import System.Environment -- getArgs
import Control.Monad  
import Text.Printf
import System.CPUTime
import System.Console.GetOpt
import System.Exit
import System.Random
import Data.Array.IO




--------
import Types
import ParserTPTP 
import qualified ClausifyStrong as ClausifyStrong
import qualified ClausifyWeak as ClausifyWeak
import Prover
import ProverPlain
import Utility
import WriteLatex 


-- #######  OPTIONS ######

data Flag
   =  TraceAndLatex           -- -t
  | TraceLevel Int            -- -tk where k=0 (low),1 (medium), 2 (high)
  | Help                      -- -h
  | WeakClausificationFlag    -- -w -- default
  | StrongClausificationFlag  -- -s 
   deriving (Eq,Show)

flags =
       [
         Option ['h'] []       (NoArg Help)    "Print this help message",
         Option ['t'] []       (OptArg argTraceLevel "Trace level")  "Trace and Latex",
         Option ['s'] []       (NoArg StrongClausificationFlag)  "Weak clausification" ,
         Option ['w'] []       (NoArg WeakClausificationFlag)  "Weak clausification"   -- default
       ]

argTraceLevel :: Maybe String -> Flag
argTraceLevel (Just k) = TraceLevel $ read  k
argTraceLevel Nothing = TraceAndLatex

getTraceLevelArgs ::  [Flag] -> Maybe TraceLevel
getTraceLevelArgs args  =
  if ( TraceAndLatex `elem` args ) then  Just TraceLevel_high_with_latex 
  else
    let mLevel = find isTraceLevel args
    in    
    case mLevel of
     Just (TraceLevel 0) -> Just TraceLevel_low
     Just (TraceLevel 1) -> Just TraceLevel_medium
     Just (TraceLevel 2) -> Just TraceLevel_high
     _   -> Nothing

isTraceLevel :: Flag -> Bool
isTraceLevel (TraceLevel _) = True
isTraceLevel _              = False

--------------------------------------------------------------------------------
-- main
-- ###  MAIN ###

main :: IO ()
main =
  do
    (args, files) <- getArgs >>= parse
    let mtraceLev = getTraceLevelArgs args
        file = head files
        clausificationType = if StrongClausificationFlag `elem` args then  StrongClausification else  WeakClausification
    putStrLn $ "+++ Reading file '" ++ show file ++ "'..."
    withParseFile  file mtraceLev clausificationType
--    case mtraceLev of
--      Just traceLevel ->   withParseFile  file  (processTrace file clausificationType) 
--      _               ->   withParseFile  file (processPlain file clausificationType)  -- no trace



------------------------
-- parse arguments

parse :: [String] -> IO ([Flag], [FilePath])
-- return arguments and input files in the command line 
parse argv = case getOpt Permute flags argv of
        (args,inputFiles,[]) ->
          do
           if Help `elem` args then
              do
                hPutStrLn  stderr  help --   (usageInfo header flags)
                exitWith ExitSuccess
           else
             do
              ( when ( null inputFiles ) $
                do
                  hPutStrLn stderr $ "No input file" ++ help
                  exitWith (ExitFailure 1)
               )  
              return  (args,inputFiles)  
        (_,_,errs)      ->
          do
            hPutStrLn stderr $ ( concat errs ) ++ help 
            exitWith (ExitFailure 1)
       -- where header = "Usage: intuitR [OPTION] ..  [file] ..."


help :: String
help = [r|
Usage: intuitR [OPTION] FILE

FILE
 text file containing the input formula F (mandatory), see README for the syntax

OPTIONS
 -t     trace (maximum level) and generate output files 
 -t0    minimum trace level, no output files 
 -t1    medium  trace level, no output files
 -t2    maximum trace level, no output files
 -s     strong clausification 
 -w     weak clausification (default)
 -h     print help
|]  -- end string


withParseFile ::  FilePath  ->  Maybe TraceLevel ->  ClausificationType -> IO ()
withParseFile file mtraceLev clausificationType  =
  do putStrLn ("+++ Reading file '" ++ show file ++ "'...")
     mForms <- parseFileTPTP file
     case (mForms,mtraceLev) of
       (Left err,_) -> print err  >> fail "parse error"
       (Right inputForms, Just traceLev )  -> processTrace file clausificationType traceLev inputForms
       (Right inputForms, Nothing) -> processPlain file  clausificationType  inputForms
       


-- prover with trace
processTrace :: FilePath -> ClausificationType -> TraceLevel  -> [Input (Form Name)] -> IO ()
processTrace file clausType traceLev inputForms = 
  do
     let clausifyInputForms = if clausType ==  WeakClausification then ClausifyWeak.clausifyInputForms else  ClausifyStrong.clausifyInputForms
     putStrLn $ "+++ Clausification ("  ++ show clausType ++   ")..."
     -- putStrLn $ unlines $ map show inputForms
     startClausify <- getCPUTime
     let (cs,ics,mainGoal,countImplReductions,cache) = clausifyInputForms inputForms
      --  cs:   flat clauses
      --  ics:  implication clauses
      --  mainGoal: atom (standard name: "$goal")
      --  cache: map name |--> simple form  |-- name (local cache)
         (countCs,countIcs) = (length cs, length ics )
         
     putStrLn ("+++ Created " ++ show countCs ++ " flat clauses and "
                              ++ show countIcs ++ " implication clauses")
     endClausify <- getCPUTime 
     ( when( traceLev >=  TraceLevel_high) $
       do
           putStrLn $ "+++ Number of reduced implication clauses: " ++ show countImplReductions
           putStrLn $ "==== FLAT CLAUSES (" ++ show countCs ++  ") ====" 
           putStr $ unlines $ map printClause cs 
           putStrLn $ "==== IMPLICATION CLAUSES (" ++ show countIcs ++  ") ====" 
           putStr $ unlines $ map printImplClause ics
           putStrLn  $ "=== INTERNAL MAP ===\n" ++  printCache cache  
           putStrLn  $ "=== SUBSTITUTION ===\n" ++  printCacheSubst cache 
         ) -- end when
     putStrLn ("+++ Proving (intuitR NEW)")
     hFlush stdout
     startProver <- getCPUTime
     proveProblem  traceLev file cs ics mainGoal
     endProver <- getCPUTime
     printTimings  ( Just (startClausify, endClausify) )  (startProver,endProver)
   
   
       
-- prover without trace 
processPlain :: FilePath ->  ClausificationType -> [Input (Form Name)] -> IO ()
processPlain file clausType inputForms =
  do
     let clausifyInputForms = if clausType ==  WeakClausification then ClausifyWeak.clausifyInputForms else  ClausifyStrong.clausifyInputForms
     putStrLn $ "+++ Clausification ("  ++ show clausType ++   ")..."
     startClausify <- getCPUTime
     let (cs',ics, mainGoal,_,cache) = clausifyInputForms inputForms
         cs = cs'
     -- cs <- shuffle cs'
     --  cs:  flat clauses
     -- ics:  implication clauses
     --  mainGoal  = atom (standard name: "$goal")
     putStrLn ("+++ Created " ++ show (length cs) ++ " flat clauses and "
                              ++ show (length ics) ++ " implication clauses")
     endClausify <- getCPUTime   
     putStrLn ("+++ Proving (intuitR NEW)")
     hFlush stdout   
     startProver <- getCPUTime
     proveProblemPlain file cs ics  mainGoal
     endProver <- getCPUTime
     printTimings (Just(startClausify, endClausify)) (startProver,endProver)

printTimings ::  Maybe (Integer ,  Integer) ->  (Integer, Integer) -> IO ()
-- print clausification and prover times
-- first arg:   Just(startClausify , endClausify) or Nothing if no clausification has been performed
-- second arg:  (startProver, endProver)
printTimings  mClausifyTimes  (startProver, endProver) =
  do
     let time_clausify = 
           case  mClausifyTimes of
               Just(startClausify,endClausify) ->  (fromIntegral (endClausify - startClausify)) / (10^12)
               Nothing  -> 0
     let  time_prover =  ( fromIntegral (endProver - startProver) ) / (10^12)
     putStrLn   ( concat $ replicate  80 "*" )
     ( when (isJust mClausifyTimes) $
             printf "Clausification time: %0.3f sec\n" (time_clausify :: Double)
      ) --end when
     printf "Prover time:         %0.3f sec\n" (time_prover :: Double)
     ( when (isJust mClausifyTimes) $
            printf "Total time:          %0.3f sec\n" ( (time_clausify + time_prover)  :: Double)
       ) -- end when 




-- | Randomly shuffle a list
--   /O(N)/
shuffle :: [a] -> IO [a]
shuffle xs =
  do
    let n = length xs
    ar <- newArray n xs
    forM [1..n] $ \i -> do
            j <- randomRIO (i,n)
            vi <- readArray ar i
            vj <- readArray ar j
            writeArray ar j vi
            return vj
  where
    newArray :: Int -> [a] -> IO (IOArray Int a)
    newArray k xs =  newListArray (1,k) xs
-- forM :: (Traversable t, Monad m) => t a -> (a -> m b) -> m (t b)
-- forM :: [int] -> (int -> IO a) -> I0 [a] 
