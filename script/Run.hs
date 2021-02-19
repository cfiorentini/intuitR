
{-
Arguments
^^^^^^^^^

testDir:       directory containing the test files
cmd:           command to be executed 
timeBound:     time bound for each test 
proverName:    name of the prover


Compile
^^^^^^^^

 ghc --make Run.hs -o Run 
  

-}



module Main where

import System.Directory
import System.FilePath
import Control.Applicative

import System.Environment
import System.Process
import System.Exit
import System.IO
import System.Timeout


import Data.Time.Clock
import Numeric
import Text.Printf

import Data.Char
import Data.List
import Data.Ord
import Data.Function

incrementalGroups :: [String] -> [[String]]
-- incrementalGroups ["a1.txt", "b1.txt", "a2.txt", "c1.txt", "a3.txt","b2.txt"]
-- [ ["a1.txt","a2.txt","a3.txt"], ["b1.txt","b2.txt"], ["c1.txt"] ]
incrementalGroups = map (sortBy (comparing lastDigits)) . groupOn removeLastDigits

groupOn :: Ord a => (a1 -> a) -> [a1] -> [[a1]]
groupOn f = groupBy ((==) `on` f) . sortBy (comparing f)


lastDigits :: String -> Int
-- lastDigits "a11b22c33.txt" = 33
lastDigits s =
  case takeWhileRev isDigit (dropExtension s) of
    "" -> 0
    s  -> read s

removeLastDigits :: String -> String
-- removeLastDigits "a11b22c33.txt" =  "a11b22c"
removeLastDigits = dropWhileRev isDigit . dropExtension

takeWhileRev p = reverse . takeWhile p . reverse
dropWhileRev p = reverse . dropWhile p . reverse

timeIt :: IO a -> IO (Double,a)
timeIt m =
  do t0 <- getCurrentTime
     res <- m
     t1 <- getCurrentTime
     let t :: Double
         t = fromRat (toRational (diffUTCTime t1 t0))
     return (t,res)

-- diffUTCTime :: UTCTime -> UTCTime -> NominalDiffTime
-- diffUTCTime a b = a - b

--  data NominalDiffTime
--  This is a length of time, as measured by UTC. It has a precision of 10^-12 s.
--  For example, (0.010 :: NominalDiffTime) corresponds to 10 milliseconds.


-- ## MAIN ##        

main :: IO ()
main = do
  hFlush stdout
  args@[testDir,timeBound,cmd,proverName]  <- getArgs
  let  logFile = proverName ++ "_"  ++ timeBound ++ "_"
  hlogFile <- openFile logFile WriteMode
  testFiles <- filter ((\ ext -> ".p" == ext) . takeExtension)
                 <$> getDirectoryContents testDir
  let testFiles_sorted = concat (incrementalGroups testFiles)             
  mapM_ (\ f -> processFile args hlogFile f ) testFiles_sorted  
  hClose hlogFile


processFile :: [String] ->  Handle ->FilePath -> IO ()
processFile  args@[testDir,timeBound,cmd,proverName]  hlogFile testFile =
  do putStrLn testFile  
     let fullCmd = [ timeBound, cmd, (testDir </> testFile) ]
     (time,(exc,out,err)) <- timeIt (readProcessWithExitCode "timeout" fullCmd "")
     -- execute the command line 'timeout fullCmd' 
     putStrLn (printf "%0.5fs" time ++ ", " ++ show exc)
     putStrLn out
     putStrLn err
     case exc of
       ExitSuccess  ->  write_logfile hlogFile testFile (Just time) out
       _ -> write_logfile hlogFile  testFile Nothing ""
  

write_logfile :: Handle -> FilePath -> Maybe Double -> String -> IO ()
write_logfile hlogFile testFile maybe_time output =
 do
  let time_str  =
        case maybe_time of
         Just t  ->
           let result = if  "Valid" `isInfixOf` output  then "Valid" else "CountSat"
           in printf "%0.5f,%s" t result  
         Nothing -> "-,timeout" 
  hPutStrLn hlogFile (testFile ++ "," ++ time_str)      
  hFlush  hlogFile
