{-# LANGUAGE TypeOperators #-}
module Prover (
    proveProblem
    -- proveProblemPlain
  )
  where

-- import Data.IORef
import System.IO
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List 
import qualified Data.PartialOrd as POrd
import System.Directory
import System.FilePath.Posix
import System.Posix.Files
import System.FilePath
import Control.Monad.State


import Types
import MiniSat  --  https://hackage.haskell.org/package/minisat
import WriteLatex
import WriteModelGraphviz
import WriteMakeFile
import Utility







-- ##############################################
-- ######        CLAESSEN-ROSEN PROVER      #####  
-- ######     WITH DERIVATIONS AND MODELS   #####
-- ##############################################

data Control = End | Continue
  deriving Eq
type Choices = [ (ImplClause Lit, [ImplClause Lit])]
type ModOrDer a =( Either (Model a) [a] ,Control ) 

data Result a = CountSat | Proved ( [a] , Derivation a)
type SearchResult a = (Result a, Control)



initProblem :: TraceLevel -> FilePath ->  [Clause Name] -> [ImplClause Name] -> Name -> IO ProverState 
initProblem traceLev file cs ics goal =
  do
  let names = getNames cs ics goal
  sat <- newSolver
  -- eliminate sat True -- off
  -- create the literals (SAT-solver language), one for each  name occurring in the input formulas
  univ <- sequence [ newLit sat | _ <- names ] -- universe  :: [Lit]
  -- create encode/decodes maps 
  let nmToLt_map  = Map.fromList (names `zip` univ)  -- Name to Lit map
      nmToLt x = fromJust $ Map.lookup x  nmToLt_map -- :: Name -> Lit
      ltToNm_map = Map.fromList (univ `zip` names)  -- Lit to Name map
      ltToNm y = fromJust $ Map.lookup y ltToNm_map -- :: Lit -> Name
      falseLit = nmToLt false    -- false :: Name (constant)
      --  Map.lookup :: Ord k => k -> Map.Map k a -> Maybe a
  addClause sat [neg falseLit]
  -- translate cs and ics into the SAT-solver language
  let csLit =  map (fmap nmToLt) cs
      icsLit = map (mapImplClause nmToLt) ics
  -- add  clauses to sat
  sequence_
    [ addClause sat (map neg xs ++  ys) | (xs :=> ys) <- csLit ]
    {- for every clause
            [x1, .. , xn] :=> [y1 .. ym]
       in csLit add the clause
         ~x1 | ... |~xn | y1 | ... | ym
       to the SAT-solver  
   -}
  -- proving
  simplify sat
  let initGlobSt =   -- initial state
        ProverState{
            problemName = file,
            solver = sat,
            universe = univ,
            litToName = ltToNm,
            initClauses = csLit,
            initImplClauses = icsLit,
            initGoal =  nmToLt goal,
            addedCs = [],
            countAtms = length names,
            countSat = 0,
            countNo = 0,
            countAdd = 0,
            model = emptyModel,
            traceLevel = traceLev,
            isValidForm = False
            }   
  return  initGlobSt 


getNames ::  [Clause Name] -> [ImplClause Name] -> Name  -> [Name]
-- duplication free list of the  the names occurring in (ics,ics,goal)
-- NOTE:  Set.fromList :: Ord a => [a] -> Set    complexity O(n log n)
--                 nub ::  Eq a => [a] -> [a]    complexity O(n^2)
getNames  cs ics goal =
  Set.toList $ Set.fromList $ [ x | (xs :=> ys) <- cs, x <- xs ++ ys ]
                                ++ [ z | ((a:->b):->c) <- ics, z <- [a,b,c] ]
                                ++ [ goal, false ]


-- ########################################################
-- #######        PROVER  WITH  TRACE              ########
-- ########################################################


proveProblem :: TraceLevel -> FilePath -> [Clause Name] -> [ImplClause Name] -> Name -> IO ()
-- (cs,ics,goal): problem to solve in clausal form
proveProblem traceLev file cs ics goal  = 
 do
  let baseName = takeBaseName file
  initialProverSt  <- initProblem traceLev baseName cs ics goal
  let icsLit = initImplClauses initialProverSt
      goalLit = initGoal initialProverSt
  ( (res,_),finalProverSt) <-  runStateT  ( proveMain icsLit [] goalLit ) initialProverSt
  let addedClauses = addedCs finalProverSt
  -- deleteSolver $ solver  finalProverSt
  let  ltToNm = litToName finalProverSt
       problName =  "problem_"  ++ baseName
       derName= "derivation_"  ++ baseName
       modelName= "model_"  ++ baseName
       dirName = "out-" ++ baseName
       texProblemFile = combine dirName (addExtension problName ".tex")
       texDerFile = combine dirName (addExtension derName ".tex")
       gvFile =  combine dirName (addExtension modelName ".gv")
       makeFile = combine dirName  "Makefile"
       msgMake = concatN 80 "*" ++
                 "\n---> Output files are in the directory '" ++    dirName  ++ "'" ++
                 "\n---> Move into directory '" ++ dirName ++ "' and run command 'make' to compile them" 
  case res of
       Proved (_,der)  ->  -- valid
         do
           putStrLn "+++ RESULT: Valid (intuitionistically)"
           putStrLn ( writeStatistics finalProverSt )
           when(traceLev >= TraceLevel_high_with_latex)(
             sequence_ [
               createDirectoryIfMissing True dirName,  
               writeFile texProblemFile (writeLatexProblem  finalProverSt),
               writeFile texDerFile (writeLatexDerivation finalProverSt  (fmap ltToNm der)),  
               writeFile makeFile (writeMakeFile_valid  problName derName),
               putStrLn msgMake
               ]) -- end when
       CountSat ->
         do
           putStrLn "+++ RESULT: CounterSatisfiable (intuitionistically)"
           putStrLn ( writeStatistics finalProverSt )
           when(traceLev >= TraceLevel_high_with_latex)(
             sequence_ [
                createDirectoryIfMissing True dirName,             
                writeFile texProblemFile (writeLatexProblem finalProverSt),
                writeFile gvFile (writeModelGraphviz finalProverSt ),
                writeFile makeFile (writeMakeFile_countsat problName modelName),
                putStrLn msgMake
            ]) -- end when


writeStatistics :: ProverState -> String
writeStatistics pst =
  let mod =
        if (isValidForm pst) then "" else
          "\nWorlds in the countermodel: " ++ show ( sizeModel (model pst) )
      cntSat = countSat pst
      cntAdded = length  (addedCs pst)
      cntNo = countNo pst
  in 
  "Flat  clauses: " ++ show ( length (initClauses pst) )  
  ++ "\nImpl. clauses: " ++ show ( length (initImplClauses pst) )
  ++ "\nAtoms: " ++ show ( length (universe pst) )
  ++ "\nCalls to the SAT-solver: " ++ show cntSat
  ++ "\nAdded clauses: " ++  show cntAdded
  ++ "\nGenerated worlds (= No answers): " ++  show  cntNo
  ++ mod

-- ##############################################à

proveMain :: [ImplClause Lit] -> [Lit] -> Lit -> StateT ProverState IO (SearchResult Lit)
proveMain ics assumps  right  =
  do
    pst <- get  -- get prover state
    let sat = solver pst
        ics0 = initImplClauses pst
        ltToNm = litToName pst
        cntSat = countSat pst
        cntAdd = countAdd pst
        cntNo =  countNo pst
        traceLev = traceLevel pst
    when( traceLev >= TraceLevel_medium  )(    
      liftIO $ putStrLn $ inSharps ( " PROVE" ++  printStep cntSat )
     )
    when( traceLev >= TraceLevel_high  )(  
      liftIO $ putStrLn   ( printfState ltToNm ics0  cntAdd (addedCs pst) ics assumps right  )
     )
    when( traceLev >= TraceLevel_medium  )(  
      liftIO $ putStrLn  ( printStep cntSat ++ printfAsk   ltToNm cntAdd ics assumps right )
     )
    isSat <- lift $ solve sat (neg right : assumps)  --  solve :: Solver -> [Lit] -> IO Bool
    -- update prover state
    modify ( \ s -> s{countSat = cntSat + 1 }  ) 
    if isSat then  --  model found
       do
         let  cntNo =  countNo pst  -- index of the new world
          -- update prover state
         modify ( \s -> s{countNo = cntNo + 1} ) 
         trueAtms <- lift $ trueAtmsInSat sat (universe pst)
         let icsToCheck = [ ic | ic@((a:->b):->c) <- ics,
                              not (elem a trueAtms),  not (elem b trueAtms), not (elem c trueAtms) ]
             choices =  [ (ic,  ics \\ [ic]  ) | ic <- icsToCheck  ]       
             wk = cntNo 
         let newWorld = mkWorld wk trueAtms
         when( traceLev >= TraceLevel_medium  )(
          sequence_[
            liftIO $ putStrLn ( ">>> NO( " ++   printfAtmsBrace ltToNm trueAtms ++ " )" ) ,
            liftIO $ putStrLn  ( printStep cntSat ++ "Model found (new world): "
                              ++ printfWorld ltToNm newWorld )
           ])  --end when 
         when( traceLev >= TraceLevel_high  )( 
          liftIO $ putStrLn  ( printStep cntSat
                                ++ "ics to Check:\n" ++  printfImplClausesWithIndex ltToNm ics0 icsToCheck )
           )  
         loopImpls cntSat choices  newWorld assumps right
      else -- right formula is provable 
        do
          xs <- lift $ conflict sat   -- conflict :: Solver -> IO [Lit] 
{-
Let
        xs = x1, ... , xn,
  assumps1 =  [ ~x | x /=  right ] 
Then:
   sat |--   x1 | ... | xn 
   sat |--  assumps1 -> right   -}
          let assumps1 =  map neg ( xs \\ [right] )
              left = if null  assumps1 then "" else  ", " ++ printfAtms ltToNm assumps1
          when( traceLev >= TraceLevel_medium  )(
           sequence_ [ 
            liftIO $ putStrLn (">>> YES( " ++   printfAtmsBrace ltToNm assumps1 ++ " )" ),  
            liftIO $ putStrLn ( printStep cntSat ++ printR cntAdd ++ left  ++ " |-- " ++  ltToNm right ),
            liftIO $ putStrLn $ inSharps ( " END"  ++ printStep cntSat ++  "(derivation) " )
           ])  --end when 
          let endProofSearch =  (null assumps1  && right == initGoal pst )
              contr = if endProofSearch then End else Continue
              der = Axiom ( Seq(cntAdd, addedCs pst, ics, assumps1, right ) )
          when( endProofSearch )(
             -- update prover state
             modify ( \ s -> s{isValidForm = True  }  )     
            ) -- end when  
          return ( Proved (assumps1, der ),contr )    
     

loopImpls :: Int -> Choices   -> World Lit -> [Lit] ->  Lit
  -> StateT ProverState IO (SearchResult Lit)
loopImpls cntSat0 ( (impl@((a:->b):->c) ,impls) : choices )  w0  assumps right  =  
-- cntSatO: current call
  do
   pst0 <- get  -- get prover state
   let sat = solver pst0
       ics0 = initImplClauses  pst0
       cntAdd = countAdd pst0
       ltToNm = litToName pst0
       mod = model pst0
       trueAtms = getWAtms w0
       traceLev = traceLevel pst0
       allImpls = impl : impls
   when( traceLev >= TraceLevel_medium  )(   
       liftIO $ putStrLn ( printStep cntSat0 ++  "LOOP: check "
                       ++ printfImplClauseWithIndex ltToNm ics0 impl )
       )    
   res1 <-  proveMain impls (a : trueAtms)  b
   pst1 <- get -- get prover state 
   let cntSat1 = countSat pst1
       cntAdd1 = countAdd pst1
   case res1 of
      (_ , End) ->  return res1
      (CountSat, Continue)   ->
        do
         loopImpls cntSat0 choices   w0 assumps right 
      (Proved (ass1,der1),Continue) ->
         do
         let  newClause = [ x | x <- ass1, x /= a, x /= b ] :=> [c]
         when( traceLev >= TraceLevel_medium  )(
            sequence_ [  
             liftIO $ putStrLn (printStepIc ltToNm ics0 cntSat0 impl ++
                                  "proved left premise of rule ljt" ),
             liftIO $ putStrLn (printStepIc ltToNm ics0 cntSat0 impl ++
                         "new clause: " ++  printfClause ltToNm newClause ),
             liftIO $ putStrLn ( printStepIc ltToNm ics0 cntSat0  impl ++
                             printR   (cntAdd1 + 1) ++ " = "
                             ++ printR cntAdd1 ++ ", " ++  printfClause ltToNm newClause )
           ]) --end when  
         lift $ addClause sat (c : [ neg x | x <- ass1, x /= a, x /= b  ])
        -- update prover state
         -- newClauses can be duplicated, addElem adds without repetitions
         modify  ( \ s -> s{countAdd = countAdd s + 1, addedCs = addElem newClause  (addedCs s) } )
         when( traceLev >= TraceLevel_medium  )(  
           liftIO $ putStrLn ( printStepIc ltToNm  ics0 cntSat0 impl ++ "prove right premise of rule ljt" )
           ) 
         res2 <- proveMain allImpls assumps right
         pst2 <- get -- get prover state
         let cntSat2 = countSat pst2
         case res2 of
             ( CountSat, _ ) -> do
               when( traceLev >= TraceLevel_medium )(  
                  liftIO $ putStrLn $ inSharps (" END" ++ printStepIc ltToNm ics0 cntSat0 impl ++ "(model) ")
                 ) 
               return res2
             (Proved (ass2,der2),contr2) -> do
                    pst2 <- get -- get prover state
                    let k = indexRootSeq der2
                        cs1 =   getCsSeq $ getRootSeq der1
                        cs2 =   getCsSeq $ getRootSeq der2
                        cs =( union cs1 cs2 )  \\ [newClause] 
                        rootSq = Seq ( k - 1, cs, allImpls, ass2, right)
                        der = RuleImpl (rootSq, der1 , der2, impl,newClause )
                    when( traceLev >= TraceLevel_medium  )(
                      liftIO $ putStrLn $ inSharps (" END"  ++ printStepIc ltToNm ics0  cntSat0 impl
                                                    ++ "(derivation) " )
                      )
                    return ( Proved(ass2,der), contr2 ) 

loopImpls cntSat []  w0 assumps  right  =
 do
  pst <-  get -- get prover state
  let newMod = addWorld w0 (model pst)
      ltToNm = litToName pst
      traceLev = traceLevel pst
  modify ( \ s -> s{model = newMod  }  )
  when( traceLev >= TraceLevel_medium  )(
    liftIO $ putStrLn  $ inSharps (" END [" ++ show cntSat ++  "] (model) " )
    )
  when( traceLev >= TraceLevel_high  )(
     liftIO $ putStrLn  ( printfModel ltToNm newMod )
     )  
  let contr = if (assumps == []  && right == initGoal pst ) then End else Continue
  return (CountSat, contr )

-- #####################################################################


modelValueBool :: Solver -> Lit -> IO Bool
modelValueBool sat x = (Just True ==) `fmap` modelValue sat x


trueAtmsInSat :: Solver -> [Lit] -> IO [Lit]
trueAtmsInSat sat univ =
 do
  vals <- sequence [ (Just True ==) `fmap` modelValue  sat x | x <-  univ  ]
  return  [ x | (x,True) <-  univ `zip` vals ]



inSharps :: String -> String
inSharps str =
  let s = "########" in
  s ++ str ++ s  

indexSeq :: Sequent a -> Int
indexSeq ( Seq(k, cs, ics, xs, q) ) = k

indexRootSeq ::  Derivation a -> Int
indexRootSeq (Axiom sq) = indexSeq sq
indexRootSeq (RuleImpl (sq,der1,der2,ic,c) ) =  indexSeq sq
  




printfAsk :: (Lit -> Name) -> Int -> [ImplClause Lit] -> [Lit]  -> Lit -> String
printfAsk   ltToNm cntSat ics xs  right  =
  let strIcs = if null ics then "" else ", " ++ printfImplClauses ltToNm ics
      strXs = if null xs then "" else ", " ++  printfAtms ltToNm xs
      left =  printR cntSat  ++ strXs
  in   
  "@SAT: " ++ left ++ " |-- " ++ ltToNm right ++ " ?"


printW :: Int -> String
printW k = "M" ++ show k

printR :: Int -> String
printR k = "R" ++ show k



printStep :: Int -> String
printStep k = "[" ++ show k ++ "] "

printStepIc :: (Lit -> Name) -> [ImplClause Lit] ->   Int -> ImplClause Lit -> String
printStepIc  ltToName ics0 k ic =
  "[" ++ show k ++ "][" ++ printfImplClauseWithIndex ltToName ics0 ic ++ "] "




printfState :: (Lit -> Name) -> [ImplClause Lit]  -> Int ->  [Clause Lit] ->  [ImplClause Lit] -> [Lit] -> Lit
               -> String
printfState  ltToNm ics0  cntAdd addedClauses ics xs  goal =
  -- "------------ CURRENT STATE ----------------\n" ++
  "SOLVER: " ++ printR cntAdd ++
  "\nIMPLICATIONS(" ++ show (length ics) ++ "):\n"
  ++ printfImplClausesWithIndex ltToNm  ics0 ics  ++
  "\nASSUMPTIONS: " ++  printfAtms ltToNm  xs ++
  "\nRIGHT ATM: " ++   ltToNm goal ++
  -- "\nADDED CLAUSES: " ++   printfClauses  ltToNm addedClauses ++
  "\n-----------------------------------------"










