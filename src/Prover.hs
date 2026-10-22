{-# LANGUAGE TypeOperators #-}
module Prover (
    proveProblem  -- TraceLevel -> FilePath -> [Clause Name] -> [ImplClause Name] -> GoalName -> IO ()
                  -- prover with trace and derivations/countermodels
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
import System.FilePath
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.RWS

import Types
import MiniSat  --  https://hackage.haskell.org/package/minisat
import WriteLatex
import WriteModelGraphviz
import WriteMakeFile
import Utility





-- Type Lit represents the literals of the SAT-solver language


-- initial setup 
initProblem :: TraceLevel -> FilePath ->  [Clause Name] -> [ImplClause Name] -> GoalName -> IO (ProverEnv,ProverState)
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
      --  Map.lookup :: Ord k => k -> Map.Map k a -> Maybe a
      ltToNm y = fromJust $ Map.lookup y ltToNm_map -- :: Lit -> Name
      falseLit = nmToLt false    -- false :: Name (constant)
      --  Map.lookup :: Ord k => k -> Map.Map k a -> Maybe a
  when( elem false names )( -- add "not false" to the sat solver
       sequence_ [ addClause sat [ neg  (nmToLt false)  ]  ] -- false :: Name (constant)
     )
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
  let proverEnv = mkProverEnv file  univ csLit icsLit (nmToLt goal) ltToNm_map (length names)  traceLev
      initialProverState =  mkProverState sat
  return  (proverEnv,initialProverState )



-- ########################################################
-- #######        PROVER  WITH  TRACE              ########
-- ########################################################

proveProblem :: TraceLevel -> FilePath -> [Clause Name] -> [ImplClause Name] -> GoalName -> IO ()
-- (cs,ics,goal): problem to solve in clausal form
proveProblem traceLev file cs ics goal  = 
 do
  let baseName = takeBaseName file
  (proverEnv,initialProverState)  <- initProblem traceLev baseName cs ics goal
  ( res,finalProverState, _) <-  runRWST  proveMain  proverEnv  initialProverState  
  let  addedClauses = addedCs finalProverState
       traceName =  "trace_"  ++ baseName
       derName= "derivation_"  ++ baseName
       modelName= "model_"  ++ baseName
       dirName = "out-" ++ baseName
       texTraceFile = combine dirName (addExtension traceName ".tex")
       texDerFile = combine dirName (addExtension derName ".tex")
       gvFile =  combine dirName (addExtension modelName ".gv")
       makeFile = combine dirName  "Makefile"
       msgMake = (concat $ replicate  80 "*") ++
                 "\n---> Output files are in the directory '" ++    dirName  ++ "'" ++
                 "\n---> Move into directory '" ++ dirName ++ "' and run command 'make' to compile them" 
  case res of
       Valid  ->  -- valid
         do
           putStrLn "+++ RESULT: Valid (intuitionistically)"
           putStrLn ( writeStatistics  proverEnv finalProverState )
           when (countRest finalProverState > 0 &&  traceLev >= TraceLevel_medium )(
             putStrLn $ "Size (number of worlds) of the generated models: "
                 ++ show (reverse (modelsSize finalProverState)) 
            ) -- end when 
           ( when(traceLev >= TraceLevel_high_with_latex) $
             do
               createDirectoryIfMissing True dirName  
               writeFile texTraceFile (writeLatexTrace  proverEnv finalProverState)
               writeFile texDerFile (writeLatexDerivation proverEnv finalProverState)  
               writeFile makeFile (writeMakeFile_valid traceName derName)
               putStrLn msgMake
            ) -- end when
       CountSat ->
         do
           putStrLn "+++ RESULT: CounterSatisfiable (intuitionistically)"
           putStrLn ( writeStatistics  proverEnv finalProverState )
           when ( traceLev >= TraceLevel_medium )(
             putStrLn $ "Size (number of worlds) of the generated models: "
                 ++ show (reverse (modelsSize finalProverState)) 
            ) -- end when
           ( when (traceLev >= TraceLevel_high_with_latex) $
             do
                createDirectoryIfMissing True dirName             
                writeFile texTraceFile (writeLatexTrace proverEnv finalProverState)
                writeFile gvFile (writeModelGraphviz proverEnv finalProverState )
                writeFile makeFile (writeMakeFile_countsat traceName modelName)
                putStrLn msgMake
            ) -- end when


proveMain :: ProverConf SearchResult 
proveMain  =
-- main loop 
-- In (S3), the new world is adder to the empty model (thus, STEP (S1) is skipped)
  do
    env <- ask  -- get prover environment
    pst <- get  -- get prover state
    let sat = solver pst
        ics =  initImplClauses env
        goal =   initGoal env
        ltToNm = litToName env
        cntSat = countSat pst
        cntRest =  countRest pst
        traceLev = traceLevel env
        step_askSatR = AskSatR(cntSat,cntRest, goal)
    when( traceLev >= TraceLevel_high )(    
       liftIO $ putStrLn $ printStep (cntSat + 1 ) ++ printfAsk ltToNm  Nothing cntRest goal
       ) -- end when
     -- @SAT:  SAT |-- goal ?     
    isSat <- lift $ solve sat [ neg goal]  --  solve :: Solver -> [Lit] -> IO Bool
    -- update prover state
    modify ( \ s -> s{countSat = countSat s + 1 }  )
    when( traceLev >= TraceLevel_high )(
       modify ( \ s -> s{trace = addStep step_askSatR  (trace s) } ) )
    if isSat then
     -- found a classical model M such that goal \not\in M 
     -- trueAtoms = atoms in M
     do
        -- ### STEP (S3) ##
        -- start inner loop
        -- Note that the new world is added to the empty model
         trueAtms <- lift $ trueAtmsInSat sat (universe env) 
         let wk = cntSat  - cntRest -- index of the new world
             newWorld = mkWorld wk trueAtms  
             newModel = addWorld newWorld emptyModel
             step_foundW = NewWorld(wk,trueAtms)
             icsToCheck = [ ic | ic@((a:->b):->c) <- ics,
                              not (elem a trueAtms),  not (elem b trueAtms), not (elem c trueAtms) ]
              -- icsToCheck : (a->b)->c in ics such that  a \not\in M  and b \not\in M and c \not\in M
             newWorldRec = mkWorldRec newWorld icsToCheck 
         modify ( \ s -> s{model = newModel} )
         ( when( traceLev >= TraceLevel_high ) $
           do
             modify ( \s -> s{trace = addStep step_foundW (trace s) } )
             liftIO $  putStrLn  $ ">>> NO( " ++ printfAtmsBrace ltToNm trueAtms ++ " )"
             liftIO $ putStrLn $ printfAddedWorld ltToNm cntSat newWorld  newModel 
           ) -- end when
         innerLoop_S4 [ newWorldRec ] -- continue inner loop from step (S4)
       else
      --  the answer is Yes({}), thus  SAT |-- goal
      --  (cs,ics,goal) is Valid
        do 
          -- update prover state
          modify ( \ s -> s{isValidForm = True  }  )
          let  step_valid =  ProvedSat(cntRest,[], goal )
          when( traceLev >= TraceLevel_medium )(
              modify( \ s -> s{modelsSize =  sizeModel (model s) : (modelsSize s)} )
             ) -- end when
          ( when( traceLev >= TraceLevel_high ) $
            do
               liftIO $ putStrLn $ ">>> YES( {} )"   
               modify ( \ s -> s{trace = addStep step_valid (trace s)} )
            ) -- end when
          return  Valid    


innerLoop_S4 :: [ WorldRec Lit ]  -> ProverConf SearchResult 
-- Inner loop from step (S4) (selection of a pair <w, (a:->b):-> c> )

{-
  The argument is a list [ wRec1,  wRec2,  .... ]   

For every element

  wRec = {  world = w , toCheck = ics , checked = icsChecked} 

in the list we assume that:

1)  ics U icsChecked is the set of *all* the impl. clauses (a:->b):->c such that  a\not\in w and  b\not\in w and  c\not\in w
2)  For every    (a:->b):->c in icsChecked there is a world w' in the current model such that:

     w < w' and  a \in w' and b \not \in w'

   Thus w |> (a:->b):->c ( i.e., w realizes (a:->b):-> c )

-}

innerLoop_S4 [ ] =
-- no more impl. clauses to check, a countermel has been found 
 do 
  env <- ask  -- get prover environment
  let traceLev = traceLevel env
  when( traceLev >= TraceLevel_medium )(
     modify( \ s -> s{modelsSize =  sizeModel (model s) : (modelsSize s)} )
   ) -- end when
  return CountSat


innerLoop_S4 (  worldRec : worldRecs ) |  emptyToCheck worldRec =
--  all the impl. clauses in  worldRec have been checked, continue with the other worldRecs                                       
  innerLoop_S4 worldRecs


innerLoop_S4  ( worldRec  : worldRecs )  =
-- worldRec contains at least one impl. clause  to be checked
-- We check the first ic = (a:->b):->c  in toCheck
  do
   env <- ask   -- get prover environment 
   pst0 <- get  -- get prover state
   let sat = solver pst0
       cntSat =  countSat pst0
       cntRest = countRest pst0
       ltToNm = litToName env
       traceLev = traceLevel env
       w = world worldRec
       ((a:->b):->c) : ics  = toCheck worldRec  -- never fails!
   if not $ forcesImpl (a :-> b) w  (model pst0)     then
   --  there is a world w' such that w < w' and  a \in w' and b\not\in w'
   --  thus (a:->b):->c is checked (it is moved to the checked list by nextToCheck)
   --  Continue by checking the next ic for the current w   
        innerLoop_S4 ( nextToCheck worldRec  : worldRecs)
   else
   --  select the pair < w, (a:->b):->c > (STEP (S4))
   --  try to add a new world w' such that w < w' and  a \in w' and b\not\in w'
     do
      let step_selected = Check(getWIndex w,  ((a:->b):->c) )
      ( when ( traceLev >= TraceLevel_high ) $
        do
          modify  ( \ s ->s{ trace = addStep  step_selected  (trace s) } )
          liftIO $ putStrLn (   "Selected: < " ++
             printW  (getWIndex w)  ++ ", " ++  printfImplClause ltToNm   ((a:->b):->c)  ++ " >" )
          liftIO $ putStrLn $ "========================================"   
          liftIO $ putStrLn $  printStep (cntSat + 1) ++  printfAsk ltToNm ( Just (  ((a:->b):->c)  , getWIndex w))  cntRest b  
       ) -- end when
      innerLoop_S5 ( worldRec : worldRecs ) -- continue internal loop from (S5)
    

innerLoop_S5 :: [WorldRec Lit] -> ProverConf SearchResult 
innerLoop_S5  ( worldRec : worldRecs ) =
-- run inner loop from step (S5)
-- Let w be the world in  worldRec and (a->b)->c the first ic in the to check list
--  < w, (a:->b):->c > is the pair selected in (S4)
  do
    env <- ask  -- get prover environment
    pst <- get  -- get prover state
    let sat = solver pst
        ltToNm = litToName env
        cntSat = countSat pst
        cntRest =  countRest pst
        w = world worldRec
        ((a:->b):->c) : ics  = toCheck worldRec
        icsChecked = checked worldRec
        traceLev = traceLevel env
        step_askRW =  AskSatRW(cntSat,cntRest,  getWIndex w, a, b)
    -- @SAT:  SAT, w , a |-- b ?     
    isSat <- lift $ solve sat ( neg b : a : getWAtms w ) --  solve :: Solver -> [Lit] -> IO Bool
    -- update prover state
    modify ( \ s -> s{countSat = countSat s + 1 })
    when( traceLev >= TraceLevel_high )(
       modify (  \ s -> s {trace = addStep step_askRW (trace s) } )
       ) -- end when 
    if isSat then  -- No(M)
    -- found a classical model M of 'SAT \cup w \cup {a}' such that b \not\in M
    -- M generates a new world
    -- trueAtoms = atoms in M
       do
         -- ## STEP (S3) ##
         trueAtms <- lift $ trueAtmsInSat sat (universe env)
         let icsToCheck = [ ic | ic@((a':->b'):->c') <- ics ++ icsChecked,
                              not (elem a' trueAtms),  not (elem b' trueAtms), not (elem c' trueAtms) ]
             -- icsToCheck : (a':->b'):->c' in ics U icsChecked such that  a' \not\in M  and b' \not\in M and c' \not\in M
             -- Note that we have to consider ic U icsChecked (namely, *all* the ic selected when w has been created)
             wk = cntSat  - cntRest -- index of the new world
             newWorld = mkWorld wk trueAtms  
             newModel = addWorld newWorld (model pst)
             step_foundW = NewWorld(wk,trueAtms)
         -- update prover state
         modify ( \ s -> s{model = newModel}  )
         ( when( traceLev >= TraceLevel_high ) $
           do
             -- update prover state
             modify ( \ s -> s{trace = addStep step_foundW (trace s) } )
             liftIO $ putStrLn $ ">>> NO( " ++ printfAtmsBrace ltToNm trueAtms ++ " )" 
             liftIO $ putStrLn $ printfAddedWorld ltToNm cntSat newWorld  newModel 
             ) -- end when
         -- new iteration of the inner loop
         -- (a:->b) :-> c has been checked (it is moved to checked by nextToCheck)
         innerLoop_S4  ( mkWorldRec newWorld icsToCheck : nextToCheck worldRec :  worldRecs)  
     else
       -- The answer is Yes(assumps), where assumps\subseteq w U {a}
       -- thus  SAT, assumps |-- b 
       do
       -- ## STEP (S6) ## 
       -- compute assumps
        xs <- lift $ conflict sat   -- conflict :: Solver -> IO [Lit] 
        -- Let xs = x1, ... , xn, then:
        -- SAT |--   x1 | ... | xn and b is one of the xs
        let assumps =  map neg ( xs \\ [b] )
            -- assumps = ~x such that x \in xs and x <> b
            newClause = [ x | x <- assumps, x /= a  ] :=> [ c]
            step_proved =  ProvedSat(cntRest,  assumps, b )
        ( when( traceLev >= TraceLevel_high ) $
          do
            -- update prover state  
            modify ( \ s -> s{trace = addStep step_proved (trace s)  }) 
            liftIO $ putStrLn $ ">>> YES( " ++  printfAtmsBrace ltToNm assumps   ++    " )"       
          ) -- end when  
        addNewClause_and_restart newClause  
  

addNewClause_and_restart :: Clause Lit -> ProverConf  SearchResult 
addNewClause_and_restart  newClause =
-- main loop from STEP (S5)
-- newClause is the learned clause to be added to the sat solver  
  do
    env <- ask  -- get prover environment
    pst <- get  -- get prover state
    let sat = solver pst
        cntSat =  countSat pst
        cntRest = countRest pst
        ltToNm = litToName env
        traceLev = traceLevel env
        step_newc = NewClause(cntSat, cntRest,newClause)
    lift $ satAddClause sat  newClause 
            -- update prover state
    modify( \ s -> s{
              countRest = countRest pst + 1,
              addedCs =  newClause : addedCs s,
              modelsSize =  sizeModel (model s) : (modelsSize s)
             })
    ( when( traceLev >= TraceLevel_high ) $
      do
         -- update prover state
        modify  ( \ s -> s{trace = addStep step_newc (trace s) } ) 
        liftIO $ putStrLn  $   "new clause:\n" ++  printfClause ltToNm newClause 
        liftIO $ putStrLn $ printR   (cntRest + 1) ++ " = " ++ printR cntRest ++ ", " ++  printfClause ltToNm newClause 
        liftIO $ putStrLn ( "###########  RESTART " ++ show (cntRest + 1)  ++
                          "  ###########" )
       )-- end when
    proveMain -- ## RESTART 
   
-- #############################################################à


writeStatistics :: ProverEnv -> ProverState -> String
writeStatistics env pst =
  let mod =
        if (isValidForm pst) then "" else
          "\nWorlds in the countermodel: " ++ show ( sizeModel (model pst) )
  in 
  "Flat  clauses: " ++ show ( length (initClauses env) )  
  ++ "\nImpl. clauses: " ++ show ( length (initImplClauses env) )
  ++ "\nAtoms: " ++ show ( length (universe env) )
  ++ "\nCalls to the SAT-solver: " ++ show ( countSat pst ) 
  ++ "\nRestarts: " ++  show (countRest pst)
  ++ mod




printfAsk :: (Lit -> Name) -> Maybe(ImplClause Lit,Int) -> Int -> Lit -> String
printfAsk   ltToNm appliedRule cntRest right  =
  let left = case appliedRule of
        Nothing -> ""
        Just((a :-> b) :->c ,k ) -> ", " ++ printW k ++ ", " ++ ltToNm a
  in
  "@SAT: " ++ printR  cntRest  ++  left ++ " |-- " ++ ltToNm right ++ " ?" 
   -- "\n-------  CURRENT STATE ----------" ++
   -- "\nASSUMPTIONS: " ++   printfAtms ltToNm assumps ++  --show  ( map  ltToNm  assumps) ++
   -- "\nRIGHT: " ++  ltToNm  right ++
   -- "\nIMPL: " ++ printfImplClauses  ltToNm  impls  ++
   -- "\nADDED CLAUSES: " ++   printfClauses   ltToNm addedClauses ++
   -- "\nMODEL: " ++   printfModel   ltToNm  mod ++
   --"\n--------------------------------"


printW :: Int -> String
printW k = "W" ++ show k

printR :: Int -> String
printR k = "R" ++ show k



printStep :: Int -> String
printStep k = "[" ++ show k ++ "] "

printfAddedWorld :: (a -> Name) ->  Int -> World a -> Model a -> String
printfAddedWorld ltToNm cntSat newW newM =
         "New world:\n" ++  printfWorld ltToNm newW ++ "\n"
          ++  "Current model:\n" ++ printfModel ltToNm newM

















