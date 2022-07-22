{-# LANGUAGE TypeOperators #-}
module Prover (
  proveProblemPlain,  -- plain prover 
  proveProblem        -- prover with trace and derivations/countermodels
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


import Types
import MiniSat  --  https://hackage.haskell.org/package/minisat
import WriteLatex
import WriteModelGraphviz
import WriteMakeFile
import Utility


data Control = End | Continue
  deriving Eq

data Result a = CountSat | Proved [a] 
type SearchResult a = (Result a, Control)

-- Type Lit represents the literals of the SAT-solver language



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
            countAtms = length names,
            countSat = 0,
            countRest = 0,
            addedCs = [],
            model = emptyModel,
            modelsSize = [],
            trace = emptyTrace,
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
  ( (res,_),finalProverSt) <-  runStateT  proveMain initialProverSt
  let addedClauses = addedCs finalProverSt
  -- deleteSolver $ solver  finalProverSt
  let  traceName =  "trace_"  ++ baseName
       derName= "derivation_"  ++ baseName
       modelName= "model_"  ++ baseName
       dirName = "out-" ++ baseName
       texTraceFile = combine dirName (addExtension traceName ".tex")
       texDerFile = combine dirName (addExtension derName ".tex")
       gvFile =  combine dirName (addExtension modelName ".gv")
       makeFile = combine dirName  "Makefile"
       msgMake = concatN 80 "*" ++
                 "\n---> Output files are in the directory '" ++    dirName  ++ "'" ++
                 "\n---> Move into directory '" ++ dirName ++ "' and run command 'make' to compile them" 
  case res of
       Proved _  ->  -- valid
         do
           putStrLn "+++ RESULT: Valid (intuitionistically)"
           putStrLn ( writeStatistics finalProverSt )
           when (countRest finalProverSt > 0 &&  traceLev >= TraceLevel_medium )(
             putStrLn $ "Size (number of worlds) of the generated models: "
                 ++ show (reverse (modelsSize finalProverSt)) 
            ) -- end when 
           when(traceLev >= TraceLevel_high_with_latex)(
             sequence_ [
               createDirectoryIfMissing True dirName,  
               writeFile texTraceFile (writeLatexTrace  finalProverSt),
               writeFile texDerFile (writeLatexDerivation  finalProverSt),  
               writeFile makeFile (writeMakeFile_valid traceName derName),
               putStrLn msgMake
            ]) -- end when
       CountSat ->
         do
           putStrLn "+++ RESULT: CounterSatisfiable (intuitionistically)"
           putStrLn ( writeStatistics finalProverSt )
           when ( traceLev >= TraceLevel_medium )(
             putStrLn $ "Size (number of worlds) of the generated models: "
                 ++ show (reverse (modelsSize finalProverSt)) 
            ) -- end when
           when(traceLev >= TraceLevel_high_with_latex)(
             sequence_ [
                createDirectoryIfMissing True dirName,             
                writeFile texTraceFile (writeLatexTrace finalProverSt),
                writeFile gvFile (writeModelGraphviz finalProverSt ),
                writeFile makeFile (writeMakeFile_countsat traceName modelName),
                putStrLn msgMake
            ]) -- end when

writeStatistics :: ProverState -> String
writeStatistics pst =
  let mod =
        if (isValidForm pst) then "" else
          "\nWorlds in the countermodel: " ++ show ( sizeModel (model pst) )
  in 
  "Flat  clauses: " ++ show ( length (initClauses pst) )  
  ++ "\nImpl. clauses: " ++ show ( length (initImplClauses pst) )
  ++ "\nAtoms: " ++ show ( length (universe pst) )
  ++ "\nCalls to the SAT-solver: " ++ show ( countSat pst ) 
  ++ "\nRestarts: " ++  show (countRest pst)
  ++ mod

proveMain :: StateT ProverState IO (SearchResult Lit)
-- main loop of proof search
proveMain =
  do
    pst <- get  -- get prover state
    let sat = solver pst
        ics =  initImplClauses pst
        goal =   initGoal pst
        ltToNm = litToName pst
        cntSat = countSat pst
        cntRest =  countRest pst
        traceLev = traceLevel pst
        step_askSatR = AskSatR(cntSat,cntRest, goal)
    when( traceLev >= TraceLevel_high )(    
       liftIO $ putStrLn $ printStep cntSat ++ printfAsk ltToNm  Nothing cntRest goal
       ) -- end when 
    isSat <- lift $ solve sat [ neg goal]  --  solve :: Solver -> [Lit] -> IO Bool
    -- update prover state
    modify ( \ s -> s{countSat = countSat s + 1 }  )
    when( traceLev >= TraceLevel_high )(
       modify ( \ s -> s{trace = addStep step_askSatR  (trace s) } ) )
     -- @SAT:  SAT |-- goal ?   
    if isSat then
     -- found a classical model M of SAT  such that goal \not\in M 
     -- trueAtoms = atoms in M
     do
         trueAtms <- lift $ trueAtmsInSat sat (universe pst) 
         let wk = cntSat  - cntRest -- index of the new world
             newWorld = mkWorld wk trueAtms  
             newModel = addWorld newWorld emptyModel
             step_foundW = NewWorld(wk,trueAtms)
             icsToCheck = [ ic | ic@((a:->b):->c) <- ics,
                              not (elem a trueAtms),  not (elem b trueAtms), not (elem c trueAtms) ]
         -- icsToCheck : (a->b)->c in ics such that  a \not\in M  and b \not\in M and c \not\in M
         modify ( \ s -> s{model = newModel} )
         when( traceLev >= TraceLevel_high )(
          sequence_ [
           modify ( \s -> s{trace = addStep step_foundW (trace s) } ),
           liftIO $  putStrLn  $ ">>> NO( " ++ printfAtmsBrace ltToNm trueAtms ++ " )",
           liftIO $ putStrLn $ printfAddedWorld ltToNm cntSat newWorld  newModel
           -- liftIO $ putStrLn ( "ICS to check (Main)\n" ++   printfImplClauses  ltToNm  icsToCheck )  
           ]) -- end when
         loopImpls [ (newWorld,icsToCheck) ] -- inner loop
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
          when( traceLev >= TraceLevel_high )(
           sequence_[
               liftIO $ putStrLn $ ">>> YES( {} )"   , 
               modify ( \ s -> s{trace = addStep step_valid (trace s)} )
           ]) -- end when
          return ( Proved [],End )    

loopImpls :: [(World Lit,[ImplClause Lit])]  -> StateT ProverState IO (SearchResult Lit)
-- Inner loop
--  The argument is a list of the form
--      [(w1,ics1), (w2,ics2) .... ]   // choice list
--  Let  (w',ics') be  an element in the list and let  (a->b)->c in ics'.
--   We *assume* that   a\not\in w' and  b\not\in w' and  c\not\in w'
--   We check whether the current model contains a world  w'' such that w' < w'' and   a\in w'' and  b\not\in w'' 
--  If this is the case, a new world must be generated

loopImpls [(w,[])] =
-- no more choices, a countermel has been found and proof search ends
 do 
  pst <- get  -- get prover state
  let traceLev = traceLevel pst
  when( traceLev >= TraceLevel_medium )(
     modify( \ s -> s{modelsSize =  sizeModel (model s) : (modelsSize s)} )
   ) -- end when
  return (CountSat, End )


loopImpls ( (w,[]) : choices ) =  loopImpls choices
-- no more choiches for w, continue with the choices for other worlds

loopImpls  ( (w, impl@((a:->b):->c) :impls) : choices )  =  
  do
   pst0 <- get  -- get prover state
   let sat = solver pst0
       cntSat =  countSat pst0
       cntRest = countRest pst0
       ltToNm = litToName pst0
       traceLev = traceLevel pst0
   if not $ forcesImpl (a :-> b) w  (model pst0)     then
   --  there is a world w' such that w < w' and  a \in w' and b\not\in w'
   --  thus (w,impl) is not selected 
   --  Continue by checking the remaining impls for the current w   
      loopImpls ((w,impls) : choices)
   else
   --  select the pair < w, impl=(a->b)->c) >
   --  try to add a new world w' such that w < w' and  a \in w' and b\not\in w'
     do
      let step_selected = Check(getWIndex w, impl )
      when( traceLev >= TraceLevel_high )(
       sequence_ [
        -- update prover state
        modify  ( \ s ->s{ trace = addStep  step_selected  (trace s) } ),
        liftIO $ putStrLn ( printStep (cntSat - 1 ) ++  "Selected: < " ++
           printW  (getWIndex w)  ++ ", " ++  printfImplClause ltToNm impl ++ " >" ),
        liftIO $ putStrLn $ "========================================",   
        liftIO $ putStrLn (printStep cntSat ++
                printfAsk ltToNm ( Just (impl, getWIndex w))  cntRest b  )
       ]) -- end when
      res1 <-  loopImpls_aux ( (w, impl : impls) : choices ) -- continue internal loop
      case res1 of
        (_, End) ->  return res1 -- a solution to the input problem has already been found
        ( CountSat, Continue )   -> loopImpls  ((w,impls) : choices)  
        ( Proved assumps ,Continue ) ->
        --  SAT , assumps |-- b
            do
            let newClause = [ x | x <- assumps, x /= a  ] :=> [ c]
                step_newc = NewClause(cntSat, cntRest,newClause)
            lift $ addClause sat (c : [ neg x | x <- assumps, x /= a, x /= b  ])
            -- update prover state
            modify( \ s -> s{
                     countRest = cntRest + 1,
                     addedCs =  newClause : addedCs s,
                     modelsSize =  sizeModel (model s) : (modelsSize s)
                })
            when( traceLev >= TraceLevel_high )(
             sequence_[
              -- update prover state
              modify  ( \ s -> s{trace = addStep step_newc (trace s) } ), 
              liftIO $ putStrLn  $ printStep cntSat ++  "new clause: " ++  printfClause ltToNm newClause ,
              liftIO $ putStrLn ( printStep cntSat ++   printR   (cntRest + 1) ++ " = "
                ++ printR cntRest ++ ", " ++  printfClause ltToNm newClause ),
              liftIO $ putStrLn ( "###########  RESTART " ++ show (cntRest + 1)  ++
                              "  ###########" )
              ])-- end when
            proveMain   -- restart


loopImpls_aux :: [(World Lit,[ImplClause Lit])] -> StateT ProverState IO (SearchResult Lit)
loopImpls_aux ( (w, (a:->b):->c : ics) : choices)  =
-- run inner loop from step (S5)
-- < w, impl=(a->b)->c > is the pair selected in (S4)
-- ics: implClauses to be checked for w
-- choices: other possible choices  
  do
    pst <- get  -- get prover state
    let sat = solver pst
        ltToNm = litToName pst
        cntSat = countSat pst
        cntRest =  countRest pst
        traceLev = traceLevel pst
        step_askRW =  AskSatRW(cntSat,cntRest,  getWIndex w, a, b)
    -- @SAT:  SAT, w , a |-- b ?     
    isSat <- lift $ solve sat ( neg b : a : getWAtms w ) --  solve :: Solver -> [Lit] -> IO Bool
    -- update prover state
    modify ( \ s -> s{countSat = countSat s + 1 })
    when( traceLev >= TraceLevel_high )(
       modify (  \ s -> s {trace = addStep step_askRW (trace s) } ) ) 
    if isSat then  -- No(M)
    -- found a classical model M of 'SAT \cup w \cup {a}' such that b \not\in M
    -- M generates a new world
    -- trueAtoms = atoms in M
       do
         trueAtms <- lift $ trueAtmsInSat sat (universe pst)
         let icsInit =  initImplClauses pst
             icsToCheck = [ ic | ic@((a':->b'):->c') <- icsInit,
                              not (elem a' trueAtms),  not (elem b' trueAtms), not (elem c' trueAtms) ]
             -- icsToCheck : (a'->b')->c' in icsInit such that  a' \not\in M  and b' \not\in M and c' \not\in M
             wk = cntSat  - cntRest -- index of the new world
             newWorld = mkWorld wk trueAtms  
             newModel = addWorld newWorld (model pst)
             step_foundW = NewWorld(wk,trueAtms)
         -- update prover state
         modify ( \ s -> s{model = newModel}  )
         when( traceLev >= TraceLevel_high )(
           sequence_[
             -- update prover state
             modify ( \ s -> s{trace = addStep step_foundW (trace s) } ),
             liftIO $ putStrLn $ ">>> NO( " ++ printfAtmsBrace ltToNm trueAtms ++ " )" ,
             liftIO $ putStrLn $ printfAddedWorld ltToNm cntSat newWorld  newModel ,
             liftIO $ putStrLn ( "ICS to check (loop)\n" ++   printfImplClauses  ltToNm  icsToCheck ) 
             ])   -- end when
         loopImpls  (( newWorld, icsToCheck) : (w,ics) : choices ) -- new iteration of the inner loop
       else
       -- The answer is Yes(assumps), where assumos\subseteq w \cup {a}
       -- thus  SAT, assumps |-- b 
       do
       -- compute assumps
        xs <- lift $ conflict sat   -- conflict :: Solver -> IO [Lit] 
        -- Let xs = x1, ... , xn, then:
        -- SAT |--   x1 | ... | xn and b is one of the xs
        let assumps =  map neg ( xs \\ [b] )
        -- assumps = ~x such that x \in xs and x <> b
            step_proved =  ProvedSat(cntRest,  assumps, b )
        when( traceLev >= TraceLevel_high )(
           sequence_[
             -- update prover state  
            modify ( \ s -> s{trace = addStep step_proved (trace s)  }), 
            liftIO $ putStrLn $ ">>> YES( " ++  printfAtmsBrace ltToNm assumps   ++    " )"       
          ])  
        return ( Proved assumps,Continue )    
     



-- #########################################################
-- #####        PLAIN PROVER  (NO TRACE)               #####
-- #########################################################


proveProblemPlain :: FilePath -> [Clause Name] -> [ImplClause Name] -> Name -> IO ()
proveProblemPlain file cs ics goal  = 
 do
  initialProverSt  <- initProblem NoTrace file cs ics goal
  let icsLit = initImplClauses initialProverSt
      goalLit = initGoal initialProverSt
  ( (res,_),finalProverSt) <-  runStateT  proveMainPlain initialProverSt
  -- putStrLn ""
  -- deleteSolver $ solver  finalProverSt
  case res of
       Proved _  ->
         do
           putStrLn "+++ RESULT: Valid (intuitionistically)"
       CountSat ->
         do
           putStrLn "+++ RESULT: CounterSatisfiable (intuitionistically)"

proveMainPlain ::  StateT ProverState IO (SearchResult Lit)
-- main loop of proof search
{-
*NOTE*

The function solve of the SAT-solver has type

 solve :: Solver -> [Lit] -> IO Bool

Thus, we cannot eliminate the IO moonad from proverMainPlain 
-}

proveMainPlain =
  do
    pst <- get  -- get prover state
    let sat = solver pst
        ics =  initImplClauses pst
        goal =   initGoal pst
    isSat <- lift $ solve sat [ neg goal]  --  solve :: Solver -> [Lit] -> IO Bool
    -- @SAT:  SAT |-- goal ?   
    if isSat then
     -- found a classical model M of SAT  such that goal \not\in M 
     -- trueAtoms = atoms in M
     do
         trueAtms <- lift $ trueAtmsInSat sat (universe pst) 
         let newWorld = mkWorld 0 trueAtms  -- all worlds have index 0 
             newModel = addWorld newWorld emptyModel
             icsToCheck = [ ic | ic@((a:->b):->c) <- ics,
                              not (elem a trueAtms),  not (elem b trueAtms), not (elem c trueAtms) ]
         -- icsToCheck : (a->b)->c in ics such that  a \not\in M  and b \not\in M and c \not\in M
         modify ( \ s -> s{model = newModel }  )
         loopImplsPlain [ (newWorld,icsToCheck) ] -- inner loop
     else
      --  the answer is Yes({}), thus  SAT |-- goal
      --  (cs,ics,goal) is Valid
      do
         modify ( \ s -> s{isValidForm = True }  )   
         return ( Proved [],End )    
        

        
loopImplsPlain :: [(World Lit,[ImplClause Lit])]  -> StateT ProverState IO (SearchResult Lit)
-- Inner loop

loopImplsPlain [(w,[])] =  return (CountSat, End )
-- no more choices, a countermel has been found and proof search ends

loopImplsPlain ( (w,[]) : choices ) =  loopImplsPlain choices
-- no more choiches for w, continue with the choices for other worlds

loopImplsPlain  ( (w, impl@((a:->b):->c) :impls) : choices )  =  
  do
   pst0 <- get  -- get prover state
   let sat = solver pst0
   if not $ forcesImpl (a :-> b) w  (model pst0)     then
   --  there is a world w' such that w < w' and  a \in w' and b\not\in w'
   --  thus (w,impl) is not selected 
   --  Continue by checking the remaining impls for the current w   
      loopImplsPlain ((w,impls) : choices)
   else
   --  select the pair < w, impl=(a->b)->c) >
   --  try to add a new world w' such that w < w' and  a \in w' and b\not\in w'
     do
      res1 <-  loopImplsPlain_aux ( (w, impl : impls) : choices ) -- continue internal loop
      case res1 of
        (_, End) ->  return res1 -- a solution has already been found
        ( CountSat, Continue )   -> loopImplsPlain  ((w,impls) : choices)  
        ( Proved assumps ,Continue ) ->
        --  SAT , assumps |-- b
            do
             lift $ addClause sat (c : [ neg x | x <- assumps, x /= a, x /= b  ])
             proveMainPlain   -- restart



loopImplsPlain_aux :: [(World Lit,[ImplClause Lit])] -> StateT ProverState IO (SearchResult Lit)
loopImplsPlain_aux ( (w, (a:->b):->c : ics) : choices)  =
-- run inner loop from step (S5)
  do
    pst <- get  -- get prover state
    let sat = solver pst
    -- @SAT:  SAT, w , a |-- b ?     
    isSat <- lift $ solve sat ( neg b : a : getWAtms w ) --  solve :: Solver -> [Lit] -> IO Bool
    if isSat then  -- No(M)
    -- found a classical model M of 'SAT \cup w \cup {a}' such that b \not\in M
    -- M generates a new world
    -- trueAtoms = atoms in M
       do
         trueAtms <- lift $ trueAtmsInSat sat (universe pst)
         let icsInit =  initImplClauses pst
             icsToCheck = [ ic | ic@((a':->b'):->c') <- icsInit,
                              not (elem a' trueAtms),  not (elem b' trueAtms), not (elem c' trueAtms) ]
             -- icsToCheck : (a'->b')->c' in icsInit such that  a' \not\in M  and b' \not\in M and c' \not\in M
             newWorld = mkWorld 0 trueAtms -- all worlds have index 0  
             newModel = addWorld newWorld (model pst)
         -- update prover state
         modify ( \ s -> s{model = newModel} )
         loopImplsPlain  (( newWorld, icsToCheck) : (w,ics) : choices ) -- new iteration of the inner loop
       else
       -- The answer is Yes(assumps), where assumps\subseteq w \cup {a}
       -- thus  SAT, assumps |-- b 
       do
       -- compute assumps
        xs <- lift $ conflict sat   -- conflict :: Solver -> IO [Lit] 
        -- Let xs = x1, ... , xn, then:
        -- SAT |--   x1 | ... | xn and b is one of the xs
        let assumps =  map neg ( xs \\ [b] )
        -- assumps = ~x such that x \in xs and x <> b
        return ( Proved assumps,Continue )    
     



-- #############################################################à



trueAtmsInSat :: Solver -> [Lit] -> IO [Lit]
trueAtmsInSat sat univ =
-- atoms from univ which are true in the solver
  do
  vals <- sequence [ (Just True ==) `fmap` modelValue  sat x | x <-  univ  ]
  -- vals = (x,b) where b=True if x is true in sat, b=False  otherwise 
  return  [ x | (x,True) <-  univ `zip` vals ]

-- modelValue :: Solver -> Lit -> IO (Maybe Bool)



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
         printStep cntSat ++  "Added new world:\n" ++ 
         printStep cntSat ++ printfWorld ltToNm newW ++ "\n" ++
         printStep cntSat ++  "Current model:\n" ++
         printfModel ltToNm newM

















