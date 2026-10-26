{-# LANGUAGE TypeOperators #-}
module ProverPlain (
  proveProblemPlain --  FilePath -> [Clause Name] -> [ImplClause Name] -> GoalName -> IO ()
                    --  plain prover (without trace)

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
import Control.Monad (when)
import Control.Monad.State
import Control.Monad.RWS

import Types
import MiniSat  --  https://hackage.haskell.org/package/minisat
import Utility




-- initial setup
initProblem :: TraceLevel -> FilePath ->  [Clause Name] -> [ImplClause Name] -> Name -> IO (ProverEnv,ProverState)
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



-- #########################################################
-- #####        PLAIN PROVER  (NO TRACE)               #####
-- #########################################################


proveProblemPlain :: FilePath -> [Clause Name] -> [ImplClause Name] -> GoalName -> IO ()
proveProblemPlain file cs ics goal  = 
 do
  (proverEnv,initialProverState)  <- initProblem NoTrace file cs ics goal
  let icsLit = initImplClauses proverEnv
      goalLit = initGoal proverEnv
  ( res,_,_) <-  runRWST  proveMainPlain proverEnv initialProverState
  case res of
       Valid  ->
           putStrLn "+++ RESULT: Valid (intuitionistically)"
       CountSat ->
           putStrLn "+++ RESULT: CounterSatisfiable (intuitionistically)"

proveMainPlain :: ProverConf SearchResult
-- main loop 
-- In (S3), the new world is adder to the empty model (thus, STEP (S1) is skipped)

{-
*NOTE*

The function solve of the SAT-solver has type

 solve :: Solver -> [Lit] -> IO Bool

Thus, we cannot eliminate the IO moonad from proverMainPlain 
-}

proveMainPlain =
  do
    env <-  ask -- get prover environment
    pst <- get  -- get prover state
    let sat = solver pst
        ics =  initImplClauses env
        goal =   initGoal env
    isSat <- lift $ solve sat [ neg goal]  --  solve :: Solver -> [Lit] -> IO Bool
    -- @SAT:  SAT |-- goal ?   
    if isSat then
     -- found a classical model M of SAT  such that goal \not\in M 
     -- trueAtoms = atoms in M
     do
         -- ### STEP (S3) ##
         -- start inner loop
         -- Note that the new world is added to the empty model
         trueAtms <- lift $ trueAtmsInSat sat (universe env) 
         let newWorld = mkWorld 0 trueAtms  -- all the worlds have index 0 
             newModel = addWorld newWorld emptyModel
             icsToCheck = [ ic | ic@((a:->b):->c) <- ics,
                              not (elem a trueAtms),  not (elem b trueAtms), not (elem c trueAtms) ]
         -- icsToCheck : (a->b)->c in ics such that  a \not\in M  and b \not\in M and c \not\in M
             newWorldRec = mkWorldRec newWorld icsToCheck 
         modify ( \ s -> s{model = newModel }  )
         innerLoopPlain_S4 [ newWorldRec ] -- continue inner loop from step (S4)
     else
      --  the answer is Yes({}), thus  SAT |-- goal
      --  (cs,ics,goal) is Valid
      do
         modify ( \ s -> s{isValidForm = True }  )   
         return Valid
        
innerLoopPlain_S4 :: [ WorldRec Lit ]  -> ProverConf SearchResult 
-- Inner loop from step (S4) (selection of a pair <w, (a:->b):-> c> )
{-
  The argument is a list [ wRec1,  wRec2,  .... ]   

For every element

  wRec = {  world = w , toCheck = ics , checked = icsChecked} 

in the list we assume that:

1)  ics U icsChecked is the set of *all* the impl. clauses (a:->b):->c such that  a\not\in w and  b\not\in w and  c\not\in w
2)  For every    (a:->b):->c in icsChecked  there is a world w' in the current model such that:

     w < w' and  a \in w' and b \not \in w'

   Thus w |> (a:->b):->c ( i.e., w realizes (a:->b):-> c )

-}

innerLoopPlain_S4 [ ] =
-- no more impl. clauses to check, a countermel has been found 
  return CountSat


innerLoopPlain_S4 (  worldRec : worldRecs ) |  emptyToCheck worldRec =
--  all the impl. clauses in  worldRec have been checked, continue with the other worldRecs                                       
  innerLoopPlain_S4 worldRecs



innerLoopPlain_S4  ( worldRec  : worldRecs )  =
-- worldRec contains at least one impl. clause  to be checked
-- We check the first ic = (a:->b):->c  in toCheck
  do
   pst0 <- get  -- get prover state
   let sat = solver pst0
       w = world worldRec
       ((a:->b):->c) : ics  = toCheck worldRec  -- never fails!
   if not $ forcesImpl (a :-> b) w  (model pst0)     then
   --  there is a world w' such that w < w' and  a \in w' and b\not\in w'
   --  thus  (a:->b):->c is checked (it is moved to the checked list by nextToCheck)
   --  Continue by checking the next ic for the current w 
        innerLoopPlain_S4  ( nextToCheck worldRec  : worldRecs)
   else 
   --  select the pair < w, (a:->b):->c) >  (STEP (S4))
   --  try to add a new world w' such that w < w' and  a \in w' and b\not\in w'
      innerLoopPlain_S5 ( worldRec : worldRecs ) -- continue internal loop from (S5)

innerLoopPlain_S5 :: [WorldRec Lit] -> ProverConf SearchResult 
innerLoopPlain_S5  ( worldRec : worldRecs ) =
-- run inner loop from step (S5)
-- Let w be the world in  worldRec and (a->b)->c the first ic in the to check list
--  < w, (a:->b):->c > is the pair selected in (S4)
  do
    env <- ask  -- get prover environment
    pst <- get  -- get prover state
    let sat = solver pst
        w = world worldRec
        ((a:->b):->c) : ics  = toCheck worldRec
        icsChecked = checked worldRec
    -- @SAT:  SAT, w , a |-- b ?     
    isSat <- lift $ solve sat ( neg b : a : getWAtms w ) --  solve :: Solver -> [Lit] -> IO Bool
    if isSat then  -- No(M)
    -- found a classical model M of 'SAT \cup w \cup {a}' such that b \not\in M
    -- M generates a new world
    -- trueAtoms = atoms in M
       do
         -- ## STEP (S3) ##
         trueAtms <- lift $ trueAtmsInSat sat (universe env)
         let icsInit = initImplClauses env
             icsToCheck = [ ic | ic@((a':->b'):->c') <-  ics ++ icsChecked,
                              not (elem a' trueAtms),  not (elem b' trueAtms), not (elem c' trueAtms) ]
             -- icsToCheck : (a':->b'):->c' in ics U icsChecked such that  a' \not\in M  and b' \not\in M and c' \not\in M
             -- Note that we have to consider ic U icsChecked (namely, *all* the ic selected when w has been created)
             newWorld = mkWorld 0 trueAtms -- all the worlds have index 0  
             newModel = addWorld newWorld (model pst)
         -- update prover state
         modify ( \ s -> s{model = newModel} )
          -- new iteration of the inner loop
         -- (a:->b) :-> c has been checked (it is moved to checked by nextToCheck)
         innerLoopPlain_S4  ( mkWorldRec newWorld icsToCheck : nextToCheck worldRec :  worldRecs) 
       else
       -- The answer is Yes(assumps), where assumps\subseteq w \cup {a}
       -- thus  SAT, assumps |-- b 
       do
       -- ## STEP (S6)  
       -- compute assumps
        xs <- lift $ conflict sat   -- conflict :: Solver -> IO [Lit] 
        -- Let xs = x1, ... , xn, then:
        -- SAT |--   x1 | ... | xn and b is one of the xs
        let assumps =  map neg ( xs \\ [b] )
            -- assumps = ~x such that x \in xs and x <> b
            newClause = [ x | x <- assumps, x /= a  ] :=> [ c]
        lift $ satAddClause sat  newClause
        proveMainPlain -- ## RESTART 
 













