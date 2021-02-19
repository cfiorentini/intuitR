{-# LANGUAGE TypeOperators #-}
module Types
 where

import MiniSat
import qualified Data.PartialOrd as POrd
import qualified Data.Set as Set

-- ######### FORMULA ##########

type Name = String


false :: Name
false = "$false"


true :: Name
true = "$true"



data Form
  = Atom Name
  | Form :&: Form
  | Form :|: Form
  | Form :=>: Form
  | Form :<=>: Form
  | TRUE
  | FALSE
 deriving ( Eq, Ord )

instance Show Form where
  show (Atom a)    = a
  show (p :&: q)   = "(" ++ show p ++ " & " ++ show q ++ ")"
  show (p :|: q)   = "(" ++ show p ++ " | " ++ show q ++ ")"
  show (p :=>: q)  = "(" ++ show p ++ " => " ++ show q ++ ")"
  show (p :<=>: q) = "(" ++ show p ++ " <=> " ++ show q ++ ")"
  show TRUE        =  true  --- "$true"
  show FALSE       =  false -- "$false"



data a :-> b = a :-> b
  deriving ( Eq, Ord )

instance (Show a, Show b) => Show (a :-> b) where
  show (x :-> y) = "(" ++ show x ++ ") -> (" ++ show y ++ ")"




data Clause a = [a] :=> [a]
   deriving ( Eq, Ord )

instance Functor Clause where
  fmap f (xs :=> ys) = (map f xs) :=> (map f ys)



type ImplClause a = (a :-> a) :-> a

instance (Show a) => Show (Clause a) where
  show (xs :=> ys) = show xs ++ " =>  " ++ show ys


mapImplClause ::  (a -> b) -> ImplClause a -> ImplClause b
mapImplClause f ((a :-> b):-> c) = (f a :->  f b):->  f c 

-- ########  PROVER STATE ####

data ProverState =
  ProverState{
     problemName :: String, -- the name of the problem
     solver :: Solver,   -- the SAT-solver 
     universe :: [Lit],   -- all literals occurring in the solver
     initClauses :: [Clause Lit],  -- initial cs (flat clauses)
     initImplClauses :: [ImplClause Lit],  -- initial ics (implication clauses)
     initGoal ::  Lit, -- main goal
     litToName :: Lit -> Name,   -- maps a Lit to the corresponding atom 
     countAtms :: Int,   -- count the atoms in (initClauses,initImplClauses,initGoal)
     countSat :: Int,    -- count the calls to the SAT-solver
     countRest :: Int,   -- count the restarts
     addedCs :: [Clause Lit] ,  -- clauses added to the  SAT-solver (learned clauses)
     model :: Model Lit,    -- model 
     modelsSize :: [Int], -- list of the size (number of worlds)of the generated models (just before a restart)
     trace :: Trace Lit,  --  trace
     traceLevel :: TraceLevel, -- trace level
     isValidForm :: Bool -- True iff the input formula is valid
  }

initGoalName :: ProverState ->  Name
initGoalName gst = ltToNm $ initGoal gst
 where  ltToNm = litToName gst 

initClausesName :: ProverState ->  [Clause Name]
initClausesName gst = map (fmap ltToNm) (initClauses gst) 
   where  ltToNm = litToName gst 

initImplClausesName ::  ProverState ->  [ImplClause Name]
initImplClausesName gst = map (mapImplClause ltToNm)  (initImplClauses gst)
    where  ltToNm = litToName gst 

addedCsName :: ProverState ->  [Clause Name]
addedCsName gst = map (fmap ltToNm) (addedCs gst) 
   where  ltToNm = litToName gst 

-- ##################    MODEL  ########################à

data World a = Wd(Int, Set.Set a)
  deriving (Eq, Ord, Show)

fmapWd :: (Ord a ,Ord b) => (a -> b) -> (World a -> World b)
fmapWd  f ( Wd(k, xs) ) = Wd ( k, Set.map f  xs )


mkWorld :: Ord a => Int -> [a] -> World a
mkWorld k atms = Wd( k ,Set.fromList atms )

  
getWIndex :: World a -> Int
getWIndex (Wd(k,_) ) = k
  

getWSetAtms :: World a -> Set.Set a
getWSetAtms (Wd(_,xs)) = xs

getWAtms :: World a -> [a]
getWAtms (Wd(_,xs)) = Set.toList xs


instance Ord a => POrd.PartialOrd (World a)  where
  (<=) (Wd(k1,s1)) (Wd(k2,s2)) = Set.isSubsetOf s1 s2
  (<)  (Wd(k1,s1)) (Wd(k2,s2)) = Set.isProperSubsetOf s1 s2

--data Model a = Mod( Set.Set(  World a ) ) 
data Model a = Mod( [World a ] ) 
  deriving (Show)

fmapMod :: (Ord a ,Ord b) => (a -> b) -> (Model a -> Model b)
fmapMod  f ( Mod ws ) = Mod (  map (fmapWd f)  ws )

isEmptyModel :: Model a -> Bool
isEmptyModel (Mod ws) = null ws

mkModel :: [World a ] -> Model a
mkModel ws = Mod ws

getWorlds ::  Model a -> [World a ] 
getWorlds (Mod ws) = ws



addWorld ::Ord a =>  World a -> Model a -> Model a
addWorld w (Mod ws) = Mod $  w : ws

emptyModel :: Model a --Lit
emptyModel = Mod []

sizeModel :: Model a -> Int 
sizeModel mod = length ( getWorlds mod)

forcesAt ::  Ord a => a -> World a -> Bool
forcesAt p w   = Set.member p $ getWSetAtms w 

forcesImpl :: Ord a => (a :-> a) -> World a ->  Model a ->   Bool
forcesImpl (p :-> q)  w mod =
  null ( filter ( \w' ->  (POrd.<=) w w' &&  forcesAt p w' && not (forcesAt  q w' ))  (getWorlds mod) )


-- ##################   TRACE   ########################à

data TraceLevel =
  NoTrace
  | TraceLevel_low  -- only basic statistics (number of calls to SAT-solver, restarts) 
  | TraceLevel_medium -- also trace the size of generated models 
  | TraceLevel_high --  print all the traced information
  | TraceLevel_high_with_latex  -- also generate the tex files
   deriving ( Eq, Ord )

data TraceStep a =
  Check( Int, ImplClause a )  
  | AskSatR(Int,Int, a )  
  | AskSatRW(Int,Int, Int,a,a )  
  | NewWorld( Int, [a] ) 
  | ProvedSat(Int,[a],a) 
  | NewClause(Int,Int, Clause a) 
{-

Check(k, impl):  check the pair < world_k , impl > 
AskSatR(countSat,countRest, right ):    R_countRest |-- c right ?
AskSatRW(countSat,countRest, k , a, b ):  R_countRest, world_k, a |-- c b ?
NewWorld(k, atms ):  generated a new world of index k from atms  
ProvedSat(countRest,assumps,right) --  R_countRest, assmups |--c  right
NewClause(countSat,countRest, phi) --  phi is anew clauses   

-}

instance Functor TraceStep where
  fmap f (Check(k,ic)) = Check( k ,mapImplClause f ic )
  fmap f  (AskSatR(cntSat,cntRest,right)) = AskSatR (cntSat,cntRest, f right)
  fmap f  (AskSatRW(cntSat,cntRest, wk,a, right)) = AskSatRW (cntSat,cntRest,wk,f a,  f right)
  fmap f (NewWorld (k, xs) ) = NewWorld( k, map f xs)
  fmap f (ProvedSat(k,xs,right)) = ProvedSat(k , map f xs , f right)
  fmap f ( NewClause(cntSat, cntRest,c) ) = NewClause(cntSat,cntRest, fmap f c)


traceName ::  ProverState -> Trace Name
traceName gst = fmap ltToNm (trace gst) 
  where  ltToNm = litToName gst

data Trace a = Trace [TraceStep a]


instance Functor Trace where
  fmap f (Trace steps) = Trace( map (fmap f) steps )

emptyTrace :: Trace a --Lit
emptyTrace = Trace []

addStep :: TraceStep a ->   Trace a -> Trace a
addStep step (Trace steps) = Trace (step: steps) 

addSteps :: [TraceStep a] ->   Trace a -> Trace a
addSteps [] tr = tr
addSteps (s1 :steps) tr =
  addStep s1  (addSteps steps tr)

getSteps :: Trace a -> [TraceStep a]
getSteps (Trace steps) = reverse steps

