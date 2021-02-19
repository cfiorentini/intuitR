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
  show TRUE        = true  -- "$true"
  show FALSE       = false -- "$false"



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
     addedCs :: [Clause Lit] ,  -- clauses added to the  SAT-solver (learned clauses)
     countAtms :: Int,   -- count the atoms in (initClauses,initImplClauses,initGoal)
     countSat :: Int,    -- count the calls to the SAT-solver
     countNo :: Int,   -- count the  answers NO(_), used for world indexes
     countAdd :: Int,  -- count the added clauses
     model :: Model Lit,
     traceLevel :: TraceLevel,
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


-- ##################   DERIVATION  ########################à

data Sequent a = Seq(Int, [Clause a], [ImplClause a], [a], a)
instance Functor Sequent where
  fmap f (Seq(k, cs, ics,  xs, right )) =
    Seq(k, map (fmap f) cs ,  map (mapImplClause f) ics , map f xs, f right ) 

 

data Derivation a =
    Axiom( Sequent a )
  | RuleImpl( Sequent a, Derivation a, Derivation a, ImplClause a, Clause a)
  --  RuleImpl(root,left, rightDer, mainForm, newClause )

instance Functor Derivation where
  fmap f (Axiom sq) = Axiom (fmap f sq)
  fmap f (RuleImpl (rootSq, der1, der2,ic,c ) ) =
          RuleImpl (fmap f rootSq, fmap f der1, fmap f der2, mapImplClause f ic, fmap f c )

getRootSeq :: Derivation a -> Sequent a
getRootSeq (Axiom sq) = sq
getRootSeq (RuleImpl (sq, _,_,_,_)) = sq

getCsSeq ::  Sequent a -> [ Clause a]
getCsSeq  (Seq(_, cs, _ , _, _) ) = cs


-- ##################    MODEL  ########################

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
-- add the w world to the model mod
-- Note that w can belong to mod
addWorld w mod =
  let ws = getWorlds mod 
  in
  if  any (POrd.== w) ws then mod  
  else  Mod $  w : ws

emptyModel :: Model a --Lit
emptyModel = Mod []

sizeModel :: Model a -> Int 
sizeModel mod = length ( getWorlds mod)

forcesAt ::  Ord a => a -> World a -> Bool
forcesAt p w   = Set.member p $ getWSetAtms w 

forcesImpl :: Ord a => (a :-> a) -> World a ->  Model a ->   Bool
forcesImpl (p :-> q)  w mod =
  null ( filter ( \w' ->  (POrd.<=) w w' &&  forcesAt p w' && not (forcesAt  q w' ))  (getWorlds mod) )


-- ##################   TRACE LEVELS  ########################à

data TraceLevel =
  NoTrace
  | TraceLevel_low  -- only basic statistics (number of calls to SAT-solver, restarts) 
  | TraceLevel_medium --  
  | TraceLevel_high --  print all the traced information
  | TraceLevel_high_with_latex  -- also generate the tex files
   deriving ( Eq, Ord )


