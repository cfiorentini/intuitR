{-# LANGUAGE TypeOperators #-}
module Types
 where

import MiniSat
import Data.Maybe
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.RWS

import Data.List
import qualified Data.PartialOrd as POrd
import qualified Data.Set as Set
import qualified Data.Map as Map

-- ######### FORMULA ##########

type Name = String
type GoalName = Name

-- some constant

false :: Name
false = "$false"


true :: Name
true = "$true"

mainGoalName :: Name
mainGoalName = "$goal"

isNewName :: Name -> Bool
isNewName p =
  head p == '$'



data Form a 
  = TRUE
  | FALSE
  | Atom a
  | (Form a) :&: (Form a)
  | (Form a) :|: (Form a)
  | (Form a ) :=>: (Form a)
  | (Form a) :<=>: (Form a)
   deriving ( Eq, Ord )


instance (Show a) =>  Show (Form a) where
  show (Atom a)    = show a
  show (p :&: q)   = "(" ++ show p ++ " & " ++ show q ++ ")"
  show (p :|: q)   = "(" ++ show p ++ " | " ++ show q ++ ")"
  show (p :=>: q)  = "(" ++ show p ++ " => " ++ show q ++ ")"
  show (p :<=>: q) = "(" ++ show p ++ " <=> " ++ show q ++ ")"
  show TRUE        =  true  --- "$true"
  show FALSE       =  false -- "$false"


instance Functor Form where
  fmap g (Atom p)    = Atom (g p)
  fmap g (f1 :&: f2)   = (fmap g f1)  :&:  (fmap g f2 )
  fmap g (f1 :|: f2)   = (fmap g f1)  :|:  (fmap g f2 )
  fmap g (f1 :=>: f2)  = (fmap g f1)  :=>:  (fmap g f2 )
  fmap g (f1 :<=>: f2) = (fmap g f1)  :<=>:  (fmap g f2 )
  fmap g TRUE        =  TRUE
  fmap g FALSE       =  FALSE 


data LogicalOp = NoOp | NegOp | AndOp | OrOp | ImplOp | IffOp 
  deriving Eq

mainLogicalOp :: Form Name-> LogicalOp

mainLogicalOp  f | f == TRUE || f == FALSE = NoOp
mainLogicalOp (Atom _) = NoOp 
mainLogicalOp (f1 :&: f2 ) = AndOp
mainLogicalOp (f1 :|: f2 ) = OrOp
mainLogicalOp (f1 :=>: FALSE ) = NegOp
mainLogicalOp (f1 :=>: Atom f2 ) | f2 == false = NegOp
mainLogicalOp (f1 :=>: f2 ) = ImplOp
mainLogicalOp (f1 :<=>: f2 ) = IffOp



-- used to represent TPTP formulas
data Input a = Input Name FormRole a
 deriving ( Eq, Ord )

instance Show a => Show (Input a) where
  show (Input name role x) =
    "fof(" ++ name ++ ", " ++ show role ++ ", " ++ show x ++ " )."

data FormRole =
  Axiom
  | Conjecture
 deriving ( Eq, Ord )

instance Show FormRole where
  show Axiom       = "axiom"
  show Conjecture = "conjecture"



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


data ClausificationType = WeakClausification | StrongClausification
  deriving Eq

instance Show  ClausificationType where
  show  WeakClausification =  "Weak clausification"
  show  StrongClausification =  "Strong clausification" 

--  SIMPLE FORMULA sf
--  sf ::= (p1 & p2)  ||  (p1 | p2)  ||  (p1 => p2) || (p1 <=> p2 )
--           p1, p2 atoms

data SimpleForm 
  = Name :&&: Name
  | Name :||: Name
  | Name :==>: Name
  | Name :<==>: Name
 deriving ( Eq, Ord, Show )


simpleFormToForm :: SimpleForm -> Form Name
simpleFormToForm (n1 :&&: n2)   = (Atom n1)  :&: (Atom n2)
simpleFormToForm (n1 :||: n2)   = (Atom n1)  :|: (Atom n2)
simpleFormToForm (n1 :==>: n2)  = (Atom n1)  :=>: (Atom n2)
simpleFormToForm (n1 :<==>: n2) = (Atom n1)  :<=>: (Atom n2) 




type Cache = Map.Map Name SimpleForm 

cache_to_nameFormList :: Cache -> [(Name, Form Name)]
cache_to_nameFormList cache =
  map ( \(name,sf ) -> ( name, simpleFormToForm sf) )  (Map.toList cache)

cache_to_sortedNameFormList :: Cache -> [(Name, Form Name)]
cache_to_sortedNameFormList  cache =
  sortOn (indexNewName .fst ) ( cache_to_nameFormList cache)

cacheSize :: Cache -> Int
cacheSize  = Map.size 



indexNewName  :: Name -> Int
-- newName: $p0, $p1, ....
-- $p0 |-> 0,   $p1 |-> 1,  $p10 |-> 10, ...
indexNewName newName =
  -- read $ fromJust $ stripPrefix "$p" newName
  read $ fromMaybe "-1" $ stripPrefix "$p" newName  -- ????????



-- ########  PROVER STATE ####

data SearchResult  = CountSat | Valid 

-- constant fields 
data ProverEnv =
  ProverEnv{
     problemName :: String, -- the name of the problem
     universe :: [Lit],   -- all literals occurring in the solver
     initClauses :: [Clause Lit],  -- initial cs (flat clauses)
     initImplClauses :: [ImplClause Lit],  -- initial ics (implication clauses)
     initGoal ::  Lit, -- main goal
     litToName_map ::  Map.Map Lit  Name ,  -- maps a Lit to the corresponding atom
     countAtms :: Int,   -- count the atoms in (initClauses,initImplClauses,initGoal)
     traceLevel :: TraceLevel -- trace level
  }

mkProverEnv :: String -> [Lit] ->  [Clause Lit] -> [ImplClause Lit] -> Lit -> Map.Map Lit Name -> Int -> TraceLevel -> ProverEnv
mkProverEnv problName univ cs ics goal ltToNm_map cntAtms  traceLev =
   ProverEnv{
            problemName = problName,
            universe = univ,
            initClauses = cs,
            initImplClauses = ics,
            initGoal =  goal,
            litToName_map = ltToNm_map,
            countAtms = cntAtms,
            traceLevel = traceLev
            }


-- fields that can be updated 
data ProverState =
  ProverState{
     solver :: Solver,   -- the SAT-solver 
     countSat :: Int,    -- count the calls to the SAT-solver
     countRest :: Int,   -- count the restarts
     addedCs :: [Clause Lit] ,  -- clauses added to the  SAT-solver (learned clauses)
     model :: Model Lit,    -- model 
     modelsSize :: [Int], -- list of the size (number of worlds)of the generated models (just before a restart)
     trace :: Trace Lit,  --  trace
     isValidForm :: Bool -- True iff the input formula is valid
  }

mkProverState :: Solver  -> ProverState
mkProverState sat   =
   ProverState{
            solver = sat,
            countSat = 0,
            countRest = 0,
            addedCs = [],
            model = emptyModel,
            modelsSize = [],
            trace = emptyTrace,
            isValidForm = False
            }


-- newtype RWST r w s (m :: * -> *) a
-- A monad transformer adding reading an environment of type r, collecting an output of type w and updating a state of type s to an inner monad m.
-- The Writer w is not used 

type ProverConf = RWST ProverEnv () ProverState IO


-- the name of a literal
-- we assume that the literal is defined
litToName ::   ProverEnv -> Lit ->  Name
litToName  env lit =
     fromJust $ Map.lookup lit (litToName_map env)
     
initGoalName :: ProverEnv ->  GoalName 
initGoalName env =
   ltToNm $  initGoal env
   where
     ltToNm =   litToName env   -- > Lit ->  Name

initClausesName :: ProverEnv -> [Clause Name]
initClausesName env  =
  map (fmap ltToNm) (initClauses env)
  where
    ltToNm =   litToName env   -- > Lit ->  Name

initImplClausesName ::  ProverEnv ->   [ImplClause Name]
initImplClausesName env  =
  map (mapImplClause ltToNm) (initImplClauses env)
  where
    ltToNm =   litToName env   -- > Lit ->  Name


addedCsName :: ProverEnv -> ProverState ->  [Clause Name]
addedCsName env pst =
  map (fmap ltToNm ) (addedCs pst) 
    where
    ltToNm =   litToName env   -- > Lit ->  Name

-- ####### INNER LOOP #######
--  record  associated with a world

data WorldRec a =
  WorldRec{
     world ::  World a,         -- world w
     toCheck :: [ImplClause a], -- to be checked 
     checked ::  [ImplClause a]  -- checked (all the ics are realized in w, see the comment below) 
     }


{-  The inner loops works on a list 


      [ wRec1,  wRec2,  .... ]   

For every element

  wRec = {  world = w , toCheck = ics , checked = icsChecked} 

in the list we assume that:

1)  ics U icsChecked is the set of *all* the impl. clauses (a:->b):->c such that  a\not\in w and  b\not\in w and  c\not\in w
2)  For every    (a:->b):->c in icsChecked   there is a world w' in the current model such that:

    w < w' and  a \in w' and b \not \in w'

    This implies that w |>  (a:->b):->c  (namely, w realizes (a:->b):->c)

-}

-- make a new WorlRec with empty  checked list  
mkWorldRec :: World Lit -> [ImplClause Lit] -> WorldRec Lit
mkWorldRec w ics =
  WorldRec{world =  w , toCheck = ics ,  checked = [] } 
         
emptyToCheck ::  WorldRec Lit -> Bool
emptyToCheck wRec = null $ toCheck wRec

-- the first ic in toCheck is moved to the checked list
-- We assume that the toCheck list is not empty
nextToCheck ::  WorldRec Lit -> WorldRec Lit 
nextToCheck (WorldRec{world = w , toCheck = ic : ics , checked = icsChecked} ) =
  WorldRec{world = w , toCheck = ics , checked = ic : icsChecked}



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



traceName ::  ProverEnv -> ProverState -> Trace Name
traceName env pst = fmap (litToName env) (trace pst) 



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



type Substitution = Map.Map Name (Form Name)


applySubst :: Substitution -> Form Name -> Form Name

applySubst subst TRUE = TRUE
applySubst subst FALSE = FALSE

applySubst subst (Atom a) =
  case Map.lookup a subst of
      Just f -> applySubst subst f
      Nothing -> Atom a

applySubst subst (f1 :&: f2) =
  (applySubst subst f1 ) :&: (applySubst subst f2)

applySubst subst (f1 :|: f2) =
  (applySubst subst f1 ) :|: (applySubst subst f2)

applySubst subst (f1 :=>: f2) =
  (applySubst subst f1 ) :=>: (applySubst subst f2)

applySubst subst (f1 :<=>: f2) =
  (applySubst subst f1 ) :<=>: (applySubst subst f2)


cache_to_nameFormSubstList ::  Cache ->   [(Name, Form Name)]
--  list (name,form) such that  form is the formula equivalent to name
cache_to_nameFormSubstList  cache   =
  let nameFormList = cache_to_sortedNameFormList cache
      subst = Map.fromList  nameFormList
  in  map (\(name,form) ->  (name, (applySubst subst form)) ) nameFormList

cache_to_subst  :: Cache   -> Substitution
-- substitution     extracted from the cache
cache_to_subst  = Map.fromList . cache_to_nameFormSubstList  


sortNames ::  [Name] -> [Name]  
sortNames xs =
  let (g,ys) = partition (\x -> x == "$goal") xs
      (newAtms,atms)  =  partition isNewName ys
  in sort atms ++ g ++ sortOn indexNewName newAtms  
  
