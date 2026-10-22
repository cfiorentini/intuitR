{-# LANGUAGE TypeOperators #-}
module ClausifyStrong
  (  clausifyInputForms   -- [Input Form] -> ([Clause Name],[ImplClause Name],GoalName,Int)
  )
 where


import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Control.Monad
import Control.Monad.State

import Types

--  SIMPLE FORMULA sf
--  sf ::= (p1 & p2)  ||  (p1 | p2)  ||  (p1 => p2) || (p1 <=> p2 )
--           p1, p2 atoms
{-

data SimpleForm 
  = Name :&&: Name
  | Name :||: Name
  | Name :==>: Name
  | Name :<==>: Name
 deriving ( Eq, Ord, Show )

-}


-- mkNewName :: Int -> Name
-- make the name of a new atom,  having form "$pk", with k >= 0
mkNewName :: Int -> Name
mkNewName k =  "$p" ++ show k



clausifyInputForms0 :: [Input (Form Name)] ->  ([Clause Name],[ImplClause Name],GoalName,Int,Cache)
--  build the clausification (cs,ics,goal) of the input formula,
--  NO REDUCTION
clausifyInputForms0 inputFs =
  let  (cs0, ics0,cache) = clausifyForms 0 (goalify inputFs)
       cs  =  cs0 ++ [ [b] :=> [c] | (a :-> b ) :-> c <- ics0, b /= false, b /= c ]
  in (cs,ics0,mainGoalName,0,cache)       
-- count: number of reduced implication clauses







clausifyInputForms :: [Input (Form Name)] ->  ([Clause Name],[ImplClause Name],GoalName,Int,Cache)
--  build the clausification (cs,ics,goal) of the input formula,
--  count the number of reduced implication clauses, as defined below 
clausifyInputForms inputFs =
  let  (cs0, ics0,cache) = clausifyForms 0 (goalify inputFs)
       (countImplReductions, cs1,ics) = reduceImplClauses ics0
       cs  =  cs0 ++ cs1 ++ [ [b] :=> [c] | (a :-> b ) :-> c <- ics, b /= false, b /= c ]
  in (cs,ics,mainGoalName,countImplReductions,cache)       
-- count: number of reduced implication clauses




data ClausState =
  ClaussState{
    clausCache :: Map.Map SimpleForm  Name ,  -- map  simple form  |-- name (local cache)
    clausIndex :: Int,    -- index of the next new name 
    clausCs ::  Set.Set (Clause Name),      --  clauses         created during clausification
    clausIcs :: Set.Set (ImplClause Name), --  impl. clauese    created during clausification
    clausCountReducedIcs :: Int
    }         

mkClausState :: Int -> ClausState
mkClausState index =
  ClaussState{
    clausCache  = Map.empty,
    clausIndex = index, 
    clausCs = Set.empty,
    clausIcs = Set.empty,
    clausCountReducedIcs = 0
    }     



clausifyForms ::  Int -> [Form Name] ->   ([Clause Name],[ImplClause Name],Cache)
-- Clausify the input formulas starting new names with index k.
-- Return the pair (cs,ics) corresponding the the computed clauses and inmpl. clauses 
clausifyForms k forms =
  let
    finalClausSt = execState (mclausifyForms forms) (mkClausState k)
    finalCache = clausCache finalClausSt
    -- newIndex = clausIndex finalClausSt 
    cs  = Set.toList $ clausCs finalClausSt 
    ics = Set.toList $ clausIcs  finalClausSt
    -- countReducedIcs = clausCountReducedIcs finalClausSt
  in     
  (cs,ics, invertMap finalCache)       

invertMap :: (Ord a, Ord b) => Map.Map a b -> Map.Map b a
invertMap m =
   Map.fromList $ map swap (Map.toList m )
   where swap(a,b) = (b,a)


mclausifyForms ::  [Form Name] ->  State ClausState ()
-- clausification of a list of formulas
mclausifyForms  fs =
  sequence_ [ clausifyForm (simplify f) | f <- fs ] 




{-

REDUCE IMPLICATION CLAUSES WITH SAME ANTECEDENT

Clauses with the same antecedent are reduced as follows:

 (a:->b):-> c1, ... , (a:->b):-> cn

with n >= 2 is reduced to

   (c1:-> newAtm), .... , (cn:-> newAtm),  (a:->b):-> newAtm

where newAtm is a new propositional variable

-}

reduceImplClauses ::  [ImplClause Name] ->    (Int,[Clause Name], [ImplClause Name])
--  ** Same strategy as ClaessenRosen **
--  Return (tot,cs1,ics1) where:
--  tot: total amount of clauses with the same antecedent
--  cs1: new clauses (ck:-> newAtm) generated during the process
--  ics1:  implication clauses obtained after reduction
--  *NOTE*:  if no implication clauses is reduced, ics1 is in general a permutation of ics 

reduceImplClauses ics =  
  let sames = Map.toList (Map.fromListWith (++) [ (a:->b,[c]) | ((a:->b):->c) <- ics ])
  in evalState ( reduceImplClausesMon sames )  (0,0,[],[])



reduceImplClauses1 ::  [ImplClause Name] ->   IO (Int,[Clause Name], [ImplClause Name])
--  Return (tot,cs1,ics1) where:
--  tot: total amount of clauses with the same antecedent
--  cs1: new clauses (ck:-> newAtm) generated during the process
--  ics1:  implication clauses obtained after reduction
--         If ics does not contain implications to be reduced, then ics1 = ics 
--         (in ClaessenRosen, ics1 is a permutation of ics) 
reduceImplClauses1 ics =  
  do
  let sames = Map.toList (Map.fromListWith (++) [ (a:->b,[c]) | ((a:->b):->c) <- ics ])
  if (any ( \ (a:->b, cs) -> length cs > 2) sames ) then
    -- at least an ic to reduce
    return $ evalState ( reduceImplClausesMon sames )  (0,0,[],[])
  else
   -- nothing to reduce
    return (0,[],ics)

type SameAnt =  ( (Name :-> Name), [Name] )
--    ( (a :->b), [c1,..c_n] ) represent the list of clauses
--   (a:->b):-> c1, ... , (a:->b):-> cn
--   having the same antecedent a:-> b

reduceImplClausesMon :: [SameAnt]
  -> State (Int,Int,[Clause Name],[ImplClause Name])  (Int,[Clause Name], [ImplClause Name])
-- state: next index, number of reduced ics, cs, ics

reduceImplClausesMon [] =
  do 
  (n,count,cs,ics) <- get
  return (count,cs,ics) 

reduceImplClausesMon ( (a :-> b,[c])  : sames) =
  do
  (n,count,cs, ics) <- get
  put (n, count,cs, ((a:->b):-> c) : ics )
  reduceImplClausesMon sames



reduceImplClausesMon ( (a :-> b,xs)  : sames) =
--  length xs >= 2 
  do
  (n,count,cs, ics) <- get
  let k = length cs
      newAtm = "$q" ++ show n
      newCs = [ [newAtm] :=> [x] | x <- xs ]
  put (n + 1, count + k, newCs ++ cs ,  ((a :-> b ) :->  newAtm ) : ics )
  reduceImplClausesMon sames



--------------------------------------------------------

goalify :: [Input (Form Name)] -> [Form Name]
goalify []                            = []
goalify (Input s Axiom f       : inps) = f : goalify inps
goalify (Input s Conjecture f : iforms) =
  case f of
    f1 :=>: f2 -> f1 : goalify (Input s Conjecture f2 : iforms )
    _        -> (f :=>: Atom mainGoalName) : goalify iforms


--------------------------------------------------------------------------------
-- 1) logical constants TRUE and FALSE
-- 2) equal subformulas (e.g., f & f |---> f )

simplify :: Form Name -> Form Name

simplify (f1 :&: f2) = simplify f1 .&. simplify f2
 where
  f1     .&. f2 | f1 == f2 = f1
  TRUE   .&. f2     = f2
  f1     .&. TRUE   = f1
  FALSE  .&. f2     = FALSE
  f1     .&. FALSE  = FALSE
  f1     .&. f2     = f1 :&: f2

simplify (f1 :|: f2) = simplify f1 .|. simplify f2
 where
  f1 .|. f2 | f1 == f2 = f1
  TRUE   .|. f2     = TRUE
  f1     .|. TRUE   = TRUE
  FALSE  .|. f2     = f2
  f1     .|. FALSE  = f1
  f1     .|. f2     = f1 :|: f2

simplify (f1 :=>: f2) = simplify f1 .=>. simplify f2
 where
  f1 .=>. f2 | f1 == f2 = TRUE
  TRUE    .=>. f2     = f2
  f1      .=>. TRUE   = TRUE
  FALSE   .=>. f2     = TRUE
  f1      .=>. FALSE  = f1 :=>: Atom false -- cannot be simplified away
  f1      .=>. f2     = f1 :=>: f2

simplify (f1 :<=>: f2) = simplify f1 .<=>. simplify f2
 where
  f1 .<=>. f2 | f1 == f2 = TRUE
  TRUE   .<=>. f2     = f2
  f1     .<=>. TRUE   = f1
  FALSE  .<=>. f2     = f2 :=>: Atom false
  f1     .<=>. FALSE  = f1 :=>: Atom false
  f1     .<=>. f2     = f1 :<=>: f2

simplify f = f

---------------------------------------------------------------
-- CLAUSIFICATION OF A FORMULA
-- The clausification procedure updates the state
clausifyForm :: Form Name-> State ClausState ()
-- any formula

clausifyForm TRUE        =  return ()  -- do nothing
clausifyForm FALSE       =  addClause ([] :=> []) -- add empty clause
clausifyForm (Atom a)    =  addClause ([] :=> [a])

clausifyForm (f1 :&: f2)  =
  clausifyForm f1 >> clausifyForm f2

clausifyForm (f1 :<=>: f2) =
  do p1 <- nameEquivWith f1
     p2 <- nameEquivWith f2
     addClauses [ [p1] :=> [p2] , [p2] :=> [p1] ]

clausifyForm (f1 :|: f2)   = clausifyOr [] [f1,f2]
clausifyForm (f1 :=>: f2)  = clausifyImpl f1 f2

clausifyOr :: [Name] -> [Form Name] -> State ClausState ()
-- clausifyOr [p1 .. pm] [f1 ... fn]  (with p1 ... pm atoms, f1 .. fn any formulas)
-- clausify  the formula
--   p1 | ...| pm | f1 |... |fn
clausifyOr ps [] =  addClause ([] :=> ps)
clausifyOr ps ((f1 :|: f2) : fs) =  clausifyOr ps (f1 : f2 : fs)
clausifyOr ps (f1 : fs) =
  do p1 <- nameEquivWith f1
     clausifyOr (p1:ps) fs

clausifyImpl :: Form Name  -> Form Name -> State ClausState ()
-- clausifyImpl f1 f2
-- clausify the formula f1 => f2
clausifyImpl (Atom a)  (Atom b)   = addClause ([a] :=> [b])

clausifyImpl (Atom a)  (f1 :&: f2)  = clausifyImpl (Atom a) f1 >> clausifyImpl (Atom a) f2
clausifyImpl (f1 :|: f2) (Atom b)   = clausifyImpl f1 (Atom b) >> clausifyImpl f2 (Atom b)

clausifyImpl f1  (f2 :=>: f3) = clausifyImpl (f1 :&: f2) f3

clausifyImpl (f1:=>:f2)  f3 =
  do p1 <- nameEquivWith f1
     p2 <- nameEquivWith f2
     p3 <- nameEquivWith f3
     addImplClause ((p1:->p2):->p3)

clausifyImpl f1 f2  =
  do p1s <- namesAnd f1
     p2s <- namesOr  f2
     addClause (p1s :=> p2s)

namesAnd :: Form Name ->  State ClausState  [Name]
-- namesAnd (f1 & ... & fn)
-- [p1 ... pn] such that pk is a name for fk, for every 1 <= k <= n
namesAnd (f1 :&: f2) =
  do p1s <- namesAnd f1
     p2s <- namesAnd f2
     return (p1s ++ p2s)
namesAnd f =
  do p <- nameEquivWith f
     return [p]

namesOr :: Form Name  -> State ClausState  [Name]
-- namesOr (f1 | ... | fn)
-- [p1 ... pn] such that pk is a name for fk, for every 1 <= k <= n
namesOr (f1 :|: f2) =
  do p1s <- namesOr f1
     p2s <- namesOr f2
     return (p1s ++ p2s)
namesOr f  =
  do p <- nameEquivWith f
     return [p]

nameEquivWith :: Form Name -> State ClausState Name
-- return a name equivalent with f, possibly updating the state
nameEquivWith  (Atom a) = return a

nameEquivWith  (f1 :&: f2) =
--  p1 |--> f1
--  p2 |--> f2  
--   q |--> f1 & f2
--  NEW  CS:  q => p1, q => p2, p1 & p2 => q 
  do p1 <- nameEquivWith  f1
     p2 <- nameEquivWith  f2
     q  <- nameEquivWith_simpleForm  (p1 :&&: p2)
     addClauses [ [q]   :=> [p1] , [q]   :=> [p2] , [p1,p2] :=> [q] ]
     return q

nameEquivWith (f1 :|: f2) =
--  p1 |--> f1
--  p2 |--> f2  
--   q |--> f1 | f2
--  NEW  CS:  q => p1 | p2,  p1  => q,  p2 => q 
  do p1 <- nameEquivWith  f1
     p2 <- nameEquivWith  f2
     q  <- nameEquivWith_simpleForm  (p1 :||: p2)
     addClauses [ [q] :=> [p1,p2] , [p1] :=> [q] , [p2] :=> [q] ]
     return q

nameEquivWith  (f1 :=>: f2) =
--  p1 |--> f1
--  p2 |--> f2  
--   q |--> f1 => f2
--  NEW  CS:  q & p1 =>  p2
--  NEW ICS:  (p1 => p2) => q  
  do p1 <- nameEquivWith  f1 
     p2 <- nameEquivWith  f2
     q  <- nameEquivWith_simpleForm  (p1 :==>: p2)
     addClause  ([q,p1] :=> [p2])
     addImplClause ((p1:->p2) :-> q)
     return q

nameEquivWith  (f1 :<=>: f2) =
--  p1 |-->  f1
--  p2 |-->  f2  
--   q |-->  p1 <=> p2
--  q1 |-->  p1 => p2
--  q2 |-->  p2 => p1  
--  NEW  CS:   q & p1 =>  p2,   q & p2 =>  p1
--            q1 & p1 =>  p2,  q2 & p2 =>  p1  ######## DELETED !!!! #######
--            q1 & q2 => q  
--  NEW ICS:  (p1 => p2) => q1,  (p2 => p1) => q2   
  do p1 <- nameEquivWith f1
     p2 <- nameEquivWith f2
     q1 <- nameEquivWith_simpleForm (p1 :==>: p2)
     q2 <- nameEquivWith_simpleForm (p2 :==>: p1)
     q  <- nameEquivWith_simpleForm (p1 :<==>: p2)
     addClauses [
       [q,p1] :=> [p2] , [q,p2] :=> [p1] ,
       -- [q1,p1] :=> [p2], [q2,p2] :=> [p1],
       [q1,q2] :=> [q], [q1,q2] :=> [q]
      ]
     addImplClauses [ (p1:->p2) :-> q1 ,  (p2:->p1) :-> q2 ]
     return q


normalForm :: SimpleForm -> SimpleForm
-- simple form ::= (p1 & p2)  ||  (p1 | p2)  ||  (p1 => p2) || (p1 <=> p2 )
--                  p1, p2 atoms
normalForm  (p1 :&&: p2)   | p1 > p2 = p2 :&&: p1
normalForm  (p1 :||: p2)   | p1 > p2 = p2 :||: p1
normalForm  (p1 :<==>: p2) | p1 > p2 = p2 :<==>: p1
normalForm  sf = sf

nameEquivWith_simpleForm :: SimpleForm -> State ClausState  Name
-- return a name equivalen with a simple form, by inspecting (and possibly updating) the cache
nameEquivWith_simpleForm sf =
  do
    clausSt <- get
    let normal_sf = normalForm sf
        cache =  clausCache clausSt 
    case Map.lookup  normal_sf cache  of
       Just p -> return p
       Nothing ->
        do
          let n = clausIndex clausSt
              newName = mkNewName n
              newCache = Map.insert normal_sf newName cache 
          modify( \s ->  s{clausCache = newCache, clausIndex = n + 1 } ) 
          return newName      

addClause :: Clause Name -> State ClausState ()
addClause c =
  modify( \s -> s{ clausCs = Set.insert c (clausCs s) })

addClauses :: [Clause Name] -> State ClausState ()
addClauses cs =
  sequence_ [ addClause c | c <- cs ]
  
addImplClause :: ImplClause Name -> State ClausState ()
addImplClause ic =
   modify( \s -> s{ clausIcs = Set.insert ic (clausIcs s) } )

addImplClauses :: [ImplClause Name] -> State ClausState ()
addImplClauses ics =
  sequence_ [ addImplClause ic | ic <- ics ]


