{-# LANGUAGE TypeOperators #-}
module Clausify
  (  clausify
  )
 where

import ParseProblem hiding ( name )
import qualified Control.Applicative as CA
import qualified Data.Map as Map
import Data.List
import Control.Monad
import Control.Monad.State


import Types


clausify :: [Input Form] -> IO([Clause Name],[ImplClause Name],Name,Int)
--  build the clausification (cs,ics,goal) of the input formula,
--  count the number of reduced implication clauses, as defined below 
clausify fs =
  do
  let  (cs0, ics0,goal) = clausify_base (goalify fs)
  (countImplReductions, cs1,ics) <- reduceImplClauses ics0
  let  cs  =  cs0 ++ cs1 ++ [ [b] :=> [c] | (a :-> b ) :-> c <- ics, b /= false ]
  return (cs,ics,goal,countImplReductions)       
-- count: number of reduced implication clauses

{-

REDUCE IMPLICATION CLAUSES WITH SAME ANTECEDENT

Clauses with the same antecedent are reduced as follows:

 (a:->b):-> c1, ... , (a:->b):-> cn

with n >= 2 is reduced to

   (c1:-> newAtm), .... , (cn:-> newAtm),  (a:->b):-> newAtm

where newAtm is a new propositional variable

-}

reduceImplClauses ::  [ImplClause Name] ->   IO (Int,[Clause Name], [ImplClause Name])
--  ** Same strategy as ClaessenRosen **
--  Return (tot,cs1,ics1) where:
--  tot: total amount of clauses with the same antecedent
--  cs1: new clauses (ck:-> newAtm) generated during the process
--  ics1:  implication clauses obtained after reduction
--  *NOTE*:  if no implication clauses is reduced, ics1 is in general a permutation of ics 

reduceImplClauses ics =  
  do
  let sames = Map.toList (Map.fromListWith (++) [ (a:->b,[c]) | ((a:->b):->c) <- ics ])
  return $ evalState ( reduceImplClausesMon sames )  (0,0,[],[])



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
-- ORIGINAL CLAUSIFICATION PROCEDYRE BY CLAESSEN&ROSEN

clausify_base :: [Form] -> ([Clause Name],[ImplClause Name],Name)
clausify_base fs =  (cs, ics,"$goal")
  where
      (_,cs,ics) = run (sequence_ [ clauseForm (simplify f) | f <- fs ]) 
 
goalify :: [Input Form] -> [Form]
goalify []                            = []
goalify (Input s Fact f       : inps) = f : goalify inps
goalify (Input s Conjecture f : inps) =
  case f of
    a :=>: b -> a : goalify (Input s Conjecture b : inps)
    _        -> (f :=>: Atom "$goal") : goalify inps


prop :: Int -> Name
prop k = "$p" ++ show k

--------------------------------------------------------------------------------

simplify :: Form -> Form
simplify (p :&: q) = simplify p .&. simplify q
 where
  p .&. q | p == q = p
  TRUE  .&. q     = q
  p     .&. TRUE  = p
  FALSE .&. q     = FALSE
  p     .&. FALSE = FALSE
  p     .&. q     = p :&: q

simplify (p :|: q) = simplify p .|. simplify q
 where
  p .|. q | p == q = p
  TRUE  .|. q     = TRUE
  p     .|. TRUE  = TRUE
  FALSE .|. q     = q
  p     .|. FALSE = p
  p     .|. q     = p :|: q

simplify (p :=>: q) = simplify p .=>. simplify q
 where
  p .=>. q | p == q = TRUE
  TRUE  .=>. q     = q
  p     .=>. TRUE  = TRUE
  FALSE .=>. q     = TRUE
  p     .=>. FALSE = p :=>: Atom false -- cannot be simplified away
  p     .=>. q     = p :=>: q

simplify (p :<=>: q) = simplify p .<=>. simplify q
 where
  p .<=>. q | p == q = TRUE
  TRUE  .<=>. q     = q
  p     .<=>. TRUE  = p
  FALSE .<=>. q     = q :=>: Atom false
  p     .<=>. FALSE = p :=>: Atom false
  p     .<=>. q     = p :<=>: q

simplify p = p



--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

clauseForm :: Form -> M ()
clauseForm TRUE        = do return ()
clauseForm FALSE       = do clause ([] :=> [])
clauseForm (Atom a)    = do clause ([] :=> [a])
clauseForm (p :&: q)   = do clauseForm p
                            clauseForm q
clauseForm (p :<=>: q) = do a <- nameEquivWith p
                            b <- nameEquivWith q
                            clause ([a] :=> [b])
                            clause ([b] :=> [a])
clauseForm (p :|: q)   = do clauseOr [] [p,q]
clauseForm (p :=>: q)  = do clauseImpl p q

clauseOr :: [Name] -> [Form] -> M ()
clauseOr as []               = do clause ([] :=> as)
clauseOr as ((p :|: q) : ps) = do clauseOr as (p : q : ps)
clauseOr as (p         : ps) = do a <- nameThatImplies p
                                  clauseOr (a:as) ps

clauseImpl :: Form -> Form -> M ()
clauseImpl (Atom a)  (Atom b)   = do clause ([a] :=> [b])
clauseImpl (Atom a)  (p :&: q)  = do clauseImpl (Atom a) p
                                     clauseImpl (Atom a) q
clauseImpl (p :|: q) (Atom b)   = do clauseImpl p (Atom b)
                                     clauseImpl q (Atom b)
clauseImpl p         (q :=>: r) = do clauseImpl (p :&: q) r
clauseImpl (p:=>:q)  r          = do a <- nameThatImplies p
                                     b <- nameImpliedBy q
                                     c <- nameThatImplies r
                                     iclause ((a:->b):->c)
clauseImpl p         q          = do as <- namesAnd p
                                     bs <- namesOr  q
                                     clause (as :=> bs)

namesAnd :: Form -> M [Name]
namesAnd (p :&: q) = do as <- namesAnd p
                        bs <- namesAnd q
                        return (as ++ bs)
namesAnd p         = do a <- nameImpliedBy p
                        return [a]

namesOr :: Form -> M [Name]
namesOr (p :|: q) = do as <- namesOr p
                       bs <- namesOr q
                       return (as ++ bs)
namesOr p         = do a <- nameThatImplies p
                       return [a]

nameEquivWith   = name True True
nameThatImplies = name True False
nameImpliedBy   = name False True

name :: Bool -> Bool -> Form -> M Name
name impls impld (Atom a) =
  do return a

name impls impld (p :&: q) =
  do a <- name impls impld p
     b <- name impls impld q
     (c,impls',impld') <- nameFor impls impld (a :&&: b)
     when impls' $ clause ([c]   :=> [a])
     when impls' $ clause ([c]   :=> [b])
     when impld' $ clause ([a,b] :=> [c])
     return c

name impls impld (p :|: q) =
  do a <- name impls impld p
     b <- name impls impld q
     (c,impls',impld') <- nameFor impls impld (a :||: b)
     when impls' $ clause ([c] :=> [a,b])
     when impld' $ clause ([a] :=> [c])
     when impld' $ clause ([b] :=> [c])
     return c

name impls impld (p :=>: q) =
  do a <- name impld impls p -- flipped!
     b <- name impls impld q
     (c,impls',impld') <- nameFor impls impld (a :==>: b)
     when impls' $ clause  ([c,a] :=> [b])
     when impld' $ iclause ((a:->b) :-> c)
     return c

name impls impld (p :<=>: q) =
  do a <- name True True p
     b <- name True True q
     (c, impls', impld') <- nameFor impls impld (a :<==>: b)
     when impls' $ clause ([c,a] :=> [b])
     when impls' $ clause ([c,b] :=> [a])
     when impld' $
       do (c1,_,_) <- nameFor False True (a :==>: b)
          (c2,_,_) <- nameFor False True (b :==>: a)
          iclause ((a:->b) :-> c1)
          iclause ((b:->a) :-> c2)
          clause ([c1,c2] :=> [c])
     return c

--------------------------------------------------------------------------------

data Triple
  = Name :&&: Name
  | Name :||: Name
  | Name :==>: Name
  | Name :<==>: Name
 deriving ( Eq, Ord, Show )

type Cache = Map.Map Triple (Name, Bool, Bool)

data Seq a = List [a] | Seq a :++: Seq a

toList :: Seq a -> [a]
toList (List xs)           = xs
toList (List xs :++: q)    = xs ++ toList q
toList ((p :++: q) :++: r) = toList (p :++: (q :++: r))

newtype M a = M (Cache -> Int -> (a, Cache, Int, Seq (Clause Name), Seq (ImplClause Name)))

instance Functor M where
  f `fmap` M h =
    M (\c n -> let (x, c', n', cs, ics) = h c n in (f x, c', n', cs, ics))

instance CA.Applicative M where
  pure  = return
  (<*>) = ap

instance Monad M where
  return x =
    M (\c n -> (x, c, n, List [], List []))

  M h >>= k =
    M (\c n -> let (x, c1, n1, cs1, ics1) = h c n
                   M h2                   = k x
                   (y, c2, n2, cs2, ics2) = h2 c1 n1
                in (y, c2, n2, cs1:++:cs2, ics1:++:ics2))

run :: M a -> (a, [Clause Name], [ImplClause Name])
run (M h) = (x, toList cs, toList ics)
 where
  (x, _, _, cs, ics) = h Map.empty 0

nameFor :: Bool -> Bool -> Triple -> M (Name, Bool, Bool)
nameFor impls impld t =
  M (\c n -> case Map.lookup t' c of
               Just (x, impls', impld') ->
                 ( (x, impls && not impls', impld && not impld')
                 , Map.insert t' (x, impls || impls', impld || impld') c
                 , n
                 , List []
                 , List []
                 )

               Nothing -> n' `seq`
                 ( (x, impls, impld)
                 , Map.insert t' (x, impls, impld) c
                 , n'
                 , List []
                 , List []
                 )
                where
                 n' = n+1
                 x  = prop n)
 where
  t' = norm t

  norm (a :&&: b)   | a > b = b :&&: a
  norm (a :||: b)   | a > b = b :||: a
  norm (a :<==>: b) | a > b = b :<==>: a
  norm t                    = t

clause :: Clause Name -> M ()
clause cl = M (\c n -> ((), c, n, List [cl], List []))

iclause :: ImplClause Name -> M ()
iclause cl = M (\c n -> ((), c, n, List [], List [cl]))

--------------------------------------------------------------------------------

