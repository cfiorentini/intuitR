{-# LANGUAGE TypeOperators #-}
module Utility(
       trueAtmsInSat,    -- Solver -> [Lit] -> IO [Lit]
       getNames,         --  [Clause Name] -> [ImplClause Name] -> GoalName  -> [Name]
       satAddClause,     -- Solver -> Clause Lit -> IO Bool
       satAddClauses,    -- Solver -> [Clause Lit] -> IO ()
       splitName,        --  Name -> (String,String)
                         -- p11 |-> (p,11) ,  p123q14 |-> (p123,14)  , pqr |-> (pqr, "")  
       printClause,       --   Clause a -> String
       printImplClause,   --   ImplClause a -> String
       printfAtmsBrace,   --   (a -> Name) ->  [a] -> String
       printfClause,      --   (a -> Name) ->  Clause a -> String
       printfImplClause,  --   (a -> Name) ->  ImplClause a -> String
       printfImplClauses,  --  (a -> Name) ->  [ImplClause a] -> String
       printfWorld,        --  (a -> Name) ->  World a -> String
       printfModel,         --  (a -> Name) ->  Model a -> String
       printCache,         --   Cache -> String
       printCacheSubst    --   Cache -> String  print the cache with all the substitutions applied
     )
  
   where

import MiniSat
import qualified Data.Set as Set

import Types

--------------------------------------------------------------------------------
---   ###  SAT SOLVER


trueAtmsInSat :: Solver -> [Lit] -> IO [Lit]
trueAtmsInSat sat univ =
-- atoms from univ which are true in the solver
  do
  vals <- sequence [ (Just True ==) `fmap` modelValue  sat x | x <-  univ  ]
  -- vals = (x,b) where b=True if x is true in sat, b=False  otherwise 
  return  [ x | (x,True) <-  univ `zip` vals ]


getNames ::  [Clause Name] -> [ImplClause Name] -> GoalName  -> [Name]
-- duplication free list of the  the names occurring in (ics,ics,goal)
-- NOTE:  Set.fromList :: Ord a => [a] -> Set    complexity O(n log n)
--                 nub ::  Eq a => [a] -> [a]    complexity O(n^2)
getNames  cs ics goal =
  Set.toList $ Set.fromList $ [ x | (xs :=> ys) <- cs, x <- xs ++ ys ]
                                ++ [ z | ((a:->b):->c) <- ics, z <- [a,b,c] ]
                                ++ [ goal, false ]


satAddClause :: Solver -> Clause Lit -> IO Bool
-- [x1, ... , xm]  :=> [y1, .... yn]
--  corresponds to the clause
-- ~x1 v ... v ~xm v y1 v ... v yn
satAddClause sat  (xs :=> ys ) =
  addClause sat ( [ neg x | x <- xs ] ++ ys  )
--  addClause :: Solver -> [Lit] -> IO Bool

satAddClauses :: Solver -> [Clause Lit] -> IO ()
satAddClauses  sat clauses  =
  mapM_ ( satAddClause sat ) clauses 




--------------------------------------------------------------------------------

-- #### PRINT (for trace)



printfListSep :: String -> (a -> String) ->  [a] -> String
-- first argument: separator between elements
printfListSep sep f []   = "" 
printfListSep sep f [x]   = f x
printfListSep sep f (x:xs)   = f x ++ sep ++ printfListSep sep f  xs

printfList :: (a -> String) -> [a] -> String
printfList  = printfListSep ", " 

printfListNl :: (a -> String) -> [a] -> String
printfListNl = printfListSep "\n" 

{-
printfListGen :: String -> (a -> String) ->  [a] -> String
-- first argument: separator between elements
printfListGen sep f []   = "" 
printfListGen sep f [x]   = f x
printfListGen sep f (x:xs)   = f x ++ sep ++ printfListGen sep f  xs
-}



printfAtms ::   (a -> Name) ->  [a] -> String
printfAtms  f xs = printfList f  xs


printfAtmsSq ::   (a -> Name) ->  [a] -> String
printfAtmsSq  f xs = "[" ++ printfAtms f xs ++ "]"

printfAtmsBrace ::   (a -> Name) ->  [a] -> String
printfAtmsBrace  f xs = "{" ++ printfAtms f xs ++ "}"

printfClause :: (a -> Name) ->   Clause a -> String
printfClause f   ( [] :=> [] ) = false  
printfClause f   ([] :=> ys) = printfAtms f ys  
printfClause f  (xs :=> ys) =
  printfAtms f xs ++ " -> " ++ printfAtms f ys  

printClause :: Clause Name -> String
printClause  = printfClause  id

printfClauses :: (a -> Name) ->  [Clause a] -> String
printfClauses f cs =  printfList (printfClause f )  cs

printClauses :: [Clause Name] -> String
printClauses  = printfClauses  id

printfImplClause :: (a -> Name) ->  ImplClause a -> String
printfImplClause f ((a :-> b) :-> c)  = 
      "(" ++ f a ++ " -> " ++  f b ++ ") -> " ++ f c

printImplClause :: ImplClause Name -> String
printImplClause = printfImplClause  id


printfImplClauses :: (a -> Name) ->  [ImplClause a] -> String
printfImplClauses f ics =
  printfList (printfImplClause f )  ics


-- ########## WORLDS

printfWorld :: (a -> Name) ->  World a -> String
printfWorld f w =
  "W" ++  show (getWIndex w) ++ " = "
  ++ printfAtmsBrace f (getWAtms w )

printfWorlds :: (a -> Name) -> [World a] -> String
printfWorlds  f ws =
  printfListSep  " ;\n   "  (printfWorld f)  ws


printfModel :: (a -> Name) ->  Model a -> String
printfModel f mod = "<< " ++  printfWorlds f  (getWorlds mod)  ++ " >>"

isDigit :: Char -> Bool
isDigit c = (c >= '0') && (c <= '9' ) 

splitName :: Name -> (String,String)
-- split name and index:
-- p11 |-> (p,11) ,  p123q14 |-> (p123,14)  , pqr |-> (pqr, "")  
splitName atm =
  let atmRev = reverse atm
      (kRev, nameRev) = span isDigit atmRev 
  in
  (reverse nameRev, reverse kRev)  


-- pretty print formulas 

betweenParens :: String -> String
betweenParens f = "(" ++ f ++ ")"  


--printfForm :: (a -> Name) -> Form a -> String
printfForm :: Show a => (a -> Name) -> Form a -> String  
printfForm pf (Atom atm)  = pf atm

printfForm pf (f1 :&: f2) =
 let sf1 = printfForm pf f1
     sf2 = printfForm pf f2
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,AndOp,NegOp] then sf1 else betweenParens sf1
     sf2' = if (mainLogicalOp (fmap pf f2)) `elem`[ NoOp,AndOp,NegOp] then sf2 else betweenParens sf2
 in sf1'  ++ " & " ++  sf2'

printfForm pf (f1 :|: f2) =
 let sf1 = printfForm pf f1
     sf2 = printfForm pf f2
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,OrOp,NegOp] then sf1 else betweenParens sf1
     sf2' = if (mainLogicalOp (fmap pf f2)) `elem`[ NoOp,OrOp,NegOp] then sf2 else betweenParens sf2
 in sf1'  ++ " | " ++  sf2'


printfForm pf (f1 :=>: FALSE )  =
 let sf1 = printfForm pf f1
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,NegOp] then sf1 else betweenParens sf1
 in "~" ++  sf1'

printfForm pf (f1 :=>: Atom f2 ) | (pf f2) == false  =
 let sf1 = printfForm pf f1
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,NegOp] then sf1 else betweenParens sf1
 in "~" ++  sf1'

printfForm pf (f1 :=>: f2 )  =
 let sf1 = printfForm pf f1
     sf2 = printfForm pf f2
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,NegOp] then sf1 else betweenParens sf1
     sf2' = if (mainLogicalOp (fmap pf f2)) `elem`[ NoOp,NegOp] then sf2 else betweenParens sf2
 in sf1'  ++ " => " ++  sf2'

printfForm pf (f1 :<=>: f2 )  =
 let sf1 = printfForm pf f1
     sf2 = printfForm pf f2
     sf1' = if (mainLogicalOp (fmap pf f1)) `elem`[ NoOp,NegOp] then sf1 else betweenParens sf1
     sf2' = if (mainLogicalOp (fmap pf f2)) `elem`[ NoOp,NegOp] then sf2 else betweenParens sf2
 in sf1'  ++ " <=> " ++  sf2'

-- printfForm pf f   = show f -- to remove!!!!
  

-- printfForms :: (a -> Name) -> [Form a] -> String
printfForms :: Show a  => (a -> Name) -> [Form a] -> String -- DELETE !!!
printfForms pf forms =
  printfList (printfForm pf ) forms



printCache ::  Cache -> String
printCache cache =
    let nameFormList =  cache_to_sortedNameFormList cache
        items =  map  (\(name,form) ->   name ++ "  |--->  " ++ printfForm id form  )  nameFormList 
    in printfListSep "\n" id items


printCacheSubst ::  Cache  -> String
printCacheSubst cache   =
    let items =  map  (\(name,form) ->   name ++ "  |--->  " ++ printfForm id form  )  (cache_to_nameFormSubstList cache)
    in printfListSep "\n" id items
