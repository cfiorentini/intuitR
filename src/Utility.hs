{-# LANGUAGE TypeOperators #-}
module Utility

   where

import MiniSat
import qualified Data.Set as Set

import Types

--------------------------------------------------------------------------------

-- #### PRINT (for trace)

printfListGen :: String -> (a -> String) ->  [a] -> String
-- first argument: separator between elements
printfListGen sep f []   = "" 
printfListGen sep f [x]   = f x
printfListGen sep f (x:xs)   = f x ++ sep ++ printfListGen sep f  xs

printfList :: (a -> String) -> [a] -> String
printfList  = printfListGen ", " 

printfListNl :: (a -> String) -> [a] -> String
printfListNl = printfListGen "\n" 


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
  printfListGen  " ;\n   "  (printfWorld f)  ws


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

concatN :: Int -> String -> String
--  concatenate str n times
concatN n str =  concat $ map (\_ -> str) [1 .. n] 
