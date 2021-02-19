{-# LANGUAGE QuasiQuotes #-}
{- quasi quotation
String are enclosed between   [r| and  |]
-}


module  WriteModelGraphviz
  (
     writeModelGraphviz
  )
where

import Text.RawString.QQ

import Data.List
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.PartialOrd as POrd

import Types
import Utility

type BaseName = String


writeModelGraphviz :: ProverState  -> String
writeModelGraphviz pst  =
  let ltToNm =  litToName pst
      baseName = problemName pst
      mod = fmapMod ltToNm  ( model  pst ) in
  preamble baseName ++  graphSettings 
  ++ writeWorlds mod
  ++ writeSuccs mod
  ++ "} // end model\n"





succWorld :: Ord a => World a -> [World a] -> [World a]
-- list of the labels (int) of the successors of w in the list of worlds ws 
succWorld w ws =
  let greater_than_w = filter ( (POrd.<) w )  ws  
  in   POrd.minima greater_than_w



  
buildSuccList :: Ord a => Model a -> [(World a, World a)]
buildSuccList mod =
  let ws =  getWorlds mod  in
  [ (w, w') |  w  <- ws, w' <- succWorld w ws ]



worldName :: World Name -> String
worldName w = "w" ++ show (getWIndex w) 

writeWorldName w =  "w" ++ writeSub (show  (getWIndex w) ) 

writeSub :: String -> String
writeSub k = "<SUB>" ++  k ++ "</SUB>"

-- stripDoubleQuote  :: String ->String
-- stripDoubleQuote s = filter (\x -> x /= '"') s

tildeCod :: String
tildeCod = "&#771;"

-- writeAtm :: Show a => a -> String
writeAtm :: Name -> String
writeAtm p | p == false = "&perp"
writeAtm p | p == "$goal" = "g" ++ tildeCod

writeAtm ('$': atm) =
  let (atmName, k ) = splitName atm
  in
  case k of
    [] ->   atmName ++ ""
    _  ->   atmName ++ tildeCod ++ writeSub k 

writeAtm atm =
  let (atmName, k ) = splitName atm
  in
  case k of
    [] ->  atmName 
    _  ->  atmName  ++ writeSub k 


writeAtms :: [Name] -> String
writeAtms [] =""
writeAtms [p] = writeAtm p
writeAtms (p1:ps) = writeAtm  p1 ++ ", " ++ writeAtms ps



writeWorld ::  World Name -> String
writeWorld w =
  worldName w ++ "  [label = <"  
  ++ "<B>" ++  writeWorldName w ++ "</B>: "
 ++ writeAtms (getWAtms w) ++ ">]"



writeWorlds :: Model Name -> String
writeWorlds mod =
  "\n// NODES\n" ++  unlines ( map writeWorld (getWorlds mod ) )
-- unlines :: [String] -> String
-- unlines ["a", "b", "c"] = "a\nb\nc\n"


writeSucc :: (World Name,World Name) -> String
writeSucc (w1,w2) = worldName w1 ++ " -- " ++ worldName w2


writeSuccs :: Model Name -> String
writeSuccs mod = 
  "\n// LINKS\n" ++  unlines ( map  writeSucc $ buildSuccList mod )






preamble :: String -> String
preamble src  =
  let srcgv = src ++ ".gv"
      srcpng = src ++ ".png" in
  "\
  \/***  SOURCE GRAPHVIZ FILE  ***\n\
  \\n\
  \Compile with:\n\
  \\n\
  \  dot " ++  srcgv ++   " -Tpng -o " ++ srcpng ++ "\n\
  \\n\
  \Edit this file or change the compilation options to modify the layout\n\
  \\n\
  \***/\n\n\
  \"

graphSettings :: String
graphSettings=[r|
graph ObjectDiagram {
  graph [
    rankdir= BT
    overlap = false
  ];
  node [
    fontsize = "16"
    shape = "record"
    style = filled
    fillcolor = palegreen
  ];
  label=""
  fontsize=12;

|] -- end string


