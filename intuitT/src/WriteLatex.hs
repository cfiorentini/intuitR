{-# LANGUAGE QuasiQuotes #-}
{- quasi quotation
String are enclosed between   [r| and  |]
-}


module  WriteLatex
  (
     writeLatexProblem,
     writeLatexDerivation,
     Context(..) 
  )

where

import Text.RawString.QQ
import Data.List
import Data.Maybe


import Types
import Utility



data Context  =  Context {
  cntGoal :: Name,
  cntCs :: [Clause Name],
  cntIcs :: [ImplClause Name],
  cntAddedCs ::  [Clause Name]
  }

mkContext :: ProverState -> Context
mkContext pst =
  Context{
    cntGoal = initGoalName pst, 
    cntCs = initClausesName pst,
    cntIcs = initImplClausesName pst,
    cntAddedCs = reverse $ addedCsName pst          
  }

getIndexIcs :: Context -> ImplClause Name  -> Int
getIndexIcs context ic =
    fromJust $  elemIndex  ic   (cntIcs context)

getIndexAddedCs :: Context -> Clause Name  -> Int
getIndexAddedCs context ic =
  fromJust $ elemIndex ic (cntAddedCs context)


data Size = Small | Large
  deriving Eq

-- ##############################################


writeLatexProblem ::  ProverState  -> String
writeLatexProblem pst  =
    preamble Large
    ++ writeProblemPresentation pst 
    ++ writeProblemDescription pst 
    ++ endDocument

writeLatexDerivation ::  ProverState  ->  Derivation Name  -> String
writeLatexDerivation pst der  =
    let context = mkContext pst
        legenda =
          "\n$X_I\\,=\\, X\\setminus"
          ++ "\\{\\,k~|~k\\in I\\,\\}$, "
          ++  "$R_{n+1}\\,=\\,R_0,\\varphi_0,\\dots,\\varphi_n$"
    in
    preamble Small
    ++ writeProblemName pst
    ++ legenda
    ++ "\n\\[\n"
    ++ writeDer context der
    ++ "\\]\n"
    ++ endDocument

-- ###############################################



writeProblemPresentation :: ProverState  -> String
writeProblemPresentation pst  =
  let result =  if  isValidForm pst then "{\\bf Proved}"
                else "{\\bf Not Proved}"
      ltToNm =  litToName pst
      countMod = if  isValidForm pst then "" else
        writeNL 1 ++ "Worlds in the countermodel: " ++ show (sizeModel $ model pst )
  in
  writeProblemName pst  
  ++ "\\[\n"
  ++ " \\provesi{R_0, X}{" ++ writeName (ltToNm (initGoal pst)) ++ "}\\,? \n" 
  ++  "\\]"
  ++ writeNL 1 ++  result  ++ writeNL 1
  ++ "Clauses in $R_0$: " ++  show (length (initClauses pst))
  ++ writeNL 1
  ++ "Clauses in $X$: " ++  show (length (initImplClauses pst))
  ++ writeNL 1
  ++ "Atoms: " ++  show (countAtms pst)
  ++ writeNL 1
  ++ "Calls to the SAT-solver: " ++ show (countSat pst)
  ++ writeNL 1
  ++ "Added clauses (= YES answers): " ++ show (countAdd pst)
  ++ writeNL 1
  ++ "Generated worlds (= NO answers): " ++  show (countNo pst)
  ++ countMod
  
writeProblemName :: ProverState   -> String
writeProblemName pst =
   "\\subsection*{Problem  \\lstinline|" ++ problemName pst ++ "|}\n"
  
writeProblemDescription ::  ProverState   -> String
writeProblemDescription pst   =
  let context = mkContext pst in
  "\n\\subsection*{Problem description}\n"
  ++ "Flat clauses $R_0$ ("
  ++ show (length $ cntCs context) ++  "):\n"
  ++ "\\begin{enumerate}"
  ++ writeContextCs  (cntCs context)
  ++ "\n\\end{enumerate}\n"
  -----------------------------
  ++ "Implication clauses $X$ ("
  ++ show (length $ cntIcs context ) ++  "):"
  ++ writeNL 1
  ++ writeContextIcs context  (cntIcs context)
  ---------------------------
  ++ "Added clauses ("
  ++ show (length $ cntAddedCs context) ++  "):"
  ++ writeNL 1
  ++ writeContextAddedCs context  ( cntAddedCs context )


writeContextCs :: [Clause Name] -> String
writeContextCs  [] = ""
writeContextCs  [c] = "\n\\item" ++ writeInMath ( writeClause c )
writeContextCs  (c1 : cs) =
  "\n\\item " ++ writeInMath  ( writeClause  c1 )  
  ++ writeContextCs  cs

writeContextIcs :: Context  -> [ImplClause Name] -> String
writeContextIcs context  [] = ""
writeContextIcs context  [ic] =
   writeInMath ( writeImplClauseDefinition context  ic )
   ++ writeNL 1
writeContextIcs context (ic1 : ics) =
   writeInMath ( writeImplClauseDefinition context  ic1 )  
  ++ writeNL 1 ++ writeContextIcs context  ics

writeImplClauseDefinition :: Context  -> ImplClause Name -> String
writeImplClauseDefinition context  ic =
  let  k =  getIndexIcs context   ic    in
  writeLambda k  ++ "\\,=\\," ++  writeImplClause ic


writeContextAddedCs :: Context -> [Clause Name] -> String
writeContextAddedCs context  [] = ""
writeContextAddedCs context  [c] =
  writeInMath (  writeAddedClauseDef context  c )
writeContextAddedCs context (c1 : cs) = 
  writeInMath ( writeAddedClauseDef context  c1 )  
  ++ writeNL 1 ++ writeContextAddedCs context  cs

writeAddedClauseDef :: Context -> Clause Name -> String
writeAddedClauseDef context  c =
   let k = getIndexAddedCs context c  in
   writePhi k ++ "\\,=\\,"
   ++  writeClause c


-- ##############################################   



writeSqAsk :: String -> [Name] -> Name -> String
writeSqAsk str [] right =
  "\\provesc{" ++ str ++ "}{"  ++ writeName right ++ "}\\;?"


writeNL :: Int -> String
writeNL k = "\n\\\\[" ++ show k ++ "ex]\n"

writeR :: Int -> String
writeR k = "R_{" ++ show k ++ "}"

writePhi :: Int -> String
writePhi k = "\\varphi_{" ++ show k ++ "}"

writeLambda :: Int -> String
writeLambda k = "\\lambda_{" ++ show k ++ "}"


writeInMath :: String -> String
writeInMath s = "$" ++ s ++ "$"



-- ##############################################

  
writeDer :: Context  -> Derivation Name -> String
writeDer context (RuleImpl( rootSq , der1 , der2, mainIc, newC )) =
  "\\infer["
  ++ writeRuleImpl context mainIc newC
  ++ "]{"
  ++ writeSeq context rootSq ++ "}{\n" 
  ++ writeDer context der1 ++ " &\n "
  ++ writeDer context der2 ++ "}\n" 

writeDer context (Axiom sq) =
  let  Seq(k,cs,ics,xs,right) = sq in
  "\\infer{\n" 
  ++ writeSeq context sq ++ "}{\n"
  ++  writeSeqCl k xs right ++ "}\n"


writeRuleImpl :: Context  -> ImplClause Name -> Clause Name ->  String
writeRuleImpl context ic c  =
  writeLambda  $ getIndexIcs context ic   

writeSeq :: Context -> Sequent Name -> String
writeSeq context (Seq(k,cs,ics,xs,right)) =
     let 
       strCs =  writeSeqAddedCs context cs
       strIcs =  if null ics then "" else ", " ++ writeSeqIcs context ics
       strXs = if null xs then "" else  ",\\, " ++ writeNames  ",\\, "  xs
       left = strCs ++ strIcs ++ strXs
     in
     "\\seq{" ++ left ++ "}{" ++ writeName right ++ "}"

writeSeqAddedCs ::  Context -> [Clause Name] -> String
-- pretty print the added clauses of a sequent
writeSeqAddedCs context cs =
  let
   indexList =  sort $ map  ( \c -> getIndexAddedCs context c  ) cs
   (consecutive,rest) = span (\k -> (k == (fromJust $ elemIndex k indexList))) indexList
    -- consecutive: max sequence 0,1,2,3 ... in indexList
    -- rest: the remaining indexes
   k = length consecutive  
  in   
  if null rest then writeR k else 
    writeR k ++  ", " ++  writeList writePhi rest

writeSeqIcs ::  Context -> [ImplClause Name] -> String
-- pretty print the implication clauses of a sequent
writeSeqIcs context ics =
  let
   indexList =  map  ( \ic -> getIndexIcs context ic  ) ics
   allIndex = [0 .. (length $ cntIcs context) - 1  ]
   diffList = sort $ allIndex \\ indexList
 in
   if null diffList then "X" else
     "\\Xminus{" ++ writeList show diffList ++ "}"
     
writeSeqCl :: Int -> [Name] -> Name -> String
writeSeqCl k xs right =
  let strXs = if null xs then "" else ",\\," ++ writeNames  ",\\, " xs in
  "\\provesc{" ++   writeR k ++  strXs ++ "}{"  ++ writeName right ++ "}"

  

-- #######################################################
  
writeList :: Show a => (a -> String ) -> [a] -> String
writeList f []  = "" 
writeList f [x] = f x
writeList f (x1 : xs)  =
  f x1 ++ ",\\, " ++ writeList f xs 



writeClause :: Clause Name -> String
writeClause  ( xs  :=> ys ) =
     case (xs,ys) of
      ([],[]) -> "\\bot" 
      ([],ys) ->  writeNames "\\lor" ys
      (xs,[]) ->  writeNames "\\land" xs ++ "\\to \\bot"
      (xs,ys) ->  writeNames "\\land" xs ++ "\\to " ++  writeNames "\\lor" ys


writeImplClause :: ImplClause Name -> String
writeImplClause ((a :-> b) :-> c) =
  "(" ++ writeName a ++ "\\to " ++ writeName b ++ ")\\to " ++ writeName c


writeName :: Name -> String
writeName s | s == false = "\\bot"
writeName s | s == "$goal" = "\\goal"
writeName ('$' : atm) =
  let (atmName, k ) = splitName atm
  in "\\newAtm{" ++ atmName ++ "}{" ++ k ++ "}"
writeName atm =
  let (atmName, k ) = splitName atm
      safeName = writeSafeName atmName  
  in
  if null k then safeName else safeName ++ "_{" ++ k ++ "}"


writeNames :: String ->  [Name] -> String
-- sep: separator between names
writeNames sep [] = ""
writeNames sep [x] = writeName x
writeNames sep (x:xs) = writeName x ++ sep ++  writeNames sep xs


writeSafeName  :: String -> String
-- handle special symbols ($, _, ....)
writeSafeName name  = "{" ++ concatMap writeSafeChar name  ++ "}"

writeSafeChar :: Char -> String
writeSafeChar c | c == '$' || c== '%' || c == '_' = "\\" ++ [c]
writeSafeChar '\\' = "\\backslash "
writeSafeChar '#' = "\\sharp "
writeSafeChar c = [c]



-- ########################


preamble :: Size -> String
preamble size =
  preamble1 ++ preambleWidth size ++ preamble2

  
preamble1 = [r|\documentclass[10pt]{article}
\usepackage{proof}
\usepackage{enumitem}
\usepackage{listings}
\usepackage{amssymb}
|]  -- end string


preambleWidth Small =  [r|
\pdfpagewidth 80in  
%%\pdfpagewidth 200in %% MAX WIDTH
|]  -- end string

preambleWidth  Large =  [r|
%% \pdfpagewidth 80in  
%%\pdfpagewidth 200in %% MAX WIDTH
|]  -- end string

  

preamble2 :: String
preamble2 =  [r|
\newcommand{\goal}{\tilde{g}}
\newcommand{\newAtm}[2]{\tilde{#1}_{#2}}     
\newcommand{\seq}[2]{#1\, \Rightarrow\, #2}
\newcommand{\provesi}[2]{{#1}\,\vdash_{\mathrm{ipl}}\, #2}
\newcommand{\provesc}[2]{{#1}\,\vdash_{\mathrm{c}}\, #2}
\newcommand{\Xminus}[1]{X_{\{#1\}}}

\begin{document}

\thispagestyle{empty}

|]  -- end string



endDocument = "\n\\end{document}"


