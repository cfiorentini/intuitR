{-# LANGUAGE QuasiQuotes #-}
{- quasi quotation
String are enclosed between   [r| and  |]
-}


module  WriteLatex
  (
     writeLatexTrace,           --   ProverEnv -> ProverState  -> String
     writeLatexDerivation       --   ProverEnv -> ProverState  -> String
  )

where

import Text.RawString.QQ
import Data.List
import Data.Maybe


import Types
import Utility


data Context =  Context {
  cntGoal :: Name,            -- main goal
  cntCs  :: [Clause Name],    -- initial clauses 
  cntIcs :: [ImplClause Name], -- initial implication clauses 
  cntAddedCs ::  [Clause Name]  -- added clauses (learned clauses)
  }


mkContext :: ProverEnv -> ProverState -> Context
mkContext env pst =
  Context{
    cntGoal = initGoalName env, 
    cntCs = initClausesName env,
    cntIcs = initImplClausesName env,
    cntAddedCs = reverse $ addedCsName env pst          
  }

data SeqI  =  SeqI(Int, Name)         -- SeqI(k,g)   represents the sequent      R_k, X  =>   g 
data SeqC  =  SeqC(Int,[Name],Name)   -- SeqC(k,A,b) represents the sequent      R_k, A |--c  b  (classical provability)

data Derivation  =
   LeafAxiom SeqC
  | RuleEnd (SeqI, Derivation )  -- top rule of a derivation  
  | RuleImpl( SeqI, SeqC, Derivation, Int) --  RuleImpl(root,axiom, der', k )
                                           --  k is the index of the main implication formula




getIndexIcs :: Context -> ImplClause Name  -> Int
getIndexIcs context ic =
    fromJust $  elemIndex  ic   (cntIcs context)

getIndexAddedCs :: Context -> Clause Name  -> Int
getIndexAddedCs context ic =
  fromJust $ elemIndex ic (cntAddedCs context)


data Size = Small | Large
  deriving Eq

-- ##################################################

writeLatexTrace ::  ProverEnv -> ProverState  -> String
writeLatexTrace env pst  =
    preamble Large
    ++ writeProblemPresentation env pst 
    ++ writeTrace env pst 
    ++ writeProblemDescription env pst 
    ++ endDocument

writeLatexDerivation ::  ProverEnv -> ProverState  -> String
writeLatexDerivation env pst  =
    preamble Small   
    ++ writeProblemName env 
    ++  writeDerivation  (  buildDerivation  env pst )
    ++ endDocument



-- #################   TRACE  ###########################


writeProblemPresentation :: ProverEnv -> ProverState  -> String
writeProblemPresentation env pst  =
  let result =  if  isValidForm pst then "{\\bf Proved}"
                else "{\\bf Countersat}"
      ltToNm =  litToName env
      countMod = if  isValidForm pst then "" else
        writeNL 1 ++  "Worlds in the countermodel: " ++ show (sizeModel $ model pst )
  in
  writeProblemName env   
  ++ "\\[\n"
  ++ " \\provesi{R_0, X}{" ++ writeName (ltToNm (initGoal env)) ++ "}\\,? \n" 
  ++  "\\]"
  ++ writeNL 1 ++  result  ++ writeNL 1
  ++ "Clauses in $R_0$: " ++  show (length (initClauses env))
  ++ writeNL 1
  ++ "Clauses in $X$: " ++  show (length (initImplClauses env))
  ++ writeNL 1
  ++ "Atoms: " ++  show (countAtms env)
  ++ writeNL 1
  ++ "Calls to the SAT-solver: " ++ show (countSat pst)
  ++ writeNL 1
  ++ "Restarts: " ++  show (countRest pst)
  ++ countMod
  ++ writeNL 1
  ++ "$R_0$ and $X$ are defined at the end of the document" 

  
writeProblemName :: ProverEnv   -> String
writeProblemName env  =
   "\\subsection*{Problem  \\lstinline|" ++ problemName env  ++ "|}\n"
  
writeProblemDescription ::  ProverEnv -> ProverState   -> String
writeProblemDescription env pst   =
  let context = mkContext env pst
      initCs =  cntCs context
      initIcs = cntIcs context
      addedCs = cntAddedCs context 
  in
  "\n\\subsection*{Problem description}\n"
  ++ "Flat clauses $R_0$ ("
  ++ show (length initCs) ++  ")\n"
  ++ if null initCs then ""
     else "\\begin{enumerate}" ++ writeContextCs  initCs ++ "\n\\end{enumerate}\n"
  -----------------------------
  ++ "Implication clauses $X$ ("
  ++ show (length initIcs ) ++  ")"
  ++ writeNL 1
  ++ writeContextIcs context initIcs
  ---------------------------
  ++ "Added clauses ("
  ++ show (length addedCs) ++  ")"
  ++ writeNL 1
  ++ writeContextAddedCs context addedCs


writeContextCs :: [Clause Name] -> String
-- assumption: nonempty list
-- writeContextCs  [] = ""
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


writeTrace :: ProverEnv -> ProverState -> String
writeTrace env pst =  
  let  context =  mkContext env pst
       steps = getSteps $ traceName env pst
       (str, _) = writeSteps context  emptyModel steps in
  beginRestart 0 0 ++ str 


writeSteps  :: Context  -> Model Name -> [TraceStep Name] -> (String,Model Name)
writeSteps context  mod  [] = ("" , emptyModel) -- never happens
writeSteps context  mod [step] =
  let result =
        case step of
          ProvedSat(_,_,_) -> "\\subsection*{Goal proved}"
          otherwise  ->   "\\subsection*{Countermodel found}"
      (str1, mod1) = writeStep context  mod  step 
  in
  ( str1 ++   endRestart ++ result , mod1 )
  
writeSteps context  mod0  (step1 : steps) =
      let (str1,mod1) =  writeStep context  mod0 step1
          (str2,mod2) =  writeSteps context  mod1 steps in
      (str1 ++ str2, mod2)

writeStep  :: Context  ->  Model Name -> TraceStep Name -> (String, Model Name)
writeStep  context mod step =
  let str = writeStepStr context   step in
  case step of
   NewWorld(wk,xs) ->
       let newMod = addWorld (mkWorld wk xs) mod
           str1 = str ++  "\n" ++ writeModel context  newMod in
       (str1, newMod)
   ProvedSat(_,_,_) -> (str, emptyModel) 
   _ -> (str,mod)

writeStepStr :: Context  ->  TraceStep Name -> String
writeStepStr context  (Check (k,impl))    =
  let j =  getIndexIcs  context impl 
      str = "\\stru{"
             ++  writeW k
             ++   ",\\,"
             ++ writeLambda j ++ "\\,=\\,"
              ++  writeImplClause impl ++ "}" 
  in
  "Selected: "
  ++ writeInMath str
  ++ "\n" 

writeStepStr context   (AskSatR(cntSat,cntRet,right)) =
  "\\item " 
  ++ writeInMath ( writeSqAsk (writeR cntRet) [] right )
   ++  "\n\n"

writeStepStr context   (AskSatRW(cntSat,cntRet,wk,a,right)) =
  "\\item "
  ++ writeInMath ( writeSqAsk (writeR cntRet ++ ",\\," ++  writeW wk  ) [a] right )
  ++ "\n\n"
  
writeStepStr context   (NewWorld(wk,xs))  = 
  "$\\No{\\," ++ writeNameSet xs ++ "\\,}$"
  ++ "\n\nNew world: "
  ++ writeInMath (writeW wk )   ++ "\n\n" 

writeStepStr context  (ProvedSat (cntRet,xs,right)) = 
  "$\\Yes{\\,"  ++ writeNameSet xs  ++ "\\,}$\n\n"
  ++ writeInMath (writeSqProved (writeR cntRet) xs right )
  ++ "\n\n" 
  
writeStepStr context (NewClause(cntSat, cntRest, c) ) =
   "New clause: "
  ++ writeInMath ( writePhi cntRest ++ "\\,=\\," ++ writeClause c )
  ++ "\n\n" 
  ++ writeInMath (writeR (cntRest + 1) ++ "\\,=\\," ++ writeR cntRest  ++ ", "
                  ++  writePhi cntRest )
  ++ endRestart
  ++ beginRestart (cntSat + 1) (cntRest +1)



beginRestart :: Int -> Int -> String
beginRestart 0 0 =
   "\n\\subsubsection*{Start }\n\n"
   ++ "\\begin{enumerate}[label=(\\arabic*),start=0]\n"
beginRestart cntSat  cntRest = -- | cntSat > 0, cntRest > 0 =
   "\n\\subsubsection*{Restart " ++ show cntRest ++  "}\n\n"
   ++ "\\begin{enumerate}[label=(\\arabic*), start=" ++ show cntSat ++ "]\n" 


endRestart :: String
endRestart = "\\end{enumerate}\n"

writeSqAsk :: String -> [Name] -> Name -> String
writeSqAsk str [] right =
  "\\provesc{" ++ str ++ "}{"  ++ writeName right ++ "}\\;?"

writeSqAsk str xs  right =
 "\\provesc{" ++ str ++ ",\\," ++ writeNames ",\\, " xs ++  "}{"
    ++ writeName right ++ "}\\;?"

writeSqProved :: String -> [Name] -> Name -> String
writeSqProved  str [] right =
  "\\provesc{" ++str ++ "}{" ++ writeName right ++ "}"
writeSqProved str xs  right =
  "\\provesc{" ++str ++ ",\\," ++ writeNames ",\\, "  xs  ++ "}{" 
  ++ writeName right ++ "}"



-- #################   MODEL  ###########################


writeModel :: Context  -> Model Name -> String
writeModel context mod | isEmptyModel mod  = "\\emptyset"  
writeModel context mod =
   "\\begin{center}\n"
  ++ "\\small\n"
  ++ "\\begin{tabular}{l|l|l}\n"
  ++ headerModel
  ++ writeNL 1
  ++ "\\hline" ++ writeHLine
  ++ writeWorlds context mod (getWorlds mod) 
  ++  "\\end{tabular}\n"
  ++ "\\end{center}\n\n"
  
writeHLine :: String
writeHLine = "\\hline &&\\\\[-1.5ex]\n"

  
headerModel :: String
headerModel = 
  "$W$ & & $\\lambda$ s.t.~$w\\nrealof{W}\\lambda$" 

writeWorlds :: Context -> Model Name -> [World Name] -> String
-- ASSUMPION: model is nonempty
writeWorlds context  mod [w]   =
  writeWorldDescription context  mod w 

writeWorlds context  mod (w1:ws)   =
  writeWorldDescription context  mod w1 
  ++ writeNL 1
  ++ writeHLine
  ++ writeWorlds context  mod ws 

writeWorldDescription :: Context  -> Model Name -> World Name -> String
writeWorldDescription context  mod w =
  let wk = getWIndex w
      xs = getWAtms w
      ics =  cntIcs context
      icsToCheck = implsToCheck ics  mod w
      lambdaIcsToCheck = map (\ ic -> writeLambda (getIndexIcs context ic )) icsToCheck
  in
  writeInMath (writeW wk)
  ++ " & "
  ++ writeInMath ( writeNamesEmptyset xs )
  ++ " & "
  ++ writeInMath ( writeListEmptyset lambdaIcsToCheck )
  ++ "\n"


implsToCheck :: [ImplClause Name]  -> Model Name -> World Name -> [ImplClause Name]
implsToCheck impls mod w =
  [ impl | impl@((a :-> b) :-> c) <- impls ,
                 not(forcesAt a w),  not(forcesAt b w),  not(forcesAt c w), 
                 forcesImpl (a :-> b) w  mod   ]


writeW :: Int -> String
writeW k = "w_{" ++ show k ++ "}"


writeWorld :: Int -> [Name] -> String
writeWorld k xs =  writeW k ++  "\\,=\\," ++ writeNameSet xs


-- #################   DERIVATION  ###########################

writeDerivation :: Derivation -> String
writeDerivation  der =
  writeInMath $ writeDer der

buildDerivation :: ProverEnv -> ProverState -> Derivation
buildDerivation env pst =
  let context = mkContext env pst
      steps = getSteps $ traceName env pst in
  buildDer context 0 steps


buildDer :: Context -> Int -> [TraceStep Name] -> Derivation
-- last: last index of a selected implication
buildDer  context last (ProvedSat(rk,assumps,g) : _) | null assumps   = LeafAxiom (SeqC (rk,[],g) ) 
-- ProvedSat(k,assumps,g)  (where g is the main goal)
--  Rk |--c g 
-- end of derivation (axiom)

buildDer  context last ( (ProvedSat(rk,assumps,right)) : steps ) =
-- ProvedSat(k,assumps,right):
--   Rk, assumps |--c right
  let der1 = buildDer context last steps
      root = SeqI(rk, cntGoal context) in
  case der1 of
   LeafAxiom _ -> RuleEnd (root,der1)
   _       ->
           RuleImpl( root, SeqC(rk,assumps,right),der1,last)

buildDer context last ( (Check( _, impl )) : steps ) =
  let last' = getIndexIcs context impl in
  buildDer context last' steps

buildDer context last ( _ : steps ) = buildDer context last steps


writeDer :: Derivation -> String

writeDer (LeafAxiom seqC) =  writeSeqC seqC
  
writeDer (RuleEnd(seqI,der1)) =
  "\\infer{"
  ++ writeSeqI seqI ++ "}{"
  ++ writeDer der1 ++ "}"

writeDer (RuleImpl( root, seqC , der1, k)) =
  "\\infer["
  ++ writeLambda  k 
  ++ "]{"
  ++ writeSeqI root  ++ "}{\n" 
  ++ writeSeqC seqC  ++ " &\n "
  ++ writeDer  der1 ++ "}\n" 


writeSeqC ::  SeqC -> String
writeSeqC (SeqC(k,xs,right)) =    -- Rk, xs |--c right 
  let left = if null xs then "" else  ", " ++ writeNames ",\\, "  xs in
  "\\provesc{" ++ writeR k ++ left ++ "}{" ++ writeName right ++ "}"
  
writeSeqI ::  SeqI -> String
writeSeqI (SeqI(k,right)) =    -- Rk, X => right 
   "\\seq{" ++ writeR k ++ ", X}{" ++ writeName right ++ "}"

-- ###############  PRIMITIVE FUNCTIONS  ###############

beginArray :: String -> String
beginArray format =  "\\[\n\\begin{array}{" ++ format ++ "}\n"

endArray :: String
endArray =  "\n\\end{array}\n\\]\n"

writeMBox :: String -> String
writeMBox str = "\\mbox{" ++ str ++ "}"

writeNL :: Int -> String
writeNL k = "\n\\\\[" ++ show k ++ "ex]\n"

writeR :: Int -> String
writeR k = "R_{" ++ show k ++ "}"

writePhi :: Int -> String
writePhi k = "\\varphi_{" ++ show k ++ "}"

writeLambda :: Int -> String
writeLambda k = "\\lambda_{" ++ show k ++ "}"

writeNameSet :: [Name] -> String
writeNameSet [] = "\\emptyset"
writeNameSet xs = "\\{\\," ++ writeNames  ",\\, " xs ++ "\\,\\}"

writeInMath :: String -> String
writeInMath s = "$" ++ s ++ "$"

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




writeClauses :: Context   -> [Clause Name] -> String
writeClauses context  cs  = writeList writeClause  cs



writeImplClause :: ImplClause Name -> String
writeImplClause ((a :-> b) :-> c) =
  "(" ++ writeName a ++ "\\to " ++ writeName b ++ ")\\to " ++ writeName c



writeName :: Name -> String
writeName s | s == false = "\\bot"
writeName s | s == mainGoalName = "\\goal"
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

writeNamesEmptyset :: [Name] -> String
writeNamesEmptyset [] = "\\emptyset"
writeNamesEmptyset  xs = writeNames ",\\, " xs


writeListEmptyset :: [Name] -> String
writeListEmptyset  [] = "\\emptyset"
writeListEmptyset  [x] = x
writeListEmptyset  (x:xs) = x ++ ",\\, " ++  writeListEmptyset xs

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
\newcommand{\stru}[1]{\langle #1 \rangle} % structure
\newcommand{\Yes}[1]{\mathrm{Yes}(#1)}
\newcommand{\No}[1]{\mathrm{No}(#1)}
\newcommand{\nrealof}[1]{{\ntriangleright}_{#1}}

\begin{document}

\thispagestyle{empty}

|]  -- end string



endDocument = "\n\\end{document}"
