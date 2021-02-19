{-# LANGUAGE QuasiQuotes #-}
{- quasi quotation
String are enclosed between   [r| and  |]
-}



module  WriteMakeFile
  (
    writeMakeFile_valid,
    writeMakeFile_countsat
  )
where

import Text.RawString.QQ

type ProblemName = String
type DerName = String
type ModelName = String

writeMakeFile_valid :: ProblemName -> DerName -> String
writeMakeFile_valid  problName derName =
   preamble_valid  problName derName ++  body_valid

writeMakeFile_countsat :: ProblemName -> ModelName -> String
writeMakeFile_countsat problName modelName =
   preamble_countsat problName modelName  ++  body_countsat

preamble_valid :: ProblemName -> DerName -> String
preamble_valid problName derName  =   
  "PROBLEM=" ++ problName ++ "\n"
  ++ "DERIVATION=" ++ derName ++ "\n"


preamble_countsat :: ProblemName -> ModelName -> String
preamble_countsat problName modelName =   
  "PROBLEM=" ++ problName ++ "\n"
  ++ "MODEL=" ++ modelName ++ "\n"


{-

NOTE: in Makefile, use TAB (and not spaces) 
To insert TAB: Ctrl q TAB

-}

body_valid :: String
body_valid = [r|

all:
	@echo -- Compiling files ...
	pdflatex -halt-on-error ${PROBLEM}.tex  > /dev/null
	pdflatex -halt-on-error ${DERIVATION}.tex  > /dev/null
	@echo "---> output in ${PROBLEM}.pdf, ${DERIVATION}.pdf"
	@rm -f *.log  *.aux

clean:
	@echo  -- Cleaning  ...        
	@rm -f *.pdf  *.log  *.aux *.gv
|]  -- end string


  
body_countsat :: String
body_countsat = [r|
all:
	@echo -- Compiling files ...
	pdflatex -halt-on-error ${PROBLEM}.tex  > /dev/null
	dot ${MODEL}.gv -Tpng -o ${MODEL}.png
	@echo "---> output in ${PROBLEM}.pdf, ${MODEL}.png"

clean:
	@echo  -- Cleaning  ...        
	@rm -f *.pdf  *.log  *.aux *.gv  *.gnv
|]  -- end string
