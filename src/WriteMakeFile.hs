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

type TraceName = String
type DerName = String
type ModelName = String

writeMakeFile_valid :: TraceName ->DerName -> String
writeMakeFile_valid  traceName derName =
   preamble_valid  traceName derName ++  body_valid

writeMakeFile_countsat :: TraceName -> ModelName -> String
writeMakeFile_countsat traceName modelName =
   preamble_countsat traceName modelName  ++  body_countsat

preamble_valid :: TraceName -> DerName -> String
preamble_valid traceName derName  =   
  "TRACE=" ++ traceName ++ "\n"
  ++ "DERIVATION=" ++ derName ++ "\n"


preamble_countsat :: TraceName -> ModelName -> String
preamble_countsat traceName modelName =   
  "TRACE=" ++ traceName ++ "\n"
  ++ "MODEL=" ++ modelName ++ "\n"

  {-

NOTE: in Makefile, use TAB (and not spaces) 
To insert TAB: Ctrl q TAB

-}

body_valid :: String
body_valid = [r|

all: 
	@echo -- Compiling files ...
	pdflatex -halt-on-error ${TRACE}.tex  > /dev/null
	pdflatex -halt-on-error ${DERIVATION}.tex  > /dev/null
	@echo "---> output in ${TRACE}.pdf, ${DERIVATION}.pdf"
	@rm -f *.log  *.aux

clean:
	@echo  -- Cleaning  ...        
	@rm -f *.pdf  *.log  *.aux *.gv
|]  -- end string





body_countsat :: String
body_countsat = [r|

all:
	@echo -- Compiling files ...
	pdflatex -halt-on-error ${TRACE}.tex  > /dev/null
	dot ${MODEL}.gv -Tpng -o ${MODEL}.png
	@echo "---> output in  ${TRACE}.pdf, ${MODEL}.png"	
	@rm -f *.log  *.aux

clean:
	@echo  -- Cleaning  ...        
	@rm -f *.pdf  *.log  *.aux *.gv  *.png
|]  -- end string
