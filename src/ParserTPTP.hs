module ParserTPTP(
  parseFormula,    --     String ->  IO ( Either ParseError [Input (Form Name)] )
  parseFileTPTP    --   FilePath ->  IO ( Either ParseError [Input (Form Name)] )
  )
 where

import System.IO
import System.Environment
import Data.List as List
import Control.Monad
import Text.Parsec.Char
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import  Types



{-

buildExpressionParser :: Stream s m t => OperatorTable s u m a -> ParsecT s u m a -> ParsecT s u m a

buildExpressionParser table term builds an expression parser for terms term with operators from table,
taking the associativity and precedence specified in table into account.

Prefix and postfix operators of the same precedence can only occur once (i.e. --2 is not allowed if - is prefix negate).

Every lexical parser from the ParsecToken module will skip whitespace after each symbol parsed;
parsers which skip trailing whitespace are called lexeme parsers (the lexeme combinator can be used to define them).

-}


languageDef =
   emptyDef { Token.commentStart    = "/*" ,
              Token.commentEnd      = "*/" ,
              Token.commentLine     = "%" ,
              Token.identStart      = letter ,
              Token.identLetter     = alphaNum <|> oneOf "!$?^+-_",
              Token.reservedNames   = [ "fof" 
                                      ],
              Token.reservedOpNames = ["$true", "$false", "~", "&", "|", "=>", "<=>"]
            }


lexer = Token.makeTokenParser languageDef

lexeme     = Token.lexeme     lexer 
identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
parens     = Token.parens     lexer -- parses surrounding parenthesis:
                                    -- parens p
                                    -- takes care of the parenthesis and
                                    -- uses p to parse what's inside them
integer    = Token.integer    lexer -- parses an integer
comma      = Token.comma      lexer -- parses a comma
dot        = Token.dot        lexer -- parses a dot
whiteSpace = Token.whiteSpace lexer -- parses whitespace



--  each sublist contains operators with the same precedence
operatorTable = [
                 -- [ unaryPref "~"  negate  ] , treated apart
                 [  
                   binaryInf "&"  ( :&: )  AssocLeft ,
                   binaryInf "|"  ( :|: )  AssocLeft
                ],   
                [
                   binaryInf   "=>"   ( :=>: )  AssocRight ,
                   binaryInf   "->"   ( :=>: )  AssocRight ,
                   binaryInf   "<=>"  ( :<=>: ) AssocRight ,
                   binaryInf   "<->"  ( :<=>: ) AssocRight
                ]
              ]

unaryPref :: String -> (a -> a) -> Operator Char st a
unaryPref  opName fun  = Prefix ( reservedOp opName >> return fun )

binaryInf :: String -> (a -> a -> a) -> Assoc -> Operator Char st a
binaryInf opName fun assoc  = Infix ( reservedOp opName  >> return fun  ) assoc
-- unaryPost :: String -> (a -> a) -> Operator Char st a
-- unaryPost opName fun       = Postfix ( reservedOp opName >>  return fun )



-- main parser for a TPTP definition or a formula (possibly with comments)
-- Build a list of elements of the form:
--     Input Axiom form | Input Conjecture formula
-- The definition
-- [Input Axiom f1, .... , Input Axiom fk, Input Conjecture f ]
-- represents the formula
--  ( f1 & ... & fk =>  f )
-- If a single formula f is parsed, the returned list is
--  [Input Conjecture f ]
tptpDef :: Parser [Input (Form Name)]
tptpDef =
  do
    skipMany lineComment
    spaces
    f <- (  inputFormula  <|>  fofSeq )
    eof
    return f


-- line starting with "%", possibly followed by spaces (e.g., empty lines)
lineComment :: Parser ()
lineComment =
  ( string "%" >> manyTill anyChar endOfLine >>  spaces >> return () )  





{-
  A formula is specified by a sequence of fof definitions of the form

      fof(identifier, axiom, formula).         // assumption
      fof(identifier, conjecture, formula).    // conclusion

The sequence of assumptions might be empty.
 We assume that there is exactly one conjecture.
The defined formula is

  (/\ assumptions) => conclusion 

represented by a list  of type [Input (Form Name)]


-}

-- parse a nonempty sequence of fof definitions
fofSeq :: Parser [Input (Form Name)]
fofSeq = many1 fof  -- at least one fof

-- parse the role of a fomula (axiom or conjecture)
formRole :: Parser FormRole 
formRole =
  ( string "axiom" >> return Axiom )
  <|>
  ( string "conjecture" >> return Conjecture )


-- parse a fof definition 
fof :: Parser (Input (Form Name))
fof  =
  do
    reserved "fof"
    inputForm <- parens fofArgs
    dot
    return inputForm


-- parse the fof arguments (identifier, formRole, formula)
fofArgs :: Parser (Input (Form Name))
fofArgs  =
  do
    id <- identifier
    comma
    fRole <- formRole 
    comma
    f <- form
    return (Input id  fRole f)

-- parse a formula
form :: Parser (Form Name)
form =  buildExpressionParser operatorTable form'

form' :: Parser (Form Name)
form' =
  parens form
  <|> atomicForm
  <|> negForm
  <?> "formula"

-- parse an atomic formula  (including the constants $true or $false)
atomicForm :: Parser (Form Name)
atomicForm =
  ( reserved "$true"  >> return ( TRUE ) )
  <|>
  ( reserved "$false" >> return ( FALSE ) )
  <|>
  Atom <$> identifier


-- parse a negated formula
-- NOTE: buildExpressionParse does not accept formulas of the kind "~ ~ p", this is why we parse them apart 
negForm ::  Parser (Form Name)
negForm =
  try ( reservedOp "~" >>  negate <$> parens form  )  
  <|>
  try ( reserved "~" >>   negate <$> negForm )
  -- with reserveOp, double negation "~~ " (without spaces) is not correctly parsed
  <|>
  ( reservedOp "~" >>    negate <$> atomicForm )
   where negate f = f :=>: FALSE
    
-- parse a single formula 
inputFormula :: Parser [Input (Form Name)]
inputFormula =  
  do
    f <- form
    return [ Input "" Conjecture f ]

-- MAIN  

parseFormula ::  String -> IO ( Either ParseError [Input (Form Name)] )
parseFormula str = return $  parse tptpDef "" str


parseFileTPTP :: FilePath ->  IO ( Either ParseError [Input (Form Name)] )
parseFileTPTP  = parseFromFile tptpDef   
 
{-
main :: IO ()
main =
  do
    args <- getArgs
    f <- parseFile $ List.head args  
    print f
-}
