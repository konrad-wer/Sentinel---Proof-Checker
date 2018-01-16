module Parser  (parseProof) where

-- "You've never heard of the Millennium Falcon?
-- …It's the ship that made the Kessel Run in less than twelve parsecs."

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import AST
import Control.Monad

import System.IO


languageDef =
  emptyDef { Token.commentStart    = "/*"
            , Token.commentEnd      = "*/"
            , Token.commentLine     = "//"
            , Token.identStart      = letter
            , Token.identLetter     = alphaNum
            , Token.reservedNames   = [ "proof"
                                      , "goal"
                                      , "end"
                                      , "axiom"
                                      , "true"
                                      , "false"
                                      , "All"
                                      , "Exists" ]
            , Token.reservedOpNames = ["^", "v", "=>", "<=>", "~",  "|",  ":", ";", "."]
            }
            
            
lexer = Token.makeTokenParser languageDef            
            
identifier = Token.identifier lexer -- parses an identifier
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp = Token.reservedOp lexer -- parses an operator
parens     = Token.parens     lexer -- parses surrounding parenthesis
squares    = Token.squares    lexer -- parses surrounding square brackets
braces     = Token.braces     lexer -- parses surrounding braces
integer    = Token.integer    lexer -- parses an integer
semi       = Token.semi       lexer -- parses a semicolon
whiteSpace = Token.whiteSpace lexer -- parses whitespace


proofParser = whiteSpace >> p_Block `endBy` reservedOp "."

p_Block = 
  p_MainProof <|>
  p_Axiom

p_Axiom = do
  p <- getPosition 
  reserved "axiom"
  reservedOp ":"
  f <- p_Formula 
  return $ EAxiom p f
  
  
p_MainProof = do 
  p <- getPosition
  reserved "goal"
  name <- identifier
  reservedOp ":"
  g <- p_Formula
  reserved "proof"
  pr <- p_Proof
  reserved "end"  
  return $ EProof p name g pr

p_Proof = do
  list <- (p_Proof' `sepBy1` reservedOp ";")
  return $ ESeq list
  
  
p_Proof' = 
  try (squares p_Frame) <|>  
  try (squares p_FrameFreshVar) <|>
  try (squares p_FrameFreshVarNoAss) <|> 
  do 
  p <- getPosition
  f <- p_Formula 
  return $ EFormula p f
  
p_Frame = do
  p <- getPosition
  ass <- p_Formula
  reservedOp ":"
  pr <- p_Proof
  return $ EFrame p ass pr
  
p_FrameFreshVar = do
  p <- getPosition
  v <- identifier 
  reservedOp "|"
  ass <- p_Formula
  reservedOp ":"
  pr <- p_Proof
  return $ EExistsFrame p v ass pr
  
p_FrameFreshVarNoAss = do
  p <- getPosition
  v <- identifier 
  reservedOp "|"
  pr <- p_Proof
  return $ EAllFrame p v pr

logicOperators = [ [Prefix (reservedOp "~"   >> return ENeg)],
                   [Infix  (reservedOp "^"   >> return EAnd) AssocLeft],
                   [Infix  (reservedOp "v"   >> return EOr ) AssocLeft],
                   [Infix  (reservedOp "=>"  >> return EImp) AssocRight],
                   [Infix  (reservedOp "<=>" >> return EIff ) AssocLeft]]

p_Formula =  buildExpressionParser logicOperators p_Term
p_Term =  
  parens p_Formula <|> 
  (reserved "true"  >> return (EBool True )) <|>
  (reserved "false" >> return (EBool False)) <|>
  (identifier >>= \id -> return $ EVar id) <|>
  p_All <|>
  p_Exists 


p_All = do 
  reserved "All"
  v <- identifier
  f <- braces p_Formula
  return $ EAll v f
  
p_Exists = do 
  reserved "Exists"
  v <- identifier
  f <- braces p_Formula
  return $ EExists v f
  
parseProof s =  parse proofParser "" s 