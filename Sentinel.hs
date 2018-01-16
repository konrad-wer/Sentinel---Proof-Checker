--Sentinel - ProofChecker - created by Konrad Werbliński

import Parser
import AST
import ProofChecker
import Text.Parsec
import System.Environment

parseFile :: String -> IO [Block SourcePos]
parseFile file = do
  p  <- readFile file
  case parseProof p of
    Left e  -> print e >> fail "parse error"
    Right r -> return r
    
readArgs :: [a] -> Maybe(a, Maybe a)    
readArgs [] = Nothing
readArgs (input : output : _) = return (input, return output)
readArgs (h : _) = return (h, Nothing)     
    
main :: IO()
main = do
  args <- getArgs
  case readArgs args of
    Nothing -> putStr "\nUsage: Sentinel Input_filename [Output_filename]\n\n"
    Just (infile, outfile) -> do
      ast <- parseFile infile 
      case outfile of
        Nothing -> putStr ("\n" ++ (checkAllProofs (takeAllAxioms ast) $ takeAllProofs ast) ++ "\n") 
        Just outfile -> writeFile outfile $ checkAllProofs (takeAllAxioms ast) $ takeAllProofs ast
  return ()
  