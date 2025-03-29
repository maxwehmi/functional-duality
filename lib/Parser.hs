{-# LANGUAGE OverloadedStrings #-}
module Parser where
import qualified Data.Set as Set
import Text.Parsec
import Poset
import Text.Parsec.String (Parser)
import Control.Monad (void)
import DL (showLattice)

-----The intended input is Set: x, y, z, k ... Order: (x,y), (k,z), ...

parseOrderedSet :: Parser (OrderedSet String)
parseOrderedSet = do
  elements <- parseSetLine
  relations <- parseOrderLine
  eof  
  return $ OS (Set.fromList elements) (Set.fromList relations)

parseSetLine :: Parser [String]
parseSetLine = do
  void $ string "Set:" <* spaces
  identifier `sepBy` (symbol ",")
  
parseOrderLine :: Parser [(String, String)]
parseOrderLine = do
  void $ string "Order:" <* spaces
  pair `sepBy` (symbol ",")


symbol :: String -> Parser String
symbol s = try (spaces *> string s <* spaces)

identifier :: Parser String
identifier = many1 letter <* spaces

pair :: Parser (String, String)
pair = between (symbol "(") (symbol ")") $ do
  a <- identifier
  void $ symbol ","
  b <- identifier
  return (a, b)


oneexample :: IO ()
oneexample = do
  let input = "Set: a, b, c\nOrder: (a, b), (b, c)"
  case parse parseOrderedSet "" input of
    Left err -> print err
    Right os -> showOrdSet os