{-# LANGUAGE OverloadedStrings #-}
module BerlusconiSilvio where 
import qualified Data.Set as Set
import Text.Parsec
    ( letter, spaces, string, between, eof, many1, sepBy, parse, try )
import Poset
import Text.Parsec.String (Parser)
import Control.Monad (void)

import Priestley (PriestleySpace (PS), showPriestley)

-----The intended input is Set: x, y, z, k ... LatOrder: (x,y), (k,z), ...

parseOrderedSet :: Parser (OrderedSet String)
parseOrderedSet = do
  elements <- parseSetLine
  relations <- parseOrderLine
  eof
  return $ OS (Set.fromList elements) (Set.fromList relations)

parseSetLine :: Parser [String]
parseSetLine = do
  void $ string "Set:" <* spaces
  identifier `sepBy` symbol ","

parseOrderLine :: Parser [(String, String)]
parseOrderLine = do
  void $ string "LatOrder:" <* spaces
  pair `sepBy` symbol ","

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

-- (Lattice)
oneexample :: IO ()
oneexample = do
  let input = "Set: a, b, c\nLatOrder: (a, b), (b, c)"
  case parse parseOrderedSet "" input of
    Left err -> print err
    Right os -> showOrdSet os

    -- encoding for Topological (Priestley) spaces should be Space: x, y, z... Topology: [a, b, ...],  [d, b. ...],... SpaceOrder: (a,b), (c,d), ...


parsePSSpace :: Parser (PriestleySpace String)
parsePSSpace = do
  base <- parseBase
  topology <- parseTopology
  order <- parseOrder
  eof
  return $ PS (Set.fromList base) (Set.fromList topology) (Set.fromList order)

parseBase :: Parser [String]
parseBase = do
  void $ string "Space:" <* spaces
  identifier `sepBy` symbol ","

parseOrder :: Parser [(String, String)]
parseOrder = do
  void $ string "SpaceOrder:" <* spaces
  pair `sepBy` symbol ","

parseTopology :: Parser [Set.Set String]
parseTopology = do
  void $ string "Topology:" <* spaces
  open `sepBy` symbol ","

open :: Parser (Set.Set String)
open = do
  elements <- between (symbol "[") (symbol "]") $
    identifier `sepBy` symbol ","
  return $ Set.fromList elements
--PriestleySpace
twoexample :: IO ()
twoexample = do
  let input = "Space: a, b, c\nTopology: [], [a], [a,b] \nSpaceOrder: (a,b), (b,c)"
  case parse parsePSSpace "" input of
    Left err -> print err
    Right os -> showPriestley os