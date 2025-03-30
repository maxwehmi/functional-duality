\begin{code}
module ParsingStuff where 
import qualified Data.Set as Set
import Text.Parsec( letter, spaces, string, between, eof, many1, sepBy, parse, try, alphaNum )
import Poset
import Text.Parsec.String (Parser)
import Control.Monad (void)
import Priestley (PriestleySpace (PS), showPriestley)
import System.IO

\end{code}
\section{Parsing for user interface}
In order to make the executable a (somewhat) practical tool, we wrote two simple parsers to allow our \verb{Main.exe} to take in direct input for the user. \newline 
The Intended syntax is really simple, so we opted for writing the whole thing using \textit{Parsec} rather then generating it with Happy and Alex. \newline 
All the parsers here function similarily, as they look for specific symbols signaling the beginning and the end of the intended input and for strings/pairs of strings/lists of strings separated by a comma. Further, every parser is 
composed of different subordinate parsers which function in a similar way, but look only for specific elements within the input (e.g. for pairs rather than lists).
\subsection{Syntax}
\begin{itemize}

\item[Lattices:] For lattices, the intended syntax is $$Set: <elements of the set, separated by a comma> \,\,Order: <ordered pairs, separated by a comma>$$
E.g. \textit{Set: x, y, z, k ... Order: (x,y), (k,z), ...} is a valid input instance.  

\item[P. Spaces:]For Priestley spaces, the intended syntax is $$Space: <elements of the set, separated by a comma> \,\, Topology: <lists of elements, separated by a comma>\,\,Order:<ordered pairs, separated by a comma>$$
E.g. \textit{-- encoding for Topological (Priestley) spaces should be Space: x, y, z... Topology: [a, b, ...],  [d, b. ...],... Order: (a,b), (c,d), ...} is a valid input instance.


\end{itemize}
The input should be given in one line, if, for logging or other purposes, multiple lines are preferred, adding "\n" between the various items will record a line break in the input. 


\begin{code}


parseOrderedSet :: Parser (OrderedSet String)
parseOrderedSet = do
  elements <- parseSetLine
  spaces
  relations <- parseOrderLine
  spaces 
  eof
  return $ OS (Set.fromList elements) (Set.fromList relations)

parseSetLine :: Parser [String]
parseSetLine = do
  void $ string "Set:" <* spaces
  identifier `sepBy` symbol ","

parseOrderLine :: Parser [(String, String)]
parseOrderLine = do
  void $ string "Order:" <* spaces
  pair `sepBy` symbol ","


symbol :: String -> Parser String
symbol s = try (spaces *> string s <* spaces)

identifier :: Parser String
identifier = many1 alphaNum <* spaces

pair :: Parser (String, String)
pair = between (symbol "(") (symbol ")") $ do
  a <- identifier
  void $ symbol ","
  b <- identifier
  return (a, b)

parsePSSpace :: Parser (PriestleySpace String)
parsePSSpace = do
  base <- parseBase
  spaces
  topology <- parseTopology
  spaces 
  order <- parseOrder
  eof
  return $ PS (Set.fromList base) (Set.fromList topology) (Set.fromList order)

parseBase :: Parser [String]
parseBase = do
  void $ string "Space:" <* spaces
  identifier `sepBy` symbol ","

parseOrder :: Parser [(String, String)]
parseOrder = do
  void $ string "Order:" <* spaces
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

\end{code}

Last, we have some rudimentary test cases, the last of which mimics parts of the intended behavior of the executable. 
\begin{code}
  -- (Lattice)
oneexample :: IO ()
oneexample = do
  let input = "Set: a, b, c\nOrder: (a, b), (b, c)"
  case parse parseOrderedSet "" input of
    Left err -> print err
    Right os -> showOrdSet os
--PriestleySpace
twoexample :: IO ()
twoexample = do
  let input = "Space: a, b, c\nTopology: [], [a], [a,b] \nOrder: (a,b), (b,c)"
  case parse parsePSSpace "" input of
    Left err -> print err
    Right os -> showPriestley os

threeexample :: IO ()
threeexample = do
  putStr "Enter OrderedSet (e.g., 'Set: a, b, c  Order: (a,b), (b,c)'): "
  hFlush stdout
  input <- getLine  
  case parse parseOrderedSet "" input of
    Left err -> print err
    Right os -> showOrdSet os

\end{code}