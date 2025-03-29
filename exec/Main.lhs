\section{Wrapping it up in an exectuable}\label{sec:Main}

We will now use the library form Section \ref{sec:Basics} in a program.

\begin{code}
module Main where

import Basics
import Poset
import DL
import Priestley
import Representation
import ParsingStuff
import Text.Parsec (parse)
import Text.Parsec.String (Parser)
import Text.Read (readMaybe)
import Data.Set as Set
import Test.QuickCheck (Arbitrary, arbitrary, generate, Gen)

getUserInput :: IO Int
getUserInput = do
  number <- getLine
  case readMaybe number :: Maybe Int of
    Nothing -> do
      putStrLn "Sorry, that is not a valid input. Please give a number from 1 to 7."
      getUserInput
    Just n -> 
      if ((n < 8) && (n > 0)) then return n else do
      putStrLn "Sorry, that is not a valid input. Please give a number from 1 to 7."
      getUserInput

getDL :: IO (Lattice String)
getDL = do
  putStrLn "The intended input is Set: x, y, z, k ... Order: (x,y), (k,z), ... \n\
  \You may give the minimal relation, and we shall take the minimal poset for your input.\n"
  inputOS <- getLine
  case parse parseOrderedSet "" inputOS of
    Left err -> do
          print err
          putStr "Incorrect input, please try again.\n\n"
          getDL
      -- also tell user whehter antisymmetry has been forced?
    Right os -> return (makeLattice $ makePoSet os)

getOS :: IO (OrderedSet String)
getOS = do
  putStrLn "The intended input is Set: x, y, z, k ... Order: (x,y), (k,z), ... \n\
  \You may give the minimal relation, and we shall take the minimal poset for your input.\n\
  \We are assuming the discrete topology as we are working with finite Priestley spaces.\n"
  inputOS <- getLine
  case parse parseOrderedSet "" inputOS of
    Left err -> do
          print err
          putStr "Incorrect input, please try again.\n"
          getOS
      -- also tell user whehter antisymmetry has been forced?
    Right os -> return (makePoSet os)
  
getApprovedDL :: IO (Lattice String)
getApprovedDL = do
  lattice <- getDL
  case checkDL lattice of
    True  -> return lattice
    False -> do
      putStrLn "This is not a distributive lattice, please try again."
      getApprovedDL

getApprovedOS :: IO (OrderedSet String)
getApprovedOS = do
    os <- getOS
    case checkPoset os of
      True -> return os
      False -> do
          putStr "The input is not a poset (breaks antisymmetry), please try again. \n"
          getApprovedOS

main :: IO ()
main = do
  putStrLn "Welcome to our MSL program! \n\
    \ \n\
    \This is a program that works with finite \n\
    \distributive lattices and Priestley spaces \n\ 
    \to help you with all your mathematical needs. \n\
    \What would you like to do? \n\
    \ \n\
    \(1) Check distributive lattice \n\
    \(2) Check Priestley space \n\
    \(3) Generate arbitrary distributive lattice \n\
    \(4) Generate arbitrary Priestley Space \n\
    \(5) Translate from algebra to topology. \n\
    \(6) Translate from topology to algebra \n\
    \(7) Check Representation Theorem for a lattice \n\ 
    \(8) Check Representation Theorem for a space \n"
  -- might remove 7,8

  userInput <- getUserInput
  putStrLn $ "\nYou selected option " ++ show userInput ++ "\n"
  case userInput of 
    1 -> do
      putStrLn "------------ Check Lattice -------------"
      lattice <- getDL
      if checkDL lattice then putStrLn "This is a lattice! \n" else putStrLn "This is not a lattice \n"
      showLattice lattice
    2 -> do 
      putStrLn "------------ Check Priestley Space -------------"
      os <- getOS
      if checkAntiSym $ os then putStrLn "This is a Priestley space \n" else putStrLn "This is not a Priestley Space \n"
      showOrdSet os
    3 -> do
      lattice <- generate (arbitrary :: Gen (Lattice Int))
      showLattice lattice

      putStr "Would you like to translate this lattice to its dual Priestley Space? y/n: "
      answer <- getLine
      case answer of
        "y" -> showPriestley $ priesMap lattice
        _  -> putStrLn "No problem! Glad we could help you :)"

      putStr "Now that we're at it, want to translate back to a lattice? y/n: "
      answer <- getLine
      case answer of
        "y" -> do 
            showLattice $ simplifyDL1 $ clopMap $ priesMap lattice
            putStrLn "Like expected, it's the same lattice we started with!"
            putStrLn "Enough duality for today!"
        _  -> putStrLn "No problem! Glad we could help you :)"

    4 -> do
      space <- generate (arbitrary :: Gen (PriestleySpace Int))
      showPriestley space

      putStr "Would you like to translate this Priestley to its dual lattice? y/n: "
      answer <- getLine
      case answer of
        "y" -> showLattice $ clopMap space
        _  -> putStrLn "No problem! Glad we could help you :)"
        
      putStr "Now that we're at it, want to translate back to a Priestley space? y/n: "
      answer <- getLine
      case answer of
        "y" -> do
            showPriestley $ simplifyPS1 $ priesMap $ clopMap space
            putStrLn "Like expected, it's the same space we started with!"
            putStrLn "Enough duality for today!"
        _  -> putStrLn "No problem! Glad we could help you :) \n"
        
    5 -> do 
      lattice <- getApprovedDL
      putStrLn "This is a valid lattice, we can now translate it!"
      showPriestley $ priesMap lattice
    6 -> do 
      os <- getApprovedOS
      let space = PS (set os) (Set.powerSet $ set os) (rel os)
      putStrLn "This is a valid Priestley space, we can now translate!"
      showLattice $ clopMap space
    _ -> putStrLn "error, run again"


\end{code}

\begin{verbatim}
stack build
stack exec myprogram
\end{verbatim}
