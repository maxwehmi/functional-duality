\section{Wrapping it up in an executable}\label{sec:Main}

\begin{comment}
\begin{code}
module Main where

import Poset
import DL
import Priestley
import Representation
import ParsingStuff

import Text.Parsec (parse)
import Text.Read (readMaybe)
import Data.Set as Set
import Test.QuickCheck (arbitrary, generate, Gen)
\end{code}
\end{comment}

When excecuting the program, we want to give the user 6 options. The first two check whether some input is a distributive and Priestley space respectively. The second two will generate arbitrary instances,
furthermore, the user will be prompted to get the dual and the dual of the dual. In the last two options, the user can directly choose to translate a lattice or space, and then again will be given the option to 
get the dual, and the dual of the dual.

When using the program, the lattices will pop up in a window using 
\textit{graphviz} and \textit{libx11}, and the mathematical aspects will be printed in the terminal.
%Especially option number (4) gives interesting spaces and dual lattices, as the size and complexity of the lattice can become much greater than the space.
Note that when running the program some users have experienced problems with the backspace key. This is a problem of the local language interpreter of VScode together with ghci having no input buffer by default, to bypass it just run the program in the OS shell. 





\begin{code}
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
    \(5) Translate from algebra to topology \n\
    \(6) Translate from topology to algebra \n"
\end{code}

\begin{comment}
\begin{code}
  userInput <- getUserInput
  putStrLn $ "\nYou selected option " ++ show userInput ++ "\n"
  case userInput of 
    1 -> do
      putStrLn "------------ Check Distributive Lattice -------------"
      lattice <- getDL
      case checkDL lattice of 
        True -> do 
          putStrLn "This is a lattice! \n"
          putStrLn $ show lattice
          showLattice lattice
          userDualizeDL lattice
        False -> do
          putStrLn "This is not a lattice: \n"
          putStrLn $ show lattice

    2 -> do 
      putStrLn "------------ Check Priestley Space -------------"
      os <- getOS
      case (checkAntiSym $ os) of
        True -> do
          putStrLn "This is a Priestley space \n"
          let space = PS (set os) (Set.powerSet $ set os) (rel os)
          putStrLn $ show space
          showPriestley space
          userDualizePS space
        False -> do
          putStrLn "This is not a Priestley Space \n"
          putStrLn $ show os

    3 -> do
      putStrLn "------------ Arbitrary Distributive Lattice -------------"
      lattice <- generate (arbitrary :: Gen (Lattice Int))
      putStrLn $ (show lattice) ++ "\n"
      showLattice lattice
      userDualizeDL lattice

    4 -> do
      putStrLn "------------ Arbitrary Priestley Space -------------"
      space <- generate (arbitrary :: Gen (PriestleySpace Int))
      putStrLn $ (show space) ++ "\n"
      showPriestley space
      userDualizePS space
        
    5 -> do 
      putStrLn "------------ Translate Distributive Lattice -------------"
      lattice <- getApprovedDL
      putStrLn "This is a valid lattice, we can now translate it!"
      showLattice lattice
      showPriestley $ simplifyPS1 $ priesMap lattice
      userDualizeDL lattice

    6 -> do 
      putStrLn "------------ Translate Priestley Space -------------"
      os <- getApprovedOS
      let space = PS (set os) (Set.powerSet $ set os) (rel os)
      putStrLn "This is a valid Priestley space, we can now translate!"
      showPriestley space
      showLattice $ simplifyDL1 $ clopMap space
      userDualizePS space

    _ -> putStrLn "error, run again"

getUserInput :: IO Int
getUserInput = do
  number <- getLine
  case readMaybe number :: Maybe Int of
    Nothing -> do
      putStrLn "Sorry, that is not a valid input. Please give a number from 1 to 7."
      getUserInput
    Just n -> 
      if ((n < 7) && (n > 0)) then return n else do
      putStrLn "Sorry, that is not a valid input. Please give a number from 1 to 7."
      getUserInput
\end{code}
\end{comment}

The functions below, \texttt{getDL}and \texttt{getOS} will ask for a set and an order and take the transitive and reflexive closure. A parser is used to help parsing the user input. Furthermore, the functions \texttt{getApprovedDL} and \texttt{getApprovedOS} will prompt the user to give an input untill that input is a correct distributive lattice or ordered set respectively. Lastly, the functions \texttt{userDualizeDL} and \texttt{userDualizePS} will take in a lattice or space and prompt
the user to take the dual and the dual of the dual. 

\begin{code}
getDL :: IO (Lattice String)
getDL = do
  putStrLn "The intended input is Set: x, y, z, k ... Order: (x,y), (k,z), ...  \n\
  \You may give the minimal relation, and we shall close take the minimal poset containing your input.\n"
  inputOS <- getLine
  case parse parseOrderedSet "" inputOS of
    Left err -> do
          print err
          putStr "Incorrect input, please try again.\n\n"
          getDL
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
    Right os -> return (makePoSet os)
  
getApprovedDL :: IO (Lattice String)
getApprovedDL = do
  lattice <- getDL
  case (checkDL lattice && (checkPoset $ carrier lattice)) of
    True  -> return lattice
    False -> do
      putStrLn "This is not a distributive lattice, please try again."
      getApprovedDL

getApprovedOS :: IO (OrderedSet String)
getApprovedOS = do
  os <- getOS
  case (checkPoset os && checkPoset os) of
    True -> return os
    False -> do
      putStr "The input is not a poset (breaks antisymmetry), please try again. \n"
      getApprovedOS

userDualizeDL :: Ord a => (Lattice a) -> IO ()
userDualizeDL lattice = do
  putStr "Would you like to translate this lattice to its dual Priestley Space? y/n: "  
  answer <- getLine
  case answer of
    "y" -> do 
      let dualPS = simplifyPS1 $ priesMap lattice
      putStrLn $ "Dual space: \n" ++ show dualPS ++ "\n"
      showPriestley dualPS
      putStr "Now that we're at it, want to translate back to a lattice? y/n: "
      answer2 <- getLine
      case answer2 of
        "y" -> do 
            let dualdualDL = simplifyDL1 $ clopMap $ priesMap lattice
            putStrLn $ "Dual algebra: \n" ++ show dualdualDL ++ "\n" 
            showLattice dualdualDL
            putStrLn "Like expected, it's the same lattice we started with! (Proof by picture!)"
            putStrLn "Enough duality for today!"
        _  -> putStrLn "No problem! Glad we could help you :)"
    _  -> putStrLn "No problem! Glad we could help you :)"

userDualizePS :: Ord a => (PriestleySpace a) -> IO ()
userDualizePS space = do
  putStr "Would you like to translate this Priestley to its dual lattice? y/n: "
  answer <- getLine
  case answer of
    "y" -> do 
      let dualDL = simplifyDL1 $ clopMap space
      putStrLn $ "Dual algebra: \n" ++ show dualDL ++ "\n" 
      showLattice dualDL
      putStr "Now that we're at it, want to translate back to a Priestley space \n\ 
      \Warning! This translation could be very computationally heavy. y/n: "
      answer2 <- getLine
      case answer2 of
        "y" -> do
            let dualdualPS = simplifyPS1 $ priesMap $ clopMap space
            putStrLn $ "Dual space: \n" ++ show dualdualPS ++ "\n"
            showPriestley dualdualPS
            putStrLn "Like expected, it's the same space we started with! (Proof by picture!)"
            putStrLn "Enough duality for today!"
        _  -> putStrLn "No problem! Glad we could help you :) \n"
    _  -> putStrLn "No problem! Glad we could help you :)"
\end{code}

To run the executable, with a terminal on the project's folder:
\begin{verbatim}
stack build
stack exec myprogram
\end{verbatim}
