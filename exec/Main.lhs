\section{Wrapping it up in an exectuable}\label{sec:Main}

We will now use the library form Section \ref{sec:Basics} in a program.

\begin{code}
module Main where

import Basics
import Poset
import DL
import Priestley
import Representation

main :: IO ()
main = do
  putStrLn "Welcome to our MSL program! This is a program that works with finite \n\
  \distributive lattices and Priestley spaces to help you with all your mathematical needs. \n\
  \What would you like to do? \n\
  \(1) Check distributive lattice \n\
  \(2) Check Priestley space \n\
  \(3) Generate arbitrary distributive lattice \n\
  \(4) Generate arbitrary Priestley Space \n\
  \(5) Translate from algebra to topology. \n\
  \(6) Translate from topology to algebra \n\
  \(7) Check Representation Theorem \n"
  choice <- getLine
  putStrLn choice

\end{code}

We can run this program with the commands:

\begin{verbatim}
stack build
stack exec myprogram
\end{verbatim}

The output of the program is something like this:

\begin{verbatim}
Hello!
GoodBye
\end{verbatim}
