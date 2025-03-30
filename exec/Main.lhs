%\section{Wrapping it up in an exectuable}\label{sec:Main}

We will now use the library form Section \ref{sec:Basics} in a program.

\begin{code}
module Main where

import Basics
import Poset
import DL
import Priestley
import Representation
import ParsingStuff
main :: IO ()
main = threeexample

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
