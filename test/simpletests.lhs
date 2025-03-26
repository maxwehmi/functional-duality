
\section{Simple Tests}
\label{sec:simpletests}

We now use the library QuickCheck to randomly generate input for our functions
and test some properties.

\begin{code}
module Main where

import Basics
import Mapping
import DL
import Poset
import Priestley

import Test.Hspec
import Test.QuickCheck
\end{code}

The following uses the HSpec library to define different tests.
Note that the first test is a specific test with fixed inputs.
The second and third test use QuickCheck.

\begin{code}
main :: IO ()
main = hspec $ do
  describe "Basics" $ do
    it "All arbitrary Ordered Sets should be Posets (for now the tests just use Ordered Sets on Integers, but the type does not really matter)" $
      property $ \ o -> checkPoset (o :: OrderedSet Int)
    it "All arbitrary Lattices should be distributive Lattices (for now the tests just use Ordered Sets on Integers, but the type does not really matter)" $
      property $ \ l -> checkDL (l :: Lattice Int)
    it "All arbitrary Priestley Spaces should be Priestley Spaces (for now the tests just use Ordered Sets on Integers, but the type does not really matter)" $
      property $ \ ps -> checkPriestley (ps :: PriestleySpace Int)
\end{code}

To run the tests, use \verb|stack test|.

To also find out which part of your program is actually used for these tests,
run \verb|stack clean && stack test --coverage|. Then look for ``The coverage
report for ... is available at ... .html'' and open this file in your browser.
See also: \url{https://wiki.haskell.org/Haskell_program_coverage}.
