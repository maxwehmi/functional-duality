
\section{Simple Tests}
\label{sec:simpletests}

We now use the library QuickCheck to test our functions and finally check if representation holds.
\begin{comment}
\begin{code}
module Main where

import Test.Hspec
import Test.QuickCheck

import DL
import Poset
import Priestley
import Representation


\end{code}
\end{comment}

In our tests, we check if the arbitrary instances are generated correctly, i.e. that they have the properties we want them to have. Then we use the fast representation check to confirm that representation holds. We specified the type in all of our datastructures to be \verb:Int:, to resolve hlint errors. We only check these properties, because the tests take very long even for very small instances. Further, our main goal was to confirm that representation holds.

\begin{code}
main :: IO ()
main = hspec $ do
  describe "Basics" $ do
    it "All arbitrary Ordered Sets should be Posets" $
      property $ \ o -> checkPoset (o :: OrderedSet Int)
    it "All arbitrary Lattices should be distributive Lattices" $
      property $ \ l -> checkDL (l :: Lattice Int)
    it "All arbitrary Priestley Spaces should be Priestley Spaces" $
      property $ \ ps -> checkPriestley (ps :: PriestleySpace Int)
    it "All arbitrary Priestley spaces should be isomorphic to their simplified counterpart" $
     property $ \ ps -> simplificationPScheck (ps :: PriestleySpace String)
    it "All arbitrary lattices should be isomorphic to their simplified counterpart" $
     property $ \ l -> simplificationDLcheck (l :: Lattice String)
    it "The dual of the dual of a distributive lattice should be isomorphic to the original lattice" $
      property $ \ l -> checkRepresentationDLfast (l :: Lattice Int)
    it "The dual of the dual of a Priestley Space should be isomorphic to the original space" $
      property $ \ ps -> checkRepresentationPSfast (ps :: PriestleySpace Int)
\end{code}

To run the tests, use \texttt{stack test}. On GitHub, the tests sometimes get cancelled and we could not figure out in time why that is the case. However, local tests confirm that everything is working as it should.