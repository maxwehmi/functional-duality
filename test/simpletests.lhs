
\section{Simple Tests}
\label{sec:simpletests}

We now use the library QuickCheck to randomly generate input for our functions
and test some properties.

\begin{code}
module Main where

import Test.Hspec
import Test.QuickCheck
import qualified Data.Set as Set 

import Basics
import DL
import Poset
import Priestley
import Representation
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
    it "The dual of the dual of a distributive lattice should be isomorphic to the original lattice" $
      property $ \ l -> checkRepresentationDLfast (l :: Lattice Int)
    it "The dual of the dual of a Priestley Space should be isomorphic to the original space" $
      property $ \ ps -> checkRepresentationPSfast (ps :: PriestleySpace Int)
\end{code}

To run the tests, use \verb|stack test|.

To also find out which part of your program is actually used for these tests,
run \verb|stack clean && stack test --coverage|. Then look for ``The coverage
report for ... is available at ... .html'' and open this file in your browser.
See also: \url{https://wiki.haskell.org/Haskell_program_coverage}.


\subsection{More tests} % clean up and expand this

-- Below are a few test cases. 'myos' is a poset. Furthermore, 'mylat1' is a non well-defined lattice, meaning
-- that the functions for 'meet' and 'join' do not coincide with 'findMeet' and 'findJoin'. Lastly, mylat is 
-- a lattice. 

-- \begin{code}

-- myos :: OrderedSet Int
-- myos = Poset.closurePoSet $ OS (Set.fromList [1,2,3,4, 5]) (Set.fromList [(1,2), (2,4), (1,3),(3,4),(4,5)])

-- -- not well-defined lattice
-- mylat1 :: Lattice Int
-- mylat1 = L myos (-) (+)

-- mylat :: Lattice Int
-- mylat = makeLattice myos

-- myos2 :: OrderedSet Int
-- myos2 = Poset.closurePoSet $ OS (Set.fromList [1,2,3,4,5]) (Set.fromList [(1,2), (2,4), (1,3),(3,4)])

-- mylat2 :: Lattice Int
-- mylat2 = makeLattice myos2

-- \end{code}



-- \subsection{Examples}
-- Here are some toy examples to work with. 

-- \begin{code}
-- os6 :: OrderedSet Integer
-- os6 = OS (Set.fromList [1, 2, 3]) 
--          (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,3), (1,3)])

-- os7 :: OrderedSet Integer
-- os7 = OS (Set.fromList [1, 2, 3]) 
--          (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,1), (1,3), (3,1)])

-- os8 :: OrderedSet Integer
-- os8 = OS (Set.fromList [1, 2, 3]) 
--          (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,3), (3,2)])

-- os9 :: OrderedSet Integer
-- os9 = OS (Set.fromList [1, 2, 3]) 
--          (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,3), (3,2), (1,3)])

-- os10 :: OrderedSet Integer
-- os10 = OS (Set.fromList [1, 2, 3]) 
--           (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,1)])

-- os11 :: OrderedSet Integer
-- os11 = OS (Set.fromList [1, 2, 3]) 
--           (Set.fromList [(2,2), (3,3), (1,2), (2,3), (1,3)])
-- os12 :: OrderedSet Integer
-- os12 = OS (Set.fromList [1, 2, 3]) 
--           (Set.fromList [(2,2), (3,3), (1,2), (2,3)])

-- os13 :: OrderedSet Integer
-- os13 = OS (Set.fromList [1, 2, 3]) 
--           (Set.fromList [(2,2), (3,3), (1,2), (2,3), (3,1)])

-- os14 :: OrderedSet Integer
-- os14 = OS (Set.fromList [1, 2, 3, 4, 5]) 
--           (Set.fromList [(1,1), (2,2), (3,3), (4,4), (5,5), 
--                          (1,2), (2,3), (1,3), (4,5), (1,4), (2,5)])

-- os15 :: OrderedSet Integer
-- os15 = OS (Set.fromList [1, 2, 3, 4, 5, 6]) 
--           (Set.fromList [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), 
--                          (1,2), (2,3), (3,4), (4,5), (5,6), (1,3), (1,4), (1,5), (1,6)])

-- os16 :: OrderedSet Integer
-- os16 = OS (Set.fromList [1, 2, 3, 4, 5]) 
--           (Set.fromList [(1,1), (2,2), (3,3), (4,4), (5,5), 
--                          (1,2), (2,3), (1,3), (4,5), (5,4)])

-- os17 :: OrderedSet Integer
-- os17 = OS (Set.fromList [1, 2, 3]) 
--           (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,1), (1,3), (3,1)])

-- os18 :: OrderedSet Integer
-- os18 = OS (Set.fromList [1, 2, 3]) 
--           (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,1)])

-- os19 :: OrderedSet Integer
-- os19 = OS Set.empty Set.empty


-- myOS :: OrderedSet Integer
-- myOS = OS (Set.fromList [1..4]) (Set.fromList [(1,4), (4,5), (5,4),(4,1),(2,1),(2,2),(3,3),(3,1),(1,1),(4,4)])

-- emptyRelOS :: OrderedSet Integer
-- emptyRelOS = OS (Set.fromList[1..4]) (Set.fromList [])

-- myCircle :: OrderedSet Integer
-- myCircle = OS (Set.fromList [1,2,3]) (Set.fromList [(1,2),(2,3),(3,1)])

-- \end{code}