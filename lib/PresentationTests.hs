module PresentationTests where 
import qualified Data.Set as Set
import DL
import Priestley
import Poset 
import Representation
import Data.GraphViz.Types.Monadic
import Data.GraphViz.Types.Generalised
import Data.GraphViz.Attributes
import Data.GraphViz.Attributes.Colors

import Data.GraphViz.Attributes.Complete (RankDir(FromBottom))
import qualified Data.GraphViz.Attributes.Complete as Data.GraphViz.Attributes

import Data.GraphViz.Commands

import qualified Data.GraphViz.Attributes.Complete as A
import Data.GraphViz.Attributes.Colors.SVG (SVGColor(Teal))
import Data.GraphViz.Printing
import Test.QuickCheck
--import BerlusconiSilvio


myOS5:: OrderedSet Int
myOS5 = OS (Set.fromList [0,1,2,3]) (Set.fromList [(0,1), (0,2), (1,3), (1,3), (2,3)])

myPoset1:: OrderedSet Int
myPoset1 = closurePoSet myOS5

myLattice1:: Lattice Int 
myLattice1 = makeLattice myPoset1

mySpace :: PriestleySpace (Filter Int)
mySpace = priesMap myLattice1


--- >>> showLattice myLattice1

--- >>> showOrdSet myOS5

--- >>> showPriestley mySpace
