module Printdot where
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

import qualified Data.Set as Set
import Test.QuickCheck

import DL 
import Poset 
import Priestley 

import Representation 
--import Mapping 
import Basics 




myOS5:: OrderedSet Int
myOS5 = OS (Set.fromList [0,1,2,3]) (Set.fromList [(0,1), (0,2), (1,3), (1,3), (2,3)])

myPoset1:: OrderedSet Int
myPoset1 = closurePoSet myOS5

myLattice1:: Lattice Int 
myLattice1 = makeLattice myPoset1

mySpace :: PriestleySpace (Filter Int)
mySpace = priesMap myLattice1

snelliusOS :: OrderedSet Int 
snelliusOS = OS (Set.fromList [0.. 10]) (Set.fromList [(0,1), (0,2),(1,3),(1,5),(2,4),(2,5),(3,6),(4,7),(6,8),(7,8),(8,9),(9,10)]) 


snelliusDL :: Lattice Int 
snelliusDL = makeLattice (forcePoSet snelliusOS)

snelliusPS :: PriestleySpace Int
snelliusPS = PS (Set.fromList [0.. 5]) (Set.powerSet (Set.fromList [0.. 5])) (Set.fromList [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,1),(1,2),(1,3),(1,4),(1,5),(2,2),(2,4),(3,3),(3,5),(4,4),(5,5)])





--- >>> showPriestley (priesMap myLattice1)
-- No instance for (PrintDot (Filter Int))
--   arising from a use of `showPriestley'
-- In the expression: showPriestley (priesMap myLattice1)
-- In an equation for `it_atFT':
--     it_atFT = showPriestley (priesMap myLattice1)


--- >>> showLattice myLattice1

--- >>> showOrdSet myOS5

--- >>> showPriestley mySpace

--- >>> generate arbitrary :: IO (Lattice Int)
-- OS {set = fromList [-30,-22], rel = fromList [(-30,-30),(-30,-22),(-22,-22)]}; Meet: fromList [(-30,-30,-30),(-30,-22,-30),(-22,-30,-30),(-22,-22,-22)]; Join: fromList [(-30,-30,-30),(-30,-22,-22),(-22,-30,-22),(-22,-22,-22)]

--- >>> showLattice (generate arbitrary :: IO (Lattice Int))
