
module Prettyprinting where

import DL
import Poset
import Priestley
import qualified Data.Set as Set
import qualified Data.Maybe as M


import Data.GraphViz.Types.Monadic
import Data.GraphViz.Types.Generalised
import Data.GraphViz.Attributes
import Data.GraphViz.Attributes.Colors
import Data.GraphViz.Commands
import Data.GraphViz.Attributes.Complete (RankDir(FromBottom))
import qualified Data.GraphViz.Attributes.Complete as Data.GraphViz.Attributes
import Data.GraphViz.Printing





toGraphRel' :: Relation a -> Dot a
toGraphRel'  =  mapM_ (uncurry (-->)) 

toGraphRel:: Relation a -> DotGraph a
toGraphRel r = digraph' $  do 
                        graphAttrs [Data.GraphViz.Attributes.RankDir Data.GraphViz.Attributes.FromBottom]
                        toGraphRel' r 

toyRel:: Relation Int
toyRel = Set.fromList [(0,1)]

--toGraphOrd :: Ord a => OrderedSet a -> DotGraph a 
--toGraphOrd p = toGraphRel (rel (fromReflTrans p) )




showOrdSet ::(Ord a, Data.GraphViz.Printing.PrintDot a) => OrderedSet a -> IO ()
showOrdSet p = runGraphvizCanvas' (toGraphRel (rel p)) Xlib


showLattice ::(Ord a, Data.GraphViz.Printing.PrintDot a) => Lattice a -> IO ()
showLattice l = runGraphvizCanvas' (toGraphRel (rel (carrier l))) Xlib

 
showPriestley ::(Ord a, Data.GraphViz.Printing.PrintDot a) => PriestleySpace a -> IO ()
showPriestley p = runGraphvizCanvas' (toGraphRel (relationPS p)) Xlib 



fromTransitive::Ord a => OrderedSet a -> OrderedSet a
fromTransitive (OS s r) = OS s k where
              k = Set.difference r (Set.fromList [(x,y)| (x,y) <- Set.toList r,   any (\z -> Set.member (x,z)  r && Set.member (z,y) r ) s   ])


fromReflexive::Ord a => OrderedSet a -> OrderedSet a
fromReflexive (OS s r) = OS s k where
   k = Set.difference r (Set.fromList [(x,y)| (x,y) <- Set.toList r, x == y])

fromReflTrans::Ord a => OrderedSet a -> OrderedSet a
fromReflTrans  = fromTransitive.fromReflexive
 