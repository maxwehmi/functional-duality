\begin{code}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
module PrettyGraphs where
import Data.Set as Set
import qualified Data.Maybe as M
import DL 
import Poset
import Priestley


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





\end{code}

This section is dedicated to the visualization of the structure of the most fundamental mathematical objects we have insofar defined and operated with: that is ordered sets, lattices and Priestley Spaces. 



\begin{code}




toGraphRel' :: Relation a -> Dot a
toGraphRel'  =  mapM_ (uncurry (-->)) 

toGraphRel:: Relation a -> DotGraph a
toGraphRel r = digraph' $  do 
                        edgeAttrs [A.Dir A.NoDir]
                        nodeAttrs [A.Shape A.PointShape, A.FontSize 0.0, A.Width 0.1] --, A.Label (StrLabel "")]
                        graphAttrs[A.RankDir A.FromBottom]
                        toGraphRel' r 

toyRel:: Relation Int
toyRel = Set.fromList [(0,1)]





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
 

\end{code}

