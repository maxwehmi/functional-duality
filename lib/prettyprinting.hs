
-- module Prettyprinting where

-- import DL
-- import Poset
-- import Priestley
-- import qualified Data.Set as Set
-- import qualified Data.Maybe as M


-- import Data.GraphViz.Types.Monadic
-- import Data.GraphViz.Types.Generalised
-- import Data.GraphViz.Attributes
-- import Data.GraphViz.Attributes.Colors

-- import Data.GraphViz.Commands

-- import qualified Data.GraphViz.Attributes.Complete as A
-- import Data.GraphViz.Attributes.Colors.SVG (SVGColor(Teal))
-- import Data.GraphViz.Printing





-- toGraphRel' :: Relation a -> Dot a
-- toGraphRel'  =  mapM_ (uncurry (-->)) 

-- toGraphRel:: Relation a -> DotGraph a
-- toGraphRel r = digraph' $  do 
--                         edgeAttrs [A.Dir A.NoDir]
--                         nodeAttrs [A.Shape A.PointShape, A.FontSize 0.0, A.Width 0.1] 
--                         graphAttrs[A.RankDir A.FromBottom]
--                         toGraphRel' r 

-- toyRel:: Relation Int
-- toyRel = Set.fromList [(0,1)]

-- --toGraphOrd :: Ord a => OrderedSet a -> DotGraph a 
-- --toGraphOrd p = toGraphRel (rel (fromReflTrans p) )




-- showOrdSet ::(Ord a, Data.GraphViz.Printing.PrintDot a) => OrderedSet a -> IO ()
-- showOrdSet p = runGraphvizCanvas' (toGraphRel $ rel (fromReflTrans p)) Xlib


-- showLattice ::(Ord a, Data.GraphViz.Printing.PrintDot a) => Lattice a -> IO ()
-- showLattice l = runGraphvizCanvas' (toGraphRel (rel (fromReflTrans $ carrier l))) Xlib

 
-- showPriestley ::(Ord a, Data.GraphViz.Printing.PrintDot a) => PriestleySpace a -> IO ()
-- showPriestley p = runGraphvizCanvas' (toGraphRel $ rel $ fromReflTrans $ getOrderedSet p) Xlib 



-- fromTransitive::Ord a => OrderedSet a -> OrderedSet a
-- fromTransitive (OS s r) = OS s k where
--               k = Set.difference r (Set.fromList [(x,y)| (x,y) <- Set.toList r,   any (\z -> Set.member (x,z)  r && Set.member (z,y) r ) s   ])


-- fromReflexive::Ord a => OrderedSet a -> OrderedSet a
-- fromReflexive (OS s r) = OS s k where
--    k = Set.difference r (Set.fromList [(x,y)| (x,y) <- Set.toList r, x == y])

-- fromReflTrans::Ord a => OrderedSet a -> OrderedSet a
-- fromReflTrans  = fromTransitive.fromReflexive
 

-- myos1 :: OrderedSet Int
-- myos1 = Poset.closurePoSet $ OS (Set.fromList [1,2,3,4, 5]) (Set.fromList [(1,2), (2,4), (1,3),(3,4),(4,5)])