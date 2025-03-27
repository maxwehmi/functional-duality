
module Prettyprinting where

import DL
import Poset
import qualified Data.Set as Set
import qualified Data.Maybe as M


import Data.GraphViz.Types.Monadic
import Data.GraphViz.Types.Generalised
import Data.GraphViz.Attributes
import Data.GraphViz.Attributes.Colors
import Data.GraphViz.Commands
import Data.GraphViz.Attributes.Complete (RankDir(FromBottom))
import qualified Data.GraphViz.Attributes.Complete as Data.GraphViz.Attributes
--toGraph:: OrderedSet a -> DotGraph String
--toGraph t =  digraph' $ toGraph' t where
--         toGraph' :: OrderedSet a -> Dot String
--         toGraph'(OS s r) = do
--         
--          mapM_ toGraph' ts
--toGraph:: OrderedSet a -> DotGraph String
--toGraph t = mapM_ digraph' (rel t) 
--
--graph1:: DotGraph String
--graph1 = digraph' (Str "G") $ do
--
--   cluster'  $ do
--       graphAttrs [style filled, color LightGray]
--       nodeAttrs [style filled, color White]
--       "a0" --> "a1"
--       "a1" --> "a2"
--       "a2" --> "a3"
--       graphAttrs [textLabel "process #1"]
--
--   cluster'  $ do
--       nodeAttrs [style filled]
--       "b0" --> "b1"
--       "b1" --> "b2"
--       "b2" --> "b3"
--       graphAttrs [textLabel "process #2", color Blue]
--
--   "start" --> "a0"
--   "start" --> "b0"
--   "a1" --> "b3"
--   "b2" --> "a3"
--   "a3" --> "end"
--   "b3" --> "end"
--
--   node "start" [shape MDiamond]
--   node "end" [shape MSquare]
--
toGraph' :: Relation a -> Dot a
toGraph'  =  mapM_ (uncurry (-->)) 

toGraph:: Relation a -> DotGraph a
toGraph r = digraph' $  do 
                        graphAttrs [Data.GraphViz.Attributes.RankDir Data.GraphViz.Attributes.FromBottom]
                        toGraph' r 

toyRel:: Relation Int
toyRel = Set.fromList [(0,1)]

fromTransitive::Ord a => OrderedSet a -> OrderedSet a
fromTransitive (OS s r) = OS s k where
              k = Set.difference r (Set.fromList [(x,y)| (x,y) <- Set.toList r,   any (\z -> Set.member (x,z)  r && Set.member (z,y) r ) s   ])


fromReflexive::Ord a => OrderedSet a -> OrderedSet a
fromReflexive (OS s r) = OS s k where
   k = Set.difference r (Set.fromList [(x,y)| (x,y) <- Set.toList r, x == y])

fromReflTrans::Ord a => OrderedSet a -> OrderedSet a
fromReflTrans  = fromTransitive.fromReflexive
 