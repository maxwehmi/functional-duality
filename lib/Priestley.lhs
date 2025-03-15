{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
\section{Priestley Spaces}

\begin{code}
module Priestley where

import Data.Set (Set, toList, fromList, intersection, union, difference, filter, map, size, elemAt, isSubsetOf, member, empty, cartesianProduct)

import Data.Bifunctor (bimap)

import Poset
import Mapping

--import qualified Data.IntMap as Data.set

type Topology a = Set (Set a)

data TopoSpace a = TS {
    setTS :: Set a,
    topologyTS :: Topology a
}

data PriestleySpace a = PS {
    setPS :: Set a,
    topologyPS :: Topology a,
    relationPS :: Relation a
}

checkTopology :: Ord a => TopoSpace a -> Bool
--Checks topology condition, really assumes the input is finite
checkTopology (TS space top) = member space top && member empty top && unionClosure top == top && intersectionClosure top == top 
   -- all (\ y -> all (\ x -> member (union x y) top ) top) top &&
   -- all (\ y -> all (\ x -> member (intersection x y) top ) top) top 


fixTopology :: Ord a => TopoSpace a -> TopoSpace a
--makes the input space into a topological space
fixTopology (TS space top) = TS space fixedTop  where 
    fixedTop  = fromList [space, empty] `union` unionClosure (intersectionClosure top)

unionStep :: (Ord a) => Topology a -> Topology a
unionStep x = Data.Set.map (uncurry union) (cartesianProduct x x)


intersectionStep :: (Ord a) => Topology a -> Topology a
intersectionStep x = Data.Set.map (uncurry intersection) (cartesianProduct x x)

unionClosure :: (Eq a, Ord a) => Topology a -> Topology a
unionClosure y = do 
                let cycle1 = unionStep y
                if y == cycle1 
                then y
                else unionStep cycle1 



intersectionClosure :: (Eq a, Ord a) => Topology a -> Topology a
intersectionClosure z = do 
                let cycle1 = intersectionStep z
                if z == cycle1 
                then z
                else intersectionStep cycle1 


getTopoSpace :: PriestleySpace a -> TopoSpace a
getTopoSpace p = TS (setPS p) (topologyPS p)

getOrderedSet :: PriestleySpace a -> OrderedSet a
getOrderedSet p = OS (setPS p) (relationPS p)

checkPriestley :: (Eq a, Ord a) => PriestleySpace a -> Bool
checkPriestley p = checkTopology (getTopoSpace p) && checkPoset (getOrderedSet p) && checkPSA p 
-- since we are only working with finite spaces, they are always compact

checkPSA :: (Eq a, Ord a) => PriestleySpace a -> Bool
-- i'll write this in the most retarded way possible for now, also, I figured, this always holds in the finite case anyway
checkPSA (PS space top order) = all (\ pair -> 
 implies (pair `notElem` order) (any (\ open -> elem (fst pair) open 
   && notElem (snd pair) open) (clopUp (PS space top order)) )) $ allPairs space 

allPairs :: Set a -> [(a,a)]
allPairs space = [(x,y) | x <- toList space ,y <- toList space ]
-- extracts the set of all orderedpairs form the carrier set (could also be done differently)
implies :: Bool -> Bool -> Bool
implies x y = not x || y
--usual implication shorthand 


clopUp :: Ord a => PriestleySpace a -> Topology a
-- In the finite case those are just the upsets, I think it's at least honest to implement a general checker anyway
clopUp (PS space top ord) = intersection (clopens top ) (upsets top) where 
        clopens = Data.Set.filter (\ x -> difference space x `elem` top)  
        upsets = Data.Set.filter (\ y -> y == upClosure y ord)

-- takes upset
upClosure :: (Eq a, Ord a) => Set a -> Relation a -> Set a 
upClosure set1 relation = Data.Set.map snd (Data.Set.filter (\ x -> fst x `elem` set1 ) relation) `union` set1 

inclusionOrder :: Ord a => Topology a -> Relation (Set a)
-- Constructs (maybe) an order out of the clopen upsets of a given PS
inclusionOrder x = fromList [ (z ,y) |  z <- toList x, y <- toList x, isSubsetOf z y ]
--This may give problems if we convert too many times from spaces to the clopup Dual, we could Use Data.Set.Monad and have a monad instance to avoid nesting sets
--into sets multiple times 

{-
This goes commented since for whatever reason there VsCode won't allow me to import the DL file

clopMap :: PriestleySpace a -> Lattice a 
clopMap = if {checkDBLattice $ makeLattice $ (\ x -> (\ y -> OS y inclusionOrder y) clopUp x) == True} 
        then {makeLattice $ (\ x -> (\ y -> OS y (inclusionOrder y)) clopUp x) }
    |   else {error "104!"}
 -}
\end{code}

When working with Priestley Space, we want to be able to check if two given ones are "similar enough", i.e. isomorphic. This will become important when we want to confirm that a Priestley Space is isomorphic to the dual of its dual. \\
To check isomorphism, we have to be given two Priestley Spaces and a map between them. The map is an isomorphism, if it is actually a map, bijective, a homoemorphism on the topological spaces and an order isomorphism on the relations. If the map is an isomorphism, the spaces are isomorphic. 

\begin{code}
checkIso :: (Eq a, Ord a) => PriestleySpace a -> PriestleySpace a -> Map a a -> Bool
checkIso (PS sa ta ra) (PS sb tb rb) mapping = checkMapping sa mapping 
    && checkBijective sb mapping 
    && checkHomoemorphism ta tb mapping
    && checkOrderIso ra rb mapping
\end{code}

Assuming bijectivity (by laziness of \&\&), to check that the given map is a homeomorphism, we have to check that it is an open and continuous map, i.e. it maps opens to opens and the preimages of opens are also open. This means that applying the map to an open set in the topology of the domain should yield an element of the topology of the codomain, so applying it to the set of opens of the domain (its topology) should yield a subset of the opens of the codomain (its topology). Similarly, we check that the preimage of the topology of the codomain is a subset of the topology of the domain.

\begin{code}
checkHomoemorphism :: (Ord a, Ord b) => Topology a -> Topology b -> Map a b -> Bool
checkHomoemorphism ta tb mapping = 
    mapTop mapping ta `isSubsetOf` tb
    && premapTop mapping tb `isSubsetOf` ta
\end{code}

To apply the map to every open and thus every element of every open, we have to nest \verb:Data.Set.map: twice. Again, we deal similarly with the preimages.

\begin{code}
mapTop :: (Ord a, Ord b) => Map a b -> Topology a -> Topology b
mapTop mapping = Data.Set.map (Data.Set.map (getImage mapping))

premapTop :: (Ord a, Ord b) => Map a b -> Topology b -> Topology a
premapTop mapping = Data.Set.map (Data.Set.map (getPreimage mapping))
\end{code}

Lastly, it remains the check that the map is an order isomorphism, which means that two elements $x,y$ of the domain satisfy $x\leq y$ in the domain iff $f(x)\leq f(y)$ in the codomain (here $f$ is the map). This means that applying the map component wise to every pair of the relation in the domain should yield the relation of the codomain and vice versa. 

\begin{code}
checkOrderIso :: (Ord a, Ord b) => Relation a -> Relation b -> Map a b -> Bool
checkOrderIso ra rb mapping = mapRel mapping ra == rb && premapRel mapping rb == ra
\end{code}

Similar to above, we have to nest \verb:Data.Set.map: with \verb:Data.Bifunctor.bimap: to apply the map to both components of all pairs in the relation.

\begin{code}
mapRel :: (Ord a, Ord b) => Map a b -> Relation a -> Relation b
mapRel mapping = Data.Set.map (Data.Bifunctor.bimap (getImage mapping) (getImage mapping))

premapRel :: (Ord a, Ord b) => Map a b -> Relation b -> Relation a
premapRel mapping = Data.Set.map (bimap (getPreimage mapping) (getPreimage mapping))







\end{code}