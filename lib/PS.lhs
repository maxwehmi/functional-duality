{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
\section{Priestley Spaces}

\begin{code}
module PriestleySpaces where

import Data.Set (Set, toList, fromList, intersection, union, difference, filter, map, size, elemAt, isSubsetOf, isProperSubsetOf)

import Data.Bifunctor (bimap)

import Poset

--import qualified Data.IntMap as Data.set


data TopoSpace a = TS {
    setTS :: Set a,
    topologyTS :: Set (Set a)
}

data PriestleySpace a = PS {
    setPS :: Set a,
    topologyPS :: Set (Set a),
    relationPS :: Relation a
}

checkTopology :: TopoSpace a -> Bool
checkTopology = undefined
-- use library from other topology project

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
   && notElem (snd pair) open) (clopUp (PS space top order)) )) $ allpairs space 

allpairs :: Set a -> [(a,a)]
allpairs space = [(x,y) | x <- toList space ,y <- toList space ]
-- extracts the set of all orderedpairs form the carrier set (could also be done differently)
implies :: Bool -> Bool -> Bool
implies x y = not x || y
--usual implication shorthand 


clopUp :: Ord a => PriestleySpace a -> Set (Set a)
-- In the finite case those are just the upsets, I think it's at least honest to implement a general checker anyway
clopUp (PS space top ord) = intersection (clopens top ) (upsets top) where 
        clopens = Data.Set.filter (\ x -> difference space x `elem` top)  
        upsets = Data.Set.filter (\ y -> y == upClosure y ord)

upClosure :: (Eq a, Ord a) => Set a -> Relation a -> Set a 
upClosure set1 relation = Data.Set.map snd (Data.Set.filter (\ x -> fst x `elem` set1 ) relation) `union` set1 

inclusionOrder :: Ord a => Set (Set a) -> Relation (Set a)
-- Constructs (maybe) an order out of the clopen upsets of a given PS
inclusionOrder x = fromList [ (z ,y) |  z <- toList x, y <- toList x, isSubsetOf z y ]
--This may give problems if we convert too many times from spaces to the clopup Dual, we could Use Data.Set.Monad and have a monad instance to avoid nesting sets
--into sets multiple times 

{-
This goes commented since for whatever reason there VsCode won't allow me to import the DL file

clopMap :: PriestleySpace a -> Lattice a 
clopMap = if {checkBDLattice $ makeLattice $ (\ x -> (\ y -> OS y inclusionOrder y) clopUp x) == True} 
        then {makeLattice $ (\ x -> (\ y -> OS y (inclusionOrder y)) clopUp x) }
    |   else {error "104!"}
 -}
evaluateMap :: (Ord a, Ord b) => Set (a,b) -> a -> b
evaluateMap mapping x | size (images mapping x) == 1 = elemAt 0 (images mapping x)
                      | otherwise = error "Given Relation is not a mapping" 

images :: (Ord a, Ord b) => Set (a,b) -> a -> Set b
images mapping x = Data.Set.map snd $ Data.Set.filter (\ (y,_) -> x == y) mapping

getPreimage :: Eq b => Set (a,b) -> b -> a
getPreimage mapping y | size (getPreimages y mapping) == 1 = fst $ elemAt 0 (getPreimages y mapping)
                      | otherwise = error "Either no or too many preimages"

getPreimages :: Eq b => b -> Set (a,b) -> Set (a,b)
getPreimages y = Data.Set.filter (\ (_,z) -> z == y)



checkIso :: (Eq a, Ord a) => PriestleySpace a -> PriestleySpace a -> Set (a,a) -> Bool
checkIso (PS sa ta ra) (PS sb tb rb) mapping = checkMapping sa mapping 
    && checkBijective sb mapping 
    && checkTopologyMap ta tb mapping 
    && checkRelationMap ra rb mapping

checkMapping :: Eq a => Set a -> Set (a,b) -> Bool
checkMapping sa mapping = all (\ x -> size (getMappings x mapping) == 1) sa

getMappings :: Eq a => a -> Set (a,b) -> Set (a,b)
getMappings x = Data.Set.filter (\ (y,_) -> y == x)

checkBijective :: Eq b => Set b -> Set (a,b) -> Bool
checkBijective sb mapping = all (\ y -> size (getPreimages y mapping) == 1) sb

checkTopologyMap :: (Eq a, Eq b, Ord a, Ord b) => Set (Set a) -> Set (Set b) -> Set (a,b) -> Bool
checkTopologyMap ta tb mapping = mapTop mapping ta == tb && premapTop mapping tb == ta

mapTop :: (Ord a, Ord b) => Set (a,b) -> Set (Set a) -> Set (Set b)
mapTop mapping = Data.Set.map (Data.Set.map (evaluateMap mapping))

premapTop :: (Ord a, Ord b) => Set (a,b) -> Set (Set b) -> Set (Set a)
premapTop mapping = Data.Set.map (Data.Set.map (getPreimage mapping))

checkRelationMap :: (Eq a, Eq b, Ord a, Ord b) => Relation a -> Relation b -> Set (a,b) -> Bool
checkRelationMap ra rb mapping = mapRel mapping ra == rb && premapRel mapping rb == ra

mapRel :: (Ord a, Ord b) => Set (a,b) -> Relation a -> Relation b
mapRel mapping = Data.Set.map (Data.Bifunctor.bimap (evaluateMap mapping) (evaluateMap mapping))

premapRel :: (Ord a, Ord b) => Set (a,b) -> Relation b -> Relation a
premapRel mapping = Data.Set.map (bimap (getPreimage mapping) (getPreimage mapping))







\end{code}