{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
\section{Priestley Spaces}

\begin{code}
module PriestleySpaces where

import Data.Set (Set, toList, fromList, intersection, union, difference, filter, map)

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







\end{code}