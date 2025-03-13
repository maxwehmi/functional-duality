\section{Disributive Lattices}

\begin{code}
module DistributiveLattices where

import Poset
import qualified Data.Set as Set 

data Lattice a = L {
    carrier :: OrderedSet a,
    meet :: a -> a -> a,
    join :: a -> a -> a 
    }


isTop :: Ord a => Lattice a -> a -> Bool
isTop l x = all (\y -> elem (y, x) (rel k)) (set k)
    where
     k = carrier l

top :: Ord a =>Lattice a -> Maybe a
top l = Set.lookupMax (Set.filter (isTop l) (set $ carrier l))

isBot :: Ord a => Lattice a -> a -> Bool
isBot l x = all (\y -> elem (x,y) (rel k)) (set k)
    where
     k = carrier l

bot :: Ord a =>Lattice a -> Maybe a
bot l = Set.lookupMin (Set.filter (isBot l) (set $ carrier l))


-- The four above functions are used to check if a given element of a given lattice is its top/bottom element and to obtain the top/bottom element of a lattice if it exists














checkBoundedness :: Ord a => Lattice a -> Bool
checkBoundedness l = top l /= Nothing && bot l /= Nothing 

checkDistributivity :: Lattice a -> Bool
checkDistributivity = undefined

checkClosedMeetJoin :: Lattice a -> Bool
checkClosedMeetJoin = undefined

checkLattice :: Lattice a -> Bool
checkLattice = undefined 

makeLattice :: OrderedSet a -> Lattice a 
makeLattice = undefined




\end{code}