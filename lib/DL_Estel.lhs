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
 
-- delete later:
-- type Relation a = Set.Set (a,a) 
-- data OrderedSet a = OS (Set.Set a) (Relation a) 

-- checks whether there is a top and a bottom element
checkBoundedness :: Lattice a -> Bool
checkBoundedness = undefined

-- OrderedSet :: (set :: Set.Set a,  relation :: Set.Set (a,a))
top :: Lattice a -> Maybe a
top = undefined

bottom :: Lattice a -> Maybe a
bottom = undefined

-- TODO TEST THIS! -- xx Es
checkDistributivity :: Eq a => Lattice a -> Bool
-- check for any interpretation, that 
-- law 1: (a v (b n c) == (a v b) n (a v c)) 
-- law 2: and (a n (b n c) == (a n b) v (a n c)) 
-- this function takes any tuple of three points in the lattice,
-- and checks whether law 1 & law 2 hold.
checkDistributivity (L (OS set _) m v) = and 
                        [(a `m` (b `v` c) == (a `m` b) `v` (a `m` c))
                            && (a `v` (b `m` c) == (a `v` b) `m` (a `v` c))
                        | a <- Set.toList set, b <- Set.toList set, c <- Set.toList set]

checkClosedMeetJoin :: Lattice a -> Bool
checkClosedMeetJoin = undefined

-- finds meet & join in lattice, independant of 
findMeet :: Lattice a -> a -> a -> Maybe a
findJoin :: Lattice a -> a -> a -> Maybe a
-- find all lower bounds, and take the maximum
-- needs top to be a maybe function
-- findMeet (L (OS set rel) _ _) x y  = findGreatest (OS upperBounds (filter (\(v,w) -> v ) rel))
                    -- where upperBounds = filter (\z -> (z, x) `Set.member` rel && (z, y) `Set.member` rel) (Set.toList set)
findMeet = undefined
findJoin = undefined

findGreatest :: Ord a => OrderedSet a -> Maybe a
findGreatest (OS set rel) = if all (\x -> (x, greatest) `Set.member` rel) (Set.toList set) then Just greatest else Nothing
                    where greatest = foldr (\new old -> (if (old, new) `Set.member` rel then new else old)) (head $ Set.toList set) set

-- test ordered Set
myos :: OrderedSet Int
myos = OS (Set.fromList [1,2]) (Set.fromList [(1,1), (1,2), (2,2)])

-- uses meet & join function inside lattice, for arb meets & joins
-- only works on finite lattices.
-- think about whether we can do this by folding???
arbMeet :: Lattice a -> a -> a -> a
arbJoin :: Lattice a -> a -> a -> a
-- arbJoin l a1 a2  = rfold (\x y -> meet l $ )
arbJoin = undefined
arbMeet = undefined

checkLattice :: Lattice a -> Bool
checkLattice = undefined 

makeLattice :: OrderedSet a -> Lattice a 
makeLattice = undefined

\end{code}