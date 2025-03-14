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

-- when lattice is a poset, this should return a singleton with the top,
-- or empty set with no top, so nothing
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

-- TODO TEST THIS! -- xx Es
checkDistributivity :: Eq a => Lattice a -> Bool
-- check for any interpretation, that 
-- law 1: (a v (b n c) == (a v b) n (a v c)) 
-- law 2: and (a n (b n c) == (a n b) v (a n c)) 
-- this function takes any tuple of three points in the lattice,
-- and checks whether law 1 & law 2 hold.
checkDistributivity (L (OS s _) m v) = and 
                        [(a `m` (b `v` c) == (a `m` b) `v` (a `m` c))
                            && (a `v` (b `m` c) == (a `v` b) `m` (a `v` c))
                        | a <- Set.toList s, b <- Set.toList s, c <- Set.toList s]

-- function now checks whether join and meet under function are in lattice
-- should still check whether coincides with actual meet and join in lattice
checkClosedMeetJoin :: Ord a => Lattice a -> Bool
checkClosedMeetJoin l = all (\x -> elem (pairMeet x) lSet ) j -- x is arb. pair in l
                        &&
                        all (\x -> elem (pairJoin x) lSet) j
    where 
        lSet = set $ carrier l
        j = Set.cartesianProduct lSet lSet -- sets of pairs
        pairMeet = uncurry (meet l) 
        pairJoin = uncurry (join l)

checkBDLattice :: Ord a => Lattice a -> Bool
checkBDLattice l = checkBoundedness l
                    &&
                   checkDistributivity l
                    &&
                   checkClosedMeetJoin l 

-- Helper functions for checkClosedMeetJoin
-- finds meet & join in lattice, independant of 
findMeet :: Ord a => Lattice a -> a -> a -> Maybe a
findJoin :: Ord a => Lattice a -> a -> a -> Maybe a
-- find all lower bounds, and take the maximum
-- needs top to be a maybe function
-- findMeet (L (OS set rel) _ _) x y  = findGreatest (OS upperBounds (filter (\(v,w) -> v ) rel))
                    -- where upperBounds = filter (\z -> (z, x) `Set.member` rel && (z, y) `Set.member` rel) (Set.toList set)
findMeet l x y = findGreatest (carrier l) (lowerBounds (carrier l) x y)
findJoin l x y = findLeast (carrier l) (upperBounds (carrier l) x y)

-- For some ordered set (X, <=), find the greatest element of some subset S of X
findGreatest :: Ord a => OrderedSet a -> Set.Set a -> Maybe a
-- findGreatest (OS s r) s = if all (\x -> (x, greatest) `Set.member` r) (Set.toList s) then Just greatest else Nothing
                    -- where greatest = foldr (\new old -> (if (old, new) `Set.member` r then new else old)) (head $ Set.toList s) s
findGreatest os s = Set.lookupMax $ Set.filter (\x -> all (\y -> (y, x) `Set.member` rel os) s) s

findLeast :: Ord a => OrderedSet a -> Set.Set a -> Maybe a
findLeast os s = Set.lookupMax $ Set.filter (\x -> all (\y -> (x, y) `Set.member` rel os) s) s

-- set of elements above a1 and a2
upperBounds :: Ord a => OrderedSet a -> a -> a -> Set.Set a
upperBounds os a1 a2 = Set.fromList [c | c <- Set.toList $ set os, (a1, c) `Set.member` (rel os) && 
                                                           (a2, c) `Set.member` (rel os)]

lowerBounds :: Ord a => OrderedSet a -> a -> a -> Set.Set a
lowerBounds os a1 a2 = Set.fromList [c | c <- Set.toList $ set os, (c, a1) `Set.member` (rel os) && 
                                                           (c, a2) `Set.member` (rel os)]

-- test ordered Set
myos :: OrderedSet Int
myos = Poset.closurePS $ OS (Set.fromList [0,1,2,3,4, 5]) (Set.fromList [(1,2), (2,4), (1,3),(3,4),(4,5)])

mylat :: Lattice Int
mylat = L myos (findMeet myos) (findJoin myos)

-- uses meet & join function inside lattice, for arb meets & joins
-- only works on finite lattices.
-- Boundedness of l is required for this function
arbMeet :: Lattice a -> a -> a -> a
arbJoin :: Lattice a -> a -> a -> a
--arbJoin l a1 a2  = rfold (\x y -> meet l $ x y) (fromJust $ top l) upperBs
                   -- where upperBs = [c | c <- (set carrier l), (c, a1) `Set.member` (rel carrier l), 
                                       --     (c, a2) `Set.member` (rel carrier l)] -- all elements above both a1 and a2
arbJoin = undefined
arbMeet = undefined

fromJust :: Maybe a -> a
fromJust = undefined

checkLattice :: Lattice a -> Bool
checkLattice = undefined 

makeLattice :: OrderedSet a -> Lattice a 
makeLattice = undefined

\end{code}