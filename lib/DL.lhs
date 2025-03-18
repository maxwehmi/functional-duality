\section{Distributive Lattices}



\begin{code}
module DL where

import Poset
import qualified Data.Set as Set 
import qualified Data.Maybe as M



\end{code}

This section is dedicated to Distributive Lattices. A lattice is a poset $P$ such that for every $a,b \in P$ the greatest lower bound of $\{a,b\}$ (the meet of $a,b: a \wedge b$) is in $P$ and least upper bound of $\{a,b\}$ (the join of $a,b: a \vee b$) is in $P$. 

On top of this, a distributive lattice is a lattice whose meet and join satisfiy the two distributive laws: if $(L,\wedge, \vee)$ is a lattice, then: 
\begin{enumerate}

\item $\forall a,b,c in L,    a \wedge (b \vee c) =  (a \wedge b) \vee (a \wedge c)$ 

\item $\forall a,b,c in L,    a \vee (b \wedge c) = (a \vee b) \wedge (a \vee c)$


\end{enumerate}

We define the data type of lattices in the following manner:



\begin{code}
data Lattice a = L {
    carrier :: OrderedSet a,
    meet :: a -> a -> a,
    join :: a -> a -> a 
    }

\end{code}

Not every object of type lattice is an actual lattice in the mathematical sense: in particular three conditions have to be met for an object "l" of type "Lattice a", to be an actual lattice.



\begin{itemize}

\item Since we are working with finite structures, each lattice is a bound lattice.Therefore given an object l of type Lattice a, the first thing to check is whether the object "carrier l" has a maximal and a least element.

\item The object "meet l" has to be defined on every two elements of the underlying set of "carrier l" and for every such two elements it has to return their greatest lower bound.


\item The object "join l" has to be defined on every two elements of the underlying set of "carrier l" and for every such two elements it has to return their least upper bound.




\end{itemize}


The aim of the following functions is to ensure that the objects of type "Lattice a" behave as desired.



\begin{code}

isTop :: Ord a => Lattice a -> a -> Bool
isTop l x = all (\y -> (y, x) `elem` rel k) (set k)
    where
     k = carrier l

-- when lattice is a poset, this should return a singleton with the top,
-- or empty set with no top, so nothing
top :: Ord a =>Lattice a -> Maybe a
top l = Set.lookupMax (Set.filter (isTop l) (set $ carrier l))

isBot :: Ord a => Lattice a -> a -> Bool
isBot l x = all (\y -> (x,y) `elem` rel k) (set k)
    where
     k = carrier l

bot :: Ord a =>Lattice a -> Maybe a
bot l = Set.lookupMin (Set.filter (isBot l) (set $ carrier l))


-- The four above functions are used to check if a given element of a given lattice is its top/bottom element and to obtain the top/bottom element of a lattice if it exists


checkBoundedness :: Ord a => Lattice a -> Bool
checkBoundedness l = M.isJust (top l) && M.isJust (bot l)

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
checkClosedMeetJoin l = all (\x -> pairMeet x `elem` lSet ) j -- x is arb. pair in l
                        &&
                        all (\x -> pairJoin x `elem` lSet) j
    where 
        lSet = set $ carrier l
        j = Set.cartesianProduct lSet lSet -- sets of pairs
        pairMeet = uncurry (meet l) 
        pairJoin = uncurry (join l)

checkMeetJoinMakeSense :: Ord a => Lattice a -> Bool
checkMeetJoinMakeSense l = and [Just (meet l x y) == findMeet l x y |x <- Set.toList (set (carrier l)), y <- Set.toList (set (carrier l))]

-- checks whether an element is in the underlying set of the lattice
inLattice :: Ord a => a -> Lattice a -> Bool
inLattice x l = x `Set.member` set (carrier l)

checkDL :: Ord a => Lattice a -> Bool
checkDL l =        checkBoundedness l
                    &&
                   checkDistributivity l
                    &&
                   checkLattice l 

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
upperBounds os a1 a2 = Set.fromList [c | c <- Set.toList $ set os, (a1, c) `Set.member` rel os && 
                                                           (a2, c) `Set.member` rel os]

lowerBounds :: Ord a => OrderedSet a -> a -> a -> Set.Set a
lowerBounds os a1 a2 = Set.fromList [c | c <- Set.toList $ set os, (c, a1) `Set.member` rel os && 
                                                           (c, a2) `Set.member` rel os]

-- test ordered Set
myos :: OrderedSet Int
myos = Poset.closurePoSet $ OS (Set.fromList [1,2,3,4, 5]) (Set.fromList [(1,2), (2,4), (1,3),(3,4),(4,5)])

-- not well-defined lattice
mylat1 :: Lattice Int
mylat1 = L myos (-) (+)

mylat :: Lattice Int
mylat = makeLattice myos

fromJust :: Maybe a -> a
fromJust (Just x) = x
fromJust Nothing = error "Sorry, but your poset is not closed under meet and joins"
 

-- check whether actual meet & join align with functions, check whether closed under meet and join
checkLattice :: Ord a => Lattice a -> Bool
checkLattice l = checkMeetJoinMakeSense l && checkClosedMeetJoin l

-- I expect that the poset is already closed under meets and joins
-- if ordered set is not already closed under meet and join, the lattice it makes won't be either
makeLattice :: Ord a => OrderedSet a -> Lattice a 
makeLattice os = L os (\x y -> fromJust $ findMeet preLattice x y) (\x y -> fromJust $ findJoin preLattice x y)
                where preLattice = L os const const -- give it two mock functions

\end{code}