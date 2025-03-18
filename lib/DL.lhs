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

 \item $\forall a,b,c \in L,    a \wedge (b \vee c) =  (a \wedge b) \vee (a \wedge c)$ 

 \item $\forall a,b,c \in L,    a \vee (b \wedge c) = (a \vee b) \wedge (a \vee c)$


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
\\
\\
The 'top' and 'bottom' functions will give the top and bottom elements of a lattice,
and 'isTop' and 'isBottom' checks whether some element in the lattice is actually the 
top or bottom element. Furthermore, the 'checkBoundedness' function will check the existence
of a top and bottom element in a lattice. 


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

\end{code}

We want to work with distributive lattices. A lattice $L$ is distributive if for any $a,b,c \in L$ the following laws hold:
\begin{itemize}
\item Law 1: $a \vee (b \wedge c) = (a \vee b) \wedge (a \vee c)$
\item Law 2: $a \wedge (b \vee c) = (a \wedge b) \vee (a \wedge c)$
\end{itemize}
The function 'checkDistributivity' checks whether a lattice is distributive. Furthermore, law 1 and 2 are equivalent
and so the function will only check law 1, which is sufficient.

\begin{code}

checkDistributivity :: Eq a => Lattice a -> Bool
checkDistributivity (L (OS s _) m v) = and 
                        [(a `m` (b `v` c) == (a `m` b) `v` (a `m` c))
                        | a <- Set.toList s, b <- Set.toList s, c <- Set.toList s]

\end{code}

In the definition of our lattice, the lattice comes with functions called 'meet' and 'join'. We want a lattice to be 
closed under meet and join and thus, we use 'checkClosedMeetJoin' as a function to check this. Let L
be a lattice. For two arbirtray elements $a,b \in L$, we want that (meet a b) $\in L$ and (join a b) $\in L$. 

\begin{code}

-- maybe use this function but do it to ordered sets instead of lattices?
-- rewrite with more intuitive variable names?
checkClosedMeetJoin :: Ord a => Lattice a -> Bool
checkClosedMeetJoin l = all (\x -> pairMeet x `elem` lSet ) j -- x is arb. pair in l
                        &&
                        all (\x -> pairJoin x `elem` lSet) j
    where 
        lSet = set $ carrier l
        j = Set.cartesianProduct lSet lSet -- sets of pairs
        pairMeet = uncurry (meet l) 
        pairJoin = uncurry (join l)


\end{code}

Furthermore, we desire a function that checks whether some lattice is well-defined,
meaning that the function 'meet' and 'join' that come with our lattice correspond with the 
actual meet and join in the ordered set underlying the lattice. That is what the function
'checkMeetJoinMakeSense' does.

\begin{code}

checkMeetJoinMakeSense :: Ord a => Lattice a -> Bool
checkMeetJoinMakeSense l = and [Just (meet l x y) == findMeet l x y
                                && Just (join l x y) == findJoin l x y
                                |x <- Set.toList (set (carrier l)), y <- Set.toList (set (carrier l))]

\end{code}

Besides using the functions the lattice comes with for finding meets and joins, namely 'meet' and 
'join', we also need functions that will find the actual meet and join in the lattice by 
looking at the poset underlying the lattice. These functions are called 'findMeet' and 'findJoin'.Applicative
\\
\\
Let $L$ be a lattice and let $a,b \in L$ be arbitrary elements. The meet $a \wedge b$ is defined
as the greatest lower bound, and the join $a \vee b$ as the least upper bound. That is why we use helper
functions to find the upper bounds and lower bounds of $a$ and $b$, namely 'upperBounds' and 'lowerBounds'.

Subsequently, the functions 'findGreatest' and 'findLeast' will find the greatest or least element
of a subset of some lattice $L$ with respect to the ordering inside $L$.
\\
\\
Now suppose that our lattice $L$ was not a lattice after all, meaning that $L$ is not closed under 
meet and join. Then either the set of upper bounds or lower bounds will be empty, or there will be 
no greatest or least element in the set. In those cases 'findMeet' and 'findJoin' return 'Nothing'. 
In cases the functions are succesful, it will return 'Just x' where $x$ is the meet or join of the two 
input elements. 

\begin{code}

-- Helper functions for checkClosedMeetJoin
-- finds meet & join in lattice, independant of 
findMeet :: Ord a => Lattice a -> a -> a -> Maybe a
findJoin :: Ord a => Lattice a -> a -> a -> Maybe a
-- find all lower bounds, and take the maximum
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

\end{code}

To check whether some object of type 'Lattice' is actually a lattice, we check whether it is 
well-defined with respect to 'meet' and 'join' and check whether it is closed under binary
meets and joins. 

\begin{code}

-- check whether actual meet & join align with functions, check whether closed under meet and join
checkLattice :: Ord a => Lattice a -> Bool
checkLattice l = checkMeetJoinMakeSense l && checkClosedMeetJoin l

\end{code}

A distributive lattice $L$ is a bounded lattice, which follows the distributivity laws.
In our function 'checkDL', we check whether an object of type 'Lattice' is a lattice,
bounded and distributive.

As we are working in the finite case, any lattice is bounded as the finite join of all the
elements would be the top element, and the finite meet of all elements the bottom element.

\begin{code}

checkDL :: Ord a => Lattice a -> Bool
checkDL l =        checkLattice l 
                    &&
                   checkBoundedness l
                    &&
                   checkDistributivity l
                    
                   

\end{code}

Lastly, we want to be able to go from the type 'OrderedSet' to the type of 'Lattice'. 
In our function makeLattice the ordered set given as input is used as the structure of the 
lattice and the functions for 'meet' and 'join' are added. 

Still to implement is to add a check that makes sure the input ordered set is closed under meet 
and joins. 

\begin{code}

fromJust :: Maybe a -> a
fromJust (Just x) = x
fromJust Nothing = error "Sorry, but your poset is not closed under meet and joins"

makeLattice :: Ord a => OrderedSet a -> Lattice a 
makeLattice os = L os (\x y -> fromJust $ findMeet preLattice x y) (\x y -> fromJust $ findJoin preLattice x y)
                where preLattice = L os const const -- give it two mock functions

\end{code}

Below are a few test cases. 'myos' is a poset. Furthermore, 'mylat1' is a non well-defined lattice, meaning
that the functions for 'meet' and 'join' do not coincide with 'findMeet' and 'findJoin'. Lastly, mylat is 
a lattice. 

\begin{code}

myos :: OrderedSet Int
myos = Poset.closurePoSet $ OS (Set.fromList [1,2,3,4, 5]) (Set.fromList [(1,2), (2,4), (1,3),(3,4),(4,5)])

-- not well-defined lattice
mylat1 :: Lattice Int
mylat1 = L myos (-) (+)

mylat :: Lattice Int
mylat = makeLattice myos

myos2 :: OrderedSet Int
myos2 = Poset.closurePoSet $ OS (Set.fromList [1,2,3,4,5]) (Set.fromList [(1,2), (2,4), (1,3),(3,4)])

mylat2 :: Lattice Int
mylat2 = makeLattice myos2

\end{code}