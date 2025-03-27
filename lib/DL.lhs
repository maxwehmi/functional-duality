\section{Distributive Lattices}



\begin{code}
module DL where

import qualified Data.Set as Set 
import qualified Data.Maybe as M
import Test.QuickCheck

import Poset
import Basics
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

instance (Ord a, Show a) => Show (Lattice a) where
    show l = show (carrier l) ++ "; Meet: " ++ show (Set.fromList [(x,y, meet l x y) | x <- Set.toList (set (carrier l)), y <- Set.toList (set (carrier l))])  ++ "; Join: " ++ show (Set.fromList [(x,y, join l x y) | x <- Set.toList (set (carrier l)), y <- Set.toList (set (carrier l))]) 

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
                        [a `m` (b `v` c) == (a `m` b) `v` (a `m` c)
                        | a <- Set.toList s, b <- Set.toList s, c <- Set.toList s]

\end{code}

In the definition of our lattice, the lattice comes with functions called 'meet' and 'join'. We want a lattice to be 
closed under meet and join and thus, we use 'checkClosedMeetJoin' as a function to check this. Let L
be a lattice. For two arbirtray elements $a,b \in L$, we want that (meet a b) $\in L$ and (join a b) $\in L$. 

\begin{code}

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

makeLattice :: Ord a => OrderedSet a -> Lattice a 
makeLattice os = L os (\x y -> M.fromJust $ findMeet preLattice x y) (\x y -> M.fromJust $ findJoin preLattice x y)
                where preLattice = L os const const -- give it two mock functions

\end{code}

To use QuickTests in our project, we have to have also an arbitrary instance for distributive lattices. 

\begin{code}
instance (Arbitrary a, Ord a) => Arbitrary (Lattice a) where
    arbitrary = sized randomPS where
        randomPS :: (Arbitrary a, Ord a) => Int -> Gen (Lattice a)
        randomPS n = do
            o <- resize (max n 1) arbitrary
            let l = fixLattice $ fixTopBottom o
            return $ makeLattice l 

fixTopBottom :: Ord a => OrderedSet a -> OrderedSet a
fixTopBottom o = collapseTops $ collapseBottoms o

collapseTops :: Ord a => OrderedSet a -> OrderedSet a
collapseTops (OS s r) = collapseElements 
    (Set.filter 
        (\ x -> Set.size (Set.filter (\ (y,_) -> y == x) r) == 1) 
    s) (OS s r)

collapseBottoms :: Ord a => OrderedSet a -> OrderedSet a
collapseBottoms (OS s r) = collapseElements 
    (Set.filter 
        (\ x -> Set.size (Set.filter (\ (_,y) -> y == x) r) == 1)
    s) (OS s r)

collapseElements :: Ord a => Set.Set a -> OrderedSet a -> OrderedSet a
collapseElements s (OS s' r) | Set.size s == 0 = OS s' r
                             | otherwise = cleanUp $ OS new_s new_r where
                                new_s = (s' `Set.difference` s) `Set.union` Set.singleton (Set.elemAt 0 s)
                                new_r = rel $ closureTrans $ OS s' (addRelations (Set.elemAt 0 s)) 
                                addRelations x = r `Set.union` succs x `Set.union` precs x
                                succs x = Set.map (\ (_,z) -> (x,z)) $ Set.filter (\ (y,_) -> y `elem` s) r 
                                precs x = Set.map (\ (z,_) -> (z,x)) $ Set.filter (\ (_,y) -> y `elem` s) r 

fixLattice :: Ord a => OrderedSet a -> OrderedSet a
fixLattice o = 
    let recurse_o = fixDistributivity $ fixJoinMeet o
    in if recurse_o == o
        then o
        else fixLattice recurse_o

loop :: Ord a => Set.Set (a,a) -> OrderedSet a -> ((a,a) -> OrderedSet a -> OrderedSet a) -> OrderedSet a
loop s o action | Set.size s == 0 = o
                | fst s0 `Set.notMember` set o = loop (Set.delete s0 s) o action
                | snd s0 `Set.notMember` set o = loop (Set.delete s0 s) o action
                | otherwise = loop (Set.delete s0 s) (action s0 o) action where
                    s0 = Set.elemAt 0 s

fixMeet :: Ord a => OrderedSet a -> OrderedSet a
fixMeet (OS s r) = loop (s `Set.cartesianProduct` s) (OS s r) (\ (x,y) o' -> collapseElements (calculateMeets o' x y) o')

fixJoin :: Ord a => OrderedSet a -> OrderedSet a
fixJoin (OS s r) = loop (s `Set.cartesianProduct` s) (OS s r) (\ (x,y) o' -> collapseElements (calculateMeets o' x y) o')

fixJoinMeet :: Ord a => OrderedSet a -> OrderedSet a
fixJoinMeet = fixMeet . fixJoin

fixDistributivity :: Ord a => OrderedSet a -> OrderedSet a
fixDistributivity (OS s r) = loop (s `Set.cartesianProduct` s) (OS s r) 
    (\ (x,y) o' -> case () of 
        _ | any distrFailN (set o') -> collapseElements (Set.fromList [x,y]) o'
          | otherwise -> o' where
            distrFailN z = calculateMeet (calculateJoin x y) (calculateJoin x z) /= calculateJoin x (calculateMeet y z) && x < z && y < z
            calculateMeet g h = Set.elemAt 0 $ calculateMeets o' g h
            calculateJoin g h = Set.elemAt 0 $ calculateJoins o' g h
            ) 

calculateMeets :: Eq a => OrderedSet a -> a -> a -> Set.Set a
calculateMeets (OS s r) x y = Set.filter (\ z -> lowerBound z && not (any (\ w -> (z,w) `elem` r && w /= z && lowerBound w) s)) s where
    lowerBound v = (v,x) `elem` r && (v,y) `elem` r

calculateJoins :: Eq a => OrderedSet a -> a -> a -> Set.Set a
calculateJoins (OS s r) x y = Set.filter (\ z -> upperBound z && not (any (\ w -> (w,z) `elem` r && w /= z && upperBound w) s)) s where
    upperBound v = (x,v) `elem` r && (y,v) `elem` r

cleanUp :: Eq a => OrderedSet a -> OrderedSet a 
cleanUp (OS s r) = OS s (Set.filter (\ (x,y) -> x `elem` s && y `elem` s) r)
\end{code}

\subsection{Morphisms}

We want to check wether two Lattices are isomorphic. This means checking that, under some function between them, immages preserve bot,top, and all meets and joins. These suffice for the preservation of distributivity and boundedness, so we do not need to explicitly check for those.

\begin{code}

functionMorphism:: (Ord a, Ord b) => Lattice a -> Lattice b -> Map a b -> Bool
functionMorphism l1  l2 f 
    | not(checkLattice l1 && checkLattice l2) = error "not lattices"
    | not (checkMapping s1 f) = error "not a mapping"
    | otherwise = checkBijective s2 f 
                &&
                (M.fromJust $ top l1, M.fromJust $ top l2) `Set.member` f
                &&
                (M.fromJust $ bot l1, M.fromJust $ bot l2) `Set.member` f
                && 
                all 
                (\(x,y) -> M.fromJust (findJoin l2 (getImage f x) (getImage f y)) == getImage f (M.fromJust (findJoin l1 x y)))
                (s1 `Set.cartesianProduct` s1)
                &&
                all
                (\(x,y) -> M.fromJust (findMeet l2 (getImage f x) (getImage f y)) == getImage f (M.fromJust (findMeet l1 x y)))
                (s1 `Set.cartesianProduct` s1)
                where
                    s1 = set $ carrier l1
                    s2 = set $ carrier l2                         
\end{code}

                        

% \begin{code}
%-- helper functions that redfine previous function to not have Maybe... type, for ease of typechecking ----------------
% realTop:: Ord a => Lattice a -> a
% realTop l 
%     | M.isNothing (top l) = error "there's no top"
%     | otherwise =  Set.elemAt 0 (Set.filter ( isTop l ) ( set $ carrier l ))


% realBot:: Ord a => Lattice a -> a
% realBot l 
%     | M.isNothing (bot l) = error "there's no bot"
%     | otherwise =  Set.elemAt 0 (Set.filter ( isBot l ) ( set $ carrier l ))

% realJoin :: Ord a => Lattice a -> a -> a -> a
% realJoin l x y
%     | not (checkLattice l) = error "not a lattice"
%     | otherwise = realLeast ( carrier l ) ( upperBounds ( carrier l ) x y )


% realMeet :: Ord a => Lattice a -> a -> a -> a
% realMeet l x y
%     | not (checkLattice l) = error "not a lattice"
%     | otherwise = realGreatest ( carrier l ) ( lowerBounds ( carrier l ) x y )

% realGreatest :: Ord a => OrderedSet a -> Set.Set a -> a
% realGreatest os s = Set.elemAt 0 $ Set.filter (\ x -> all (\ y -> (y , x ) `Set.member` rel os) s ) s

% realLeast :: Ord a => OrderedSet a -> Set.Set a -> a
% realLeast os s = Set.elemAt 0 $ Set.filter (\ x -> all (\ y -> (x , y ) `Set.member` rel os ) s) s
% \end{code}
