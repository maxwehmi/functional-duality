\section{Distributive Lattices}



\begin{code}
module DL where

import Data.GraphViz.Commands
import Data.GraphViz.Printing
import qualified Data.Set as Set 
import qualified Data.Maybe as M
import Test.QuickCheck
import Poset
import Basics
\end{code}

This section is dedicated to Distributive Lattices. A lattice is a poset $P$ such that for every $a,b \in P$ 
the greatest lower bound of $\{a,b\}$ (the meet of $a,b: a \wedge b$) is in $P$ and least upper bound 
of $\{a,b\}$ (the join of $a,b: a \vee b$) is in $P$. 

On top of this, a distributive lattice is a lattice whose meet and join satisfiy the two distributivity laws: 
if $(L,\wedge, \vee)$ is a lattice, then: 
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
    show l = show (carrier l) ++ ";\n Meet: " ++ show ( [(x,y, meet l x y) | x <- Set.toList (set (carrier l)), y <- Set.toList (set (carrier l))])  ++ ";\n Join: " ++ show ([(x,y, join l x y) | x <- Set.toList (set (carrier l)), y <- Set.toList (set (carrier l))]) 

\end{code}

\subsection{Lattice definition} Well-definedness of lattices
Not every object of type lattice is an actual lattice in the mathematical sense: 
in particular three conditions have to be met for an object "l" of type "Lattice a", to be an actual lattice.

\begin{itemize}

 \item "l" should be \textit{bounded}, meaning it has a minimal (top) and a maximal (bottom) element. 
 However, since we are working with finite structures, 
 each lattice is a bounded lattice by taking the meet or join of all the elements. 

 \item The object "meet l" has to be defined on every two elements $a,b \in l$ and for every 
 such two elements it has to return their greatest lower bound,
 which should again be an element in "carrier l".

 \item Similarly to the meet, the object "join l" has to be defined on 
 every two elements $a,b \in l$ and for every such two elements it has to return their least upper bound.
\end{itemize}

\subsection{Check lattice properties}
The aim of the following functions is to ensure that any object of type "Lattice a" behave as desired.
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

top :: Ord a =>Lattice a -> Maybe a
top l = Set.lookupMax (Set.filter (isTop l) (set $ carrier l))

isBot :: Ord a => Lattice a -> a -> Bool
isBot l x = all (\y -> (x,y) `elem` rel k) (set k)
    where
     k = carrier l

bot :: Ord a =>Lattice a -> Maybe a
bot l = Set.lookupMin (Set.filter (isBot l) (set $ carrier l))

checkBoundedness :: Ord a => Lattice a -> Bool
checkBoundedness l = M.isJust (top l) && M.isJust (bot l)

\end{code}

Now, as mentioned above a lattice $L$ should be closed under meets and joins for any two objects in the lattice. 
The function 'checkClosedMeetJoin' checks precisely this using the 'meet' and 'join' function part of the lattice
datatype. 

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
looking at the poset underlying the lattice. These functions are called 'findMeet' and 'findJoin', used 
in 'checkMeetJoinMakeSense'.
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

findMeet :: Ord a => Lattice a -> a -> a -> Maybe a
findJoin :: Ord a => Lattice a -> a -> a -> Maybe a

findMeet l x y = findGreatest (carrier l) (lowerBounds (carrier l) x y)
findJoin l x y = findLeast (carrier l) (upperBounds (carrier l) x y)


findGreatest :: Ord a => OrderedSet a -> Set.Set a -> Maybe a
findGreatest os s = Set.lookupMax $ Set.filter (\x -> all (\y -> (y, x) `Set.member` rel os) s) s

findLeast :: Ord a => OrderedSet a -> Set.Set a -> Maybe a
findLeast os s = Set.lookupMax $ Set.filter (\x -> all (\y -> (x, y) `Set.member` rel os) s) s

upperBounds :: Ord a => OrderedSet a -> a -> a -> Set.Set a
upperBounds os a1 a2 = Set.fromList [c | c <- Set.toList $ set os, (a1, c) `Set.member` rel os && 
                                                           (a2, c) `Set.member` rel os]

lowerBounds :: Ord a => OrderedSet a -> a -> a -> Set.Set a
lowerBounds os a1 a2 = Set.fromList [c | c <- Set.toList $ set os, (c, a1) `Set.member` rel os && 
                                                           (c, a2) `Set.member` rel os]

\end{code}

We want to work with distributive lattices. As mentioned above, a lattice $L$ is distributive if for any 
$a,b,c \in L$ the distributivity laws hold.

The function 'checkDistributivity' checks whether a lattice is distributive. Furthermore, law 1 and 2 are equivalent
and so the function will only check law 1, which is sufficient.

\begin{code}

checkDistributivity :: Eq a => Lattice a -> Bool
checkDistributivity (L (OS s _) m v) = and 
                        [a `m` (b `v` c) == (a `m` b) `v` (a `m` c)
                        | a <- Set.toList s, b <- Set.toList s, c <- Set.toList s]

\end{code}

The function below checks whether a lattice object 'l' is actually a lattice in the mathematical
sense. For this, it checks whether the 'meet' and 'join' function are well-defined with respect 
to the structure, and whether 'l' is closed under binary meets and joins.

\begin{code}

checkLattice :: Ord a => Lattice a -> Bool
checkLattice l = checkMeetJoinMakeSense l && checkClosedMeetJoin l

\end{code}

Finally, we combine all the functions above to check whether some object 'l' of type 'Lattice' 
is a distributive lattice. 'checkDL' verifies whether 'l' is a lattice, whether it is bounded, 
and if it follows the distributivity laws. 

Note that as we are working in the finite case, checking boundedness is unnecessary as the bounds
already exists for finite lattices. However, we have included this for the completeness of implementation.

\begin{code}

checkDL :: Ord a => Lattice a -> Bool
checkDL l =        checkLattice l 
                    &&
                   checkBoundedness l
                    &&
                   checkDistributivity l
                    
                
\end{code}

\subsection{Generating a lattice from a poset}

Lastly, we want to be able to go from the type 'OrderedSet' to the type of 'Lattice'. 
In our function makeLattice the ordered set given as input is used as the structure of the 
lattice and the functions for 'meet' and 'join' are added.

\begin{code}

makeLattice :: Ord a => OrderedSet a -> Lattice a 
makeLattice os = L os (\x y -> M.fromJust $ findMeet preLattice x y) (\x y -> M.fromJust $ findJoin preLattice x y)
                where preLattice = L os const const 

\end{code}

When, at later stages, we will construct distributive lattices from Priestely spaces, we will get structures whose elements are sets themselves. To prevent a blow-up in size (especially, when dualizing twice), we introduce two functions, which creates a new lattice out of a given one. This new one is isomorphic to the original one, but its elements are of type \verb:Int:. This can make computation faster.

The first returns, with the new space, also a map, and is meant to be used when we care about the old elements (the map allows to reconstruct them, for example we can check that the orignal and the simplifief lattices are indeed isomorphic). The second does not return a map and it is meant to be used when we do not care about the old elements, it is in particular useful for printing purposes, as we will see in due time.

\begin{code}        
simplifyDL :: Ord a => Lattice a -> (Lattice Int, Map a Int)
simplifyDL l = (makeLattice (OS s' r'), mapping) where
    s = (set . carrier) l 
    s' = Set.fromList $ take (Set.size s) [0..]
    mapping = Set.fromList [(Set.elemAt n s, n) | n <- Set.toList s']
    r' = Set.fromList [(x,y) | 
        x <- Set.toList s', 
        y <- Set.toList s', 
        (Set.elemAt x s, Set.elemAt y s) `elem` (rel . carrier) l]




simplifyDL1 :: Ord a => Lattice a -> Lattice Int
simplifyDL1 l = (makeLattice (OS s' r')) where
    s = (set . carrier) l 
    s' = Set.fromList $ take (Set.size s) [0..]
    r' = Set.fromList [(x,y) | 
        x <- Set.toList s', 
        y <- Set.toList s', 
        (Set.elemAt x s, Set.elemAt y s) `elem` (rel . carrier) l]
\end{code}



\subsection{Generating arbitrary lattices}

To use QuickTests in our project, we shall generate arbitrary instances for distributive lattices. 

\begin{code}
instance (Arbitrary a, Ord a) => Arbitrary (Lattice a) where
    arbitrary = sized randomPS where
        randomPS :: (Arbitrary a, Ord a) => Int -> Gen (Lattice a)
        randomPS n = do
            o <- resize (max n 2) arbitrary
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
            distrFailN z = calculateMeet (calculateJoin x y) (calculateJoin x z) /= calculateJoin x (calculateMeet y z) -- && x < z && y < z
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

We want to check wether two Lattices are isomorphic. This means checking that, under some function between them, 
images preserve bottom, top, and all meets and joins. 
These suffice for the preservation of distributivity and boundedness, so we do not need to explicitly check for those.

\begin{code}


something :: Ord b => Lattice b -> b
something l2 = M.fromJust $ top l2


functionMorphism:: (Ord a, Ord b) => Lattice a -> Lattice b -> Map a b -> Bool
functionMorphism l1  l2 f 
    | not(checkLattice l1 && checkLattice l2) = error "The provided structures are not lattices."
    | not (checkMapping s1 f) = error "The provided map is not a mapping."
    | otherwise = 
                checkBijective s2 f 
                &&
                getImage f (M.fromJust $ top l1) == M.fromJust (top l2)
                &&
                getImage f (M.fromJust $ bot l1) == M.fromJust (bot l2)
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

\subsection{Printing machinery}

Analogously to its Poset-counterpart, this function actually prints the Lattice.

\begin{code}

showLattice ::(Ord a, PrintDot a) => Lattice a -> IO ()
showLattice l = runGraphvizCanvas' (toGraphOrd (fromReflTrans $ carrier l)) Xlib

\end{code}
