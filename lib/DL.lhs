\section{Distributive Lattices}
\label{DL}

\begin{comment}
Once again, let us gloss over some ugly initial imports, again necessary for pretty printing. We'll see more about it in its \hyperref[sec:dlprinting]{dedicated section} for the relevant code.


\begin{code}
module DL where

import Data.GraphViz.Commands
import Data.GraphViz.Printing

\end{code}
\end{comment}

% We import \texttt{Data.Maybe} to deal with certain functions not being assured to have a value, and otherwise simply carryover our previous work.
\begin{comment}
\begin{code}
import qualified Data.Set as Set 
import qualified Data.Maybe as M
import Test.QuickCheck
import Poset
import Basics
\end{code}
\end{comment}

\subsection{Definition}
This section is dedicated to Distributive Lattices. A lattice is a poset $P$ such that for every $a,b \in P$ 
the greatest lower bound of $\{a,b\}$ (the meet of $a,b: a \wedge b$) is in $P$ and least upper bound 
of $\{a,b\}$ (the join of $a,b: a \vee b$) is in $P$. 

On top of this, a distributive lattice is a lattice whose meet and join satisfiy the distributivity laws:
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
    show l = "(" ++ show (carrier l) ++ ";\n Meet: " ++ show ( [(x,y, meet l x y) | x <- Set.toList (set (carrier l)), y <- Set.toList (set (carrier l))])  ++ ";\n Join: " ++ show ([(x,y, join l x y) | x <- Set.toList (set (carrier l)), y <- Set.toList (set (carrier l))]) ++ ")" 
\end{code}

But note an object of this type is not necessarily an actual lattice mathematically. In partiuclar, we must check that the functions \texttt{meet} and \texttt{join} actually behave as they should mathematically, and that objects \texttt{meet l}, \texttt{join l} always exist, respecting the definition.

Furthemore, we'll be working with in finite cases. Thus our lattice should be \emph{bounded}, meaning it has a minimal ($\top$ called top) and a maximal ($\bot$ called bottom) element. 
\newline
However, since we are working with finite structures, each lattice is a bounded lattice by taking the meet or join of all the elements. We implemented checks regardless, but omit them here for space concerns.


\subsection{Checking Lattices}
\begin{comment}
The aim of the following functions is to ensure that any object of type \texttt{Lattice a} behave as desired.
\paragraph{Boundedness}
The \texttt{top} and \texttt{bottom} functions will give the top and bottom elements of a lattice, and \texttt{isTop} and \texttt{isBottom}checks whether some element in the lattice is actually the 
top or bottom element. Then, the \texttt{checkBoundedness} function will check the existence of a top and bottom element in a lattice by just checking if \texttt{top} and \texttt{bot} return a value. 


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
\end{comment}

\paragraph{Meets and Joins}
Now, as mentioned above a lattice $L$ should be closed under meets and joins for any two objects in the lattice. The function \texttt{checkClosedMeetJoin} checks precisely this using the \texttt{meet} and \texttt{join} function part of the lattice
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

Furthermore, we need a function that checks whether some lattice is well-defined, meaning that the function \texttt{meet} and \texttt{join} that come with our data type correspond with the actual meet and join of the ordered set. For this, we want functions that will find the actual meet and join in the lattice. These are \texttt{findMeet} and \texttt{findJoin}.

We'll need to find  greatest lower bound and least upper bound. So we have  helper functions \texttt{upperBounds} and \texttt{lowerBounds}. Then, the functions \texttt{findGreatest} and \texttt{findLeast} will find the greatest or least element. These funtcions are straighforward, so we omitt them.
\newline
Since we might not be in front of a lattice when we call the function, we must return a \texttt{Maybe} value.

\begin{code}
checkMeetJoinMakeSense :: Ord a => Lattice a -> Bool
checkMeetJoinMakeSense l = and [Just (meet l x y) == findMeet l x y
                                && Just (join l x y) == findJoin l x y
                                |x <- Set.toList (set (carrier l)), y <- Set.toList (set (carrier l))]

findMeet :: Ord a => Lattice a -> a -> a -> Maybe a
findJoin :: Ord a => Lattice a -> a -> a -> Maybe a

findMeet l x y = findGreatest (carrier l) (lowerBounds (carrier l) x y)
findJoin l x y = findLeast (carrier l) (upperBounds (carrier l) x y)
\end{code}

\begin{comment}
\begin{code}
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
\end{comment}

\paragraph{Distributivity}
We want to work with distributive lattices. As mentioned above, a lattice $L$ is distributive if for any $a,b,c \in L$ the distributivity laws hold. Note the laws are inter-derivable. So it suffices to check just one.

\begin{code}
checkDistributivity :: Eq a => Lattice a -> Bool
checkDistributivity (L (OS s _) m v) = and 
                        [a `m` (b `v` c) == (a `m` b) `v` (a `m` c)
                        | a <- Set.toList s, b <- Set.toList s, c <- Set.toList s]
\end{code}

\paragraph{Bringing it together}
Then we can check whether a lattice object \texttt{l} is actually a lattice in the mathematical sense. Aswell as it being distributive

% Note that as we are working in the finite case, checking boundedness is unnecessary as the bounds already exists for finite lattices. However, we have included this for the completeness of implementation.

\begin{code}
checkLattice :: Ord a => Lattice a -> Bool
checkLattice l = checkMeetJoinMakeSense l && checkClosedMeetJoin l

checkDL :: Ord a => Lattice a -> Bool
checkDL l =        checkLattice l 
                    &&
                   checkBoundedness l
                    &&
                   checkDistributivity l
\end{code}


\subsection{Generating a Lattices}
We also want to be able \emph{make} a lattice of type \texttt{Lattice}  from a given \texttt{OrderedSet}.

For this, we use the constructor on the ordered set with "mock" functions to make it of the \texttt{Lattice} type. Then we forcing them to be the \texttt{findMeet} and \texttt{findJoin} insetad, we'll have something that is indeed a lattice.

\begin{code}
makeLattice :: Ord a => OrderedSet a -> Lattice a 
makeLattice os = L os (\x y -> M.fromJust $ findMeet preLattice x y) (\x y -> M.fromJust $ findJoin preLattice x y)
                where preLattice = L os const const -- give it two mock functions
\end{code}

When, at later stages, we will construct distributive lattices from Priestely spaces, we will get structures whose elements are sets themselves. 

\begin{comment}To prevent a blow-up in size (especially, when dualizing twice), we introduce two functions, which creates a new lattice out of a given one. This new one is isomorphic to the original one, but its elements are of type \texttt{Int}. This can make computation faster.

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

\paragraph{Arbitrary lattices}
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
\end{comment}


\subsection{Morphisms} 

We want to check wether two Lattices are isomorphic. Two lattices $L,L'$ are isomrophic if there is an function $f: L \to L'$ such that:
\begin{itemize}
\item $f$ is a bijection
\item Top and bottme are preserved: $f(\top) = \top'$ and $f(\bot')= \bot'$
\item Meets are preserved: $f(x \wedge y) = f(x) \wedge f(y)$
\item Joins are preserved: $f(x \vee y) = f(x) \vee f(y)$.

\end{itemize}

The code for this mirrors the definition straighforwardly, if with some clutter to grab values. 

\begin{code}
functionMorphism:: (Ord a, Ord b) => Lattice a -> Lattice b -> Map a b -> Bool
functionMorphism l1  l2 f 
    | not(checkLattice l1 && checkLattice l2) = error "The provided structures are not lattices."
    | not (checkMapping s1 f) = error "The provided map is not a mapping."
    | otherwise = 
        checkBijective s2 f 
        && f `getImage` M.fromJust (top l1) == M.fromJust (top l2)
        && f `getImage` M.fromJust  (bot l1) == M.fromJust (bot l2)
        
        &&  all 
        (\(x,y) -> M.fromJust (findJoin l2 (f `getImage` x) (f `getImage` y)) == f `getImage` M.fromJust (findJoin l1 x y))
            (s1 `Set.cartesianProduct` s1)
        
        &&  all
        (\(x,y) -> M.fromJust (findMeet l2 (f `getImage` x) (f `getImage` y)) == f `getImage` M.fromJust (findMeet l1 x y))
            (s1 `Set.cartesianProduct` s1)
        where
            s1 = set $ carrier l1
            s2 = set $ carrier l2                         
\end{code}


\paragraph{Printing machinery} \label{sec:dlprinting}
% \begin{code}
% showLattice ::(Ord a, Data.GraphViz.Printing.PrintDot a) => Lattice a -> IO ()
% showLattice l = runGraphvizCanvas' (toGraphRel (rel (fromReflTrans $ carrier l))) Xlib

% myos1 :: OrderedSet Int
% myos1 = Poset.closurePoSet $ OS (Set.fromList [1,2,3,4, 5]) (Set.fromList [(1,2), (2,4), (1,3),(3,4),(4,5)])
% \end{code}


% \subsection{Printing machinery}


Analogously to its Poset-counterpart, this function actually prints the Lattice.\footnote{for more detail, see the \hyperref[sec:posetprinting]{subsection 3.4}}

\begin{code}
showLattice ::(Ord a, PrintDot a) => Lattice a -> IO ()
showLattice l = runGraphvizCanvas' (toGraphOrd (fromReflTrans $ carrier l)) Xlib
\end{code}
