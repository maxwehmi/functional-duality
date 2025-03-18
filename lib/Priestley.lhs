
\begin{code}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use infix" #-}
module Priestley where
import Data.Set (Set, toList, fromList, intersection, union, difference, filter, map, size, elemAt, isSubsetOf, member, empty, cartesianProduct)
import Data.Bifunctor (bimap)
import DL 
import Poset
import Mapping
\end{code}
\section{Priestley Spaces}

We introduce the main data types of this section. \newline 
In the definition of the types, we keep it as close as possible to their mathematical counterparts: 
\begin{enumerate}[label=\ roman *)]
\item a Topological Space is a set \textit{X} endowed with a collection of subsets of \textit{X} $\tau$. \newline 
In particular it is required that $X,\emptyset$ are elements of $\tau$, and $\tau$ is closed under finitary intersections and arbitrary unions. \newline 
Notice that, since we are working with finite cases, finitary and arbitrary unions (and intersections) coincide.
\item a Priestley space is a Topological Space endowed with a partial order $\leq$ on its carrier set. Moreover, it satisfies the following Priestley Separation Axiom:
$$ \text{PSA:} x\not \leq y \rightarrow \exists C\subseteq X (C=\uparrow C \& C \in \tau \& (X\setminus C)\in \tau \& x\in C \& y\notin C) $$
Intuitively, for any $x,\,y$ that are not related by $\leq$, there exists a upwards-closed set in the topology that separates them. Moreover, the complement of such set should also be in the topology.\newline 
Elements of $\tau$ such that their complement in $X$
 also is in the topology are called \enquote{Clopen Sets}.
  \end{enumerate}
\begin{code}
type Topology a = Set (Set a)

data TopoSpace a = TS {
    setTS :: Set a,
    topologyTS :: Topology a
}

data PriestleySpace a = PS {
    setPS :: Set a,
    topologyPS :: Topology a,
    relationPS :: Relation a
}

\end{code}




\subsection{Set-theoretic preliminaries}
In order to deal effectively with topological spaces, we first define some Set-theoretic preliminary notions. In addition to the standard functions drawn from \enquote{Data.set} library
we define new functions to compute the closure of a given set under arbitrary unions and intersections. \newline 
In both cases, we first define functions to perform a one-step intersection (resp. union) of a set with itself, and then iterate the function until the resulting set 
is identical to its own one-step intersection (resp. union) closure. 

\begin{code} 
unionStep :: (Ord a) => Topology a -> Topology a
unionStep x = Data.Set.map (uncurry union) (cartesianProduct x x)
intersectionStep :: (Ord a) => Topology a -> Topology a
intersectionStep x = Data.Set.map (uncurry intersection) (cartesianProduct x x)

unionClosure :: (Eq a, Ord a) => Topology a -> Topology a
unionClosure y = do 
                let cycle1 = unionStep y
                if y == cycle1 
                then y
                else unionStep cycle1 
intersectionClosure :: (Eq a, Ord a) => Topology a -> Topology a
intersectionClosure z = do 
                let cycle1 = intersectionStep z
                if z == cycle1 
                then z
                else intersectionStep cycle1 
\end{code}

\subsection{Topology basics}
We now introduce some machinery to work on topological spaces, and in particular, to ensure our spaces respect the Priestley separation axiom.\newline 

The following function check whether a Topological space given as input respects the requirements spelled above.\newline 
It is assumed that the input is finite. In case the input does not respect the conditions, the second function adjusts the space so that it meets the requirements.

\begin{code}
checkTopology :: Ord a => TopoSpace a -> Bool
checkTopology (TS space top) = member space top && member empty top && unionClosure top == top && intersectionClosure top == top 
\end{code}

\begin{code}
fixTopology :: Ord a => TopoSpace a -> TopoSpace a
fixTopology (TS space top) = TS space fixedTop  where 
    fixedTop  = fromList [space, empty] `union` unionClosure (intersectionClosure top)

\end{code}
The next functions allow us to extract from a given Priestley space its underlying set together with the topology, and its underlying carrier set together with its order.
\begin{code}

getTopoSpace :: PriestleySpace a -> TopoSpace a
getTopoSpace p = TS (setPS p) (topologyPS p)

getOrderedSet :: PriestleySpace a -> OrderedSet a
getOrderedSet p = OS (setPS p) (relationPS p)
\end{code}

Next, we define a function to check whether a given Space really is a Priestley space. \newline 
We make use of some secondary helper functions:
\begin{enumerate}[label=\ roman *)]
\item the implementation for \enquote{implies} is routine,
\item the \enquote{allPairs} function extracts the totality of order pairs,
from the carrier set $X$ (this is required for the antecedent of the PSA axiom above),
\item the \enquote{clopUpset} function extracts all the elements from the topology which are both upward-closed and clopen by checking that their complement with respect to the space also is in the topology, and by checking that their are identical to their upwards-closure.\newline 
Recall that a subset $S$ of an ordered set is upward-closed if and only if whenever $x\in S$ and $x\leq y$
 implies $y\in S$.  \newline
 This function makes use of the \enquote{upClosure} function, which computes the upwards-closure of any given set with respect to the given order.
 


\end{enumerate}
The output of those is then fed to the \enquote{checkPSA} function, which then ensures the validity of the Priestley separation axiom for all points in $X$ not related by $\leq$.

\begin{code}
checkPriestley :: (Eq a, Ord a) => PriestleySpace a -> Bool
checkPriestley p = checkTopology (getTopoSpace p) && checkPoset (getOrderedSet p) && checkPSA p 

checkPSA :: (Eq a, Ord a) => PriestleySpace a -> Bool

checkPSA (PS space top order) = all (\ pair -> 
 implies (pair `notElem` order) (any (\ open -> elem (fst pair) open 
   && notElem (snd pair) open) (clopUp (PS space top order)) )) $ allPairs space 

allPairs :: Set a -> [(a,a)]
allPairs space = [(x,y) | x <- toList space ,y <- toList space ]

implies :: Bool -> Bool -> Bool
implies x y = not x || y

clopUp :: Ord a => PriestleySpace a -> Topology a
clopUp (PS space top ord) = intersection (clopens top) (upsets top) where 
        clopens = Data.Set.filter (\ x -> difference space x `elem` top)  
        upsets = Data.Set.filter (\ y -> y == upClosure y ord)

upClosure :: (Eq a, Ord a) => Set a -> Relation a -> Set a 
upClosure set1 relation = Data.Set.map snd (Data.Set.filter (\ x -> fst x `elem` set1 ) relation) `union` set1 
\end{code}
\subsection{Dual maps and Isomorphisms}
We present some functions to check basic properties of topological spaces.
In particular, we want to be able to decide whether two spaces are isomorphic. this is going to come in handy when exploring the duality with algebras. \newline 
We also present the first step towards implementing the algebra duality: keeping things brief, the set of Clopen Upset of a Priestley space 
is going to form a distributive lattice under the order induced by set-theoretic inclusion. \newline 
To this extent, we implement a function to extract an order based on set-theoretic inclusion between sets, which we canlater apply to the Clopen Upsets of our topology.\newline 
Next, we construct a lattice using the Clopen Upsets of our topological space and endowing this set with the desired inclusion-order. We make use of functions from the \enquote{DL} section to both construct the lattice and check it is distributive.
\begin{code}

inclusionOrder :: Ord a => Topology a -> Relation (Set a)
inclusionOrder x = fromList [ (z ,y) |  z <- toList x, y <- toList x, isSubsetOf z y ]

clopMap :: Ord a => PriestleySpace a -> Lattice (Set a)
clopMap  ps = do 
              let result = makeLattice $  OS (clopUp ps) (inclusionOrder (clopUp ps)) 
              if checkDL result then result else error "104!"

\end{code}

When working with Priestley Space, we want to be able to check if two given ones are "similar enough", i.e. isomorphic. This will become important when we want to confirm that a Priestley Space is isomorphic to the dual of its dual. \\
To check isomorphism, we have to be given two Priestley Spaces and a map between them. The map is an isomorphism, if it is actually a map, bijective, a homoemorphism on the topological spaces and an order isomorphism on the relations. If the map is an isomorphism, the spaces are isomorphic. 

\begin{code}
checkIso :: (Eq a, Ord a) => PriestleySpace a -> PriestleySpace a -> Map a a -> Bool
checkIso (PS sa ta ra) (PS sb tb rb) mapping = checkMapping sa mapping 
    && checkBijective sb mapping 
    && checkHomoemorphism ta tb mapping
    && checkOrderIso ra rb mapping
\end{code}

Assuming bijectivity (by laziness of \&\&), to check that the given map is a homeomorphism, we have to check that it is an open and continuous map, i.e. it maps opens to opens and the preimages of opens are also open. This means that applying the map to an open set in the topology of the domain should yield an element of the topology of the codomain, so applying it to the set of opens of the domain (its topology) should yield a subset of the opens of the codomain (its topology). Similarly, we check that the preimage of the topology of the codomain is a subset of the topology of the domain.

\begin{code}
checkHomoemorphism :: (Ord a, Ord b) => Topology a -> Topology b -> Map a b -> Bool
checkHomoemorphism ta tb mapping = 
    mapTop mapping ta `isSubsetOf` tb
    && premapTop mapping tb `isSubsetOf` ta
\end{code}

To apply the map to every open and thus every element of every open, we have to nest \verb:Data.Set.map: twice. Again, we deal similarly with the preimages.

\begin{code}
mapTop :: (Ord a, Ord b) => Map a b -> Topology a -> Topology b
mapTop mapping = Data.Set.map (Data.Set.map (getImage mapping))

premapTop :: (Ord a, Ord b) => Map a b -> Topology b -> Topology a
premapTop mapping = Data.Set.map (Data.Set.map (getPreimage mapping))
\end{code}

Lastly, it remains the check that the map is an order isomorphism, which means that two elements $x,y$ of the domain satisfy $x\leq y$ in the domain iff $f(x)\leq f(y)$ in the codomain (here $f$ is the map). This means that applying the map component wise to every pair of the relation in the domain should yield the relation of the codomain and vice versa. 

\begin{code}
checkOrderIso :: (Ord a, Ord b) => Relation a -> Relation b -> Map a b -> Bool
checkOrderIso ra rb mapping = mapRel mapping ra == rb && premapRel mapping rb == ra
\end{code}

Similar to above, we have to nest \verb:Data.Set.map: with \verb:Data.Bifunctor.bimap: to apply the map to both components of all pairs in the relation.

\begin{code}
mapRel :: (Ord a, Ord b) => Map a b -> Relation a -> Relation b
mapRel mapping = Data.Set.map (Data.Bifunctor.bimap (getImage mapping) (getImage mapping))

premapRel :: (Ord a, Ord b) => Map a b -> Relation b -> Relation a
premapRel mapping = Data.Set.map (bimap (getPreimage mapping) (getPreimage mapping))







\end{code}