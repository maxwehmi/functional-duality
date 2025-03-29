\section{Priestley Spaces}

We introduce the main data types of this section.

\begin{code}

module Priestley where


import Data.GraphViz.Commands
import Data.GraphViz.Printing
import qualified Data.Set as Set 
import Data.Bifunctor (bimap)
import Test.QuickCheck
import Poset
import Basics


\end{code}

In the definition of the types, we keep it as close as possible to their mathematical counterparts: 

\begin{enumerate}
\item a Topological Space is a set $X$ endowed with a collection $\tau$ of subsets of $X$. \newline 
In particular it is required that $X,\emptyset$ are elements of $\tau$, and $\tau$ is closed under finitary intersections and arbitrary unions. \newline 
Notice that, since we are working with finite cases, finitary and arbitrary unions (and intersections) coincide.
\item a Priestley space is a Topological Space endowed with a partial order $\leq$ on its carrier set. Moreover, it satisfies the following Priestley Separation Axiom: \newline
For any $x\not \leq y$, there is a clopen Upset $C$, such that $x \in C$ and $y \notin C$. \newline
Intuitively, for any $x,\,y$ that are not related by $\leq$, there exists a upwards-closed set in the topology that separates them. Moreover, the complement of such set should also be in the topology. Recall that a subset $S$ of an ordered set is upward-closed if and only if whenever $x\in S$ and $x\leq y$
implies $y\in S$.
Elements of $\tau$ such that their complement in $X$ also is in the topology are called "Clopen Sets".
\end{enumerate}

\begin{code}
type Topology a = Set.Set (Set.Set a)

data TopoSpace a = TS {
    setTS :: Set.Set a,
    topologyTS :: Topology a
}
    deriving (Eq, Ord,Show)

data PriestleySpace a = PS {
    setPS :: Set.Set a,
    topologyPS :: Topology a,
    relationPS :: Relation a
}
    deriving (Eq, Ord,Show)

\end{code}


\subsection{Set-theoretic preliminaries}
In order to deal effectively with topological spaces, we first define some Set-theoretic preliminary notions. In addition to the standard functions drawn from \verb:Data.Set: library,
we define new functions to compute the closure of a given set under arbitrary unions and intersections. \newline 
In both cases, we first define functions to perform a one-step intersection (resp. union) of a set with itself, and then iterate the function until the resulting set 
is identical to its own one-step intersection (resp. union) closure. 

\begin{code} 
unionStep :: (Ord a) => Topology a -> Topology a
unionStep x = Set.map (uncurry Set.union) (Set.cartesianProduct x x)

intersectionStep :: (Ord a) => Topology a -> Topology a
intersectionStep x = Set.map (uncurry Set.intersection) (Set.cartesianProduct x x)

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
checkTopology (TS space1 t) = Set.member space1 t 
    && Set.member Set.empty t 
    && all (\u -> all (\v -> (u `Set.union` v) `elem` t) t) t
    && all (\u -> all (\v -> (u `Set.intersection` v) `elem` t) t) t
    
fixTopology :: Ord a => TopoSpace a -> TopoSpace a
fixTopology (TS space2 t) = TS space2 fixedTop  where 
    fixedTop  = Set.fromList [space2, Set.empty] `Set.union` unionClosure (intersectionClosure t)
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

\begin{enumerate}
\item the implementation for "implies" is routine,

\item the "clopUpset" function extracts all the elements from the topology which are both upward-closed and clopen by checking that their complement with respect to the space also is in the topology, and by checking that their are identical to their upwards-closure.\newline 
Recall that a subset $S$ of an ordered set is upward-closed if and only if whenever $x\in S$ and $x\leq y$
 implies $y\in S$.  \newline
 This function makes use of the "upClosure" function, which computes the upwards-closure of any given set with respect to the given order.
\end{enumerate} 


The output of those is then fed to the "checkPSA" function, which then ensures the validity of the Priestley separation axiom for all points in $X$ not related by $\leq$.

\begin{code}
checkPriestley :: (Eq a, Ord a) => PriestleySpace a -> Bool
checkPriestley p = checkTopology (getTopoSpace p) && checkPoset (getOrderedSet p) && checkPSA p 

checkPSA :: (Eq a, Ord a) => PriestleySpace a -> Bool
checkPSA (PS space3 t order) = all (\ pair -> 
 implies (pair `notElem` order) (any (\ open -> elem (fst pair) open 
   && notElem (snd pair) open) (clopUp (PS space3 t order)) )) $ Set.cartesianProduct space3 space3 

clopUp :: Ord a => PriestleySpace a -> Topology a
clopUp (PS space4 t ord) = Set.intersection (clopens t) (upsets t) where 
        clopens = Set.filter (\ x -> Set.difference space4 x `elem` t)  
        upsets = Set.filter (\ y -> y == upClosure y ord)

upClosure :: (Eq a, Ord a) => Set.Set a -> Relation a -> Set.Set a 
upClosure set1 relation = Set.map snd (Set.filter (\ x -> fst x `elem` set1 ) relation) `Set.union` set1 
\end{code}

\subsection{Isomorphisms}

When working with Priestley Space, we want to be able to check if two given ones are "similar enough", i.e. isomorphic. This will become important when we want to confirm that a Priestley Space is isomorphic to the dual of its dual. \\
To check isomorphism, we have to be given two Priestley Spaces and a map between them. The map is an isomorphism, if it is actually a map, bijective, a Homeomorphism on the topological spaces and an order isomorphism on the relations. If the map is an isomorphism, the spaces are isomorphic. 

\begin{code}
checkIso :: (Ord a, Ord b) => PriestleySpace a -> PriestleySpace b -> Map a b -> Bool
checkIso (PS sa ta ra) (PS sb tb rb) mapping = checkMapping sa mapping 
    && checkBijective sb mapping 
    && checkHomeomorphism ta tb mapping
    && checkOrderIso ra rb mapping
\end{code}

Assuming bijectivity (by laziness of \&\&), to check that the given map is a Homeomorphism, we have to check that it is an open and continuous map, i.e. it maps opens to opens and the preimages of opens are also open. This means that applying the map to an open set in the topology of the domain should yield an element of the topology of the codomain, so applying it to the set of opens of the domain (its topology) should yield a subset of the opens of the codomain (its topology). Similarly, we check that the preimage of the topology of the codomain is a subset of the topology of the domain.

\begin{code}
checkHomeomorphism :: (Ord a, Ord b) => Topology a -> Topology b -> Map a b -> Bool
checkHomeomorphism ta tb mapping = 
    all (\x -> Set.map (getImage mapping) x `elem` tb) ta 
    && all (\ x -> Set.map (getPreimage mapping) x `elem` ta) tb
    --mapTop mapping ta `Set.isSubsetOf` tb
    -- && premapTop mapping tb `Set.isSubsetOf` ta
\end{code}

To apply the map to every open and thus every element of every open, we have to nest \verb:Set.map: twice. Again, we deal similarly with the preimages.

\begin{code}
mapTop :: (Ord a, Ord b) => Map a b -> Topology a -> Topology b
mapTop mapping = Set.map (Set.map (getImage mapping))

premapTop :: (Ord a, Ord b) => Map a b -> Topology b -> Topology a
premapTop mapping = Set.map (Set.map (getPreimage mapping))
\end{code}

Lastly, it remains the check that the map is an order isomorphism, which means that two elements $x,y$ of the domain satisfy $x\leq y$ in the domain iff $f(x)\leq f(y)$ in the codomain (here $f$ is the map). This means that applying the map component wise to every pair of the relation in the domain should yield the relation of the codomain and vice versa. 

\begin{code}
checkOrderIso :: (Ord a, Ord b) => Relation a -> Relation b -> Map a b -> Bool
checkOrderIso ra rb mapping = mapRel mapping ra == rb && premapRel mapping rb == ra
\end{code}

Similar to above, we have to nest \verb:Set.map: with \verb:Data.Bifunctor.bimap: to apply the map to both components of all pairs in the relation.

\begin{code}
mapRel :: (Ord a, Ord b) => Map a b -> Relation a -> Relation b
mapRel mapping = Set.map (Data.Bifunctor.bimap (getImage mapping) (getImage mapping))

premapRel :: (Ord a, Ord b) => Map a b -> Relation b -> Relation a
premapRel mapping = Set.map (bimap (getPreimage mapping) (getPreimage mapping))
\end{code}

\subsection{Arbitrary PriestleySpace}

To be able to use QuickCheck, we also have to write an Arbitrary instace for PriestleySpaces:

\begin{code}
instance (Arbitrary a, Ord a) => Arbitrary (PriestleySpace a) where
    arbitrary = sized randomPS where
        randomPS :: (Arbitrary a, Ord a) => Int -> Gen (PriestleySpace a)
        randomPS n = do
            os <- resize (min n 5) arbitrary
            let s = set os
            t <- Set.fromList <$> sublistOf (Set.toList $ Set.powerSet s)
            let t' = topologyTS $ fixTopology $ TS s t
            let r' = rel $ forcePoSet $ OS s (rel os)
            return $ fixPS $ PS s t' r'
\end{code}

After generating a space, which might not fulfill all requirements yet, we have to make it into a Priestley space using helper functions. Since we already have the machinary to make a set of subsets into a topology, we just have to make sure that the Priestley Seperation axiom is satisfied. By adding all missing upsets, we make sure that it is definetely satisfied. 

\begin{code}
fixPS :: Ord a => PriestleySpace a -> PriestleySpace a
fixPS (PS s t r) = PS s (topologyTS $ fixTopology $ TS s (topologyPS $ fixPSA $ PS s t r)) r

fixPSA :: Ord a => PriestleySpace a -> PriestleySpace a
fixPSA (PS s t r) = PS s (t `Set.union` getMissingUpsets s r) r 

getMissingUpsets :: Ord a => Set.Set a -> Relation a -> Topology a
getMissingUpsets s r = Set.map (\ x -> upClosure (Set.singleton x) r) firsts `Set.union` Set.map (\ x -> s `Set.difference` upClosure (Set.singleton x) r) firsts where
    firsts = Set.map fst $ Set.cartesianProduct s s `Set.difference` r
\end{code}

\subsection{Printing machinery}

When we say that we print a Priestley space, we mean that we print the underlying relation. This can be done with the functions from Poset:

\begin{code}

instance PrintDot a => PrintDot (Set.Set a) where 
    unqtDot x = unqtDot (head (Set.toList x))




showPriestley ::(Ord a, Data.GraphViz.Printing.PrintDot a) => PriestleySpace a -> IO ()

showPriestley p = runGraphvizCanvas' (toGraphOrd $ fromReflTrans $ getOrderedSet p) Xlib 




\end{code}



% Put this somewhere where its used 

When we will test representation later, we will get Priestley spaces, whose elements are sets themselves. To prevent a blow-up in size (espcially, when dualizing twice), we introduce a function, which creates a new Priestley space out of a given one. This new one is isomorphic to the original one, but its elements are of type \verb:Int:. This can make computation faster. With the new space, we also return a map, so we can still access the elements in a certain way by looking to which number a set gets mapped.

\begin{code}
simplifyPS :: Ord a => PriestleySpace a -> (PriestleySpace Int, Map a Int)
simplifyPS (PS s t r) = (PS s' t' r', mapping) where
    s' = Set.fromList $ take (Set.size s) [0..]
    mapping = Set.fromList [(Set.elemAt n s, n) | n <- Set.toList s']
    t' = mapTop mapping t 
    r' = mapRel mapping r
\end{code}
