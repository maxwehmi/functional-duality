\section{Priestley Spaces}
\label{sec:Priestley}
\begin{comment}
We introduce usual imports for printings.

\begin{code}
module Priestley where
import qualified Data.Set as Set 
import Test.QuickCheck
import Poset
import Basics
import Data.GraphViz.Commands
import Data.GraphViz.Printing
\end{code}

And the main data types of this section.
\end{comment}

\begin{code}
import Data.Bifunctor (bimap)
import Control.Lens.Internal.Deque (fromList)
\end{code}

\subsection{Definitions}
A Topological Space $(X,\tau)$ is a set $X$ endowed with a collection of its subsets $\tau \subseteq \wp(X)$. Such that:
\begin{itemize}
    \item $\emptyset,X \in \tau$
    
    \item $\tau$ is closed under \emph{arbitrary} unions: If $\{U_i\}_{i \in I} \subseteq \tau$, then $\bigcup\limits_{i \in I} U_i \in \tau$
    
    \item $\tau$ is closed under \emph{finite} intersections: If $\{U_0,\dots,U_n\} \subseteq \tau $, then $U_0 \cap \dots \cap U_n \in \tau$
\end{itemize}

Notice that, since we are working with finite cases, finitary and arbitrary unions (and intersections) coincide.

Then, a  Priestley space is a Topological Space endowed with a partial order $\leq$ on its carrier set; such that or any $x,y$, if $x\not\leq y$, then there exists a upwards-closed set $\uparrow \!\!C$ such that $\uparrow \!\!C$ is clopen and $x \in \uparrow \!\!C$ and $y \notin \uparrow \!\!C$. Intuitively, we say $\uparrow \!\!C$ is separates $x$ and $y$.
\newline
Formally, this would be the following Priestly Separation axiom:
$$x \not \leq y \rightarrow \exists C (C \in \tau \land X\setminus C \in \tau \land C = \uparrow C \land x\in C \land y\notin C)$$
% In the definition of the types, we keep it as close as possible to their mathematical counterparts:

Then our types are:\footnote{We omit it, but also defined a \texttt{Show} instances to print nicely our objects from the terminal (beside their graphViz representation).}

\begin{code}
type Topology a = Set.Set (Set.Set a)

data TopoSpace a = TS {
    setTS :: Set.Set a,
    topologyTS :: Topology a
}
    deriving (Eq, Ord)

data PriestleySpace a = PS {
    setPS :: Set.Set a,
    topologyPS :: Topology a,
    relationPS :: Relation a
}
    deriving (Eq, Ord)
\end{code}

\begin{comment}
\begin{code}
instance Show a => Show (TopoSpace a) where
    show (TS s t  ) = "{Set: " ++ show (Set.toList s) ++ ";\n"
                        
                        ++ "Top:" ++ show (map Set.toList (Set.toList t)) ++ "}" 


instance Show a => Show (PriestleySpace a) where
    show (PS s t r ) = "{Set: " ++ show (Set.toList s) ++ ";\n"
                        ++ "Top: " ++ show (map Set.toList (Set.toList t)) ++ ";\n"
                        ++ "Rel: " ++ show (Set.toList r) ++ "}"
\end{code}
\end{comment}


\paragraph{Set-theoretic preliminaries}
In order to deal effectively with topological spaces, we first define some Set-theoretic preliminary notions. In addition to the standard functions drawn from \texttt{Data.Set} library,
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

\subsection{Checking Topologies}
We now introduce some machinery to work on topological spaces, and in particular, to ensure our spaces respect the Priestley separation axiom.

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

The next functions allow us to extract from a given Priestley space its underlying set together with the topology, and its underlying carrier set together with its order. The second in particular is useful when it comes to printing via graphViz, since it allows to have one uniform instance for \texttt{OrderedSet} which applies easily to Lattices and Priestley spaces.

\begin{code}
getTopoSpace :: PriestleySpace a -> TopoSpace a
getTopoSpace p = TS (setPS p) (topologyPS p)

getOrderedSet :: PriestleySpace a -> OrderedSet a
getOrderedSet p = OS (setPS p) (relationPS p)
\end{code}

Next, we define a function to check whether a given Space really is a Priestley space. 

We make use of some secondary helper functions: The \texttt{clopUpset} function extracts all the elements from the topology which are both upward-closed and clopen by checking that their complement with respect to the space also is in the topology, and by checking that their are identical to their upwards-closure.

This function makes use of the \texttt{upClosure} function, which computes the upwards-closure of any given set with respect to the given order.

The output of is then fed to the \texttt{checkPSA} function, which then ensures the validity of the Priestley separation axiom for all points in $X$ not related by $\leq$.

\begin{code}
checkPriestley :: (Eq a, Ord a) => PriestleySpace a -> Bool
checkPriestley p = checkTopology (getTopoSpace p) && checkPoset (getOrderedSet p) && checkPSA p 

checkPSA :: (Eq a, Ord a) => PriestleySpace a -> Bool
checkPSA (PS space3 t order) = all (\ pair -> 
 implies (pair `notElem` order) (any (\ clopupset -> elem (fst pair) clopupset 
   && notElem (snd pair) clopupset) (clopUp (PS space3 t order)) )) $ Set.cartesianProduct space3 space3 

clopUp :: Ord a => PriestleySpace a -> Topology a
clopUp (PS space4 t ord) = Set.intersection (clopens t) (upsets t) where 
        clopens = Set.filter (\ x -> Set.difference space4 x `elem` t)  
        upsets = Set.filter (\ y -> y == upClosure y ord)

upClosure :: (Eq a, Ord a) => Set.Set a -> Relation a -> Set.Set a 
upClosure set1 relation = Set.map snd (Set.filter (\ x -> fst x `elem` set1 ) relation) `Set.union` set1 
\end{code}


\begin{comment}Analogously to what we said in the distributive Lattice section, to prevent a blow-up in size (especially, when dualizing twice), we introduce two functions, which creates a new Priestley space out of a given one. This new one is isomorphic to the original one, but its elements are of type \verb:Int:. This can make computation faster.

The use of the functions is analogous to their distributive lattice counterparts. Last, for the purpose of testing, we write a function checking that the original and the reduced space are isomorphic.

\begin{code}
simplifyPS :: Ord a => PriestleySpace a -> (PriestleySpace Int, Map a Int)
simplifyPS (PS s t r) = (PS s' t' r', mapping) where
    s' = Set.fromList $ take (Set.size s) [0..]
    mapping = Set.fromList [(Set.elemAt n s, n) | n <- Set.toList s']
    t' = mapTop mapping t 
    r' = mapRel mapping r


simplifyPS1 :: Ord a => PriestleySpace a -> PriestleySpace Int
simplifyPS1 (PS s t r) = PS s' t' r' where
    s' = Set.fromList $ take (Set.size s) [0..]
    mapping = Set.fromList [(Set.elemAt n s, n) | n <- Set.toList s']
    t' = mapTop mapping t 
    r' = mapRel mapping r

simplificationPScheck :: Ord a => PriestleySpace a -> Bool
simplificationPScheck x = uncurry (checkIso x) (simplifyPS x)
\end{code}
\end{comment}

\subsection{Isomorphisms}

When working with Priestley Space, we want to be able to check if two given ones are "similar enough", i.e. isomorphic. This will become important when we want to confirm that a Priestley Space is isomorphic to the dual of its dual.

Two Priestley Spaces are isomorphic, if there is a map $f$ between them such that: 

\begin{itemize}
\item $f$ is bijective
\item $f$ is a Homeomorphism on the topologies: $f$ is
open and continuous, resepctively, it maps opens to opens and the preimages of opens are also open
\item $f$ is an order isomorphism on the relations: for any $x, y$, $x \leq y$ iff $f(x) \leq f(y)$
\end{itemize}

For homeomorphism we can check that applying the map to an open set in the topology of the domain should yield an element of the topology of the codomain, so applying it to the set of opens of the domain (its topology) should yield a subset of the opens of the codomain (its topology). And similarly that the preimage of the topology of the codomain is a subset of the topology of the domain.


\begin{code}
checkIso :: (Ord a, Ord b) => PriestleySpace a -> PriestleySpace b -> Map a b -> Bool
checkIso (PS sa ta ra) (PS sb tb rb) mapping = checkMapping sa mapping 
    && checkBijective sb mapping 
    && checkHomeomorphism ta tb mapping
    && checkOrderIso ra rb mapping

checkHomeomorphism :: (Ord a, Ord b) => Topology a -> Topology b -> Map a b -> Bool
checkHomeomorphism ta tb mapping = 
    all (\x -> Set.map (getImage mapping) x `elem` tb) ta 
    && all (\ x -> Set.map (getPreimage mapping) x `elem` ta) tb
\end{code}

To apply the map to every open and thus every element of every open, we have to nest \verb:Set.map: twice. Again, we deal similarly with the preimages.

\begin{code}
mapTop :: (Ord a, Ord b) => Map a b -> Topology a -> Topology b
mapTop mapping = Set.map (Set.map (getImage mapping))

premapTop :: (Ord a, Ord b) => Map a b -> Topology b -> Topology a
premapTop mapping = Set.map (Set.map (getPreimage mapping))
\end{code}

Lastly, it remains the check that the map is an order isomorphism. For this we can check that applying the map component wise to every pair of the relation in the domain should yield the relation of the codomain and vice versa. 

Similar to above, we have to nest \texttt{Set.map} with \texttt{Data.Bifunctor.bimap} to apply the map to both components of all pairs in the relation.

\begin{code}
checkOrderIso :: (Ord a, Ord b) => Relation a -> Relation b -> Map a b -> Bool
checkOrderIso ra rb mapping = mapRel mapping ra == rb && premapRel mapping rb == ra

mapRel :: (Ord a, Ord b) => Map a b -> Relation a -> Relation b
mapRel mapping = Set.map (Data.Bifunctor.bimap (getImage mapping) (getImage mapping))

premapRel :: (Ord a, Ord b) => Map a b -> Relation b -> Relation a
premapRel mapping = Set.map (bimap (getPreimage mapping) (getPreimage mapping))
\end{code}

\subsection{Arbitrary PriestleySpace}

To be able to use QuickCheck, we also have to write an Arbitrary instance for PriestleySpaces:

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

After generating a space, which might not fulfill all requirements yet, we have to make it into a Priestley space using helper functions. Since we already have the machinery to make a set of subsets into a topology, we just have to make sure that the Priestley Seperation axiom is satisfied. By adding all missing upsets, we make sure that it is definetely satisfied.
\newline
To recover the missing clopen up-sets, since we are in the finite case, it suffices to add to the topology the point-generated upset from a given element of the poset. 

Unfortunately, there is no standard way to calculate a clopen upset given a collection of elements without first knowing the full topology over the space. This means both that this function is one of the few that (even in principle) would not be correct to use when dealing with infinite spaces, and also that finding a computationally feasible method to fill the missing clopen upset in the infinite case could be rather tricky.

\begin{code}
fixPS :: Ord a => PriestleySpace a -> PriestleySpace a
fixPS (PS s t r) = PS s (topologyTS $ fixTopology $ TS s (topologyPS $ fixPSA $ PS s t r)) r

fixPSA :: Ord a => PriestleySpace a -> PriestleySpace a
fixPSA (PS s t r) = PS s (t `Set.union` getMissingUpsets s r) r 

getMissingUpsets :: Ord a => Set.Set a -> Relation a -> Topology a
getMissingUpsets s r = Set.map (\ x -> upClosure (Set.singleton x) r) firsts `Set.union` Set.map (\ x -> s `Set.difference` upClosure (Set.singleton x) r) firsts where
    firsts = Set.map fst $ Set.cartesianProduct s s `Set.difference` r
\end{code}

\paragraph{Printing machinery}
Analogously to its Poset and Lattice counterparts, this function actually prints thePriestely Space.\footnote{for more detail, see the \hyperref[sec:posetprinting]{subsection 3.4}}

\begin{code}
showPriestley ::(Ord a, Data.GraphViz.Printing.PrintDot a) => PriestleySpace a -> IO ()
showPriestley p = runGraphvizCanvas' (toGraphOrd $ fromReflTrans $ getOrderedSet p) Xlib
\end{code}



