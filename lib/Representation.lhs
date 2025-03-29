\section{Representation}
\label{sec:representation}

The Representation Theorem refers to the fact that the dual of the dual of a Priestley Space is isomorphic to the space itself. Similarly, the dual of the dual of a distributive lattice is isomorphic to the lattice itself. With our implementations, we aim to confirm this fact for finite Priestley spaces and distributive lattices. In this module, we implement and use the necessary machinery to test this. 

\begin{code}
module Representation where
import Data.Maybe
import qualified Data.Set as Set 
import Basics
import Poset
import DL
import Priestley
\end{code}

\subsection{Filters of Lattices the dual space of a lattice}

In order to compute the dual space of our lattices, we first need to be able to isolate filters within them. \newline 
Intuitively, a filter is a collection of elements of an ordered set such that it is closed upwards and closed under finite meets. In our case the only relevant filters 
are going to be \textit{Prime filters}, which are just filters that do not contain the bottom element of the lattice, and that never contain a join of two elements without 
also containing at least one of the two. \newline 

First, we make a type-shorthand for filters (those are just sets of elements), 
and we implement helper functions to compute them.

\begin{code}
type Filter a = Set.Set a 
\end{code}

The functions below shall be used to find the prime filters. 

\begin{code}
closeOnceUnderMeet :: Ord b => Lattice b -> Set.Set b -> Set.Set b
closeOnceUnderMeet lattice1 set1 =  Set.map (uncurry (meet lattice1) ) (Set.cartesianProduct set1 set1 ) 

meetClosure :: (Eq a, Ord a) => Lattice a -> Set.Set a -> Set.Set a 
meetClosure lattice2 set2 = do 
                let cycle2 = closeOnceUnderMeet lattice2 set2 
                 in   
                 if set2 == cycle2 then set2 
                else closeOnceUnderMeet lattice2 cycle2
\end{code}

Next, we want to extract from a given lattice the set of its prime filters. 
We thus first implement a function to check primeness of a given filter, and then we pull the strings 
together, making use of the "upClosure" function from above. \newline 
Notice that the extra contextual information about the undelrying lattice si required, since the meet (resp.join) of two elements are only defined with respect to the underlying lattices structure (there is no "absolute" meet/join of elements).

\begin{code}
isPrime :: (Eq a, Ord a) =>  Lattice a -> Filter a -> Bool 
isPrime lattice filter1 = (filter1 /= Set.empty) && and (Set.toList 
                        (Set.map 
                        (\ x -> implies 
                                (Set.member (uncurry (join lattice) x) filter1) 
                                (Set.member (fst x) filter1 || Set.member (snd x) filter1)) 
                        (Set.cartesianProduct  (set (carrier lattice)) (set (carrier lattice)))))


findFilters :: (Eq a, Ord a) => Lattice a -> Set.Set (Filter a)
findFilters lattice = let base = set (carrier lattice)
                          ord = rel (carrier lattice)
                      in Set.filter (\ k -> notElem (fromJust $ bot lattice) k &&
                                        (meetClosure lattice k == k ) && 
                                        upClosure k ord == k ) 
                                (Set.powerSet base) 

findPrimeFilters :: (Eq a, Ord a) => Lattice a -> Set.Set (Filter a)
findPrimeFilters lattice = Set.filter (isPrime lattice) (findFilters lattice)

\end{code}

The function \verb:priestleyTopology: calculates the topology for the dual of a given lattice. This topology is generated (on a space $X$ ) by $\varphi(a)$ and $\varphi(a)^C$ for elements $a$ of the carrier of the lattice. The set $\varphi(a)$ contains all the prime filters containing $a$. \newline 
To obtain the full topology, we need to take for every $a$ $\varphi(a),\, X\setminus \varphi(a)$, and then closing the resulting family of sets first under finitary intersections and then under arbitrary unions.\newline 
Next, we use these functions to calculate the dual space of a given lattice:

\begin{code}   

phi :: (Eq a, Ord a) => Lattice a -> a -> Set.Set (Filter a)
phi lattice x = Set.filter (Set.member x) $ findPrimeFilters lattice 

priestleyTopology :: (Eq a, Ord a) => Lattice a -> Topology (Filter a)
priestleyTopology x = let phimap = Set.map (phi x) (set (carrier x)) 
                    in unionClosure $ intersectionClosure (Set.union phimap (Set.map (Set.difference(findPrimeFilters x)) phimap ))

priesMap :: (Eq a, Ord a) => Lattice a -> PriestleySpace (Filter a)
priesMap lattice = PS (findPrimeFilters lattice) (priestleyTopology lattice) (inclusionOrder (findPrimeFilters lattice))

fastPriesMap :: Ord a => Lattice a -> (PriestleySpace (Filter a), PriestleySpace Int, Map (Filter a) Int)
fastPriesMap l = (p, fst sp, snd sp) where 
        p = PS pfs (Set.powerSet pfs) (inclusionOrder pfs) 
        pfs = findPrimeFilters l
        sp = simplifyPS p
\end{code}

The \verb:fastPriesMap: is supposed to be faster version of \verb:priesMap:. As mentioned earlier, when dealing with duals of duals, the elements themselves become quite big. This makes the computation time longer. We want to avoid this by simplifying the space using the aptly named function from earlier. We also include a map to be able to compute the dual isomorphism later. We lazily calculate the topology of \verb:p: as the power set of its carrier. While all finite Priestley spaces carry the discrete topology, we tried to avoid using this fact and stick to the mathematical definition as closely as possible. However, the computation time is very long as it is and this is supposed to be the faster, but lazier version. For "proper" checks, it would be more appropriate to use \verb:priesMap:.


\subsection{Dual maps and Isomorphisms for Priestley Spaces}
We present some functions to check basic properties of topological spaces.
In particular, we want to be able to decide whether two spaces are isomorphic. this is going to come in handy when exploring the duality with algebras. \newline 
We also present the first step towards implementing the algebra duality: keeping things brief, the set of Clopen Upset of a Priestley space 
is going to form a distributive lattice under the order induced by set-theoretic inclusion. \newline 
To this extent, we implement a function to extract an order based on set-theoretic inclusion between sets, which we can later apply to the Clopen Upsets of our topology.\newline 
Next, we construct a lattice using the Clopen Upsets of our topological space and endowing this set with the desired inclusion-order. We make use of functions from the "DL" section to both construct the lattice and check it is distributive.

\begin{code}
inclusionOrder :: Ord a => Topology a -> Relation (Set.Set a)
inclusionOrder x = Set.fromList [ (z ,y) |  z <- Set.toList x, y <- Set.toList x, Set.isSubsetOf z y ]

clopMap :: Ord a => PriestleySpace a -> Lattice (Set.Set a)
clopMap  ps = do 
              let result = makeLattice $  OS (clopUp ps) (inclusionOrder (clopUp ps)) 
              if checkDL result then result else error "104!"

fastClopMap :: Ord a => PriestleySpace a -> (Lattice (Set.Set a), Lattice Int, Map (Set.Set a) Int)
fastClopMap p = (l, fst sl, snd sl) where
        l = clopMap p
        sl = simplifyDL l
\end{code}

Here we again implemented a faster version for better checks. This time we only simplified the space, without making use of other known facts about lattices. Thus, this fast version is in a sense just a renaming. Similar to above, we still keep the original dual space to be able to construct the dual isomorphism. 

\subsection{The dual isomorphisms}

The representation theorem does not only state that a Priestley space (resp. lattice) is isomorphic to the dual of its dual, but it also gives us the isomorphism. Classically, these are called $\varepsilon$ and $\varphi$. In fact, the isomorphism $\varphi$ maps can be constructed by the map $\varphi$ which created a basis for the topology of the dual of a lattice we mentioned earlier. There we used it assign to each element of $x$ of a lattice $L$ the set of filters $ F\subseteq L$ such that $x\in F$. Here we extend it to a proper map:

\begin{code}
calculatePhi :: Ord a => Lattice a -> Map a (Set.Set (Filter a))
calculatePhi l = Set.fromList [(x, phi l x) | x <- (Set.toList . set . carrier) l] 
\end{code}

Using this, we can check if representation holds for lattices. Ideally, one would use it the proper way, but testing showed that this is not feasible. There are not that many element, but they are very space intensive. Thus we also implemented a faster version. It uses the aforementioned faster versions of the dual maps. Technically, it does not check isomorphism between the lattice and the dual of its dual, but calculates certain intermediate spaces. These are isomorphic to the proper ones, but computationally better. Since we know that they are isomorphic to the actual duals of the duals, we can conclude that representation holds if these tests succeed.

\begin{code}
checkRepresentationDL :: Ord a => Lattice a -> Bool
checkRepresentationDL l = functionMorphism l (clopMap (priesMap l)) (calculatePhi l)

checkRepresentationDLfast :: Ord a => Lattice a -> Bool 
checkRepresentationDLfast l = functionMorphism l l' mapping where
        (p,sp,map1) = fastPriesMap l 
        (_,l',map2) = fastClopMap sp 
        vphi a = getImage map2 (filtersOf a)
        filtersOf b = Set.fromList [getImage map1 u | u <- (Set.toList . setPS) p, b `elem` u]
        mapping = Set.fromList [(x, vphi x) | x <- (Set.toList . set . carrier) l]
\end{code}

Similarly, an element of a Priestley space is mapped to the set of clopen upsets containing it in the dual of the dual space:

\begin{code}
calculateEpsilon :: Ord a => PriestleySpace a -> Map a (Filter (Set.Set a))
calculateEpsilon ps = Set.fromList [(x,eps x) | x <- (Set.toList . setPS) ps] where
                eps a = Set.fromList [ u | u <- (Set.toList . set . carrier . clopMap) ps, a `elem` u]
\end{code}
\begin{code}




myos1 :: OrderedSet Int
myos1 = Poset.closurePoSet $ OS (Set.fromList [1,2,3,4, 5]) (Set.fromList [(1,2), (2,4), (1,3),(3,4),(4,5)])



myOS5:: OrderedSet Int
myOS5 = OS (Set.fromList [0,1,2,3]) (Set.fromList [(0,1), (0,2), (1,3), (1,3), (2,3)])

myPoset1:: OrderedSet Int
myPoset1 = closurePoSet myOS5

myLattice1:: Lattice Int 
myLattice1 = makeLattice myPoset1


snelliusOS :: OrderedSet Int 
snelliusOS = OS (Set.fromList [0.. 10]) (Set.fromList [(0,1), (0,2),(1,3),(1,5),(2,4),(2,5),(3,6),(5,6),(5,7),(4,7),(6,8),(7,8),(8,9),(9,10)]) 


snelliusDL :: Lattice Int 
snelliusDL = makeLattice (forcePoSet snelliusOS)

\end{code}
We can use this again to check representation. Similar to above, we have implemented a "proper" version and a fast version:

\begin{code}
checkRepresentationPS :: Ord a => PriestleySpace a -> Bool
checkRepresentationPS ps = checkIso ps (priesMap (clopMap ps)) (calculateEpsilon ps)

checkRepresentationPSfast :: Ord a => PriestleySpace a -> Bool
checkRepresentationPSfast ps = checkIso ps ps' mapping where
        (l,sl,m1) = fastClopMap ps
        (_,ps',map2) = fastPriesMap sl
        eps a = getImage map2 (clopensOf a)
        clopensOf b = Set.fromList [getImage m1 u | u <- (Set.toList . set . carrier) l, b `elem` u]
        mapping = Set.fromList [(x,eps x) | x <- (Set.toList . setPS) ps]

\end{code}
