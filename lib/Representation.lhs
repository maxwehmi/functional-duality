\section{Representation}\label{sec:representation}

The Representation Theorem refers to the fact that the dual of the dual of a Priestley Space is isomorphic to the space itself. Similarly, the dual of the dual of a distributive lattice is isomorphic to the lattice itself. With our implementations, we aim to confirm this fact empirically for finite Priestley spaces and distributive lattices. In this module, we implement and use the necessary machinary to test this. 

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
together, making use of the "upClosure" function from above.
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

phi :: (Eq a, Ord a) => Lattice a -> a -> Set.Set (Filter a)
phi lattice x = Set.filter (Set.member x) $ findPrimeFilters lattice 

priestleyTopology :: (Eq a, Ord a) => Lattice a -> Topology (Filter a)
priestleyTopology x = let phimap = Set.map (phi x) (set (carrier x)) 
                    in unionClosure $ intersectionClosure (Set.union phimap (Set.map (Set.difference(findPrimeFilters x)) phimap ))

                                    
priesMap :: (Eq a, Ord a) => Lattice a -> PriestleySpace (Filter a)
priesMap lattice = PS (findPrimeFilters lattice) (priestleyTopology lattice) (inclusionOrder (findPrimeFilters lattice))
\end{code}



\subsection{Dual maps and Isomorphisms for Priestley Spaces}
We present some functions to check basic properties of topological spaces.
In particular, we want to be able to decide whether two spaces are isomorphic. this is going to come in handy when exploring the duality with algebras. \newline 
We also present the first step towards implementing the algebra duality: keeping things brief, the set of Clopen Upset of a Priestley space 
is going to form a distributive lattice under the order induced by set-theoretic inclusion. \newline 
To this extent, we implement a function to extract an order based on set-theoretic inclusion between sets, which we canlater apply to the Clopen Upsets of our topology.\newline 
Next, we construct a lattice using the Clopen Upsets of our topological space and endowing this set with the desired inclusion-order. We make use of functions from the "DL" section to both construct the lattice and check it is distributive.
\begin{code}
inclusionOrder :: Ord a => Topology a -> Relation (Set.Set a)
inclusionOrder x = Set.fromList [ (z ,y) |  z <- Set.toList x, y <- Set.toList x, Set.isSubsetOf z y ]

clopMap :: Ord a => PriestleySpace a -> Lattice (Set.Set a)
clopMap  ps = do 
              let result = makeLattice $  OS (clopUp ps) (inclusionOrder (clopUp ps)) 
              if checkDL result then result else error "104!"

\end{code}


\begin{code}
calculateEpsilon :: Ord a => PriestleySpace a -> Map a (Filter (Set.Set a))
calculateEpsilon ps = Set.fromList [(x,eps x) | x <- (Set.toList . setPS) ps] where
                eps a = Set.fromList [ u | u <- (Set.toList . set . carrier .clopMap) ps, a `elem` u]

calculatePhi :: Ord a => Lattice a -> Map a (Set.Set (Filter a))
calculatePhi l = Set.fromList [(x, phi l x) | x <- (Set.toList . set . carrier) l] 





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












--- >>> showLattice myLattice1

--- >>> showOrdSet myOS5

--- >>> showPriestley mySpace

--- >>> generate arbitrary :: IO (Lattice Int)

--- >>> showLattice (generate arbitrary :: IO (Lattice Int))

\end{code}
