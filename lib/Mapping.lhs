\section{Mappings}\label{sec:Mappings}

As in most of mathematics, maps (and more specifically isomorphisms) are of great importance to our project. As usual in mathematics, we implement maps as a set of pairs. 

\begin{code}
module Mapping where

import Data.Set (Set, map, size, elemAt, filter,fromList,toList)

type Map a b = Set (a,b)
\end{code}

Of course, we also want to evalutate maps and get preimages. For images, we are given a map and an element $x$ in the domain. Firstly, we calculate the set of second elements, such that the first element in the mapping is $x$ and similarly for preimages.

\begin{code}
getImages :: (Ord a, Ord b) => Map a b -> a -> Set b
getImages mapping x = Data.Set.map snd $ Data.Set.filter (\ (y,_) -> x == y) mapping

getPreimages :: (Ord a, Ord b) => Map a b -> b -> Set a
getPreimages mapping y = Data.Set.map fst $ Data.Set.filter (\ (_,z) -> z == y) mapping
\end{code}

Using these functions, we can check if a given set of pairs is actually a map, i.e. every element in its domain has exactly one image. Similarly, we can check bijectivity by confirming that the preimage of every element in the range is a singleton. 

\begin{code}
checkMapping :: (Ord a, Ord b) => Set a -> Map a b -> Bool
checkMapping sa mapping = all (\ x -> size (getImages mapping x) == 1) sa

checkBijective :: (Ord a, Ord b) => Set b -> Map a b -> Bool
checkBijective sb mapping = all (\ y -> size (getPreimages mapping y) == 1) sb
\end{code}

After confirming that the set of pairs is actually a map and bijective, we can evaluate it for a given point or calculate the preimage. To avoid errors, these functions should only be used after checking well-definedness and/or bijectivity.

\begin{code}
getImage :: (Ord a, Ord b) => Map a b -> a -> b
getImage mapping x | size (getImages mapping x) == 1 = elemAt 0 (getImages mapping x)
                   | otherwise = error "Given Relation is not a mapping" 

getPreimage :: (Ord a, Ord b) => Map a b -> b -> a
getPreimage mapping y | size (getPreimages mapping y) == 1 = elemAt 0 (getPreimages mapping y)
                      | otherwise = error "Either no or too many preimages"
\end{code}

Since it is not so nice to use functions in their set theoretic encoding, we define a helper functions that let us define a mapping by just "naturally" describing the function, as we would in the "everyday".

\begin{code}

makeMap :: (Ord a, Ord b) => Set a -> Set b -> (a -> b) -> Map a b
makeMap s1 s2 f = fromList [(x,y)| x <- toList s1, y <- toList s2, y == f x]

\end{code}