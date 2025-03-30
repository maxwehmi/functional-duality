\section{Basics} \label{sec:Basics}

In this section, we introduce the basics for our project. For the most part, this is concerned with maps between spaces and some other helper functions. These will be imported in all other modules.

Firstly, we import the \texttt{Data.Set} package. This will allow us to very closely mirror ``everyday" mathematical language in our definitions.

\begin{code}
module Basics where

import qualified Data.Set as Set 
\end{code}

\subsection{Mappings}

We will use maps (and more specifically isomorphisms) between spaces a lot. Like usual in mathematics, we implement them as a set of pairs.

\begin{code}
type Map a b = Set.Set (a,b)
\end{code}

Of course, we also want to evalutate maps and get preimages. For images, we are given a map and an element $x$ in the domain. Firstly, we calculate the set of second elements, such that the first element in the mapping is $x$ and similarly for preimages.

\begin{code}
getImages :: (Ord a, Ord b) => Map a b -> a -> Set.Set b
getImages f x = Set.map snd $ Set.filter (\ (y,_) -> x == y) f

getPreimages :: (Ord a, Ord b) => Map a b -> b -> Set.Set a
getPreimages f y = Set.map fst $ Set.filter (\ (_,z) -> z == y) f
\end{code}

Using these functions, we can check if a given set of pairs is actually a map, i.e. every element in its domain has exactly one image. Similarly, we can check bijectivity by confirming that the preimage of every element in the range is a singleton. 

\begin{code}
checkMapping :: (Ord a, Ord b) => Set.Set a -> Map a b -> Bool
checkMapping sa mapping = all (\ x -> Set.size (getImages mapping x) == 1) sa

checkBijective :: (Ord a, Ord b) => Set.Set b -> Map a b -> Bool
checkBijective sb mapping = all (\ y -> Set.size (getPreimages mapping y) == 1) sb
\end{code}

After confirming that the set of pairs is actually a map and bijective, we can evaluate it for a given point or calculate the preimage. To avoid errors, these functions should only be used after checking well-definedness and bijectivity.

\begin{code}
getImage :: (Ord a, Ord b) => Map a b -> a -> b
getImage mapping x | Set.size (getImages mapping x) == 1 = Set.elemAt 0 (getImages mapping x)
                   | otherwise = error "Given Relation is not a mapping" 

getPreimage :: (Ord a, Ord b) => Map a b -> b -> a
getPreimage mapping y | Set.size (getPreimages mapping y) == 1 = Set.elemAt 0 (getPreimages mapping y)
                      | otherwise = error "Either no or too many preimages"
\end{code}

Then, these allow us to read \texttt{getImages f x} as a usual $f(x)$ for a given mapping.


\begin{comment}
\subsection{Other Helpful functions}

Some known functions are nice to have as abbreviations. Here we implement boolean implication:

\begin{code}
implies :: Bool -> Bool -> Bool
implies x y = not x || y
\end{code}
\end{comment}