\section{Mappings}

\begin{code}
module Mapping where

import Data.Set (Set, map, size, elemAt, filter)

type Map a b = Set (a,b)

getImage :: (Ord a, Ord b) => Map a b -> a -> b
getImage mapping x | size (getImages mapping x) == 1 = elemAt 0 (getImages mapping x)
                   | otherwise = error "Given Relation is not a mapping" 

-- given a possible function, we get the the image of some singleton a
-- should be one to be a function
getImages :: (Ord a, Ord b) => Map a b -> a -> Set b
getImages mapping x = Data.Set.map snd $ Data.Set.filter (\ (y,_) -> x == y) mapping

getPreimage :: (Ord a, Ord b) => Map a b -> b -> a
getPreimage mapping y | size (getPreimages mapping y) == 1 = elemAt 0 (getPreimages mapping y)
                      | otherwise = error "Either no or too many preimages"

-- gets preimages for b
getPreimages :: (Ord a, Ord b) => Map a b -> b -> Set a
getPreimages mapping y = Data.Set.map fst $ Data.Set.filter (\ (_,z) -> z == y) mapping



-- checks whether this is a function (unique output)
checkMapping :: (Ord a, Ord b) => Set a -> Map a b -> Bool
checkMapping sa mapping = all (\ x -> size (getImages mapping x) == 1) sa

checkBijective :: (Ord a, Ord b) => Set b -> Map a b -> Bool
checkBijective sb mapping = all (\ y -> size (getPreimages mapping y) == 1) sb

\end{code}
