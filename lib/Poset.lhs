\section{Partially ordered sets}

\begin{code}
module Poset where

import qualified Data.Set as Set

type Relation a = Set.Set (a,a) 
data OrderedSet a = OS {set :: Set.Set a,
                         rel :: Relation a} 

-- I have changed the Relation a from "newtype ... Set .." to "type ... Set.Set .." as Relation a is a type synonim and it was giving me problems with the typechecking in other files. 

-- I have changed the data type of OrderedSet a, in order to have functions to retreive the underlying set and the underlying relation of the OrderedSet.


{- 
most operations presume to have Ord instances, has to do with Set.Set implementation.

"Most operations require that e be an instance of the Ord class."  
https://hackage.haskell.org/package/containers-0.8/docs/Data-Set.html 
-}


checkRefl :: Ord a =>  OrderedSet a -> Bool
checkRefl (OS s r) = all (\x ->  (x, x) `Set.member` r) s



checkTrans :: Ord a => OrderedSet a -> Bool
checkTrans = undefined

checkAntiSym :: Ord a => OrderedSet a -> Bool
checkAntiSym  (OS _ r) = not (any (\(x,y) -> Set.member (y, x) r) r)


checkPoset :: Ord a => OrderedSet a -> Bool
checkPoset x = checkRefl x && checkTrans x && checkAntiSym x

closurePS :: OrderedSet a -> OrderedSet a
closurePS = undefined

\end{code}