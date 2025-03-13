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

Can potentially work around this by transfering to lists, doing the checking on those, and then back,
with some Set.toList trickery, for now leaving it like this, 
if we need to not assume instances of Ord we can change it
-}


-- Test Sets ------
s1 :: Set.Set Integer
s1 = Set.fromList [1, 2, 3]
r1 :: Set.Set (Integer, Integer)
r1 = Set.fromList [(1,2), (2,1), (3,3)]
os1 :: OrderedSet Integer
os1 = OS s1 r1


s2 :: Set.Set Integer
s2 = Set.fromList [1 :: Integer, 2, 3]
r2 :: Set.Set (Integer, Integer)
r2 = Set.fromList [(1,1), (2,2), (3,3)]
os2 :: OrderedSet Integer
os2 = OS s2 r2

s3 :: Set.Set Integer
s3 = Set.fromList [1, 2, 3]
r3 :: Set.Set (Integer, Integer)
r3 = Set.fromList [(1,2), (3,3)]
os3 :: OrderedSet Integer
os3 = OS s3 r3

s4 :: Set.Set Integer
s4 = Set.fromList [1, 2, 3]
r4 :: Set.Set (Integer, Integer)
r4 = Set.fromList [(1,2), (3,1)]
os4 :: OrderedSet Integer
os4 = OS s4 r4

s5 :: Set.Set Integer
s5 = Set.fromList [1, 2, 3]
r5 :: Set.Set (Integer, Integer)
r5 = Set.fromList [(1,2), (3,1), (2,1)]
os5 :: OrderedSet Integer
os5 = OS s5 r5
--------------------------

checkRefl :: Ord a =>  OrderedSet a -> Bool
checkRefl (OS s r) = all (\x ->  (x, x) `Set.member` r) s


checkTrans :: Ord a => OrderedSet a -> Bool
checkTrans (OS _ r) = undefined

checkAntiSym :: Ord a => OrderedSet a -> Bool
checkAntiSym  (OS _ r) = not (any (\(x,y) -> x /= y && (y, x) `Set.member` r) r)

checkPoset :: Ord a => OrderedSet a -> Bool
checkPoset x = checkRefl x && checkTrans x && checkAntiSym x





closeRefl :: Ord a => OrderedSet a -> OrderedSet a
closeRefl (OS s r) = OS s (r `Set.union` Set.fromList [(x,x)| x <- Set.toList s])

relcloseTrans :: Relation a -> Relation a
relcloseTrans r = undefined

closeTrans :: OrderedSet a -> OrderedSet a
closeTrans (OS s r) = OS s (relcloseTrans r)


closurePS :: Ord a => OrderedSet a -> OrderedSet a
closurePS os
 | not (checkAntiSym os)  = error "relation isn't anti-symmetric"
 | otherwise = closeTrans $ closeRefl os

\end{code}