{-# HLINT ignore "Eta reduce" #-}
\section{Partially ordered sets}

\begin{code}
module Poset where

import qualified Data.Set as Set

type Relation a = Set.Set (a,a)

data OrderedSet a = OS {set :: Set.Set a, rel :: Relation a} 
    deriving (Eq, Ord,Show)

-- I have changed the Relation a from "newtype ... Set .." to "type ... Set.Set .." as Relation a is a type synonim and it was giving me problems with the typechecking in other files. 

-- I have changed the data type of OrderedSet a, in order to have functions to retreive the underlying set and the underlying relation of the OrderedSet.


{-
most operations presume to have Ord instances, has to do with Set.Set implementation.

"Most operations require that e be an instance of the Ord class."  
https://hackage.haskell.org/package/containers-0.8/docs/Data-Set.html 

Can potentially work around this by transfering to lists, doing the checking on those, and then back,
with some Set.toList trickery, for now leaving it like this, 
if we need to not assume instances of Ord we can change it

But I see everyone else's code also pretty much always assumes Ord.
-}

{-
leaving this in case i'm saying something stupid, but i realized 
I can just use the closure for the check condition...

checkRefl :: Ord a =>  OrderedSet a -> Bool
checkRefl (OS s r) = all (\x ->  (x, x) `Set.member` r) s
-}

checkRefl :: Ord a =>  OrderedSet a -> Bool
checkRefl os = os == closureRefl os


checkTrans :: Ord a => OrderedSet a -> Bool
checkTrans os = os == closureTrans os

checkAntiSym :: Ord a => OrderedSet a -> Bool
checkAntiSym  (OS _ r) = not (any (\(x,y) -> x /= y && (y, x) `Set.member` r) r)

checkPoset :: Ord a => OrderedSet a -> Bool
checkPoset x = checkRefl x && checkTrans x && checkAntiSym x

closureRefl :: Ord a => OrderedSet a -> OrderedSet a
closureRefl (OS s r) = OS s (r `Set.union` Set.fromList [(x,x)| x <- Set.toList s])



transPair ::  Ord a => a -> a -> [(a,a)] -> Bool
transPair x z tups =  any (\(_,y) -> (x, y) `elem` tups && (y,z) `elem` tups) tups

-- This only adds "one step" transtivity, needs to be recursed till the it becomes idempotent or something like this
transStep :: Ord a => OrderedSet a -> OrderedSet a
transStep (OS s r) = OS s (r `Set.union` Set.fromList [(x,z) | x <- Set.toList s, z <- Set.toList s, transPair x z (Set.toList r)])



-- current hakcy solution
closureTrans :: Ord a => OrderedSet a -> OrderedSet a
closureTrans  currentSet = 
        let recursedSet = transStep currentSet
        in if recursedSet == currentSet
            then currentSet 
            else closureTrans recursedSet


closurePS :: Ord a => OrderedSet a -> OrderedSet a
closurePS os
 | not (checkAntiSym os)  = error "relation isn't anti-symmetric"
 | otherwise = closureTrans $ closureRefl os


------------- Test Sets (thanks GPT) ------
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

-- Reflexive, Transitive, Anti-symmetric (Valid Poset)
os6 :: OrderedSet Integer
os6 = OS (Set.fromList [1, 2, 3]) 
         (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,3), (1,3)])

-- Reflexive, Transitive, Not Anti-symmetric (Not a Poset)
os7 :: OrderedSet Integer
os7 = OS (Set.fromList [1, 2, 3]) 
         (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,1), (1,3), (3,1)])

-- Reflexive, Not Transitive, Anti-symmetric (Not a Poset)
os8 :: OrderedSet Integer
os8 = OS (Set.fromList [1, 2, 3]) 
         (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,3), (3,2)])

-- Reflexive, Not Transitive, Not Anti-symmetric (Not a Poset)
os9 :: OrderedSet Integer
os9 = OS (Set.fromList [1, 2, 3]) 
         (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,3), (3,2), (1,3)])

-- Reflexive, Anti-symmetric, Not Transitive (Not a Poset)
os10 :: OrderedSet Integer
os10 = OS (Set.fromList [1, 2, 3]) 
          (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,1)])

-- Not Reflexive, Transitive, Anti-symmetric (Not a Poset)
os11 :: OrderedSet Integer
os11 = OS (Set.fromList [1, 2, 3]) 
          (Set.fromList [(2,2), (3,3), (1,2), (2,3), (1,3)])

-- Not Reflexive, Not Transitive, Anti-symmetric (Not a Poset)
os12 :: OrderedSet Integer
os12 = OS (Set.fromList [1, 2, 3]) 
          (Set.fromList [(2,2), (3,3), (1,2), (2,3)])

-- Not Reflexive, Not Transitive, Not Anti-symmetric (Not a Poset)
os13 :: OrderedSet Integer
os13 = OS (Set.fromList [1, 2, 3]) 
          (Set.fromList [(2,2), (3,3), (1,2), (2,3), (3,1)])

-- Reflexive, Transitive, Anti-symmetric, with more elements (Valid Poset)
os14 :: OrderedSet Integer
os14 = OS (Set.fromList [1, 2, 3, 4, 5]) 
          (Set.fromList [(1,1), (2,2), (3,3), (4,4), (5,5), 
                         (1,2), (2,3), (1,3), (4,5), (1,4), (2,5)])

-- Reflexive, Transitive, Anti-symmetric, with a larger relation (Valid Poset)
os15 :: OrderedSet Integer
os15 = OS (Set.fromList [1, 2, 3, 4, 5, 6]) 
          (Set.fromList [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), 
                         (1,2), (2,3), (3,4), (4,5), (5,6), (1,3), (1,4), (1,5), (1,6)])

-- Reflexive, Not Transitive, Anti-symmetric (Not a Poset)
os16 :: OrderedSet Integer
os16 = OS (Set.fromList [1, 2, 3, 4, 5]) 
          (Set.fromList [(1,1), (2,2), (3,3), (4,4), (5,5), 
                         (1,2), (2,3), (1,3), (4,5), (5,4)])

-- Reflexive, Transitive, Not Anti-symmetric (Not a Poset)
os17 :: OrderedSet Integer
os17 = OS (Set.fromList [1, 2, 3]) 
          (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,1), (1,3), (3,1)])

-- Reflexive, Anti-symmetric, Not Transitive (Not a Poset)
os18 :: OrderedSet Integer
os18 = OS (Set.fromList [1, 2, 3]) 
          (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,1)])

-- Empty Set (Reflexive, Transitive, Anti-symmetric as edge case)
os19 :: OrderedSet Integer
os19 = OS Set.empty Set.empty

--------------------------


\end{code}
