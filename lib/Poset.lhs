{-# HLINT ignore "Eta reduce" #-}
\section{Partially ordered sets}

\begin{code}
module Poset where

import qualified Data.Set as Set
import Data.Set.Internal

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
if we need to avoid assuming instances of Ord we can change it

But I see everyone else's code also pretty much always assumes Ord.
-}


-- leaving this in case i'm saying something stupid, but i realized I can just use the closure for the check condition...
checkReflAlt :: Ord a =>  OrderedSet a -> Bool
checkReflAlt (OS s r) = all (\x ->  (x, x) `Set.member` r) s


setEq :: Ord a => Set a -> Set a -> Bool
setEq s1 s2 = Set.toList s1 == Set.toList s2

-- this relies on the fact that "Set.fromList" eliminates duplicates, as Set shouldn't care about them
relationWellDef :: Ord a => OrderedSet a -> Bool
relationWellDef (OS s r) = s == Set.fromList (Prelude.map fst (Set.toList r) ++ Prelude.map snd (Set.toList r)) 

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

-- current hacky solution
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

\end{code}
