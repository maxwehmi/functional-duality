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
if we need to avoid assuming instances of Ord we can change it

But I see everyone else's code also pretty much always assumes Ord.
-}




tuplesUnfold :: Ord a => Relation a -> Set.Set a
tuplesUnfold r = Set.fromList (Prelude.map fst (Set.toList r) ++ Prelude.map snd (Set.toList r))

-- this relies on the fact that "Set.fromList" eliminates duplicates, as Set shouldn't care about them
checkRelationWellDef :: Ord a => OrderedSet a -> Bool
checkRelationWellDef (OS s r) = tuplesUnfold r `Set.isSubsetOf` s

unsharedElements :: Ord a => Set.Set a -> Set.Set a -> Set.Set a
unsharedElements x y = (x `Set.union` y) `Set.difference`  (x `Set.intersection` y)



-- leaving this in case i'm saying something stupid, but i realized I can just use the closure for the check condition...
checkReflAlt :: Ord a =>  OrderedSet a -> Bool
checkReflAlt (OS s r) = all (\x ->  (x, x) `Set.member` r) s

checkRefl :: Ord a =>  OrderedSet a -> Bool
checkRefl os = os == closureRefl os

checkTrans :: Ord a => OrderedSet a -> Bool
checkTrans os = os == closureTrans os

checkAntiSym :: Ord a => OrderedSet a -> Bool
checkAntiSym  (OS _ r) = not (any (\(x,y) -> x /= y && (y, x) `Set.member` r) r)


checkPoset :: Ord a => OrderedSet a -> Bool
checkPoset x = checkRefl x && checkTrans x && checkAntiSym x && checkRelationWellDef x




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

-- transitive closure can break anti-symmetry, so case was added
closurePS :: Ord a => OrderedSet a -> OrderedSet a
closurePS os
 | not (checkRelationWellDef os) = error "relation isn't well-defined"
 | not (checkAntiSym os)  = error "relation isn't anti-symmetric"
 | not (checkAntiSym $ closureTrans os) = error "relation looses anti-symmetry when transitively closed"
 | otherwise = closureTrans $ closureRefl os



-- this maybe could've been done more simply, but idk it seems to work like this
forceRelation :: Ord a => OrderedSet a -> OrderedSet a
forceRelation (OS s r) 
 | checkRelationWellDef (OS s r) = OS s r
 | otherwise = OS s ( r `Set.difference` Set.fromList ([(x,y) | x <- Set.toList $ unsharedElements s (tuplesUnfold r), y <- Set.toList s] ++ [(x,y) | y <- Set.toList $ unsharedElements s (tuplesUnfold r), x <- Set.toList s]))

forceAntiSym :: Ord a => OrderedSet a -> OrderedSet a
forceAntiSym (OS s r)
 | checkAntiSym (OS s r) = OS s r
 | otherwise = OS s (r `Set.difference` Set.fromList [(x,y)| x <- Set.toList s, y <- Set.toList s, x/= y && (y,x) `Set.member` r && (x,y) `Set.member` r])


forcePS :: Ord a => OrderedSet a -> OrderedSet a
forcePS currentSet = 
    let recursedSet = forceAntiSym $ closureTrans currentSet
        in if recursedSet == currentSet 
            then closureRefl currentSet 
            else forcePS recursedSet

---------------------------------------------------------------------------------------------------------------------------------------------------------

os6 :: OrderedSet Integer
os6 = OS (Set.fromList [1, 2, 3]) 
         (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,3), (1,3)])

os7 :: OrderedSet Integer
os7 = OS (Set.fromList [1, 2, 3]) 
         (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,1), (1,3), (3,1)])

os8 :: OrderedSet Integer
os8 = OS (Set.fromList [1, 2, 3]) 
         (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,3), (3,2)])

os9 :: OrderedSet Integer
os9 = OS (Set.fromList [1, 2, 3]) 
         (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,3), (3,2), (1,3)])

os10 :: OrderedSet Integer
os10 = OS (Set.fromList [1, 2, 3]) 
          (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,1)])

os11 :: OrderedSet Integer
os11 = OS (Set.fromList [1, 2, 3]) 
          (Set.fromList [(2,2), (3,3), (1,2), (2,3), (1,3)])
os12 :: OrderedSet Integer
os12 = OS (Set.fromList [1, 2, 3]) 
          (Set.fromList [(2,2), (3,3), (1,2), (2,3)])

os13 :: OrderedSet Integer
os13 = OS (Set.fromList [1, 2, 3]) 
          (Set.fromList [(2,2), (3,3), (1,2), (2,3), (3,1)])

os14 :: OrderedSet Integer
os14 = OS (Set.fromList [1, 2, 3, 4, 5]) 
          (Set.fromList [(1,1), (2,2), (3,3), (4,4), (5,5), 
                         (1,2), (2,3), (1,3), (4,5), (1,4), (2,5)])

os15 :: OrderedSet Integer
os15 = OS (Set.fromList [1, 2, 3, 4, 5, 6]) 
          (Set.fromList [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), 
                         (1,2), (2,3), (3,4), (4,5), (5,6), (1,3), (1,4), (1,5), (1,6)])

os16 :: OrderedSet Integer
os16 = OS (Set.fromList [1, 2, 3, 4, 5]) 
          (Set.fromList [(1,1), (2,2), (3,3), (4,4), (5,5), 
                         (1,2), (2,3), (1,3), (4,5), (5,4)])

os17 :: OrderedSet Integer
os17 = OS (Set.fromList [1, 2, 3]) 
          (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,1), (1,3), (3,1)])

os18 :: OrderedSet Integer
os18 = OS (Set.fromList [1, 2, 3]) 
          (Set.fromList [(1,1), (2,2), (3,3), (1,2), (2,1)])

os19 :: OrderedSet Integer
os19 = OS Set.empty Set.empty


myOS :: OrderedSet Integer
myOS = OS (Set.fromList [1..4]) (Set.fromList [(1,4), (4,5), (5,4),(4,1),(2,1),(2,2),(3,3),(3,1),(1,1),(4,4)])

emptyRelOS :: OrderedSet Integer
emptyRelOS = OS (Set.fromList[1..4]) (Set.fromList [])

\end{code}
