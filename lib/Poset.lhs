
\section{Partially ordered sets}



This section is devoted to the construction of posets. A poset $(P,\leq)$ is a structure such that $P$ is a set and $\leq$ is a partial order, that is $<$ is reflexive, transitive and antissimetric.

We import the standard library for sets, Data.Set, in order to be able to work with sets and we start by defining the OrderedSet data type for sets equipped with a relation.

An object (P, R) of type OrderedSet a, is not necessarily a partially ordered set, therefore we need some helper functions in order to transform R in to a partial order.









\begin{code}
module Poset where

import qualified Data.Set as Set

type Relation a = Set.Set (a,a)

data OrderedSet a = OS {set :: Set.Set a, rel :: Relation a} 
    deriving (Eq, Ord,Show)


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

checkTransAlt :: Ord a => OrderedSet a -> Bool
checkTransAlt (OS _ r) = all (\(x, _, z) -> Set.member (x, z) r) [(x, y, z) | (x, y) <- Set.toList r, (y', z) <- Set.toList r, y == y' ]

checkAntiSym :: Ord a => OrderedSet a -> Bool
checkAntiSym  (OS _ r) = not (any (\(x,y) -> x /= y && (y, x) `Set.member` r) r)


checkPoset :: Ord a => OrderedSet a -> Bool
checkPoset x = checkRefl x && checkTrans x && checkAntiSym x && checkRelationWellDef x




closureRefl :: Ord a => OrderedSet a -> OrderedSet a
closureRefl (OS s r) = OS s (r `Set.union` Set.fromList [(x,x)| x <- Set.toList s])

transPair ::  Ord a => a -> a -> OrderedSet a -> Bool
transPair x z (OS s r)=  any (\y -> (x, y) `Set.member` r && (y,z) `Set.member` r) s

-- This only adds "one step" transtivity, needs to be recursed till the it becomes idempotent or something like this
transStep :: Ord a => OrderedSet a -> OrderedSet a
transStep (OS s r) = OS s (r `Set.union` Set.fromList [(x,z) | x <- Set.toList s, z <- Set.toList s, transPair x z (OS s r)])

-- current hacky solution
closureTrans :: Ord a => OrderedSet a -> OrderedSet a
closureTrans  currentSet = 
        let recursedSet = transStep currentSet
        in if recursedSet == currentSet
            then currentSet 
            else closureTrans recursedSet

-- transitive closure can break anti-symmetry, so case was added
closurePoSet :: Ord a => OrderedSet a -> OrderedSet a
closurePoSet os
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

\end{code}


\textbf{Proposition}: \verb:`forceAntiSymm $ transClosure`:, where \verb:`forceAntiSym`: of a relation $R$, call it $R^{\dagger}$ is defined by: 

$$
R^{\dagger} = \begin{cases}
    R                                                                           & \text{ if } R \text{ is anti-symmetric} \\ 
    R \setminus \{(x,y) \mid  (x,y) \in R \wedge (y,x) \in R \wedge x \neq y\}  & \text{ otherwise}\end{cases}
$$
%% I Added the package for cancel, but in case it doesn't work still, for the recrod, \cancel is meant to function like \not, just prettier when you do it on big things like R^\dagger
\emph{Proof}:
Suppose $R$ is any relation. We know the transitive closure  $R^{+}$ transitive. Let $R^{\dagger}$ be the antisymmetric "closure" of $R^{+}$.

Suppose $xR^{\dagger}y$ and $yR^{\dagger}z$ (for distinct $x,y,z$, the cases where either of them is equal are quick). Since $R^{\dagger}$ is generated only by removing points from $R^{+}$, we must've also have $xR^{+}y , yR^{+}z$. So by transitivity $xR^{+}z$.

If $x=y$ we're quickly done, since then $xR^{\dagger}z$. Likewise if $y=z$. So suppose they aren't equal to each other.

Now suppose for contradiction $x \cancel{R^{\dagger}} z$. Latex does not know \cancel, I dont know what this should mean
Again by how $R^{\dagger}$ was defined, we must've had $zR^{+}x$. (If we didn't, then $(x,z) \notin \{(x,y) \mid  (x,y) \in R \wedge (y,x) \in R \wedge x \neq y\}$, and so we'd have $(x,z) \in R^{+} \setminus \{(x,y) \mid  (x,y) \in R \wedge (y,x) \in R \wedge x \neq y\}$).

But then by transitivity of $R^{+}$ we'd have $yR^{+}x$. But then $(x,y) \in \{(x,y) \mid  (x,y) \in R \wedge (y,x) \in R \wedge x \neq y\}$, so by definition $(x,y) \notin R^{\dagger}$, i.e. see above: $x\cancel{R^{\dagger}} y$, contradicting our assumption.


\begin{code}

forcePoSet :: Ord a => OrderedSet a -> OrderedSet a
forcePoSet os = closureRefl $  forceAntiSym $ closureTrans os

-- forcePoSet :: Ord a => OrderedSet a -> OrderedSet a
-- forcePoSet currentSet = 
--     let recursedSet = forceAntiSym $ closureTrans currentSet
--         in if recursedSet == currentSet 
--             then closureRefl currentSet 
--             else forcePoSet recursedSet

\end{code}

Here's some GPT-generated test sets

\begin{code}
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

myCircle :: OrderedSet Integer
myCircle = OS (Set.fromList [1,2,3]) (Set.fromList [(1,2),(2,3),(3,1)])

\end{code}