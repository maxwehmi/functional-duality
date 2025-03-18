
\section{Partially ordered sets}



This section is devoted to the construction of posets. A poset $(P,\leq)$ is a structure such that $P$ is a set and $\leq$ is a partial order, that is $\leq$ is reflexive, transitive and antissimetric.

We import the standard library for sets, Data.Set, in order to be able to work with sets and we start by defining the OrderedSet data type for sets equipped with a relation.

An object (P, R) of type OrderedSet a, is not necessarily a partially ordered set, therefore we need some helper functions in order to transform R in to a partial order.









\begin{quote}
I have changed the Relation a from "newtype ... Set .." to "type ... Set.Set .." as Relation a is a type synonim and it was giving me problems with the typechecking in other files. 

I have changed the data type of OrderedSet a, in order to have functions to retreive the underlying set and the underlying relation of the OrderedSet.      
\end{quote}


\begin{code}
module Poset where

import qualified Data.Set as Set

type Relation a = Set.Set (a,a)

data OrderedSet a = OS {set :: Set.Set a, rel :: Relation a} 
    deriving (Eq, Ord,Show)
\end{code}

\subsection{some helping functions}

Firstly, a function that "unfolds/unwraps" the tuples in a set of tuples, i.e. a relation. The purpose is that we might, want to check all the objects the relation includes. So we make a set of them.
The idea is that we get the list of first elements in all the tuples by mapping fst to all the elements of R. And likewise for second. Then joining those lists and making a set from the resulting list gives us our set of elements of R.

\begin{code}
tuplesUnfold :: Ord a => Relation a -> Set.Set a
tuplesUnfold r = Set.fromList (Prelude.map fst (Set.toList r) ++ Prelude.map snd (Set.toList r))
\end{code}

We might want to get the set of unshared elements between two sets. This is fairly self-explanatory.

\begin{code}
unsharedElements :: Ord a => Set.Set a -> Set.Set a -> Set.Set a
unsharedElements x y = (x `Set.union` y) `Set.difference`  (x `Set.intersection` y)
\end{code}


\subsection{Checks}

We might want to check if the relation over an ordered set is well-defined, in the sense that the "domain" and "co-domain" of the relation are a subset of the carrier set. Yes, the implementation of OrdSet does accept cases that are non-well defined in this sense.

Using \texttt{tuplesUnfold} this is easy to do. (Though note I rely on the fact that \texttt{Set.fromList} eliminates duplicates, as \texttt{Set} shouldn't care about them, sets being extensional and all. But might want to double check it actually does so).

\begin{code}
checkRelationWellDef :: Ord a => OrderedSet a -> Bool
checkRelationWellDef (OS s r) = tuplesUnfold r `Set.isSubsetOf` s
\end{code}


Checking for relations conditions are fairly self-explanatory and readable. If reflexive and transitive closure have been defined correctly, then it's a matter of checking closure is idempotent. But, I'm also including alternative checks, as a sanity test that doesn't rely on closures being correctly defined. Anti-symmetry is clear.

With the 3 properties checks, checking PoSets is quick (I additionally include checking the relation is well defined).

\begin{code}
checkRefl :: Ord a =>  OrderedSet a -> Bool
checkRefl os = os == closureRefl os

checkTrans :: Ord a => OrderedSet a -> Bool
checkTrans os = os == closureTrans os

checkTransAlt :: Ord a => OrderedSet a -> Bool
checkTransAlt (OS _ r) = all (\(x, _, z) -> Set.member (x, z) r) [(x, y, z) | (x, y) <- Set.toList r, (y', z) <- Set.toList r, y == y']

checkReflAlt :: Ord a =>  OrderedSet a -> Bool
checkReflAlt (OS s r) = all (\x ->  (x, x) `Set.member` r) s

checkAntiSym :: Ord a => OrderedSet a -> Bool
checkAntiSym  (OS _ r) = not (any (\(x,y) -> x /= y && (y, x) `Set.member` r) r)


checkPoset :: Ord a => OrderedSet a -> Bool
checkPoset x = checkRefl x && checkTrans x && checkAntiSym x && checkRelationWellDef x
\end{code}



\subsection{Closures}
The reflexive closure is readable and self-explanatory.

\begin{code}
closureRefl :: Ord a => OrderedSet a -> OrderedSet a
closureRefl (OS s r) = OS s (r `Set.union` Set.fromList [(x,x)| x <- Set.toList s])
\end{code}

Transitive closure requires a littl more working trough (at least i couldn't come up with something very simple).

Firstly, we define a "being a transitive pair" relation, meaning there is some shared $y$ for which $xRy$ and $yRz$.
\begin{code}
transPair ::  Ord a => a -> a -> OrderedSet a -> Bool
transPair x z (OS s r)=  any (\y -> (x, y) `Set.member` r && (y,z) `Set.member` r) s
\end{code}

Now, we add to the relation anything that is a transitive pair, so that we have "one-step" transitivity.

\begin{code}
transStep :: Ord a => OrderedSet a -> OrderedSet a
transStep (OS s r) = OS s (r `Set.union` Set.fromList [(x,z) | x <- Set.toList s, z <- Set.toList s, transPair x z (OS s r)])
\end{code}

Since this only adds "one-step" transtivity, we need to recurse the process until it is idempotent, i.e. the relation is fully transitive. Then we have obtained our transitive closure. This might be a bit hacky, perhaps there is a more straighforward way, similar to reflexive closure, but again it did not come to me.

\begin{code}
closureTrans :: Ord a => OrderedSet a -> OrderedSet a
closureTrans  currentSet = 
        let recursedSet = transStep currentSet
        in if recursedSet == currentSet
            then currentSet 
            else closureTrans recursedSet
\end{code}

With these two "uncontroversial closures", we can make certain OrdSets into PoSets. In particular ones where:

\begin{itemize}
\item the relation is well defined (though perhaps forcing the relation to be well defined, see later function, would work actually, so we might rid of this case).
\item the relation is anti-symmetric
\item the transitive closure does not break anti-symmetry (this can happen, cosider the set $\{a,b,c\}$ with $aRb, bRc, cRa$. Anti-symmetry is lost when closing transitively)
\end{itemize}

\begin{code}
-- transitive closure can break anti-symmetry, so case was added
closurePoSet :: Ord a => OrderedSet a -> OrderedSet a
closurePoSet os
 | not (checkRelationWellDef os) = error "relation isn't well-defined"
 | not (checkAntiSym os)  = error "relation isn't anti-symmetric"
 | not (checkAntiSym $ closureTrans os) = error "relation looses anti-symmetry when transitively closed"
 | otherwise = closureTrans $ closureRefl os
\end{code}


\subsection{Forcings}

If a given set does not have a well-defined relation, we might want to force it to be. We take the set, and remove from it the set of unshared elements. We defined a helping functions for this. So we generate this set from the list of tuples whose first element is a member of unsharedElements between the carrier set and the unfoldedTuples of the relation, conjoined with the same list but for the second element, i.e. the list of objects in the relation that are unshared with the carrier set.

\begin{code}
-- this maybe could've been done more simply, but idk it seems to work like this
forceRelation :: Ord a => OrderedSet a -> OrderedSet a
forceRelation (OS s r) 
 | checkRelationWellDef (OS s r) = OS s r
 | otherwise = OS s ( r `Set.difference` Set.fromList (
                                                        [(x,y) | (x,y) <- Set.toList r, x `Set.member` unsharedElements s (tuplesUnfold r)] 
                                                        ++ 
                                                        [(x,y) | (x,y) <- Set.toList r, y `Set.member` unsharedElements s (tuplesUnfold r)]
                                                       )
                    )
\end{code}


Even though there's no canonical anti-symmetric closure, we might nonetheless want to force anti-symmetry on an \texttt{OrdSet}.

There are two ways, we have to see which we find more adequate, both have kind of pluses and minuses % Discuss and add to them!!!!!.

\paragraph{\texttt{forceAntiSym}}
Given an OrdSet, we take away all the symmetric \emph{edges}.  So we take the relation and takeaway the set of symmetric tuples.

Pros: 
\begin{itemize}
\item it does not modify the carrier set (eg \texttt{Set.size}, the cardinality, will remain the same after the procedure).
\end{itemize}

Cons: 
\begin{itemize}
\item doesn't preserve logical properties. 
\item we should test that this does tend torawrds very trivial posets when applied after transitive closure.
\end{itemize}



 
\begin{code}
forceAntiSym :: Ord a => OrderedSet a -> OrderedSet a
forceAntiSym (OS s r)
 | checkAntiSym (OS s r) = OS s r
 | otherwise = OS s (r `Set.difference` Set.fromList [(x,y)| x <- Set.toList s, 
                                                            y <- Set.toList s, 
                                                            x/= y && (y,x) `Set.member` r && (x,y) `Set.member` r]
                    )
\end{code}

\subparagraph{Transitive preserving}

We want to make sure that forcing anti-symmetry (removing the edges way) does not make us loose an existing property of the relations. It is fairly obvious that it does not remove reflexivity given $x \neq y$ is a condition (and anyways I apply reflexivity \emph{after} forcing anti-symmetry when forcing PoSets).

But it is not obvious we don't lose transitivity, so here's a sketch of the proof.

\textbf{Proposition}: \verb:`forceAntiSymm $ transClosure`:, where \verb:`forceAntiSym`: of a relation $R$, call it $R^{\dagger}$ is defined by: 

$$
R^{\dagger} = \begin{cases}
    R                                                                           & \text{ if } R \text{ is anti-symmetric} \\ 
    R \setminus \{(x,y) \mid  (x,y) \in R \wedge (y,x) \in R \wedge x \neq y\}  & \text{ otherwise}\end{cases}
$$

(which should mirror what the Haskell definition is doing) Is transitive.

% NOTE: I Added the package for cancel in latexmarcos.tex, but in case it doesn't work still, for the record, \cancel is meant to function like \not, just prettier when you do it on big things like R^\dagger. Modify with that, or just using \neg if needed.

\emph{Proof}:
Suppose $R$ is any relation. We know the transitive closure  $R^{+}$ transitive. Let $R^{\dagger}$ be the antisymmetric "closure" of $R^{+}$.

Suppose $xR^{\dagger}y$ and $yR^{\dagger}z$ (for distinct $x,y,z$, the cases where either of them is equal are quick). Since $R^{\dagger}$ is generated only by removing points from $R^{+}$, we must've also have $xR^{+}y , yR^{+}z$. So by transitivity $xR^{+}z$.

If $x=y$ we're quickly done, since then $xR^{\dagger}z$. Likewise if $y=z$. So suppose they aren't equal to each other.

Now suppose for contradiction $x \cancel{R^{\dagger}} z$. Latex does not know \cancel, I dont know what this should mean
Again by how $R^{\dagger}$ was defined, we must've had $zR^{+}x$. (If we didn't, then $(x,z) \notin \{(x,y) \mid  (x,y) \in R \wedge (y,x) \in R \wedge x \neq y\}$, and so we'd have $(x,z) \in R^{+} \setminus \{(x,y) \mid  (x,y) \in R \wedge (y,x) \in R \wedge x \neq y\}$).

But then by transitivity of $R^{+}$ we'd have $yR^{+}x$. But then $(x,y) \in \{(x,y) \mid  (x,y) \in R \wedge (y,x) \in R \wedge x \neq y\}$, so by definition $(x,y) \notin R^{\dagger}$, i.e. $x\cancel{R^{\dagger}} y$, contradicting our assumption that $xR^{\dagger}y$.


\paragraph{\texttt{forceAntiSymAlt}}
The alternative way,
% to make Edo happy :)
is to quotient the set on the symmetric points, i.e. merge the \emph{vertex} that see each other into a cluster. 

Pros:
\begin{itemize}
\item This does preserve logical properties
\end{itemize}

Cons: 
\begin{itemize}
\item This does change the carrier set (yes, haskell's texttt{Data.Set} does not implement a meta-notion of named elements referring to the same objects. When we define a set trough a list, which is what we always do, the elements are presumed to be distinct. This is showcased by the fact that a set has a defifinite cardinality. This wouldn't be possible without such an asumption, since then [a,b,c,d] could be of card 4, but might aswell be card 1, depending on how equality turns out.)

\item doing it after taking the transitive closure (which we want to i think) often results in a huge collapse, and makes the resulting set very small. Because any loop in the initial Ord set will all collapse to one point after the forcing anti-symm(alternative) to its transitive closure. 
\end{itemize}

To obtain it from a set wrt to a relation, we compute the quotientSet wrt to anti-symmetry: remove from s the bigger x that appears in a symmetric pair. This is a cheeky trick to select one of the two elements, based on the fact that we have \texttt{Ord a}. Without that I think it would be a real pain. So for any symmetric pair, we keep the smallest element in that pair as our cluster rapresentative.

Then we just let such quotient set be the new carrier set, and force the relation to be well-defined, just as sanity check.

\begin{code}
quotientAntiSym :: Ord a => Set.Set a -> Relation a -> Set.Set a
quotientAntiSym s r = s `Set.difference` Set.fromList [x| (x,y) <- Set.toList r, (y,x) `Set.member` r, x /= y, y < x] 

forceAntiSymAlt :: Ord a => OrderedSet a -> OrderedSet a
forceAntiSymAlt (OS s r) = forceRelation $  OS (quotientAntiSym s r) r

\end{code}

The proof that this preserves transitivity is to do, but it seems fairly straightforward


(there would also be a third way that David came up with when I chatted with him abou this, whose advantage is that it does not reduce either sets nor edges by much, so we might get more consistently interesting posets from arbitrary ordsets. But its more contrived and complicated, I'll think over it better before putting it in)


\paragraph{forcePoset}

Then in light of this, it suffices to take the transitive closure first, then the anti-symmetric, to force a PoSet.

\begin{code}

forcePoSet :: Ord a => OrderedSet a -> OrderedSet a
forcePoSet  = closureRefl .  forceAntiSym .  closureTrans . forceRelation

-- forceRleation is reduntant here since it is inside forceAntiSymAlt
forcePosetAlt :: Ord a => OrderedSet a -> OrderedSet a
forcePosetAlt = closureRefl .  forceAntiSymAlt .  closureTrans

\end{code}

Here's some GPT-generated test sets to play around with.

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