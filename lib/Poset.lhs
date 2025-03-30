\section{Partially ordered sets}
\label{posets}
\begin{comment}
This first import some necessary packets for pretty printing. For details, see \hyperref[sec:posetprinting]{subsection 3.4}. We likewise import \texttt{quickCheck} as needed to run some tesets, see \hyperref[sec:simpletests]{Section 8} for that.

\begin{code}
module Poset where

import Data.GraphViz.Types.Monadic
import Data.GraphViz.Types.Generalised
import Data.GraphViz.Commands
import qualified Data.GraphViz.Attributes.Complete as A
import Data.GraphViz.Printing

import Test.QuickCheck
\end{code}
\end{comment}

\subsection{Definitions}

This section is devoted to the construction of posets. A poset $(P,\leq)$ set $P$ with a relation $\leq$, such that $\leq$ is:

\begin{itemize}
\item reflexive
\item transitive
\item antisymmetric
\end{itemize}

For our implementation, we define a relation as a set of tuples, as is standard. Then, an \texttt{OrderedSet} is our notion of a set equipped with a relation (of any kind).

\begin{code}
import qualified Data.Set as Set

type Relation a = Set.Set (a,a)

data OrderedSet a = OS {set :: Set.Set a, 
                        rel :: Relation a} 
    
\end{code}
\begin{comment}
\begin{code}
    deriving (Eq, Ord)
instance Show a => Show (OrderedSet a) where
    show (OS s r) = "{Set: " ++ show (Set.toList s) ++ ",\n "
                        ++ "Rel: " ++ show (Set.toList r) ++ "}" 
\end{code}
\end{comment}

An object of this type is not necessarily a partially ordered set, therefore we need some helper functions in order to transform it into one.

%5BB3-C9E6 %what is this?

\paragraph{Well-definedness}
Firstly we need to check given an object of type \texttt{OrderedSet a}, the relation is indeed a subset of the cartesian product of the carrier set.
%as the implementation of \texttt{OrderedSet} does accept cases which are not of this sort.
% We shall call a relation $R$ "well-defined with respect to a set $P$" iff $R \subseteq P \times P$. We shall just say "well-defined" when the carrier set is clear form the context.
\newline
For this, we shall fisrt define the function \texttt{tuplesUnfold}, which ``unfolds" the in a relation.
\newline 
Then, we can easily check for well-definedness. 

\begin{code}
tuplesUnfold :: Ord a => Relation a -> Set.Set a
tuplesUnfold r = Set.fromList (Prelude.map fst (Set.toList r) ++ Prelude.map snd (Set.toList r))

checkRelationWellDef :: Ord a => OrderedSet a -> Bool
checkRelationWellDef (OS s r) = tuplesUnfold r `Set.isSubsetOf` s
\end{code}

Moreover if the relation is not well-defined relation, we might want to force it to be. 
%The following function takes care of this by removing from a relation, set of elements in it, but not in the the carrier set.

\begin{code}
forceRelation :: Ord a => OrderedSet a -> OrderedSet a
forceRelation (OS s r) 
 | checkRelationWellDef (OS s r) = OS s r
 | otherwise = OS s ( r `Set.difference` Set.fromList (
    [(x,y) | (x,y) <- Set.toList r, x `Set.member` (tuplesUnfold r `Set.difference` s)] 
    ++ 
    [(x,y) | (x,y) <- Set.toList r, y  `Set.member` (tuplesUnfold r `Set.difference` s)]))
\end{code}


\subsection{Checks and Closures}
\paragraph{Reflexivity} 

Both closure and checks are straightforwards, and well readable from the code implementation. We simply need add, or check the existance of, reflexive tuples.

\begin{code}
closureRefl :: Ord a => OrderedSet a -> OrderedSet a
closureRefl (OS s r) = OS s (r `Set.union` Set.fromList [(x,x)| x <- Set.toList s])

checkRefl :: Ord a =>  OrderedSet a -> Bool
checkRefl (OS s r) = all (\x ->  (x, x) `Set.member` r) s
\end{code}

\paragraph{Transitivity}
The transitive closure requires a little more working:
\newline
Firstly, we define the helper function \texttt{transPair}, to check if, given any $x,z$, there is a $y$ such that $x R y \wedge y R z$.
\newline
This allows us to know which "one-step" transitive chains are currently missing. So, we add to the relation any pair which satisfies \texttt{transPair}, so that we have "one-step" transitivity.

\begin{code}
transPair ::  Ord a => a -> a -> OrderedSet a -> Bool
transPair x z (OS s r)=  any (\y -> (x, y) `Set.member` r && (y,z) `Set.member` r) s

transStep :: Ord a => OrderedSet a -> OrderedSet a
transStep (OS s r) = OS s (r `Set.union` Set.fromList [(x,z) | x <- Set.toList s, z <- Set.toList s, transPair x z (OS s r)])
\end{code}

Of course this won't suffice. 
%Now that we have enlarged our relation, new pairs which satisfy \texttt{transPair} might arise. Therefore 
In order to close for any transitive chain, we need to recursively apply the \texttt{transStep} function to our object, until it reaces a fixed point, i.e. until \texttt{transStep os == os}.

\begin{code}
closureTrans :: Ord a => OrderedSet a -> OrderedSet a
closureTrans  currentSet = 
        let recursedSet = transStep currentSet
        in if recursedSet == currentSet
            then currentSet 
            else closureTrans recursedSet
\end{code}


Checking is again fairly straightforward. 
%For any triple $(x,y,z)$, wherein $xRy$, $y'Rz$ and $y=y'$ (this is an implementation quirk, of course we're just checking $xRyRz$), we make sure that that also $xRz$.

\begin{code}
checkTrans :: Ord a => OrderedSet a -> Bool
checkTrans (OS _ r) = all (\(x, _, z) -> Set.member (x, z) r) [(x, y, z) | (x, y) <- Set.toList r, (y', z) <- Set.toList r, y == y']
\end{code}

\paragraph{Forcing Antisymmetry}

Here there are caveats. Note that it is not possible to just "close" a relation under antisymmetry. Firstly, we need to remove, rather than add. Furthermore, note that there is no unique way to obtain an anti-symmetric "reduction"  analogously to a closure: we'd want a reduction of $R$ w.r.t a property $Q$ to be the greatest $R' \subseteq R$ for which $R'$ satisfies $Q$. But there is not such set for anti-symmetry! For a given symmetric pair $(x,y),(y,x) \in R$, the smallest can be removing one, or the other.
%But there's two ways to do so. 
So an anti-symmetric reduction is not unique.

Two ways, among others, stand out as elegant in "forcing" anti-symmetry. The first consists in eliminating all symmetric pairs from the relation $R$, the second is to quotient of $P$ based on the clusters of symmetric pairs of $R$. We implement both as each has their advatages and disadvantages. But for space concerns, only look at the latter. 

\begin{comment}
\subsubsection{Removing Edges}
Given an object $(P,R)$ of type \texttt{OrderedSet a}, we eliminate all the symmetric pairs in $R$. That is we construct a new relation $R^* \subseteq R$ such that if $x \neq y$ and $(x,y) \in R$ and $(y,x) \in R$, then $\neg((x,y), (y,x) \in R^*)$.
 
\begin{code}
forceAntiSym :: Ord a => OrderedSet a -> OrderedSet a
forceAntiSym (OS s r)
 | checkAntiSym (OS s r) = OS s r
 | otherwise = OS s (r `Set.difference` Set.fromList [(x,y)| x <- Set.toList s, 
                                                            y <- Set.toList s, 
                                                            x/= y && (y,x) `Set.member` r && (x,y) `Set.member` r]
                    )
\end{code}

One the upside, this approach does not modify the carrier set. We only modify the relation, and leave the carrier set untouched. This is surely more in the ``spirit" of a closure-like operation.

A worry, is that, closing under transitivity and then anti-symmtery could significantly reduce the numbers of pairs \emph{in the relation}: in particular every (non-reflexive) cycle is eliminated from the relation.
\end{comment}

%\subsubsection{Quotienting}
% to make Edo happy :)
Given any $(P,R)$ of type \texttt{OrderedSet a}, we can quotient the set $P$ on the symmetric points, i.e. merge the \emph{vertex} that see each other into a cluster. That is, for any $x \in P$ we define the equivalence class $[x]_s$ as the set $\{y \in P| y \neq x \wedge x R y \wedge y R x \}$. We call the resulting set $P/s$.
%\footnote{Note that we need a choice for a rappresentative to leave in the set. We can leverage having an \texttt{Ord} instance, and use \texttt{y < x} for this.}

\begin{code}
quotientAntiSym :: Ord a => Set.Set a -> Relation a -> Set.Set a
quotientAntiSym s r = s `Set.difference` Set.fromList [x| (x,y) <- Set.toList r, (y,x) `Set.member` r, x /= y, y < x] 

forceAntiSymAlt :: Ord a => OrderedSet a -> OrderedSet a
forceAntiSymAlt (OS s r) = forceRelation $  OS (quotientAntiSym s r) r
\end{code}

The advantage of this approach, is that it preserve logical properties\footnote{For the knowing reader: we are guaranteed a p-morphism between the structures.}. 
% Since our topic at hand involves excatly defining logic over mathematical structures, this is certainly a nice feature.

A downside, this changes the carrier set: from $P$ we go to $P/s$. This is a bit agains the "spirit" of a "closure".
%\footnote{Note, due to Haskell's implementation, argue "it is the same set anyways, it's is just a matter of names referring to the same object". In set theory, syntactically specifying $\{a,b \}$ may well be the same set as $\{a\}$, if $b$ happens to semantically be the same name for $a$ (i.e. if $a=b$). But in Haskell's \texttt{Data.Set}, named elements are the objects. This is evident from the fact that \texttt{Set.size} returns a value without us needing to specify what equalities hold between the objects.}

Furthermore, closing under transitivity and then anti-symmterically may shrink significatly the size of the \emph{carrier set}, in particular every cycle will collapse to a single point.


\begin{comment}
\paragraph{Preservation of properties}

Since we'll want transtive, reflexive closures together with the anti-symmetric forcing, we need to make sure that our two implementation does not make us loose these properties in a relation. This is fairly obvius for the second implementation. But we want do need a small argument for the first implementation:

Reflexivity is still quick: by the very clause of anti-symmetry, only couples $(x,y)$ such that $x \neq y$ are removed. The non trivial preservation concerns transitivity: we shall therefore prove the following proposition.

\begin{prop} 
Let $(P,R)$ be a set with a relation.  For any relation, we define the antisymmetric forcing of $R$, $R^\dagger$ as:

$$
R^{\dagger} = \begin{cases}
    R                                                                           & \text{ if } R \text{ is anti-symmetric} \\ 
    R \setminus \{(x,y) \mid  (x,y) \in R \wedge (y,x) \in R \wedge x \neq y\}  & \text{ otherwise}\end{cases}
$$

Then, if $R$ was transitive, so must be $R^\dagger$.
\end{prop}

\begin{proof} 
Let that $R \subseteq P \times P$ be any transitive  relation on some fixed but arbitrary set $P$.

   Let $R^\dagger$ be as in the above definition. Now, take any $x,y,z \in P$ such that $x R^\dagger y \wedge y R^\dagger z$. We need to show that $x R^\dagger z$.

   Now since $R^\dagger \subseteq R$ by construction, $x R y \wedge y R z$. So by the transitivity of $R$, we have $x R z$. Suppose now towards contradiction that $(x,z)\cancel{\in} R^\dagger$. Therefore $z R x$ and $z\neq x$. But then, since $y R z$, by transitivity of $R$, $y R x$. 

   Clearly, since we assumed $y R^\dagger z$ and $(x,z)\cancel{\in} R^\dagger$, $y \neq x$. But then, by definition of $R^\dagger$,  $(x,y)\cancel{\in} R^\dagger$, which is a contradiction to our assumpion. Therefore  $(x,z)\in R^\dagger$ as needed.
\end{proof}

Now since our implementation of \texttt{forceAntiSym} corresponds to our definition of $R^\dagger$, we can be sure that, given an ordered set \texttt{(OS s r)}, the result of \texttt{forceAntiSym  transClosure (OS s r)}, say \texttt{(OS s r')}, \texttt{r'} is transitive. 
\end{comment}

Once again, checking is much simpler than closing.

\begin{code}
checkAntiSym :: Ord a => OrderedSet a -> Bool
checkAntiSym  (OS _ r) = not (any (\(x,y) -> x /= y && (y, x) `Set.member` r) r)
\end{code}



\subsection{From ordered sets to posets}

Finally, we are able to define functions that given any object of type \texttt{OrderedSet a}, will transform it into a poset and a checker for whether it is indeed a poset.

\begin{comment}
For the first task we take two approaches: in case everything "is behaving well", we can take the less controversial reflexive transitive closures, and obtain a poset closure without anti-symmetry caveats. The code is self explanatory here

\begin{code}
closurePoSet :: Ord a => OrderedSet a -> OrderedSet a
closurePoSet os
 | not (checkRelationWellDef os) = error "relation isn't well-defined"
 | not (checkAntiSym os)  = error "relation isn't anti-symmetric"
 | not (checkAntiSym $ closureTrans os) = error "relation looses anti-symmetry when transitively closed"
 | otherwise = closureTrans $ closureRefl os

makePoSet :: Ord a => OrderedSet a -> OrderedSet a
makePoSet  = closureRefl .  closureTrans 
\end{code}
\end{comment}

%In most cases however, we will need to engage with anti-symmetric forcing. Thus 

%We have two poset forcing functions, using our two approaches \footnote{making sure to first take the transitive closure, and the the antisymmetric closure, which we proved preserves transitivity. We ommitted the proof for space concerns. Whereas note that the opposite wouldn't do; any (non-reflexive) cycle in the relation would break anti-symmetry after transitive closing.}.

\begin{comment}
\begin{code}
forcePoSet :: Ord a => OrderedSet a -> OrderedSet a
forcePoSet  = closureRefl .  forceAntiSym .  closureTrans . forceRelation
\end{code}
\end{comment}

\begin{code}
forcePosetAlt :: Ord a => OrderedSet a -> OrderedSet a
forcePosetAlt = closureRefl .  forceAntiSymAlt .  closureTrans

checkPoset :: Ord a => OrderedSet a -> Bool
checkPoset x = checkRefl x && checkTrans x && checkAntiSym x && checkRelationWellDef x
\end{code}

Lastly, to use QuickTest to test our Implementations, we need also an arbitrary instance for Posets. We do this by generating an arbitrary \texttt{OrderedSet a}, then it generates posets, but closing it under reflexivity and transitivity and forcing anti-symmetry using the above introcued functions:


\begin{code}
instance (Arbitrary a, Ord a) => Arbitrary (OrderedSet a) where
    arbitrary = sized randomOS where
        randomOS :: (Arbitrary a, Ord a) => Int -> Gen (OrderedSet a)
        randomOS n = do
            s <- Set.fromList <$> vector (max n 1)
            r <- Set.fromList . take n <$> sublistOf (Set.toList $ Set.cartesianProduct s s)
            return $ forcePoSet $ OS s r
\end{code}



\subsection{Printing machinery}
\label{sec:posetprinting}

This section\footnote{A similar section will be present at the end of each section introducing a new mathematical structure. The implementation are always be similar.} is dedicated to the visualization of the structures we have discussed, namely posets, via what are called in mathematics \textit{Hasse diagrams}.

Our primary concern is for the picture to be clear and readable. Thus we omit all transitive and reflexive edges. 

We stuck with the mathematical convention of having unlabeled nodes, since we are in any case interested in classes of posets "up to isomorphism".\footnote{If the user wishes to label their node, this can easily be done modifying the GraphAttributes (those wrapped in square brackets) in "toGraphOrd".}

In order to print all these structures, we import the \texttt{graphViz} library, with all its dependencies. If the reader wishes to visualize the graph, they should both install \textit{graphViz} and \textit{Xlib} on their machines.
If running Ubuntu, one may simply run \texttt{sudo apt-get install libx11-dev graphviz} on bash.

It should be noted that all the types we are working with will have to be an instance of the class \texttt{PrintDot} which comes with \texttt{graphViz}. This causes some difficulties when it comes to representation; but we ommit details for space concerns. Suffice it to say, we settled for the more economical solution of always taking an isomorphic copy on INT.

%  since Data.Set
% does not have an original instance of PrintDot (Set a) and, since the Set module is imported, all homebrew instances we defined (although working) were "orphan" instances, and thus triggered a Wall warning. \newline 
% In our specific case, the orphan instance would not be a problem per se, but to avoid the warning we decided to always run the isomorphism defned above (simplifyDL1, simplifyPS1) to obtain an isomorphic copy of our poset defined on the type INT. Other solution would have required rewriting every instance of "Set" as a Newtype, or rewriting the Set module in one of our own module and add the instance there. Both solutions seemed a bit excessive and thus

% Since posets are part of the underlying structure of both lattices and priestley spaces,and its type is used to construct the types of the latter two, we define these helper function in this section.

\begin{code}
fromTransitive::Ord a => OrderedSet a -> OrderedSet a
fromTransitive (OS s r) = OS s k where
              k = Set.difference r (Set.fromList [(x,y)| (x,y) <- Set.toList r,   any (\z -> z /= x  && Set.member (x,z)  r && Set.member (z,y) r ) s   ])


fromReflexive::Ord a => OrderedSet a -> OrderedSet a
fromReflexive (OS s r) = OS s k where
   k = Set.difference r (Set.fromList [(x,y)| (x,y) <- Set.toList r, x == y])

fromReflTrans::Ord a => OrderedSet a -> OrderedSet a
fromReflTrans  = fromTransitive.fromReflexive
\end{code}

The following two functions are crucial to the visualization of the structures. They only rely on the types \texttt{Relation a} and \texttt{OrderedSet a} and therefore will be called also in the other sections.  

 \texttt{toGraphRel'} uses \texttt{mapM\_} to transform an object \texttt{r}of type \texttt{Relation a} into a  monadic action, in particular an instance of of the type \texttt{Dot a}. 

\texttt{toGraphRel} uses \texttt{digraph'} to generate a directed graph out of an object of type \texttt{Dot a}. The carrier set will be the used to generate the points and the underlying relation of the object will be then used to generate the edges of the graph. 
Notice that, although no Lattice has "isolated points", many Priestley space do which means that we could have nodes in the space which only have one reflexive arrow. 
% If we only ran the second part of the function, and just mapped "-->" over the relations, we would either lose those isolated points, or we would ahve to print every time all the reflexive arrows of the graph.
Thus it is important that we both print nodes out of the elements of the carrier set, and then construct edges using the relations. 


\begin{code}
toGraphRel :: Relation a -> Dot a
toGraphRel  =  mapM_ (uncurry (-->)) 

toGraphOrd :: (Ord a,PrintDot a) => OrderedSet a -> DotGraph a
toGraphOrd r = digraph' $ do
 
  mapM_ (`node` [A.Shape A.PointShape, A.FontSize 0.0, A.Width 0.1] )(Set.toList $ set r )

  
  edgeAttrs [A.Dir A.NoDir]
  nodeAttrs [A.Shape A.PointShape, A.FontSize 0.0, A.Width 0.1] 
  graphAttrs [A.RankDir A.FromBottom, A.NodeSep 1.0]
  toGraphRel $ rel r
\end{code}


The following function then actually outputs the picture of the ordered set. 

\begin{code}
showOrdSet ::(Ord a, Data.GraphViz.Printing.PrintDot a) => OrderedSet a -> IO ()
showOrdSet p = runGraphvizCanvas' (toGraphOrd $ fromReflTrans p) Xlib
\end{code}

