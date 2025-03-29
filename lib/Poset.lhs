
\section{Partially ordered sets}
\label{posets}

This first ugly block of import is unfortunatelly necessary for some pretty printing. We'll see more about it in the dedicated \hyperref[sec:posetprinting]{subsection}. We likewise import \texttt{quickCheck} as needed to run some tesets, see \hyperref[sec:simpletests]{Section 8} for that.



\begin{code}
module Poset where

import Data.GraphViz.Types.Monadic
import Data.GraphViz.Types.Generalised
import Data.GraphViz.Commands
import qualified Data.GraphViz.Attributes.Complete as A
import Data.GraphViz.Printing

import Test.QuickCheck
\end{code}

\subsection{Definitions}

This section is devoted to the construction of posets. A poset $(P,\leq)$ set $P$ with a relation $\leq$, such that $\leq$ is:

\begin{itemize}
\item reflexive
\item transitive
\item antisymmetric
\end{itemize}

We import the standard library for sets, Data.Set, in order to be able to work with objects that behave like sets and we start by defining the  \texttt{OrderedSet} data type for sets equipped with a relation.

An object $(P, R)$ of type \texttt {OrderedSet a}, is not necessarily a partially ordered set, therefore we need some helper functions in order to transform $R$ in to a partial order.

For our structures, we define a relation as a set of tuples, as is standard. Then, an \texttt{OrderedSet} (ordset) is our notion of our set embued with a relation (of any kind).

\begin{code}
import qualified Data.Set as Set

type Relation a = Set.Set (a,a)

data OrderedSet a = OS {set :: Set.Set a, 
                        rel :: Relation a} 
    deriving (Eq, Ord)

instance Show a => Show (OrderedSet a) where
    show (OS s r) = "{Set: " ++ show (Set.toList s) ++ ",\n "
                        ++ "Rel: " ++ show (Set.toList r) ++ "}" 




\end{code}


5BB3-C9E6

\subsection{Well-definedness}


Firstly we need to check given an object of type \texttt{OrderedSet a }, the relation is indeed a subset of the cartesian product of the carrier set, as the implementation of \texttt{OrderedSet} does accept cases which are not of this sort.

We shall call a relation $R$ "well-defined with respect to a set $P$" iff $R \subseteq P \times P$. We shall just say "well-defined" when the carrier set is clear form the context.

In order to check well-definedness of a relation we shall fisrt define the function \texttt{tuplesUnfold}, which ``unfolds" the tuples of a set of tuples, i.e. a relation.

The implementation follows this idea: given a relation $R$, we get the list of the first elements in all the tuples by mapping \texttt{fst} to all the elements of $R$. We do the same with \texttt{snd} in order to get the list of all the second elements of the tuples. We then join these lists and turn the resulting list into a set, which then gives us the set of elements of of the tuples of $R$.

\begin{code}
tuplesUnfold :: Ord a => Relation a -> Set.Set a
tuplesUnfold r = Set.fromList (Prelude.map fst (Set.toList r) ++ Prelude.map snd (Set.toList r))
\end{code}


Using \texttt{tuplesUnfold} we can now easily check for well-definedness. 

\begin{code}
checkRelationWellDef :: Ord a => OrderedSet a -> Bool
checkRelationWellDef (OS s r) = tuplesUnfold r `Set.isSubsetOf` s
\end{code}

Moreover if the relation is not well-defined relation, we might want to force it to be. The following function takes care of this by removing from a relation, set of elements in it, but not in the the carrier set.


\begin{code}
forceRelation :: Ord a => OrderedSet a -> OrderedSet a
forceRelation (OS s r) 
 | checkRelationWellDef (OS s r) = OS s r
 | otherwise = OS s ( r `Set.difference` Set.fromList (
    [(x,y) | (x,y) <- Set.toList r, x `Set.member` (tuplesUnfold r `Set.difference` s)] 
    ++ 
    [(x,y) | (x,y) <- Set.toList r, y  `Set.member` (tuplesUnfold r `Set.difference` s)]
                                                       )
                    )
\end{code}


\subsection{Checks and Closures}

Secondly, given an object of type \texttt{OrderedSet a }, the relation need not to be reflexive, anti-symmetric and transitive, as, again, the implementation of \texttt{OrderedSet} does accept cases which are not of this sort. Therefore we shall define checks and closures for our desired properties.

\subsubsection{Reflexivity} 

Both closures and checks are straightforwards, and well readable from the code implementation. We simply need add, or check the existance of, reflexive tuples.


\begin{code}
closureRefl :: Ord a => OrderedSet a -> OrderedSet a
closureRefl (OS s r) = OS s (r `Set.union` Set.fromList [(x,x)| x <- Set.toList s])

checkRefl :: Ord a =>  OrderedSet a -> Bool
checkRefl (OS s r) = all (\x ->  (x, x) `Set.member` r) s
\end{code}



\subsubsection{Transitivity}
The transitive closure requires a little more working: let $(P,R)$ be an object of type \texttt{OrderedSet a }. 

Firstly, we define the helper function \texttt{transPair}, to check if, given any $x,z$, there is a $y$ such that $x R y \wedge y R z$.

\begin{code}
transPair ::  Ord a => a -> a -> OrderedSet a -> Bool
transPair x z (OS s r)=  any (\y -> (x, y) `Set.member` r && (y,z) `Set.member` r) s
\end{code}

This allows us to know which ``one-step" transitive chains are currently missing. So, we add to the relation any pair which satisfies \texttt{transPair}, so that we have ``one-step" transitivity.

\begin{code}
transStep :: Ord a => OrderedSet a -> OrderedSet a
transStep (OS s r) = OS s (r `Set.union` Set.fromList [(x,z) | x <- Set.toList s, z <- Set.toList s, transPair x z (OS s r)])
\end{code}

Of course this won't suffice. Now that we have enlarged our relation, new pairs which satisfy \texttt{transPair} might arise. Therefore in order to fully close the relation under transitivity, for any transitive chain, we need to recursively apply the \texttt{transStep} function to our object \texttt{os} of type \texttt{OrderedSet a} until it reaces a fixed point, i.e. until \texttt{transStep os == os}. The code should be self explanatory for this:


\begin{code}
closureTrans :: Ord a => OrderedSet a -> OrderedSet a
closureTrans  currentSet = 
        let recursedSet = transStep currentSet
        in if recursedSet == currentSet
            then currentSet 
            else closureTrans recursedSet
\end{code}


Checking is again fairly straightforward. For any triple $(x,y,z)$, wherein $xRy$, $y'Rz$ and $y=y'$ (this is an implementation quirk, of course we're just checking $xRyRz$), we make sure that that also $xRz$.

\begin{code}
checkTrans :: Ord a => OrderedSet a -> Bool
checkTrans (OS _ r) = all (\(x, _, z) -> Set.member (x, z) r) [(x, y, z) | (x, y) <- Set.toList r, (y', z) <- Set.toList r, y == y']
\end{code}

\subsection{Forcing Antisymmetry}

Here some caveats must come in. Note that it is not possible to just "close" a relation under antisymmetry, as all the symmetric couples whose elements are different from each other need to be somehow eliminated. We're dealing with a ``reduction" rather than a closure. Furthermore, note that there is no unique way to obtain a reduction as we'd desire. Dually to a closure, we'd want a reduction of $R$ w.r.t a property $Q$ to be the greatest $R' \subseteq R$ for which $R'$ satisfies $Q$. But there is not such set! For a given symmetric pair $(x,y),(y,x) \in R$, the smallest change is removing one. But there's two ways to do so. So an anti-symmetric reduction is not unique.

There two ways, among others, stand out as elegant in forcing anti-symmetry regardless. The first consists in eliminating all symmetric pairs from the relation $R$, the second is to quotient of $P$ based on the clusters of symmetric pairs of $R$. We'll look at both in detail, and implement both as each has their advatages and disadvantages to them. One may be preferable to the other depending on the situation at hand.

Laslty, we shall again also define some functions that given an object of type \texttt{OrderedSet }, will check whether the relation is antisymmetric.

\subsubsection{First implementation}

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

A worry, is that, closing under transitivity and then anti-symmterically it could significantly reduce the numbers of pairs \emph{in the relation}: in particular every (non-reflexive) cycle is eliminated from the relation.


\paragraph{Second Implementation}
% to make Edo happy :)
Given any $(P,R)$ of type \texttt{OrderedSet a}, we can quotient the set $P$ on the symmetric points, i.e. merge the \emph{vertex} that see each other into a cluster. That is, for any $x \in P$ we define the equivalence class $[x]_s$ as the set $\{y \in P| y \neq x \wedge x R y \wedge y R x \}$.  


\begin{code}

quotientAntiSym :: Ord a => Set.Set a -> Relation a -> Set.Set a
quotientAntiSym s r = s `Set.difference` Set.fromList [x| (x,y) <- Set.toList r, (y,x) `Set.member` r, x /= y, y < x] 

forceAntiSymAlt :: Ord a => OrderedSet a -> OrderedSet a
forceAntiSymAlt (OS s r) = forceRelation $  OS (quotientAntiSym s r) r


\end{code}

Note that the condition \texttt{y < x} is a little trick we have to use as a means picking which elements to remove, and which to keep as the rappresentative of the equivalence class; leveraging the fact that we have \texttt{Ord} instance.

The advantage of this approach, is that it preserve logical properties (in particular, there is a $p$-morphism to the quotiented set). Since our topic at hand involves excatly defining logic over mathematical structures, this is certainly a nice feature.


On the other hand, this does change the carrier set: from $P$ we go to $P/s$, the quotient of $P$ under the equivalence relation based on symmetry \footnote{Note, due to Haskell's implementation, we cannot deem this as "the same set anyways", arguing it is just a matter of names referring to the same object. While in set theory, the set, $\{a,b \}$ as syntactically specified, may well be the same set as $\{a\}$, simply by virtue of $b$ semantically reffering to the same name as $a$ (i.e. $a=b$), in Haskell's \texttt{Data.Set}, named elements are the objects. This is evident from the fact that \texttt{Set.size} returns a value without us needing to specify what equalities hold between the objects.}


Furthermore, closing under transitivity and then anti-symmterically may shrink significatly the size of the \emph{carrier set}, in particular every cycle will collapse to a single point.



\subsubsection{Preservation of properties}

Since we'll want transtive, reflexive closures together with the anti-symmetric forcing, we need to make sure that our two implementation does not make us loose these properties in a relation. This is fairly obvius for the second implementation. But we want do need a small argument for the first implementation:

Reflexivity is still quick: by the very clause of anti-symmetry, only couples $(x,y)$ such that $x \neq y$ are removed. The non trivial preservation concerns transitivity: we shall therefore prove the following proposition.

%\textbf{Proposition}: \verb:forceAntiSymm $ transClosure:, where \verb:forceAntiSym: of a relation $R$, call it $R^{\dagger}$ is defined by: 
%

\begin{prop} 
Let $P$ be any set and $R \subseteq P \times P$ any relation defined on that set.  For any relation $R$, we define the antisymmetric forcing of $R$, $R^\dagger$ as:

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

   Now since $R^\dagger \subseteq R$ by definition, $x R y \wedge y R z$. So by the transitivity of $R$, we have $x R z$. Suppose now towards contradiction that $(x,z)\cancel{\in} R^\dagger$. Therefore $z R x$ and $z\neq x$. But then, since $y R z$, by transitivity of $R$, $y R x$. 

   Clearly, since we assumed $y R^\dagger z$ and $(x,z)\cancel{\in} R^\dagger$, $y \neq x$. But then, by definition of $R^\dagger$,  $(x,y)\cancel{\in} R^\dagger$, which is a contradiction to our assumpion. Therefore  $(x,z)\in R^\dagger$, which is what we had to show.
\end{proof}

Now since our implementation of \texttt{forceAntiSym} corresponds to our definition of $R^\dagger$, we can conclude that, given any \texttt{OS s r} of type \texttt{OrderedSet a}, in the result of \texttt{forceAntiSym  transClosure (OS s r)}, say \texttt{(OS s r')}, \texttt{r'} is transitive. 



Lastly, we define the following function in order to check for any given an object of type \texttt{OrderedSet a}, whether its relation is antisymmetric.

\begin{code}
checkAntiSym :: Ord a => OrderedSet a -> Bool
checkAntiSym  (OS _ r) = not (any (\(x,y) -> x /= y && (y, x) `Set.member` r) r)
\end{code}



\subsection{From ordered sets to posets}

Finally, given all the passages we have gone through in this section, we are able to define functions that given any object of type \texttt{OrderedSet a}, will transform it into a poset and check whether it is indeed a poset.

For the first task we take two approaches: in case everything "is behaving well", we can take the less controversial reflexive transitive closures, and obtain a poset closure without anti-symmetry caveats. The code is self explanatory here

\begin{code}
closurePoSet :: Ord a => OrderedSet a -> OrderedSet a
closurePoSet os
 | not (checkRelationWellDef os) = error "relation isn't well-defined"
 | not (checkAntiSym os)  = error "relation isn't anti-symmetric"
 | not (checkAntiSym $ closureTrans os) = error "relation looses anti-symmetry when transitively closed"
 | otherwise = closureTrans $ closureRefl os
\end{code}

In most cases however, we will need to engage with anti-symmetric forcing. Thus we have two poset forcing functions, using our two approaches \footnote{making sure to first take the transitive closure, and the the antisymmetric closure. We proved this preserve transitivity, whereas note that the opposite wouldn't do: considering for example $1 < 2 < 3 < 1$, this releation is already anti-symmteric, so our forcing function would leave it as is. But taking it's transitive closure clearly leaves us with symmetric couples. In general any cycle will result in such a problem.}


\begin{code}

makePoSet :: Ord a => OrderedSet a -> OrderedSet a
makePoSet  = closureRefl .  closureTrans 

forcePoSet :: Ord a => OrderedSet a -> OrderedSet a
forcePoSet  = closureRefl .  forceAntiSym .  closureTrans . forceRelation

-- forceRleation is reduntant here since it is inside forceAntiSymAlt
forcePosetAlt :: Ord a => OrderedSet a -> OrderedSet a
forcePosetAlt = closureRefl .  forceAntiSymAlt .  closureTrans

\end{code}


In order to check if an object of type \texttt{OrderedSet a} is indeed a poset, we define the following function:

\begin{code}
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



\subsection{Printing machinery}\label{sec:posetprinting}


 

This section is dedicated to the visualization of the structures we have discussed, namely posets, via what are called in mathematics \textit{Hasse diagrams} (a similar section will be present at the end of each section introducing a new mathematical structure the implementation will be similar in every case, but the function are displaced according to the module-dependencies).

In order to print all these structures, we import the \texttt{graphViz} library, with all its dependencies. If the reader wishes to visualize the graph, they should both install \textit{graphViz} and \textit{Xlib} on their machines.
If you (hypothetical reader, hello,) are running Ubuntu, you can run \textit{sudo apt-get install libx11-dev graphviz} on bash to install the required.


It should be noted that all the types we are working with will have to be an instance of the class \texttt{PrintDot} which comes with \texttt{graphViz}. This causes some difficulties when it comes to representation since Data.Set
does not have an original instance of PrintDot (Set a) and, since the Set module is imported, all homebrew instances we defined (although working) were "orphan" instances, and thus triggered a Wall warning. \newline 
In our specific case, the orphan instance would not be a problem per se, but to avoid the warning we decided to always run the isomorphism defned above (simplifyDL1, simplifyPS1) to obtain an isomorphic copy of our poset defined on the type INT. Other solution would have required rewriting every instance of "Set" as a Newtype, or rewriting the Set module in one of our own module and add the instance there. Both solutions seemed a bit excessive and thus we settled for the more economical one of always taking an isomorphic copy on INT. \newline 


As far as the style of the diagrams go, we stuck with the mathematical convention of having unlabeled nodes, since we are in any case interested in classes of posets "up to isomorphism". If the user wishes to label their node, this can easily be done modifying the GraphAttributes (those wrapped in square brackets) in "toGraphOrd". \newline 




Our primary concern is for the picture to be clear and readable. To this end we shall remove all transitive and reflexive edges which might occur in the structure. Since posets are part of the underlying structure of both lattices and priestley spaces,and its type is used to construct the types of the latter two, we define these helper function in this section.

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

\begin{itemize}

\item \texttt{toGraphRel'} uses \texttt{mapM\_} to transform an object \texttt{r}of type \texttt{Relation a} into a  monadic action, in particular an instance of of the type \texttt{Dot a}. 

\item \texttt{toGraphRel} uses \texttt{digraph'} to generate a directed graph out of an object of type \texttt{Dot a}. The carrier set of the object of type \texttt{OrderedSet a} will be the used to generate the points and the underlying relation of the object of type \texttt{OrderedSet a} will be the used to generate the edges of the graph. 
Notice that, although no Lattice has "isolated points", many Priestley space do which means that we could have nodes in the space which only have one reflexive arrow. If we only ran the second part of the function, and just mapped "-->" over the relations, we would either lose those isolated points, or we would ahve to print every time all the reflexive arrows of the graph. Thus it is important that we both print nodes out of the elements of the carrier set, and then construct edges using the relations. 
\end{itemize}

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


The following function actually outputs the picture of the ordered set. 

\begin{code}

showOrdSet ::(Ord a, Data.GraphViz.Printing.PrintDot a) => OrderedSet a -> IO ()
showOrdSet p = runGraphvizCanvas' (toGraphOrd $ fromReflTrans p) Xlib


\end{code}

