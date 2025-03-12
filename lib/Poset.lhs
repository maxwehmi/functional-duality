\section{Partially ordered sets}

\begin{code}
module Poset where

import qualified Data.Set as Set

newtype Relation a = Set (a,a) 
data OrderedSet a = OS (Set.Set a) (Relation a) 

checkPoset :: OrderedSet a -> Bool
checkPoset = undefined

closurePS :: OrderedSet a -> OrderedSet a
closurePS = undefined

\end{code}