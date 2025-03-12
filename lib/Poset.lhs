\section{Partially ordered sets}

\begin{code}
module Poset where

import qualified Data.Set as Set

type Relation a = Set.Set (a,a) 
data OrderedSet a = OS {set :: Set.Set a,
                         rel :: Relation a} 

-- I have changed the Relation a from "newtype ... Set .." to "type ... Set.Set .." as Relation a is a type synonim and it was giving me problems with the typechecking in other files. 

-- I have changed the data type of OrderedSet a, in order to have functions to retreive the underlying set and the underlying relation of the OrderedSet.


checkPoset :: OrderedSet a -> Bool
checkPoset = undefined

closurePS :: OrderedSet a -> OrderedSet a
closurePS = undefined

\end{code}