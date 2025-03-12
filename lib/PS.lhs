\section{Priestley Spaces}

\begin{code}
module PriestleySpaces where

import qualified Data.Set as Set 

import Poset

data TopoSpace a = TS {
    set :: Set.Set a,
    topology :: Set.Set (Set.Set a)
}

data PriestleySpace a = PS {
    topospace :: TopoSpace a,
    relation :: OrderedSet a
}

checkPriestley :: PriestleySpace a -> Bool
checkPriestley = undefined 



\end{code}