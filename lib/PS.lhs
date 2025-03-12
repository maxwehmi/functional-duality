\section{Priestley Spaces}

\begin{code}
module PriestleySpaces where

import Data.Set (Set)

import Poset

data TopoSpace a = TS {
    setTS :: Set a,
    topologyTS :: Set (Set a)
}

data PriestleySpace a = PS {
    setPS :: Set a,
    topologyPS :: Set (Set a),
    relationPS :: Relation a
}

checkTopology :: TopoSpace a -> Bool
checkTopology = undefined
-- use library from other topology project

getTopoSpace :: PriestleySpace a -> TopoSpace a
getTopoSpace p = TS (setPS p) (topologyPS p)

getOrderedSet :: PriestleySpace a -> OrderedSet a
getOrderedSet p = OS (setPS p) (relationPS p)

checkPriestley :: PriestleySpace a -> Bool
checkPriestley p = checkTopology (getTopoSpace p) && checkPoset (getOrderedSet p) && checkPSA p 
-- since we are only working with finite spaces, they are always compact

checkPSA :: PriestleySpace a -> Bool
checkPSA = undefined



\end{code}