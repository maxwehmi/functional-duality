\section{Priestley Spaces}

\begin{code}
module PriestleySpaces where

import Data.Set (Set, toList, fromList)

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
-- i'll write this in the most retarded way possible for now, also, I figured, this alwaysholds in the finite case anyway
--checkPSA (PS space top order ) = all (\ pair -> 
   -- implies (notElem pair order) (any (\ open -> elem (fst pair) open 
  --  && notElem (snd pair) open) (clopup top) )) $ allpairs space 




allpairs :: Set a -> [(a,a)]
allpairs space = [(x,y) | x <- toList space ,y <- toList space ]
-- extracts the set of all orderedpairs form the carrier set (could also be done differently)
implies :: Bool -> Bool -> Bool
implies x y = not x || y
--usual implication shorthand 
\end{code}