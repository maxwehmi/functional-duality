\section{Disributive Lattices}

\begin{code}
module DistributiveLattices where

import Poset
import qualified Data.Set as Set 

data Lattice a = L {
    carrier :: OrderedSet a,
    meet :: a -> a -> a,
    join :: a -> a -> a 
    }

checkBoundedness :: Lattice a -> Bool
checkBoundedness = undefined

checkDistributivity :: Lattice a -> Bool
checkDistributivity = undefined

checkClosedMeetJoin :: Lattice a -> Bool
checkClosedMeetJoin = undefined

checkLattice :: Lattice a -> Bool
checkLattice = undefined 

makeLattice :: OrderedSet a -> Lattice a 
makeLattice = undefined




\end{code}