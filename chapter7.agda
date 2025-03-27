----------------------------------------------------------------------
-- This Agda code is designed to accompany the thesis "Cubical models
-- of homotopy type theory - an internal approach" by Ian Orton.
--
-- Note that parts of this code (the first three modules) are adapted
-- from the code supporting Dan Licata, Ian Orton, Andrew M. Pitts
-- and Bas Spitters, "Internal Universes in Models of Homotopy Type
-- Theory", which is joint work with the other listed authors.
----------------------------------------------------------------------

module chapter7 where

----------------------------------------------------------------------
-- The postulates about the interval being tiny. Stated as the
-- existence of a right adjoint to the path functor, Int → (_)
----------------------------------------------------------------------
import tiny

----------------------------------------------------------------------
-- The "no-go" theorem for internal universes
----------------------------------------------------------------------
import no-go

----------------------------------------------------------------------
-- The construction of the universe
----------------------------------------------------------------------
import Data.universe-core

----------------------------------------------------------------------
-- Showing that the universe is closed under various type former, and
-- defining the map ua from equivalences to paths
----------------------------------------------------------------------
import Data.universe
