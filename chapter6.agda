----------------------------------------------------------------------
-- This Agda code is designed to accompany the thesis "Cubical models
-- of homotopy type theory - an internal approach" by Ian Orton.
----------------------------------------------------------------------

module chapter6 where

----------------------------------------------------------------------
-- Firstly we have the syntactic argument which decomposes univalence
-- into the five axioms. This argument is happening in the type theory
-- that we are trying to interpret (MLTT without Axiom K/UIP) rather
-- than in the internal type theory.
----------------------------------------------------------------------
import Chapter6Syntactic.Decomp

----------------------------------------------------------------------
-- The subsequent code should be interpret as happening inside the
-- internal type theory:
--
-- The axioms and constructions for stricfying objects and fibrations
----------------------------------------------------------------------
import strictness-axioms
import strictify

----------------------------------------------------------------------
-- Realigning fibration structures
----------------------------------------------------------------------
import realignment

----------------------------------------------------------------------
-- The main theorems from the chapter -- verifying axioms (1)-(5)
----------------------------------------------------------------------
import decomp
