----------------------------------------------------------------------
-- This Agda code is designed to accompany the thesis "Cubical models
-- of homotopy type theory - an internal approach" by Ian Orton.
--
-- The material before Chapter 7 can be checked with the standard
-- version of Agda. However, the material in Chapter 7 must be checked
-- with the branch of agda with support for the flat modality, called
-- agda-flat.
--
-- This file has been checked with the following versions of Agda:
--   - Agda 2.5.4 (with chapter7 commented out) in approx 1 min
--   - Agda-flat 2.6.0-1f943c9 (the whole file) in approx 3 mins
----------------------------------------------------------------------

module root where

----------------------------------------------------------------------
-- Introducing basics (e.g. equality, products etc)
----------------------------------------------------------------------
import prelude

----------------------------------------------------------------------
-- Impredicative universe of propositions and logic
----------------------------------------------------------------------
import impredicative

----------------------------------------------------------------------
-- Chapter 5: The interval, cofibrant propositons, fibrations, type
-- formers, equivalences, glueing and the univalence axiom
----------------------------------------------------------------------
import chapter5

----------------------------------------------------------------------
-- Chapter 6: Decomposing the univalence axiom into 5 simpler axioms
-- and then verifying those in the internal type theory
----------------------------------------------------------------------
import chapter6

----------------------------------------------------------------------
-- Chapter 7: Constructing a universe of fibrations from the fact that
-- the interval is "tiny". Also showing that the universe is closed
-- under type formers and defining the map ua on the universe.
----------------------------------------------------------------------
import chapter7

----------------------------------------------------------------------
-- Future work: Constructing a fibrewise fibrant replacement using (a
-- simulated form of) quoitent inductive types. Construction of the
-- circle, 𝕊¹, and the suspension, Σ A.
----------------------------------------------------------------------
import hits
