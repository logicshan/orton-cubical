----------------------------------------------------------------------
-- Note that this code is adapted from the code supporting Dan Licata,
-- Ian Orton, Andrew M. Pitts and Bas Spitters, "Internal Universes in
-- Models of Homotopy Type Theory", which is joint work with the other
-- listed authors.
----------------------------------------------------------------------

{-# OPTIONS --no-pattern-matching #-}

module no-go where

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations


{- 
We first show that if there is a universe that is weakly generic for
fibrations (for a given composition structure C), then families of
types that are fiberwise fibrant are fibrations.
-} 
record IntUniv : Set₂ where
  field
    U       : Set₁
    El      : Fib U
    code    : {Γ : Set}(Φ : Fib Γ) → Γ → U
    Elcode  : {Γ : Set}(Φ : Fib Γ) → reindex' El (code Φ) ≡ Φ

  fiberwise-fibrant-is-fibrant :
    (P : Int → Set)
    (π : (i : Int) → isFib (λ _ → P i))
    → ---------------------------------
    isFib P
  fiberwise-fibrant-is-fibrant P π = subst isFib u (snd Φ)
    where
    Φ : Fib Int
    Φ = reindex' El (λ i → code ((λ _ → P i) ,  π i) tt)

    u : fst Φ ≡ P
    u = funext (λ i → cong (λ x → fst x tt) (Elcode ((λ _ → P i) , π i)))

{-
 Next we show that if the composition structure has some reasonable
properties, there can be no such internal weakly generic universe.
-}
NoIntUniv : IntUniv → ∅
NoIntUniv iu = O≠I O=I
  where
  P : Int → Set
  P i = O ≡ i
    
  O≡ :
    (e : OI)
    (i : Int)
    → -----------------
    Comp e (λ _ → O ≡ i)
  O≡ _ _ _ _ a₀+ = (fst a₀+ , λ _ → uipImp) 

  c : Comp O' P
  c = IntUniv.fiberwise-fibrant-is-fibrant iu P (λ i e _ → O≡ e i) O' id

  O=I : O ≡ I
  O=I = fst (c cofFalse (λ ()) (refl , (λ ())))
