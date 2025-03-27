----------------------------------------------------------------------
-- This Agda code is designed to accompany the thesis "Cubical models
-- of homotopy type theory - an internal approach" by Ian Orton.   
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module quotients where 

open import prelude
open import interval using () -- Just using the {-# BUILTIN REWRITE _≡_ #-} pragma

----------------------------------------------------------------------
-- Quoitents
----------------------------------------------------------------------
infix 6 _/_ [_]/_
postulate
  -- quotient formation
  _/_ : {ℓ ℓ' : Level}(A : Set ℓ)(R : A → A → Set ℓ') → Set (ℓ ⊔ ℓ')
  
  -- quotient introduction
  [_]/_ : {ℓ ℓ' : Level}{A : Set ℓ} → A → (R : A → A → Set ℓ') → A / R

  -- generating equalities
  qeq :
    {ℓ ℓ' : Level}
    {A : Set ℓ}
    {x y : A}
    (R : A → A → Set ℓ')
    (r : R x y)
    → ------------------
    [ x ]/ R ≡ [ y ]/ R

  -- quotient induction
  qind :
    {ℓ ℓ' ℓ'' : Level}
    {A : Set ℓ}
    (R : A → A → Set ℓ')
    (B : A / R → Set ℓ'')
    (f : (x : A) → B ([ x ]/ R))
    (e : (x y : A)(r : R x y) → subst B (qeq R r) (f x) ≡ f y)
    → --------------------------------------------------------
    (y : A / R) → B y

  -- quotient computation
  qind-comp :
    {ℓ ℓ' ℓ'' : Level}
    {A : Set ℓ}
    (R : A → A → Set ℓ')
    (B : A / R → Set ℓ'')
    (f : (x : A) → B ([ x ]/ R))
    (e : (x y : A)(r : R x y) → subst B (qeq R r) (f x) ≡ f y)
    (x : A)
    → --------------------------------------------------------
    qind R B f e ([ x ]/ R) ≡ f x

{-# REWRITE qind-comp   #-}

-- N.B. Not sure if these are correct:
{-# POLARITY _/_ * * ++ ++ #-}
{-# POLARITY [_]/_ * * _ * _ #-}
