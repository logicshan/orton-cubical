----------------------------------------------------------------------
-- This Agda code is designed to accompany the thesis "Cubical models
-- of homotopy type theory - an internal approach" by Ian Orton.
--
-- This file contains the decomposition of fibration structure into
-- homogeneous fibration and transport structres. This observation
-- comes from "On Higher Inductive Types in Cubical Type Theory" by
-- Coquand, Huber and Mortberg.
--
-- The definition of a DemiEndo and its use in showing that definitions
-- preserve transport structure is due to Evan Cavallo.
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module hcomp-trans where 

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations

----------------------------------------------------------------------
-- Homogeneous fibration and transport structures
----------------------------------------------------------------------
isHComp : Set → Set
isHComp A = (e : OI)(φ : Cof)(f : [ φ ] → Int → A) →
  ⟦ a₀ ∈ A ∣ (φ , f) ∙ ⟨ e ⟩  ↗ a₀ ⟧ → ⟦ a₁ ∈ A ∣ (φ , f) ∙ ⟨ ! e ⟩ ↗ a₁ ⟧

isHFib : {Γ : Set}(A : Γ → Set) → Set
isHFib {Γ} A = (x : Γ) → isHComp (A x)

isTransp : {Γ : Set}(A : Γ → Set) → Set
isTransp {Γ} A = (e : OI)(p : Int → Γ)(φ : ⟦ φ ∈ Cof ∣ fst φ ⊃ (All i ∈ Int , p i ≈ p ⟨ e ⟩) ⟧)
  (a₀ : A (p ⟨ e ⟩)) → ⟦ a₁ ∈ A (p ⟨ ! e ⟩) ∣ (fst φ , (λ u → subst A (symm (snd φ u ⟨ ! e ⟩)) a₀)) ↗ a₁ ⟧

----------------------------------------------------------------------
-- All constant families have transport structure
----------------------------------------------------------------------
constTransp : {Γ : Set}(A : Set) → isTransp {Γ} (λ _ → A)
constTransp A e p φ a₀ = a₀ , λ u → substconst A (symm (snd φ u ⟨ ! e ⟩)) a₀

----------------------------------------------------------------------
-- Converting between the original isFib structure and these two new
-- structures
----------------------------------------------------------------------
fromFib : {Γ : Set}{A : Γ → Set} → isFib A → isHFib A × isTransp A
fromFib {Γ} {A} α = hA , tA where
  hA : isHFib A
  hA x e φ f a₀ = α e (λ _ → x) φ f a₀
  tA : isTransp A
  tA e p φ a₀ =
    α e p (fst φ)
      (λ u i → subst A (symm (snd φ u i)) a₀)
      (a₀ , (λ u → subst-anything (symm (snd φ u ⟨ e ⟩ ))))
   where
    subst-anything : ∀{x a₀}(p : x ≡ x) → subst A p a₀ ≡ a₀
    subst-anything refl = refl


toFib : {Γ : Set}{A : Γ → Set} → isHFib A → isTransp A → isFib A
toFib {Γ} {A} hA tA e p φ f a₀ =
  -- This is the answer given in the thesis:
  let ans = hA (p ⟨ ! e ⟩) e φ f' (fst a₀' , ext) in
  -- But Agda needs some convincing:
  fst ans , (λ u → trans (snd ans u) (snd (f'pre u ⟨ ! e ⟩) refl))
 where
  match : ∀{i}(x : i ≡ ⟨ ! e ⟩) (x₁ : Int) → p (cnx (! e) i x₁) ≡ p i
  match refl j = refl
  f'pre : (u : [ φ ])(i : Int) →
    ⟦ a₁ ∈ A (p ⟨ ! e ⟩) ∣ (i ≈OI (! e) , (λ u' → subst A (symm (match u' ⟨ ! e ⟩)) (f u i))) ↗ a₁ ⟧
  f'pre u i = tA e (λ j → p (cnx (! e) i j)) (i ≈OI ! e , match) (f u i)
  f' : [ φ ] → Int → A (p ⟨ ! e ⟩)
  f' u i = fst (f'pre u i)
  a₀' : ⟦ a₀' ∈ A (p ⟨ ! e ⟩) ∣ (cofFalse , _) ↗ a₀' ⟧
  a₀' = tA e p (cofFalse , (λ ())) (fst a₀)
  ext : prf ((φ , f') ∙ ⟨ e ⟩ ↗ fst a₀')
  ext u = cong₂ (λ ψ a → fst (tA e p ψ a))
    (Σext (cofEq (propext e≠!e (λ ()))) (funext (λ ()))) (snd a₀ u)

 
----------------------------------------------------------------------
-- Transport fibrations are closed under post-composition with any
-- endofunctor. (Actually, we don't even need the "functor" to
-- preserve composition). This observation is due to Evan Cavallo.
----------------------------------------------------------------------

record DemiEndo : Set (lsuc lzero) where
  constructor endo
  field
    obf : Set → Set
    homf : {A B : Set} → (A → B) → (obf A → obf B)
    presid : (A : Set) → homf (λ (a : A) → a) ≡ (λ a → a)

open DemiEndo public

endosubst : ∀ {ℓ}{Γ : Set ℓ} (F : DemiEndo) (A : Γ → Set) {x y : Γ} (p : x ≡ y)
  → homf F (subst A p) ≡ subst (obf F ∘ A) p
endosubst F A refl = presid F (A _)

TranspFibEndo : {Γ : Set} (F : DemiEndo) (A : Γ → Set) → isTransp A → isTransp (obf F ∘ A)
TranspFibEndo F A tα e p (φ , cst) y₁ =
  transpMap y₁ , λ u → cong (λ g → g y₁) (extendsMap u)
  where
  transpMap : (obf F ∘ A ∘ p) ⟨ e ⟩ → (obf F ∘ A ∘ p) ⟨ ! e ⟩
  transpMap = homf F (λ x₁ → fst (tα e p (φ , cst) x₁))

  extendsMap : prf ((φ , λ u → subst (obf F ∘ A) (symm (cst u ⟨ ! e ⟩))) ↗ transpMap)
  extendsMap u =
    trans
      (cong (homf F) (funext (λ x₁ → snd (tα e p (φ , cst) x₁) u)))
      (symm (endosubst F A (symm (cst u ⟨ ! e ⟩))))
