----------------------------------------------------------------------
-- This Agda code is designed to accompany the thesis "Cubical models
-- of homotopy type theory - an internal approach" by Ian Orton.   
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module replace where 

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import hcomp-trans
open import quotients

----------------------------------------------------------------------
-- Lemmas about subst
----------------------------------------------------------------------
substcancel :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  (B : A → Set ℓ')
  {x y : A}
  (f : (a : A) → B a)
  (p : x ≡ y)
  {z : A}
  (q : x ≡ z)
  (r : y ≡ z)
  → ------------------------
  subst B q (f x) ≡ subst B r (f y)
substcancel _ _ refl refl refl = refl

substtrans :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  (B : A → Set ℓ')
  {x y z : A}
  (p : x ≡ y)
  (q : y ≡ z)
  (r : x ≡ z)
  (b : B x)
  → ------------------------
  subst B q (subst B p b)  ≡ subst B r b
substtrans _ refl refl refl _ = refl

substcong :
  {ℓ ℓ' : Level}
  {A A' : Set ℓ}
  (B : A' → Set ℓ')
  (f : A → A')
  {x y : A}
  (p : x ≡ y)
  (b : B (f x))
  → ------------------------
  subst (B ∘ f) p b ≡ subst B (cong f p) b
substcong _ _ refl _ = refl

substnatural :
  {A : Set}
  {B : A → Set}
  {C : Set → Set}
  (f : ∀{X} → X → C X)
  {x y : A}
  (p : x ≡ y)
  (b : B x)
  → ------------------------
  subst (C ∘ B) p (f b) ≡ f (subst B p b)
substnatural _ refl _ = refl


----------------------------------------------------------------------
-- Fibrant replacement of an object
----------------------------------------------------------------------
mutual
  -- FreeComps A is the result of freely adding compositions to A
  data FreeComps (A : Set) : Set where
    pure : A → FreeComps A
    comp :
      (e : OI)
      (φ : Cof)
      (f : [ φ ] → Int → Replace A)
      (a₀ : ⟦ a₀ ∈ Replace A ∣ (φ , f) ∙ ⟨ e ⟩ ↗ a₀ ⟧)
      → FreeComps A

  -- Replace A is FreeComps A where we quotient by the equation:
  --     comp e cofTrue f a₀ = f tt
  -- i.e. we ensure that compositions always extend their partial input
  Replace : Set → Set
  Replace A = FreeComps A / TotalComps

  -- TotalComps is the inductive family describing the necessary relation
  data TotalComps {A : Set} : FreeComps A → FreeComps A → Set where
    total :
      (e : OI)
      (φ : Cof)
      (f : [ φ ] → Int → Replace A)
      (a₀ : ⟦ a₀ ∈ Replace A ∣ (φ , f) ∙ ⟨ e ⟩ ↗ a₀ ⟧)
      (u : [ φ ])
      (a : FreeComps A)
      (_ : [ a ]/ TotalComps ≡ f u ⟨ ! e ⟩)
      → TotalComps a (comp e φ f a₀)

-- The inclusion of A in Replace A
ι : {A : Set} → A → Replace A
ι a = [ pure a ]/ TotalComps

-- Replace A is always a fibrant object
replaceIsHComp : (A : Set) → isHComp (Replace A)
replaceIsHComp A e φ f a₀ = [ comp e φ f a₀ ]/ TotalComps , ext where
  ext : (u : [ φ ]) → f u ⟨ ! e ⟩ ≡ [ comp e φ f a₀ ]/ TotalComps
  ext u = qind TotalComps
    (λ a → (_ : a ≡ f u ⟨ ! e ⟩) → a ≡ [ comp e φ f a₀ ]/ TotalComps)
    (λ a p → qeq TotalComps (total e φ f a₀ u a p))
    (λ _ _ _ → funext (λ _ → uip _ _))
    (f u ⟨ ! e ⟩) refl

-- We get a principle for eliminating into fibrant objects
replaceElim :
  (A : Set)
  (B : Set)(β : isHComp B)
  (f : A → B)
  → --------------------
  Replace A → B

-- We need to mark this as terminating, but this should (hopefully) be ok
{-# TERMINATING #-}
replaceElim A B β f = elim where
  elim : Replace A → B
  f' : (x : FreeComps A) → B
  resp : (x y : FreeComps A) (r : TotalComps x y) → subst (λ _ → B) (qeq TotalComps r) (f' x) ≡ f' y
  elim = qind TotalComps (λ _ → B) f' resp
  f' (pure x) = f x
  f' (comp e φ g (a₀ , ext)) = fst (β e φ (λ u i → elim (g u i))
    (elim a₀ , λ u → cong (qind TotalComps (λ _ → B) f' resp) (ext u)))
  resp a .(comp e φ g (a₀ , ext)) (total e φ g (a₀ , ext) u .a eq) =
    proof:
      subst (λ _ → B) (qeq TotalComps (total e φ g (a₀ , ext) u a eq)) (f' a)
        ≡[ substconst _ (qeq TotalComps (total e φ g (a₀ , ext) u a eq)) (f' a) ]≡
      f' a
        ≡[ cong elim eq ]≡
      elim (g u ⟨ ! e ⟩)
        ≡[ snd (β e φ (λ u i → elim (g u i))
             (elim a₀ , λ u → cong (qind TotalComps (λ _ → B) f' resp) (ext u))) u ]≡
      fst (β e φ (λ u i → elim (g u i))
        (elim a₀ , λ u → cong (qind TotalComps (λ _ → B) f' resp) (ext u)))
        ≡[ refl ]≡
      f' (comp e φ g (a₀ , ext))
    qed

-- Every f : A --> B factors as (replaceElim f) ∘ ι
--
--  A --------> B
--   \         ➚
--    \       /
--     \    /
--      ➘ /
--   Replace A
--
replaceElimFactors :
  (A : Set)
  (B : Set)(β : isHComp B)
  (f : A → B)
  → ---------------
  (replaceElim A B β f) ∘ ι ≡ f
replaceElimFactors A B β f = refl

-- A corresponding induction principle
replaceInd :
  (A : Set)
  (B : Replace A → Set)(β : isFib B)
  (f : (a : A) → B (ι a))
  → --------------------
  (x : Replace A) → B x
{-# TERMINATING #-}
replaceInd A B β f = elim where
  elim : (x : Replace A) → B x
  f' : (x : FreeComps A) → B ([ x ]/ TotalComps)
  resp : (x y : FreeComps A) (r : TotalComps x y) → subst B (qeq TotalComps r) (f' x) ≡ f' y
  elim = qind TotalComps B f' resp
  f' (pure x) = f x
  f' (comp e φ g (a₀ , ext)) =
    let α = λ e p → replaceIsHComp A e in
    let p = fill e α (λ _ → tt) φ g a₀ ext in
    let g' u i = subst B (appCong (fst (snd p) u)) (elim (g u i)) in
    let a₀' = subst B (symm (snd (snd p))) (elim a₀) in
    let ext' u = substcancel B elim (ext u) (appCong (fst (snd p) u)) (symm (snd (snd p))) in
    let a₁' = fst (β e (fst p) φ g' (a₀' , ext')) in
    subst B (fillAtEnd e α (λ _ → tt) φ g a₀ ext) a₁'
  resp a .(comp e φ g (a₀ , ext)) (total e φ g (a₀ , ext) u .a eq) =
    let α = λ e p → replaceIsHComp A e in
    let p = fill e α (λ _ → tt) φ g a₀ ext in
    let g' u i = subst B (appCong (fst (snd p) u)) (elim (g u i)) in
    let a₀' = subst B (symm (snd (snd p))) (elim a₀) in
    let ext' u = substcancel B elim (ext u) (appCong (fst (snd p) u)) (symm (snd (snd p))) in
    let a₁' = fst (β e (fst p) φ g' (a₀' , ext')) in
    proof:

      subst B (qeq TotalComps (total e φ g (a₀ , ext) u a eq)) (f' a)

          ≡[ substcancel B elim eq
               (qeq TotalComps (total e φ g (a₀ , ext) u a eq))
               (snd (α e (λ _ → tt) φ g (a₀ , ext)) u) ]≡

      subst B (snd (α e (λ _ → tt) φ g (a₀ , ext)) u) (elim (g u ⟨ ! e ⟩))

          ≡[ symm (substtrans B
                    (appCong (fst (snd p) u))
                    (fillAtEnd e α (λ _ → tt) φ g a₀ ext)
                    (snd (α e (λ _ → tt) φ g (a₀ , ext)) u)
                    (elim (g u ⟨ ! e ⟩))) ]≡

      subst B (fillAtEnd e α (λ _ → tt) φ g a₀ ext) (g' u ⟨ ! e ⟩)
   
          ≡[ cong (subst B (fillAtEnd e α (λ _ → tt) φ g a₀ ext))
                  (snd (β e (fst p) φ g' (a₀' , ext')) u) ]≡

      subst B (fillAtEnd e α (λ _ → tt) φ g a₀ ext) a₁'

          ≡[ refl ]≡

      f' (comp e φ g (a₀ , ext))

    qed


-- And a corresponding factorisation lemma
replaceIndFactors : (A : Set)(B : Replace A → Set)(β : isFib B)(f : (a : A) → B (ι a))
  → (λ a → replaceInd A B β f (ι a)) ≡ f
replaceIndFactors A B β f = refl


-- An induction principle for eliminating into fibrewise propositions
replaceInd' :
  (A : Set)
  (B : Replace A → Set)
  (is-prop : (a : Replace A)(b b' : B a) → b ≡ b')
  (pure : (a : A) → B ([ pure a ]/ TotalComps))
  (comp :
    (e : OI)
    (φ : Cof)
    (f : [ φ ] → Int → Replace A)
    (a₀ : ⟦ a₀ ∈ Replace A ∣ (φ , f) ∙ ⟨ e ⟩ ↗ a₀ ⟧)
    (bf : (u : [ φ ])(i : Int) → B (f u i))
    (b₀ : B (fst a₀))
    → --------------
    B ([ comp e φ f a₀ ]/ TotalComps)
  )
  → --------------------
  (x : Replace A) → B x
{-# TERMINATING #-}
replaceInd' A B is-prop f c = elim where
  elim : (x : Replace A) → B x
  f' : (x : FreeComps A) → B ([ x ]/ TotalComps)
  resp : (x y : FreeComps A) (r : TotalComps x y) → subst B (qeq TotalComps r) (f' x) ≡ f' y
  elim = qind TotalComps B f' resp
  f' (pure x) = f x
  f' (comp e φ g (a₀ , ext)) = c e φ g (a₀ , ext) (λ u i → elim (g u i)) (elim a₀)
  resp x y r = is-prop ([ y ]/ TotalComps) _ (f' y)

----------------------------------------------------------------------
-- Fibrant replacement is a DemiEndo, and therefore preserves
-- transport structure
----------------------------------------------------------------------
replaceEndo : DemiEndo
replaceEndo = endo Replace replaceFunc pres-id where

  replaceFunc : {A B : Set} → (A → B) → Replace A → Replace B
  replaceFunc {A} {B} f = replaceElim A (Replace B) (replaceIsHComp B) (ι ∘ f) 

  pres-id : (A : Set) → replaceFunc id ≡ id
  pres-id A = funext (replaceInd' A (λ x → replaceFunc id x ≡ x) (λ _ → uip) (λ _ → refl) comp-case) where
    comp-case : (e : OI) (φ : Cof) (f : [ φ ] → Int → Replace A)
      (a₀ : set (Replace A) (_↗_ ((φ , f) ∙ ⟨ e ⟩))) →
      ((u : [ φ ]) (i : Int) → replaceFunc id (f u i) ≡ f u i) →
      replaceFunc id (fst a₀) ≡ fst a₀ →
      replaceFunc id ([ comp e φ f a₀ ]/ TotalComps) ≡ [ comp e φ f a₀ ]/ TotalComps
    comp-case e φ f a₀ rec-f rec-a₀ = cong (λ fa₀ → [ comp e φ (fst fa₀) (snd fa₀) ]/ TotalComps)
      (ext-principle (funext (λ u → funext (rec-f u))) rec-a₀) where
      ext-principle :
        {f f' : [ φ ] → Int → Replace A}
        {a₀  : ⟦ a₀ ∈ Replace A ∣ (φ , f)  ∙ ⟨ e ⟩ ↗ a₀ ⟧}
        {a₀' : ⟦ a₀ ∈ Replace A ∣ (φ , f') ∙ ⟨ e ⟩ ↗ a₀ ⟧}
        → f ≡ f' → fst a₀ ≡ fst a₀'
        → (f , a₀) ≡ (f' , a₀')
      ext-principle {f} refl refl = Σext refl (incMono (_↗_ ((φ , f)  ∙ ⟨ e ⟩)) _ _ refl)

replaceIsTransp : {Γ : Set}{A : Γ → Set} → isTransp A → isTransp (Replace ∘ A)
replaceIsTransp {A = A} tA = TranspFibEndo replaceEndo A tA
