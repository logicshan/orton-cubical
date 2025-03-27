----------------------------------------------------------------------
-- Note that this code is adapted from the code supporting Dan Licata,
-- Ian Orton, Andrew M. Pitts and Bas Spitters, "Internal Universes in
-- Models of Homotopy Type Theory", which is joint work with the other
-- listed authors.
----------------------------------------------------------------------

{-# OPTIONS --rewriting --no-pattern-matching #-}

module Data.universe-core where

open import prelude
open import impredicative
open import interval
open import fibrations
open import tiny

-- In this file we define the following:
U  :{♭} Set₁
El :{♭} U → Set
el :{♭} isFib El
code : {a :{♭} Level}{Γ :{♭} Set a}(A :{♭} Fib Γ) → (Γ → U)

decode : ∀{a}{Γ : Set a} → (Γ → U) → Fib Γ
decode = reindex' (El , el)

Elcode : {a :{♭} Level}{Γ :{♭} Set a}(A :{♭} Fib Γ) → decode (code A) ≡ A
codeEl : {a :{♭} Level}{Γ :{♭} Set a}(a :{♭} Γ → U) → code (decode a) ≡ a

-- First, we slightly change the type of Comp so that
-- the argument e comes second
Comp' : (Int → Set) → Set
Comp' A = (e : OI) → Comp e A

-- The display function associated with Set l
Elt : Set₁
Elt = Σ A ∈ Set , A

pr₁ : Elt → Set
pr₁ = fst

-- We define U as the pullback:
abstract
  U = Σ X ∈ (Set × √ Elt) , √` pr₁ (snd X) ≡ R Comp' (fst X)

  π₁ : U → Set
  π₁ x = fst (fst x)

  π₂ : U → √ Elt
  π₂ x = snd (fst x)

  -- Transposing the pullback square across the adjunction ℘ ⊣ √
  -- gives a commutative square
  pr₁Lπ₂ :
    --------------------------
    pr₁ ∘ L π₂ ≡ Comp' ∘ ℘` π₁ 
  pr₁Lπ₂ = 
    proof:
      pr₁ ∘ L π₂
    ≡[ L√ pr₁ π₂ ]≡
      L (√` pr₁ ∘ π₂)
    ≡[ cong♭ L (funext snd) ]≡
      L (R Comp' ∘ π₁)
    ≡[ cong♭ L (symm (R℘ π₁ Comp')) ]≡
      Comp' ∘ ℘` π₁
    qed

  -- L π₂ is of the form ⟨ C ∘ ℘` π₁ , υ ⟩, where υ is:
  υ : isFib π₁
  υ e p = subst id (cong (λ f → f p) pr₁Lπ₂) (snd (L π₂ p)) e

  Lπ₂ :
    (p : ℘ U)
    → --------------------------
    L π₂ p ≡ (Comp' (℘` π₁ p) , (λ e → υ e p))
  Lπ₂ p = Σext (cong (λ f → f p) pr₁Lπ₂) refl

  -- Hence we get a fibration in Fib U:
  El = π₁
  el = υ

  -- Now we can construct the code function:
  code {l} {Γ} Aα x = ((A x , f x) , cong (λ f → f x) u)
    where
    A = fst Aα
    α = λ p e → snd Aα e p

    f : Γ → √ Elt
    f = R (λ p → Comp' (A ∘ p) , α p)

    u : √` pr₁ ∘ f ≡ R Comp' ∘ A
    u =
      proof:
        √` pr₁ ∘ f
      ≡[ cong♭ R (symm (L√ pr₁ f)) ]≡
        R (pr₁ ∘ (λ p → Comp' (A ∘ p) , α p))
      ≡[ R℘ A Comp' ]≡
        R Comp' ∘ A
      qed
    
  -- Next we construct Elcode
  Elcode {Γ = Γ} Φ = Σext refl υ∘℘code
   where
    υ∘℘`codeΦ : isFib (fst Φ)
    υ∘℘`codeΦ e p = υ e (℘` (code Φ) p)
    υ∘℘code : υ∘℘`codeΦ ≡ snd Φ
    υ∘℘code = funext (λ e → funext (λ p → cong (λ f → f e) (congsnd (v p) refl)))
      where
      congsnd :
        {l l' : Level}
        {A : Set l}
        {B : A → Set l'}
        {z z' : Σ A B}
        (p : z ≡ z')
        (q : fst z ≡ fst z')
        → ------------------------
        subst B q (snd z) ≡ snd z'
      congsnd {B = B} {z} {z'} p q =
        proof:
          subst B q (snd z)
        ≡[ cong (λ h → subst B h (snd z)) (uip q (cong fst p)) ]≡
          subst B (cong fst p) (snd z)
        ≡[ symm (cong (λ h → h (snd z)) (subst-cong-assoc B fst p)) ]≡
          subst (λ z₁ → B (fst z₁)) p (snd z)
        ≡[ congdep snd p ]≡
          snd z'
        qed

      A : Γ → Set
      A = fst Φ

      α : (p : Int → Γ) → Comp' (A ∘ p)
      α p e = snd Φ e p

      v :
        (p : ℘ Γ)
        → --------------------------------------------------
        (Comp' (℘` A p) , λ e → υ∘℘`codeΦ e p) ≡ (Comp' (℘` A p) , α p)
      v p =
        proof:
          (Comp' (℘` A p) , λ e → υ∘℘`codeΦ e p)
        ≡[ refl ]≡
          (Comp' (℘` π₁ (℘` (code Φ) p)) , λ e → υ e (℘` (code Φ) p))
        ≡[ symm (Lπ₂ (℘`(code Φ) p)) ]≡
          L π₂ (℘`(code Φ) p)
        ≡[ cong (λ f → f p) (L℘ π₂ (code Φ)) ]≡
          (Comp' (℘` A p) , α p)
        qed

  -- The code function is natural
  code[] :
    {l1 l2 :{♭} Level}
    {Γ :{♭} Set l1}
    {Δ :{♭} Set l2}
    (Φ :{♭} Fib Γ)
    (γ :{♭} Δ → Γ)
    (x : Δ)
    → -----------------------------
    code (reindex' Φ γ) x ≡ code Φ (γ x)
  code[] {Γ} Aα γ x = Σext (Σext refl (e x)) uipImp
    where
    A = fst Aα
    α = snd Aα
    RC℘` : {l' :{♭} Level}{Γ :{♭} Set l'}(_ :{♭} Fib Γ) → Γ → √ Elt
    RC℘` Bβ = R (λ p → Comp' (fst Bβ ∘ p) , λ e → snd Bβ e p)
    e :
      (x : _ )
      → ---------------------------------------------------------
      RC℘` (reindex' Aα γ) x ≡ RC℘` Aα (γ x)
    e x = cong♭ (λ f → f x) (R℘ γ (λ p → Comp' (A ∘ p) , λ e → α e p))

  -- Next we construct codeEl
  codeEl≡id : (X : U) → code (El , el) X ≡ X
  codeEl≡id X = Σext (cong (λ f → (π₁ X , f X)) u) uipImp
    where
    u : R (λ p → Comp' (π₁ ∘ p) , λ e → υ e p) ≡ π₂
    u = cong♭ R (symm (funext Lπ₂))

  codeEl γ = funext (λ x →
    proof:
      code (reindex' (El , el) γ) x
    ≡[ code[] (El , el) γ x  ]≡
      code (El , el) (γ x)
    ≡[ codeEl≡id (γ x) ]≡
      γ x
    qed)

