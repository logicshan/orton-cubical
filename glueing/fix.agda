----------------------------------------------------------------------
-- This Agda code is designed to accompany the thesis "Cubical models
-- of homotopy type theory - an internal approach" by Ian Orton.         
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module glueing.fix where 

open import glueing.core
open import glueing.strict

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import equivs
open import Data.paths
open import Data.products
open import realignment

----------------------------------------------------------------------
-- Fixing the composition
----------------------------------------------------------------------

abstract
 FibSGlueid :
  {Φ : Int → Cof}
  {A : res Int Φ → Set}
  {B : Int → Set}
  (f : (x : Int)(u : [ Φ x ]) → A (x , u) → B x)
  (equiv : (x : Int)(v : [ Φ x ]) → Equiv' (f x v))
  → ---------------
  isFib A → isFib B → isFib (SGlue Φ A B f)
 FibSGlueid {Φ} {A} {B} f equiv α β =
  realign {Φ = Φ} {SGlue Φ A B f} (subst isFib A≡Gfst α) (FibSGlueId' {Φ = Φ} f equiv α β) where
    A≡Gfst : A ≡ (SGlue Φ A B f) ∘ fst
    A≡Gfst = symm (funext (λ{ (x , u) → strictness Φ A B f x u}))


FibSGlue-open :
  {a : Level}
  {Γ : Set a}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → ---------------
  isFib A → isFib B → isFib (SGlue Φ A B f)
FibSGlue-open {a} {Γ} {Φ} {A} {B} f equiv α β e p = FibSGlueid (λ x → f (p x)) (λ x → equiv (p x)) (reindex A α (λ{ (i , u) → (p i , u)})) (reindex B β p) e id

FibSGlue :
  {a : Level}
  {Γ : Set a}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → ---------------
  isFib A → isFib B → isFib (SGlue Φ A B f)
abstract
 FibSGlue {a} {Γ} {Φ} {A} {B} f equiv α β e p = FibSGlue-open {a} {Γ} {Φ} {A} {B} f equiv α β e p

FibSGlue-unfold :
  {a : Level}
  {Γ : Set a}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  → ---------------
  FibSGlue {a} {Γ} {Φ} {A} {B} ≡ FibSGlue-open {a} {Γ} {Φ} {A} {B}
abstract
 FibSGlue-unfold = refl

subst-reindex :
  {a b : Level}
  {Δ : Set a}
  {Γ : Set b}
  {A A' : Γ → Set}
  (f : Δ → Γ)
  (α : isFib A)
  (eq : A ≡ A')
  (eq' : A ∘ f ≡ A' ∘ f)
  → ---------------
  subst isFib eq' (reindex A α f) ≡ reindex A' (subst isFib eq α) f
subst-reindex _ _ refl refl = refl

reindex-FibSGlue :
  {a : Level}
  {Γ : Set a}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  (α : isFib A)
  (β : isFib B)
  (e : OI)
  (p : Int → res Γ Φ)
  → ---------------
  reindex (SGlue Φ A B f) (FibSGlue {Φ = Φ} f equiv α β) fst e p ≡ subst isFib (symm (funext (λ{ (x , u) → strictness Φ A B f x u}))) α e p
abstract
 reindex-FibSGlue {ℓ} {Γ} {Φ} {A} {B} f equiv α β e p =
  proof:
     reindex (SGlue Φ A B f) (FibSGlue {Φ = Φ} f equiv α β) fst e p
   ≡[ refl ]≡
     realign α'' (FibSGlueId' {Φ = Φ'} f' equiv' α' β') e id
   ≡[ cong (λ α'' → realign α'' (FibSGlueId' {Φ = Φ'} f' equiv' α' β') e id) natural  ]≡
     realign (reindex (SGlue Φ A B f ∘ fst) α''' ρ) (FibSGlueId' {Φ = Φ'} f' equiv' α' β') e id
   ≡[ refl  ]≡
     realign {Φ = Φ} {SGlue Φ A B f} α''' (FibSGlue'-open {Φ = Φ} f equiv α β) e (fst ∘ p)
   ≡[ cong (λ f → f e p) (isFixed {Φ = Φ} {SGlue Φ A B f} α''' (FibSGlue'-open {Φ = Φ} f equiv α β))  ]≡
     α''' e p
   ≡[ refl  ]≡
     subst isFib (symm (funext (λ{ (x , u) → strictness Φ A B f x u}))) α e p
  qed
   where
    Φ' = Φ ∘ fst ∘ p
    A' = A ∘ ((fst ∘ p) ×id)
    B' = B ∘ fst ∘ p
    f' = λ x → f (fst (p x))
    equiv' = (λ x → equiv (fst (p x)))
    β' = reindex B β (fst ∘ p)
    ρ = (fst ∘ p) ×id
    eq=' = symm (funext (λ{ (x , u) → strictness Φ' A' B' f' x u}))
    eq= = symm (funext (λ{ (x , u) → strictness Φ A B f x u}))
    α' : isFib (A ∘ ρ)
    α' = (reindex A α ρ)
    α'' : isFib (SGlue Φ' A' B' f' ∘ fst)
    α'' = subst isFib eq=' α'
    α''' : isFib (SGlue Φ A B f ∘ fst)
    α''' = subst isFib eq= α
    natural : α'' ≡ reindex (SGlue Φ A B f ∘ fst) α''' ρ
    natural = subst-reindex ρ α eq= eq='

SGlueFib :
  ∀{ℓ}{Γ : Set ℓ}
  (Φ : Γ → Cof)
  (A : Fib (res Γ Φ))
  (B : Fib Γ)
  (f : (x : Γ)(u : [ Φ x ]) → fst A (x , u) → fst B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → --------------
  Fib Γ
SGlueFib {_} {Γ} Φ (A , α) (B , β) f equiv = SGlue Φ A B f , FibSGlue {Γ = Γ} {Φ} {A} {B} f equiv α β

abstract
 SGlueReindex :
  ∀{ℓ}{Γ : Set ℓ}
  (Φ : Γ → Cof)
  (A : Fib (res Γ Φ))
  (B : Fib Γ)
  (f : (x : Γ)(u : [ Φ x ]) → fst A (x , u) → fst B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → --------------
  reindex' (SGlueFib Φ A B f equiv) fst ≡ A
 SGlueReindex {ℓ} {Γ} Φ (A , α) (B , β) f equiv =
   Σext (funext (λ{ (x , u) → strictness Φ A B f x u }))
     (trans (substsubst {p = symm Gfst≡A} {q = Gfst≡A} α) (cong (subst isFib Gfst≡A) (funext λ e → funext λ p → reindex-FibSGlue f equiv α β e p)))
   where
     Gfst≡A : (SGlue Φ A B f) ∘ fst ≡ A
     Gfst≡A = funext (λ{ (x , u) → strictness Φ A B f x u})
     substsubst : {x y : (res Γ Φ) → Set}{p : x ≡ y}{q : y ≡ x}(z : isFib x) → subst isFib q (subst isFib p z) ≡ z
     substsubst {p = refl} {q = refl} _ = refl

abstract
 SGlueReindex' :
  {a : Level}
  {Γ : Set a}
  (Φ : Γ → Cof)
  (A : Fib (res Γ Φ))
  (B : Fib Γ)
  (f : (x : Γ)(u : [ Φ x ]) → fst A (x , u) → fst B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  (u : (x : Γ) → [ Φ x ]) 
  → --------------
  SGlueFib Φ A B f equiv ≡ reindex' A (λ x → x , u x)
 SGlueReindex' Φ A B f equiv u = cong (λ A → reindex' A (λ x → x , u x)) (SGlueReindex Φ A B f equiv)

 uaβhelper :
  ∀{ℓ}{Γ : Set ℓ}
  (A : Fib (res (Γ × Int) i=OI))
  (B : Fib (Γ × Int))
  (f : (x : Γ × Int)(u : [ i=OI x ]) → fst A (x , u) → fst B x)
  (equiv : (x : Γ × Int)(v : [ i=OI x ]) → Equiv' (f x v))
  (x : Γ)
  → --------------
  FibSGlue {Φ = i=OI} f equiv (snd A) (snd B) O' < x ,id>
    ≡ FibSGlue' {Φ = i=OI} f equiv (snd A) (snd B) O' < x ,id>
 uaβhelper (A , α) (B , β) f equiv x =
  proof:
      FibSGlue {Φ = i=OI} f equiv α β O' < x ,id>
    ≡[ refl ]≡
      context (subst isFib eq=' (reindex A α (< x ,id> ×id)))
    ≡[ cong context (subst-reindex (< x ,id> ×id) α eq= eq=') ]≡
      context (reindex (SGlue i=OI A B f ∘ fst) (subst isFib eq= α) (< x ,id> ×id))
    ≡[ refl ]≡
      realign {Φ = i=OI} (subst isFib eq= α) (FibSGlue'-open {Φ = i=OI} f equiv α β) O' < x ,id>
    ≡[ sameOtherwise {Φ = i=OI} {SGlue i=OI A B f} (subst isFib eq= α) (FibSGlue'-open {Φ = i=OI} f equiv α β) O' < x ,id> ¬∀i=OI ]≡
      FibSGlue'-open {Φ = i=OI} f equiv α β O' < x ,id>
    ≡[ cong (λ F → F f equiv α β O' < x ,id>) (FibSGlue'-unfold {Φ = i=OI}) ]≡
      FibSGlue' {Φ = i=OI} f equiv α β O' < x ,id>
  qed
    where
      SGlueOI : Int → Set
      SGlueOI = SGlue (i=OI ∘ < x ,id>) (A ∘ (< x ,id> ×id)) (B ∘ < x ,id>) (λ i → f (x , i))
      context : isFib (SGlueOI ∘ fst) → _
      context γ =
        realign {Φ = i=OI ∘ < x ,id>} {SGlueOI} γ
          (FibSGlue'-open {Φ = i=OI ∘ < x ,id>} (λ i → f (x , i)) (λ i → equiv (x , i))
            (reindex A α (< x ,id> ×id)) (reindex B β < x ,id>))
          O'
          id
      eq= : A ≡ SGlue i=OI A B f ∘ fst
      eq= = (symm (funext λ{ (x , u) → strictness i=OI A B f x u }))
      eq=' : A ∘ (< x ,id> ×id) ≡ SGlue (i=OI ∘ < x ,id>) (A ∘ (< x ,id> ×id)) (B ∘ < x ,id>) (λ i → f (x , i)) ∘ fst
      eq=' = (symm (funext λ{ (i , u) → strictness (i=OI ∘ < x ,id>) (A ∘ (< x ,id> ×id)) (B ∘ < x ,id>) (λ i → f (x , i)) i u }))
      ¬∀i=OI : [ ∀i (λ i → (i ≈O) ∨ (i ≈I)) ] → ∅
      ¬∀i=OI ∀i=OI = O≠I (subst prf O≈O≡O≈I refl) where
        cases : {i : Int} → (i ≡ O) ⊎ (i ≡ I) → prf ((O ≈ i) or ¬ (O ≈ i))
        cases (inl i=O) = ∣ inl (symm i=O) ∣
        cases (inr i=I) = ∣ inr (λ O=i → ∅-elim (O≠I (trans i=I O=i))) ∣
        O≈O≡O≈I : (O ≈ O) ≡ (O ≈ I)
        O≈O≡O≈I = cntd' (λ i → O ≈ i) (λ i → ∥∥-elim cases (λ _ _ → eq ((O ≈ i) or ¬ (O ≈ i))) (∀i=OI i)) O
