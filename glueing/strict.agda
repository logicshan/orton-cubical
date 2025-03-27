----------------------------------------------------------------------
-- This Agda code is designed to accompany the thesis "Cubical models
-- of homotopy type theory - an internal approach" by Ian Orton.      
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module glueing.strict where 

open import glueing.core

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import equivs
open import Data.paths
open import Data.products
open import strictness-axioms

----------------------------------------------------------------------
-- Strict glueing
----------------------------------------------------------------------
SGlue' :
  (Φ : Cof)
  (A : [ Φ ] → Set)
  (B : Set)
  (f : (u : [ Φ ]) → A u → B)
  → ---------------
  Set

private
 fIso' :
  (Φ : Cof)
  {A : [ Φ ] → Set}
  {B : Set}
  (w : (u : [ Φ ]) → A u → B)
  → ---------------
  (u : [ Φ ]) → A u ≅' Glue' Φ A B w
abstract
 fIso' Φ {A} {B} w u = iso where
  open _≅'_
  prfIr : {a : A u} → subst A (equ (fst Φ) u u) a ≡ a
  prfIr {a} =
    let switch = uip (equ (fst Φ) u u) refl in
    cong (λ p → subst A p a) switch
  iso : A u ≅' Glue' Φ A B w
  to iso a = glue-ptwise {Φ = Φ} w u a
  from iso (a , _ , _) = a u
  inv₁ iso = funext (λ a → prfIr)
  inv₂ iso = funext fg≡id where
    parEq : {a a' : (u : [ Φ ]) → A u} → a u ≡ a' u → a ≡ a'
    parEq {a} {a'} eq = funext (λ v → subst (λ v → a v ≡ a' v) (equ (fst Φ) u v) eq)
    fg≡id : (gl : Glue' Φ A B w) → (glue-ptwise {Φ = Φ} w u (fst gl u)) ≡ gl
    fg≡id gl = glueExt {Φ = Φ} w (glue-ptwise {Φ = Φ} w u (fst gl u)) gl fstEq sndEq where
      fstEq : fst (glue-ptwise {Φ = Φ} w u (fst gl u)) ≡ fst gl
      fstEq = parEq prfIr
      sndEq : w u (fst gl u) ≡ fst (snd gl)
      sndEq = snd (snd gl) u
  
SGlue' Φ A B w = fst (reIm Φ A (Glue' Φ A B w) (fIso' Φ w))

SGlue :
  ∀{a}{Γ : Set a}
  (Φ : Γ → Cof)
  (A : res Γ Φ → Set)
  (B : Γ → Set)
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  Γ → Set
SGlue Φ A B f x = SGlue' (Φ x) (λ u → A (x , u)) (B x) (f x)

fIso :
  ∀{ℓ}{Γ : Set ℓ}
  (Φ : Γ → Cof)
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (w : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (x : Γ) (u : [ Φ x ]) → A (x , u) ≅' Glue Φ A B w x
fIso Φ w x = fIso' (Φ x) (w x)

sglue :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (w : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (xu : res Γ Φ) → A xu → SGlue Φ A B w (fst xu)
abstract
 sglue {_} {Γ} {Φ} {A} {B} w (x , u) = (_≅'_.from iso) ∘ glue {Φ = Φ} w (x , u) where
  iso : SGlue Φ A B w x ≅' Glue Φ A B w x
  iso = isoB Φ A (Glue Φ A B w) (fIso Φ w) x

sunglue :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (w : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (x : Γ) → SGlue Φ A B w x → B x
abstract
 sunglue {_} {Γ} {Φ} {A} {B} w x = (unglue {Φ = Φ} w x) ∘ _≅'_.to iso where
  iso : SGlue Φ A B w x ≅' Glue Φ A B w x
  iso = isoB Φ A (Glue Φ A B w) (fIso Φ w) x

FibSGlueId' :
  {Φ : Int → Cof}
  {A : res Int Φ → Set}
  {B : Int → Set}
  (f : (x : Int)(u : [ Φ x ]) → A (x , u) → B x)
  (equiv : (x : Int)(v : [ Φ x ]) → Equiv' (f x v))
  → ---------------
  isFib A → isFib B → isFib (SGlue Φ A B f)
abstract
 FibSGlueId' {Φ} {A} {B} f equiv α β =
  FibIso (SGlue Φ A B f) (Glue Φ A B f) iso (FibGlue-open {Φ = Φ} f equiv α β) where
    iso : SGlue Φ A B f ≅ Glue Φ A B f
    iso x = isoB Φ A (Glue Φ A B f) (fIso Φ f) x

FibSGlue'-open :
  ∀{a}{Γ : Set a}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → ---------------
  isFib A → isFib B → isFib (SGlue Φ A B f)
FibSGlue'-open {a} {Γ} {Φ} {A} {B} f equiv α β e p =
  FibSGlueId' (λ i → f (p i)) (λ i → equiv (p i)) (reindex A α (λ{ (i , u) → p i , u })) (reindex B β p) e id

FibSGlue' :
  ∀{a}{Γ : Set a}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → ---------------
  isFib A → isFib B → isFib (SGlue Φ A B f)
abstract
 FibSGlue' {a} {Γ} {Φ} {A} {B} f equiv α β e p = FibSGlue'-open {a} {Γ} {Φ} {A} {B} f equiv α β e p

FibSGlue'-unfold :
  ∀{a}{Γ : Set a}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  → ---------------
  FibSGlue'-open {a} {Γ} {Φ} {A} {B} ≡ FibSGlue' {a} {Γ} {Φ} {A} {B}
abstract
 FibSGlue'-unfold = refl

SGlueFib' :
  ∀{ℓ}{Γ : Set ℓ}
  (Φ : Γ → Cof)
  (A : Fib (res Γ Φ))
  (B : Fib Γ)
  (f : (x : Γ)(u : [ Φ x ]) → fst A (x , u) → fst B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → --------------
  Fib Γ
SGlueFib' {_} {Γ} Φ (A , α) (B , β) f equiv = SGlue Φ A B f , FibSGlue' {Γ = Γ} {Φ} {A} {B} f equiv α β

strictness :
  ∀{ℓ}{Γ : Set ℓ}
  (Φ : Γ → Cof)
  (A : res Γ Φ → Set)
  (B : Γ → Set)
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (x : Γ)
  (u : [ Φ x ])
  → ---------------
  SGlue Φ A B f x ≡ A (x , u)
abstract
 strictness Φ A B f x u = symm (restrictsToA Φ A (Glue Φ A B f) (fIso Φ f) (x , u))

str :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (x : Γ)
  → ---------------
  Glue Φ A B f x → SGlue Φ A B f x
abstract
 str {Γ = Γ} {Φ} {A} {B} f x = _≅'_.from (isoB Φ A (Glue Φ A B f) (fIso Φ f) x)

unstr :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (x : Γ)
  → ---------------
  SGlue Φ A B f x → Glue Φ A B f x
abstract
 unstr {Γ = Γ} {Φ} {A} {B} f x = _≅'_.to (isoB Φ A (Glue Φ A B f) (fIso Φ f) x)

unstrIsGlue :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (x : Γ)
  (u : [ Φ x ])
  → ---------------
  (a : SGlue Φ A B f x ) → unstr {Γ = Γ} {Φ} {A} {B} f x a ≡ glue {Φ = Φ} f (x , u) (coe (strictness Φ A B f x u) a)
abstract
 unstrIsGlue {Γ = Γ} {Φ} {A} {B} f x u g = inner (restrictsToM Φ A (Glue Φ A B f) (fIso Φ f) x u) g where
  inner : {Am Gs : Σ X ∈ Set , X ≅' Glue Φ A B f x}(eq : Am ≡ Gs)(g : fst Gs) → _≅'_.to (snd Gs) g ≡ _≅'_.to (snd Am) (coe (symm (Σeq₁ eq)) g)
  inner refl b = refl

strIsUnglue :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (x : Γ)
  (u : [ Φ x ])
  → ---------------
  (g : Glue Φ A B f x) → str {Γ = Γ} {Φ} {A} {B} f x g ≡ coe (symm (strictness Φ A B f x u)) (fst g u)
abstract
 strIsUnglue {Γ = Γ} {Φ} {A} {B} f x u g = inner (restrictsToM Φ A (Glue Φ A B f) (fIso Φ f) x u) g where
  inner : {Am Gs : Σ X ∈ Set , X ≅' Glue Φ A B f x}(eq : Am ≡ Gs)(g : Glue Φ A B f x) → _≅'_.from (snd Gs) g ≡ coe (symm (symm (Σeq₁ eq))) (_≅'_.from (snd Am) g)
  inner refl b = refl

unstrStr :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (x : Γ)
  → ---------------
  (unstr {Γ = Γ} {Φ} {A} {B} f x) ∘ (str {Γ = Γ} {Φ} {A} {B} f x) ≡ id
abstract
 unstrStr {Γ = Γ} {Φ} {A} {B} f x = _≅'_.inv₂ (isoB Φ A (Glue Φ A B f) (fIso Φ f) x)

strUnstr :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (x : Γ)
  → ---------------
  (str {Γ = Γ} {Φ} {A} {B} f x) ∘ (unstr {Γ = Γ} {Φ} {A} {B} f x) ≡ id
abstract
 strUnstr {Γ = Γ} {Φ} {A} {B} f x = _≅'_.inv₁ (isoB Φ A (Glue Φ A B f) (fIso Φ f) x)


uaβhelper2 :
  ∀{ℓ}{Γ : Set ℓ}
  (A : Fib (res (Γ × Int) i=OI))
  (B : Fib (Γ × Int))
  (f : (x : Γ × Int)(u : [ i=OI x ]) → fst A (x , u) → fst B x)
  (equiv : (x : Γ × Int)(v : [ i=OI x ]) → Equiv' (f x v))
  (x : Γ)
  (a : SGlue i=OI (fst A) (fst B) f (x , O))
  → ---------------
  fst (FibSGlue' {Φ = i=OI} f equiv (snd A) (snd B) O' < x ,id> cofFalse ∅-elim (a , λ ()))
    ≡ str {Φ = i=OI} f (x , I) (fst (FibGlue {Φ = i=OI} f equiv (snd A) (snd B) O' < x ,id> cofFalse ∅-elim ((unstr {Φ = i=OI} f (x , O) a) , (λ ()))))
abstract
 uaβhelper2 (A , α) (B , β) f equiv x a = trans unfold (trivialFibIso (Glue i=OI A B f) (SGlue i=OI A B f) iso (FibGlue-open {Φ = i=OI} f equiv α β) < x ,id> a) where
    iso :  SGlue i=OI A B f ≅ Glue i=OI A B f
    iso x = isoB i=OI A (Glue i=OI A B f) (fIso i=OI f) x
    unfold = cong (λ F → str {Φ = i=OI} f (x , I) (fst (F f equiv α β O' < x ,id> cofFalse ∅-elim ((unstr {Φ = i=OI} f (x , O) a) , (λ ()))))) (FibGlue-unfold {Φ = i=OI})
