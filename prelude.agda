----------------------------------------------------------------------
-- This Agda code is designed to accompany the thesis "Cubical models
-- of homotopy type theory - an internal approach" by Ian Orton.   
----------------------------------------------------------------------

module prelude where

open import Agda.Primitive hiding (I) public

infix  1 Σ proof:_
infixr 2 _≡[_]≡_
infix  3 _qed
infixr 3 _,_
infixr 5  _×_ _∘_ _⊎_

----------------------------------------------------------------------
-- Identity function
----------------------------------------------------------------------
id : ∀{a}{A : Set a} → A → A
id x = x

----------------------------------------------------------------------
-- Composition
----------------------------------------------------------------------
_∘_ :
  {ℓ m n : Level}
  {A : Set ℓ}
  {B : Set m}
  {C : Set n}
  (g : B → C)
  (f : A → B)
  → -------------
  A → C
(g ∘ f) x = g (f x)

----------------------------------------------------------------------
-- Propositional equality
----------------------------------------------------------------------
open import Agda.Builtin.Equality public

trans :
  {ℓ : Level}
  {A : Set ℓ}
  {x y z : A}
  (q : y ≡ z)
  (p : x ≡ y)
  → ---------
  x ≡ z
trans q refl = q

symm :
  {ℓ : Level}
  {A : Set ℓ}
  {x y : A}
  (p : x ≡ y)
  → ---------
  y ≡ x
symm refl = refl

cong :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  {B : Set ℓ'}
  (f : A → B)
  {x y : A}
  (p : x ≡ y)
  → -----------
  f x ≡ f y
cong _ refl = refl

cong₂ :
  {ℓ ℓ' : Level}
  {A A' : Set ℓ}
  {B : Set ℓ'}
  (f : A → A' → B)
  {x y  : A}
  {x' y' : A'}
  (p : x ≡ y)
  (q : x' ≡ y')
  → --------------
  f x x' ≡ f y y'
cong₂ _ refl refl = refl

subst :
  {ℓ ℓ' : Level}
  {A  : Set ℓ}
  (B : A → Set ℓ')
  {x y : A}
  (p : x ≡ y)
  → --------------
  B x → B y
subst _  refl = λ b → b

congdep :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  {B : A → Set ℓ'}
  (f : (a : A) → B a)
  {x y : A}
  (p : x ≡ y)
  → -----------
  subst B p (f x) ≡ f y
congdep _ refl = refl

substconst :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  (B : Set ℓ')
  {x y : A}
  (p : x ≡ y)
  (b : B)
  → ------------------------
  (subst (λ _ → B) p) b ≡ b
substconst _ refl _ = refl

subst₂ :
  {ℓ ℓ' : Level}
  {A  A' : Set ℓ}
  (B : A → A' → Set ℓ')
  {x y  : A}
  {x' y' : A'}
  (p : x ≡ y)
  (p' : x' ≡ y')
  → ------------------
  B x x' → B y y'
subst₂ _ refl refl = λ b → b

subst-cong-assoc :
  {l l' l'' : Level}
  {A : Set l}
  {B : Set l'}
  (C : B → Set l'')
  (f : A → B)
  {x y : A}
  (p : x ≡ y) 
  → ------------------------------------------
  subst (λ x → C (f x)) p ≡ subst C (cong f p)
subst-cong-assoc _ _ refl = refl

uip :
  {ℓ : Level}
  {A : Set ℓ}
  {x y : A}
  (p q : x ≡ y)
  → -----------
  p ≡ q
uip refl refl = refl

uipImp :
  {ℓ : Level}
  {A : Set ℓ}
  {x y : A}
  {p q : x ≡ y}
  → -----------
  p ≡ q
uipImp {p = refl} {q = refl} = refl

appCong :
  {ℓ ℓ' : Level}
  {A : Set ℓ}
  {B : Set ℓ'}
  {f g : A → B}
  {x : A}
  (p : f ≡ g)
  → -----------
  f x ≡ g x
appCong refl = refl

----------------------------------------------------------------------
-- Equational reasoning
----------------------------------------------------------------------
proof:_ :
  {ℓ : Level}
  {A : Set ℓ}
  {x y : A}
  → ---------------------
  x ≡ y → x ≡ y
proof: p = p

_≡[_]≡_ :
  {ℓ : Level}
  {A : Set ℓ}
  (x : A)
  {y z : A}
  → -------------------
  x ≡ y → y ≡ z → x ≡ z
_ ≡[ p ]≡ q = trans q p  

_qed :
  {ℓ : Level}
  {A : Set ℓ}
  (x : A)
  → ---------
  x ≡ x
_qed _ = refl

----------------------------------------------------------------------
-- Type coersion
----------------------------------------------------------------------
coe : {A B : Set} → A ≡ B → A → B
coe refl = id

----------------------------------------------------------------------
-- Empty type
----------------------------------------------------------------------
data ∅ : Set where

∅-elim :
  {ℓ : Level}
  {A : Set ℓ}
  → ---------
  ∅ → A
∅-elim ()

----------------------------------------------------------------------
-- One-element type
----------------------------------------------------------------------
open import Agda.Builtin.Unit renaming (⊤ to Unit) public

----------------------------------------------------------------------
-- Booleans
----------------------------------------------------------------------
open import Agda.Builtin.Bool renaming (Bool to 𝔹) public

----------------------------------------------------------------------
-- Natural Numbers
----------------------------------------------------------------------
open import Agda.Builtin.Nat renaming (Nat to ℕ) public

----------------------------------------------------------------------
-- Disjoint union
----------------------------------------------------------------------
data _⊎_ {ℓ m : Level}(A : Set ℓ)(B : Set m) : Set (ℓ ⊔ m) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

----------------------------------------------------------------------
-- Dependent products
----------------------------------------------------------------------
record Σ {ℓ m : Level} (A : Set ℓ) (B : A → Set m) : Set (ℓ ⊔ m) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

syntax Σ A (λ x → B) = Σ x ∈ A , B

_×_ : {ℓ m : Level} → Set ℓ → Set m → Set (ℓ ⊔ m)
A × B = Σ A (λ _ → B)

_×'_ : {ℓ ℓ' m m' : Level}{A : Set ℓ}{A' : Set ℓ'}{B : Set m}{B' : Set m'}
  → (A → A') → (B → B') → A × B → A' × B'
(f ×' g) (a , b) = f a , g b

Σext :
  {ℓ m : Level}
  {A : Set ℓ}
  {B : A → Set m}
  {x x' : A}
  {y : B x}
  {y' : B x'}
  (p : x ≡ x')
  (q : subst B p y ≡ y')
  → --------------------
  (x , y) ≡ (x' , y')
Σext refl refl = refl

Σeq₁ :
  {ℓ ℓ' : Level}
  {A  : Set ℓ}
  {B : A → Set ℓ'}
  {x y : Σ A B}
  (p : x ≡ y)
  → --------------
  fst x ≡ fst y
Σeq₁ refl = refl

Σeq₂ :
  {ℓ ℓ' : Level}
  {A  : Set ℓ}
  {B : A → Set ℓ'}
  {x y : Σ A B}
  (p : x ≡ y)
  → --------------
  subst B (Σeq₁ p) (snd x) ≡ snd y
Σeq₂ refl = refl
