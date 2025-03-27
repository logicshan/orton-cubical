----------------------------------------------------------------------
-- This Agda code is designed to accompany the thesis "Cubical models
-- of homotopy type theory - an internal approach" by Ian Orton.       
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module Data.universe where

open import prelude
open import impredicative
open import cof
open import interval
open import fibrations
open import equivs
open import Data.products
open import Data.functions
open import Data.paths

----------------------------------------------------------------------
-- Construction of the universe
----------------------------------------------------------------------
open import Data.universe-core public

----------------------------------------------------------------------
-- The universe is closed under Σ-types
----------------------------------------------------------------------
FibΣUniversal :
  isFib {Γ = Σ A ∈ U , (El A → U)} (λ{ (A , B) → Σ x ∈ El A , El (B x) })
FibΣUniversal e p = FibΣid α β e id where
  A : Int → Set
  A i = El (fst (p i))
  α : isFib A
  α = reindex El el (fst ∘ p)
  B : (Σ i ∈ Int , A i) → Set
  B (i , a) = El (snd (p i) a)
  β : isFib B
  β = reindex El el (λ{ (i , a) → snd (p i) a})

σ : (a : U)(b : El a → U) → U
σ a b = code ((λ{ (A , B) → Σ x ∈ El A , El (B x) }) , FibΣUniversal) (a , b)

σ' :
  {Γ : Set}
  (a : Γ → U)
  (b : Σ Γ (El ∘ a) → U)
  → ---------------
  Γ → U
σ' a b x = σ (a x) (λ a → b (x , a))

σ-comp :
  {Γ : Set}
  (a : Γ → U)
  (b : Σ Γ (El ∘ a) → U)
  → ---------------
  decode (σ' a b) ≡ FibΣ' (decode a) (decode b)
σ-comp a b =
  cong
    (λ F → reindex' F (λ x → (a x , λ a → b (x , a))))
    (Elcode ((λ{ (A , B) → Σ x ∈ El A , El (B x) }), FibΣUniversal))

cong♭ :
  {ℓ ℓ' :{♭} Level}
  {A :{♭} Set ℓ}
  {B :{♭} Set ℓ'}
  (f : (_ :{♭} A) → B)
  {x y :{♭} A}
  (p : x ≡ y)
  → -----------
  f x ≡ f y
cong♭ _ refl = refl

coeΣ :
  {Γ :{♭} Set}
  {A :{♭} Fib Γ}
  (B :{♭} Fib (Σ Γ (fst A)))
  → ---------------
  Fib (Σ Γ (El ∘ code A))
coeΣ {Γ} {A} B = subst (λ A → Fib (Σ Γ (fst A))) (symm (Elcode A)) B

σ-comp' :
  {Γ :{♭} Set}
  (A :{♭} Fib Γ)
  (B :{♭} Fib (Σ Γ (fst A)))
  → ---------------
  code (FibΣ' A B) ≡ σ' (code A) (code (coeΣ B))
σ-comp' {Γ} A B =
  proof:
      code (FibΣ' A B)
    ≡[ cong♭ codeFibΣ' AB=dcAB ]≡
      code (FibΣ' (decode (code A)) (decode (code B')))
    ≡[ cong♭ code (symm (σ-comp (code A) (code B'))) ]≡
      code (decode (σ' (code A) (code B')))
    ≡[ codeEl (σ' (code A) (code B')) ]≡
      σ' (code A) (code B')
  qed where
    codeFibΣ' : (AB :{♭} Σ A ∈ Fib Γ , Fib (Σ Γ (fst A))) → Γ → U
    codeFibΣ' (A , B) = code (FibΣ' A B)
    B' : Fib (Σ Γ (El ∘ code A))
    B' = coeΣ B
    AB=dcAB : (A , B) ≡ (decode (code A) , decode (code B'))
    AB=dcAB = Σext (symm (Elcode A)) (symm (Elcode B'))

----------------------------------------------------------------------
-- The universe is closed under Π-types
----------------------------------------------------------------------
FibΠUniversal :
  isFib {Γ = Σ A ∈ U , (El A → U)} (λ{ (A , B) → (x : El A) → El (B x) })
FibΠUniversal e p = FibΠid α β e id where
  A : Int → Set
  A i = El (fst (p i))
  α : isFib A
  α = reindex El el (fst ∘ p)
  B : (Σ i ∈ Int , A i) → Set
  B (i , a) = El (snd (p i) a)
  β : isFib B
  β = reindex El el (λ{ (i , a) → snd (p i) a})

π : (a : U)(b : El a → U) → U
π a b = code ((λ{ (A , B) → (x : El A) → El (B x) }) , FibΠUniversal) (a , b)

π' :
  {Γ : Set}
  (a : Γ → U)
  (b : Σ Γ (El ∘ a) → U)
  → ---------------
  Γ → U
π' a b x = π (a x) (λ a → b (x , a))

π-comp :
  {Γ : Set}
  (a : Γ → U)
  (b : Σ Γ (El ∘ a) → U)
  → ---------------
  decode (π' a b) ≡ FibΠ' (decode a) (decode b)
π-comp a b =
  cong
    (λ F → reindex' F (λ x → (a x , λ a → b (x , a))))
    (Elcode ((λ{ (A , B) → (x : El A) → El (B x) }) , FibΠUniversal))

----------------------------------------------------------------------
-- The universe is closed under Path types
----------------------------------------------------------------------
FibPathUniversal :
  isFib {Γ = Σ A ∈ U , (El A × El A)} (λ{ (A , x , y) → x ~ y })
FibPathUniversal e p = FibPathId α e p' where
  A : Int → Set
  A i = El (fst (p i))
  α : isFib A
  α = reindex El el (fst ∘ p)
  p' : Int → Σ i ∈ Int , (A i × A i)
  p' i = i , snd (p i)

path : (a : U) → El a → El a → U
path a x y = code ((λ{ (A , x , y) → x ~ y }) , FibPathUniversal) (a , x , y)

path' :
  {Γ : Set}
  (a : Γ → U)
  → ---------------
  Σ x ∈ Γ , El (a x) × El (a x) → U
path' a (x , y , y') = path (a x) y y'
  
path-comp :
  {Γ : Set}
  (a : Γ → U)
  → ---------------
  decode (path' a) ≡ FibPath' (decode a)
path-comp a =
  cong
    (λ F → reindex' F (λ{ (x , y , y') → a x , y , y' }))
    (Elcode ((λ{ (A , x , y) → x ~ y }) , FibPathUniversal))


----------------------------------------------------------------------
-- The universe is closed under Glueing
----------------------------------------------------------------------
-- This section is a lot trickier because so much of the definition
-- of glueing is abstract that Agda can't see that it's defined
-- pointwise. The module glueing2 is a copy of glueing but where
-- the fact that SGlue is pointwise is public. FibSGlueid is currently
-- postulated, but it should be straightforward (but tedious) to
-- adapt the proofs in glueing to get what we want.

open import glueing.strict
open import glueing.fix

{-# REWRITE FibSGlue-unfold #-}

record GlueingData : Set₁ where
  constructor gdata
  field
    ϕ : Cof
    A : [ ϕ ] → U
    B : U
    f : (u : [ ϕ ]) → El (A u) → El B
    equiv : (u : [ ϕ ]) → Equiv' (f u)

SGlueUniversal : GlueingData → Set
SGlueUniversal (gdata ϕ A B f equiv) =
  SGlue' ϕ (El ∘ A) (El B) f

FibSGlueUniversal : isFib {Γ = GlueingData} SGlueUniversal
FibSGlueUniversal e p = FibSGlue {Φ = ϕ} (λ i → GlueingData.f (p i)) (λ i → GlueingData.equiv (p i)) α β e id where
      ϕ : Int → Cof
      ϕ = GlueingData.ϕ ∘ p
      A : (Σ i ∈ Int , [ ϕ i ]) → Set
      A (i , u) = El (GlueingData.A (p i) u)
      α : isFib A
      α = reindex El el (λ{ (i , u) → GlueingData.A (p i) u})
      B : Int → Set
      B i = El (GlueingData.B (p i))
      β : isFib B
      β = reindex El el (GlueingData.B ∘ p)

sglue-code : GlueingData → U
abstract
 sglue-code = code (SGlueUniversal , FibSGlueUniversal)

sglue-code' :
  {a : Level}
  {Γ : Set a}
  (g : Γ → GlueingData)
  → ---------------
  Γ → U
sglue-code' g x = sglue-code (g x)
  
sglue-comp' :
  {a : Level}
  {Γ : Set a}
  (g : Γ → GlueingData)
  → ---------------
  decode (sglue-code' g) ≡
    SGlueFib (GlueingData.ϕ ∘ g)
      (decode (λ{ (x , u) → GlueingData.A (g x) u}))
      (decode (GlueingData.B ∘ g))
      (λ x → GlueingData.f (g x))
      (λ x → GlueingData.equiv (g x))
abstract
 sglue-comp' g = cong (λ F → reindex' F g) (Elcode (SGlueUniversal , FibSGlueUniversal))


----------------------------------------------------------------------
-- The universe is a fibrant object
----------------------------------------------------------------------
-- Given a line in the universe we can transport from one end to the other
transportU : (P : Int → U)(e : OI) → El (P ⟨ e ⟩) → El (P ⟨ ! e ⟩)
transportU P e a = fst (snd (decode P) e id cofFalse ∅-elim (a , (λ ())) )

-- The induced map is a quasi-inverse
transportU-qinv : (P : Int → U)(e : OI) → Qinv (transportU P e)
transportU-qinv P e = (transportU P (! e)) , ends e , ends (! e) where
  ends : (e : OI)(b : El (P ⟨ ! e ⟩)) → transportU P e (transportU P (! e) b) ~ b
  ends O' b = transDep' {A = El ∘ P} {α = snd (decode P)}
      (fillPath (snd (decode P)) (transportU P I' b)) (fillPath' (snd (decode P)) b)
  ends I' b = transDep {A = El ∘ P} {α = snd (decode P)}
      (fillPath' (snd (decode P)) (transportU P O' b)) (fillPath (snd (decode P)) b)

-- And hence an equiv
transportU-equiv : (P : Int → U)(e : OI) → Σ f ∈ (El (P ⟨ e ⟩) → El (P ⟨ ! e ⟩)) , Equiv' f
transportU-equiv P e = (transportU P e) ,
  qinv2equiv
    (reindex El el (λ _ → P ⟨ e ⟩))
    (reindex El el (λ _ → P ⟨ ! e ⟩))
    (λ _ → transportU P e) (λ _ → transportU-qinv P e) tt

-- The type of glueing data where the partial type is in fact total
TotalGlueingData : Set₁
TotalGlueingData = Σ glueing-data ∈ GlueingData , [ GlueingData.ϕ glueing-data ]


-- We have two ways of mapping this data into U:

-- Either we take the first projection and then use the map for glueing data
total-sglue-code : TotalGlueingData → U
total-sglue-code = sglue-code' fst

-- Or we use the proof term to access the partial (code for a) type
total-partial-code : TotalGlueingData → U
total-partial-code (gd , u) = GlueingData.A gd u

-- These two maps are equal
total-codes-equal : total-sglue-code ≡ total-partial-code
total-codes-equal =
    proof:
      total-sglue-code
        ≡[ symm (codeEl total-sglue-code) ]≡
      code (decode (sglue-code ∘ fst))
        ≡[ refl ]≡
      code (reindex' (decode sglue-code) fst)
        ≡[ cong♭ (λ A → code (reindex' A fst)) (sglue-comp' (λ x → x)) ]≡
      code
        (reindex'
         (SGlueFib GlueingData.ϕ (decode total-partial-code)
           (decode GlueingData.B) GlueingData.f GlueingData.equiv)
         fst
        )
        ≡[ cong♭ code (SGlueReindex GlueingData.ϕ (decode total-partial-code) (decode GlueingData.B) GlueingData.f GlueingData.equiv) ]≡
      code (decode total-partial-code)
        ≡[ codeEl total-partial-code ]≡
      total-partial-code
    qed


-- Fibrancy of the universe. Note that we can't just use isFib
-- because of size issues with this particular development.
FibU : (e : OI)(φ : Cof)(P : [ φ ] → Int → U) →
  (Σ A ∈ U , ((u : [ φ ]) → P u ⟨ e ⟩ ≡ A)) →
  (Σ B ∈ U , ((u : [ φ ]) → P u ⟨ ! e ⟩ ≡ B))
FibU e φ P (A , Aext) = B , Bext where
  fe : (u : [ φ ]) → Σ f ∈ (El (P u ⟨ ! e ⟩) → El A) , Equiv' f
  fe u = subst (λ A → Σ f ∈ (El (P u ⟨ ! e ⟩) → El A) , Equiv' f) (Aext u) (transportU-equiv (P u) (! e))
  f : (u : [ φ ]) → El (P u ⟨ ! e ⟩) → El A
  f u = fst (fe u)
  equiv : Equiv f
  equiv u = snd (fe u)
  B : U
  B = sglue-code (gdata φ (λ u → P u ⟨ ! e ⟩) A f equiv)
  Bext : (u : [ φ ]) → P u ⟨ ! e ⟩ ≡ B
  Bext u =
    let tgd = (gdata φ (λ u → P u ⟨ ! e ⟩) A f equiv) , u in
    symm (appCong {x = tgd} total-codes-equal)

----------------------------------------------------------------------
-- Univalence
----------------------------------------------------------------------
-- Common definitions for this section. A bit ugly that they're top
-- level, but they need to be shared across proofs.
pre : {i : Int} → [ (i ≈O) ∨ (i ≈I) ] → 𝔹
pre = OI-elim (λ{ (inl _) → false ; (inr _) → true})
makeC : (A B : U){i : Int} → [ (i ≈O) ∨ (i ≈I) ] → U
makeC A B u with pre u
... | false = A
... | true = B
makeF' : (A B : U)(f : El A → El B){i : Int}(u : [ (i ≈O) ∨ (i ≈I) ]) → El (makeC A B u) → El B
makeF' A B f u = OI-elim-dep {B = λ u → El (makeC A B u) → El B} (λ{ (inl _) → f ; (inr _) → id}) u
makeE' : (A B : U)(f : El A → El B)(e : Equiv' f){i : Int}(u : [ (i ≈O) ∨ (i ≈I) ]) → Equiv' (makeF' A B f u)
makeE' A B f e u = OI-elim-dep {B = λ u → Equiv' (makeF' A B f u)} (λ{ (inl _) → e ; (inr _) → idEquiv}) u

-- UA as a map on the universe
ua :
  {A B : U}
  (f : El A → El B)
  (e : Equiv' f)
  → ---------------
  Int → U
ua {A} {B} f e = sglue-code' (λ i → gdata (i ≈O ∨ i ≈I) (makeC A B) B (makeF' A B f) (makeE' A B f e))

-- I can't seem to prove that ua f e O ≡ A and ua f e I ≡ B "smoothly",
-- but I can show this when ua is applied to crisp families:
ua-comp :
  {Γ :{♭} Set}
  {A B :{♭} Γ → U}
  (f :{♭} (x : Γ) → El (A x) → El (B x))
  (e :{♭} (x : Γ) → Equiv' (f x))
  (i :{♭} Int)
  (x : Γ)
  → ----------------
  ua (f x) (e x) i ≡ code (SGlueFib (λ _ → i ≈O ∨ i ≈I) (decode (λ{ (x , u) → makeC (A x) (B x) u})) (decode B) (λ x → makeF' (A x) (B x) (f x)) (λ x → makeE' (A x) (B x) (f x) (e x))) x
abstract
  ua-comp {Γ} {A} {B} f e i = λ x → 
    (proof:
        ua (f x) (e x) i
      ≡[ hiddenRefl x ]≡
        sglue-code' g x
      ≡[ symm (cong (λ f → f x) (codeEl (sglue-code' g))) ]≡
        code (decode (sglue-code' g)) x
      ≡[ cong♭ (λ f → code f x) (sglue-comp' g) ]≡
        code (SGlueFib (λ _ → i ≈O ∨ i ≈I) (decode (λ{ (x , u) → C x u})) (decode B) f' e') x
      ≡[ finalStep x ]≡
        code (SGlueFib (λ _ → i ≈O ∨ i ≈I) (decode (λ{ (x , u) → makeC (A x) (B x) u})) (decode B) (λ x → makeF' (A x) (B x) (f x)) (λ x → makeE' (A x) (B x) (f x) (e x))) x
    qed)
      where
        -- Type signatures
        C : (x : Γ) → [ i ≈O ∨ i ≈I ] → U
        f' : (x : Γ)(u : [ i ≈O ∨ i ≈I ]) → El (C x u) → El (B x)
        e' : (x : Γ)(u : [ i ≈O ∨ i ≈I ]) → Equiv' (f' x u)
        g : Γ → GlueingData
        hiddenRefl : (x : Γ) → ua (f x) (e x) i ≡ sglue-code' g x
        finalStep : (x : Γ) →
           code (SGlueFib (λ _ → i ≈O ∨ i ≈I) (decode (λ{ (x , u) → C x u})) (decode B) f' e') x
             ≡ code (SGlueFib (λ _ → i ≈O ∨ i ≈I) (decode (λ{ (x , u) → makeC (A x) (B x) u})) (decode B) (λ x → makeF' (A x) (B x) (f x)) (λ x → makeE' (A x) (B x) (f x) (e x))) x
        -- Careful use of abstract to make things type check in a reasonable time
        abstract
          C x = makeC (A x) (B x)
          f' x = makeF' (A x) (B x) (f x)
          e' x = makeE' (A x) (B x) (f x) (e x)
        g x' = gdata (i ≈O ∨ i ≈I) (C x') (B x') (f' x') (e' x')
        abstract
         hiddenRefl _ = refl
         finalStep _ = refl

uaO :
  {Γ :{♭} Set}
  {A B :{♭} Γ → U}
  (f :{♭} (x : Γ) → El (A x) → El (B x))
  (e :{♭} (x : Γ) → Equiv' (f x))
  → ----------------
  (x : Γ) → ua (f x) (e x) O ≡ A x
uaO {Γ} {A} {B} f e x =
    proof:
        ua (f x) (e x) O
      ≡[ ua-comp f e O x ]≡
        code (SGlueFib (λ x → O ≈O ∨ O ≈I) (decode (λ{ (x , u) → C x u })) (decode B) (λ x → f' x) (λ x → e' x)) x
      ≡[ cong (λ f → f x) (cong♭ code (SGlueReindex' (λ x → O ≈O ∨ O ≈I) (decode (λ{ (x , u) → C x u })) (decode B) (λ x → f' x) (λ x → e' x) (λ _ → ∣ inl refl ∣))) ]≡
        code (decode A) x
      ≡[ cong (λ f → f x) (codeEl A) ]≡
        A x
    qed
      where
        C : (x : Γ) → [ O ≈O ∨ O ≈I ] → U
        C x = makeC (A x) (B x)
        f' : (x : Γ)(u : [ O ≈O ∨ O ≈I ]) → El (C x u) → El (B x)
        f' x = makeF' (A x) (B x) (f x)
        e' : (x : Γ)(u : [ O ≈O ∨ O ≈I ]) → Equiv' (f' x u)
        e' x = makeE' (A x) (B x) (f x) (e x)
        g : Γ → GlueingData
        g x = gdata (O ≈O ∨ O ≈I) (C x) (B x) (f' x) (e' x)

uaI :
  {Γ :{♭} Set}
  {A B :{♭} Γ → U}
  (f :{♭} (x : Γ) → El (A x) → El (B x))
  (e :{♭} (x : Γ) → Equiv' (f x))
  → ----------------
  (x : Γ) → ua (f x) (e x) I ≡ B x
uaI {Γ} {A} {B} f e x =
    proof:
        ua (f x) (e x) I
      ≡[ ua-comp f e I x ]≡
        code (SGlueFib (λ x → I ≈O ∨ I ≈I) (decode (λ{ (x , u) → C x u })) (decode B) (λ x → f' x) (λ x → e' x)) x
      ≡[ cong (λ f → f x) (cong♭ code (SGlueReindex' (λ x → I ≈O ∨ I ≈I) (decode (λ{ (x , u) → C x u })) (decode B) (λ x → f' x) (λ x → e' x) (λ _ → ∣ inr refl ∣))) ]≡
        code (decode B) x
      ≡[ cong (λ f → f x) (codeEl B) ]≡
        B x
    qed
      where
        C : (x : Γ) → [ I ≈O ∨ I ≈I ] → U
        C x = makeC (A x) (B x)
        f' : (x : Γ)(u : [ I ≈O ∨ I ≈I ]) → El (C x u) → El (B x)
        f' x = makeF' (A x) (B x) (f x)
        e' : (x : Γ)(u : [ I ≈O ∨ I ≈I ]) → Equiv' (f' x u)
        e' x = makeE' (A x) (B x) (f x) (e x)
        g : Γ → GlueingData
        g x = gdata (I ≈O ∨ I ≈I) (C x) (B x) (f' x) (e' x)


-- We now show that ua has the correct type when applied to  ∙ ⊢ A ↦
-- families.

-- Can't use Data.paths due to size issues. Should be
-- possible to refactor to make it universe polymorphic
-- but for now I just redefine the path type specifically
-- for the universe.
PathU : U → U → Set₁
PathU A B = Σ P ∈ (Int → U) , (P O ≡ A) × (P I ≡ B)

-- UA for families
ua' :
  {Γ :{♭} Set}
  {A B :{♭} Γ → U}
  (f :{♭} (x : Γ) → El (A x) → El (B x))
  (e :{♭} (x : Γ) → Equiv' (f x))
  → ------------------
  (x : Γ) → PathU (A x) (B x)
ua' {A} {B} f e x = (ua (f x) (e x)) , uaO f e x , uaI f e x

-- To finish the proof of univalence either apply the results from chapter 5
-- to this map ua. Or else use the results of chapter 6 to verify the 5 other
-- axioms with respect to this universe.
