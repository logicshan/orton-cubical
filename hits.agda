----------------------------------------------------------------------
-- This Agda code is designed to accompany the thesis "Cubical models
-- of homotopy type theory - an internal approach" by Ian Orton.
--
-- The definition of a DemiEndo and its use in showing that definitions
-- preserve transport structure is due to Evan Cavallo.
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module hits where 

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import hcomp-trans
open import quotients
open import replace

----------------------
-- 𝕊¹ (the circle)
----------------------
open import Data.paths

data Endpoints : Int → Int → Set where
  I=O : Endpoints I O

pre𝕊¹ : Set
pre𝕊¹ = Int / Endpoints

-- Define 𝕊¹ as the fibrewise fibrant replacement of
-- pre𝕊¹ (the interval with the endpoints equated) 
𝕊¹ : Set
𝕊¹ = Replace pre𝕊¹

𝕊¹HComp : isHComp 𝕊¹
𝕊¹HComp = replaceIsHComp pre𝕊¹

-- The base point
base : 𝕊¹
base = ι ([ O ]/ Endpoints)

-- The loop from base to base
loop : base ~ base
loop = p , refl , cong ι (qeq Endpoints I=O) where
  p : Int → 𝕊¹
  p i = ι ([ i ]/ Endpoints)

-- The elimination principle
𝕊¹-elim :
  (P : 𝕊¹ → Set)
  (ρ : isFib P)
  (a : P base)
  (l : (i : Int) → P (loop at i))
  (lO : subst P (atO loop) (l O) ≡ a)
  (lI : subst P (atI loop) (l I) ≡ a)
  → ---------------------
  (x : 𝕊¹) → P x
𝕊¹-elim P ρ a l lO lI x = replaceInd pre𝕊¹ P ρ f x where
  f : (x : pre𝕊¹) → P (ι x)
  f = qind Endpoints (P ∘ ι) l resp where
    resp : (i j : Int) (r : Endpoints i j) →
      subst (P ∘ ι) (qeq Endpoints r) (l i) ≡ l j
    resp .I .O I=O =
      proof:
        subst (P ∘ ι) (qeq Endpoints I=O) (l I)
          ≡[ substcong P ι (qeq Endpoints I=O) (l I) ]≡
        subst P (cong ι (qeq Endpoints I=O)) (l I)
          ≡[ lI ]≡
        a
          ≡[ symm lO ]≡
        l O
      qed

-- 𝕊¹ is always a fibration (over any context)
𝕊¹Fib : {Γ : Set} → isFib {Γ = Γ} λ _ → 𝕊¹
𝕊¹Fib = toFib (λ _ → 𝕊¹HComp) (constTransp 𝕊¹)

-----------------------------
-- Suspension (of an object)
-----------------------------
data preSusp (X : Set) : Set where
  preNorth : preSusp X
  preSouth : preSusp X
  preMerid : X → Int → preSusp X

data MeridEnds {X : Set} : preSusp X → preSusp X → Set where
  meridO : (x : X) → MeridEnds (preMerid x O) preNorth
  meridI : (x : X) → MeridEnds (preMerid x I) preSouth

-- Quotient by sending the endpoints of merid x to north and south
preSusp' : Set → Set
preSusp' X = preSusp X / MeridEnds

-- Then fibrewise fibrantly replace to get Susp
Susp : Set → Set
Susp X = Replace (preSusp' X)

-- The terms north and south, and the paths merid
north : {X : Set} → Susp X
north = ι ([ preNorth ]/ MeridEnds)

south : {X : Set} → Susp X
south = ι ([ preSouth ]/ MeridEnds)

merid : {X : Set} → X → north ~ south
merid {X} x = p , (cong ι (qeq MeridEnds (meridO x))) , cong ι (qeq MeridEnds (meridI x)) where
  p : Int → Susp X
  p i = ι ([ preMerid x i ]/ MeridEnds)

-- Elimination/induction principle
Susp-elim :
  (X  : Set)
  (P  : Susp X → Set)
  (ρ  : isFib P)
  (an : P north)
  (as : P south)
  (al : (x : X)(i : Int) → P (merid x at i))
  (lO : (x : X) → subst P (atO (merid x)) (al x O) ≡ an)
  (lI : (x : X) → subst P (atI (merid x)) (al x I) ≡ as)
  → ---------------------
  (x : Susp X) → P x
Susp-elim X P ρ an as al lO lI = replaceInd _ P ρ f where
  f : (x : preSusp X / MeridEnds) → P (ι x)
  f = qind MeridEnds (P ∘ ι) f' resp where
    f' : (x : preSusp X) → (P ∘ ι) ([ x ]/ MeridEnds)
    f' preNorth = an
    f' preSouth = as
    f' (preMerid x i) = al x i
    resp : (x y : preSusp X) (r : MeridEnds x y) →
      subst (P ∘ ι) (qeq MeridEnds r) (f' x) ≡ f' y
    resp .(preMerid x O) .preNorth (meridO x) =
      proof:
        subst (P ∘ ι) (qeq MeridEnds (meridO x)) (al x O)
          ≡[ substcong P ι (qeq MeridEnds (meridO x)) (al x O) ]≡
        subst P (cong ι (qeq MeridEnds (meridO x))) (al x O)
          ≡[ lO x ]≡
        an
      qed
    resp .(preMerid x I) .preSouth (meridI x) =
      proof:
        subst (P ∘ ι) (qeq MeridEnds (meridI x)) (al x I)
          ≡[ substcong P ι (qeq MeridEnds (meridI x)) (al x I) ]≡
        subst P (cong ι (qeq MeridEnds (meridI x))) (al x I)
          ≡[ lI x ]≡
        as
      qed

-- preSusp' is a DemiEndo
preSuspEndo : DemiEndo
preSuspEndo = endo preSusp' func pres-id where

  preSuspFunc : {A B : Set} → (A → B) → preSusp A → preSusp B
  preSuspFunc _ preNorth = preNorth
  preSuspFunc _ preSouth = preSouth
  preSuspFunc f (preMerid x i) = preMerid (f x) i

  func : {A B : Set} → (A → B) → preSusp' A → preSusp' B
  func {A} {B} f = qind MeridEnds _ (λ x → [ preSuspFunc f x ]/ MeridEnds) resp where
    resp : (x y : preSusp A) (r : MeridEnds x y) →
      subst _ (qeq MeridEnds r) ([ preSuspFunc f x ]/ MeridEnds) ≡ [ preSuspFunc f y ]/ MeridEnds
    resp .(preMerid x O) .preNorth (meridO x) =
      trans (qeq MeridEnds (meridO (f x)))
        (substconst (preSusp' B) (qeq MeridEnds (meridO x)) _)
    resp .(preMerid x I) .preSouth (meridI x) =
      trans (qeq MeridEnds (meridI (f x)))
        (substconst (preSusp' B) (qeq MeridEnds (meridI x)) _)

  pres-id : (A : Set) → func id ≡ id
  pres-id A =
    funext (qind MeridEnds (λ x → func id x ≡ x)
      (λ{ preNorth → refl ; preSouth → refl ; (preMerid x x₁) → refl})
      (λ _ _ _ → uipImp)
    )

----------------------------------------------------------------------
-- Therefore Suspension is a DemiEndo, and hence preserves transport
-- structure
----------------------------------------------------------------------

endoComp : (g f : DemiEndo) → DemiEndo
endoComp (endo g gfunc gid) (endo f ffunc fid) =
  endo (g ∘ f) (λ h → gfunc (ffunc h)) (λ A → trans (gid (f A)) (cong gfunc (fid A)))

SuspEndo : DemiEndo
SuspEndo = endoComp replaceEndo preSuspEndo

SuspEndoIsSusp : obf SuspEndo ≡ Susp
SuspEndoIsSusp = refl

SuspIsTransp : {Γ : Set}(X : Γ → Set) → isTransp X → isTransp (Susp ∘ X)
SuspIsTransp X tX = TranspFibEndo SuspEndo X tX

----------------------------------------------------------------------
-- Hence Suspension preserves fibration structure
----------------------------------------------------------------------
SuspIsFib : {Γ : Set}(X : Γ → Set) → isFib X → isFib (Susp ∘ X)
SuspIsFib X α = toFib (λ x → replaceIsHComp (preSusp' (X x))) (SuspIsTransp X (snd (fromFib α)))


----------------------------------------------------------------------
-- Pushout
----------------------------------------------------------------------
data prePushout {X Y Z : Set}(f : X → Y)(g : X → Z) : Set where
  preLeft  : Y → prePushout f g
  preRight : Z → prePushout f g
  prePush  : X → Int → prePushout f g

data PushEnds {X Y Z}{f : X → Y}{g : X → Z} : prePushout f g → prePushout f g → Set where
  pushO : (x : X) → PushEnds (prePush x O) (preLeft (f x))
  pushI : (x : X) → PushEnds (prePush x I) (preRight (g x))

-- Quotient as before
prePushout' : {X Y Z : Set}(f : X → Y)(g : X → Z) → Set
prePushout' f g = prePushout f g / PushEnds

-- Then fibrewise fibrantly replace to get Pushout
Pushout : {X Y Z : Set}(f : X → Y)(g : X → Z) → Set
Pushout f g = Replace (prePushout' f g)

-- The terms left and right and the paths push
left : ∀{X Y Z}{f : X → Y}{g : X → Z} → Y → Pushout f g
left y = ι ([ preLeft y ]/ PushEnds)

right : ∀{X Y Z}{f : X → Y}{g : X → Z} → Z → Pushout f g
right z = ι ([ preRight z ]/ PushEnds)

push : ∀{X Y Z}{f : X → Y}{g : X → Z} → (x : X) → left (f x) ~ right (g x)
push {f = f} {g} x = p , (cong ι (qeq PushEnds (pushO x)) , cong ι (qeq PushEnds (pushI x))) where
  p : Int → Pushout f g
  p i = ι ([ prePush x i ]/ PushEnds)

-- Elimination/induction principle
Pushout-elim :
  {X Y Z : Set}
  (f  : X → Y)
  (g  : X → Z)
  (P  : Pushout f g → Set)
  (ρ  : isFib P)
  (al : (y : Y) → P (left y))
  (ar : (z : Z) → P (right z))
  (ap : (x : X)(i : Int) → P (push x at i))
  (pO : (x : X) → subst P (atO (push x)) (ap x O) ≡ al (f x))
  (pI : (x : X) → subst P (atI (push x)) (ap x I) ≡ ar (g x))
  → ---------------------
  (x : Pushout f g) → P x
Pushout-elim f g P ρ al ar ap pO pI = replaceInd _ P ρ h where
  h : (a : prePushout' f g) → P (ι a)
  h = qind PushEnds (P ∘ ι) h' resp where
    h' : (x : prePushout f g) → (P ∘ ι) ([ x ]/ PushEnds)
    h' (preLeft y) = al y
    h' (preRight z) = ar z
    h' (prePush x i) = ap x i
    resp : (x y : prePushout f g) (r : PushEnds x y) →
      subst (P ∘ ι) (qeq PushEnds r) (h' x) ≡ h' y
    resp .(prePush x O) .(preLeft _) (pushO x) =
      proof:
        subst (P ∘ ι) (qeq PushEnds (pushO x)) (ap x O)
          ≡[ substcong P ι (qeq PushEnds (pushO x)) (ap x O) ]≡
        subst P (cong ι (qeq PushEnds (pushO x))) (ap x O)
          ≡[ pO x ]≡
        al (f x)
      qed
    resp .(prePush x I) .(preRight _) (pushI x) =
      proof:
        subst (P ∘ ι) (qeq PushEnds (pushI x)) (ap x I)
          ≡[ substcong P ι (qeq PushEnds (pushI x)) (ap x I) ]≡
        subst P (cong ι (qeq PushEnds (pushI x))) (ap x I)
          ≡[ pI x ]≡
        ar (g x)
      qed

