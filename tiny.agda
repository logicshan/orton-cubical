----------------------------------------------------------------------
-- Note that this code is adapted from the code supporting Dan Licata,
-- Ian Orton, Andrew M. Pitts and Bas Spitters, "Internal Universes in
-- Models of Homotopy Type Theory", which is joint work with the other
-- listed authors.
----------------------------------------------------------------------

{- Use with Andrea Vezzosi's agda-flat -}
{-# OPTIONS --rewriting #-}

open import prelude
open import interval

module tiny where

----------------------------------------------------------------------
-- Congruence property for functions of a crisp variable
----------------------------------------------------------------------

cong♭ :
  {l :{♭} Level}
  {A :{♭} Set l}
  {l' : Level}
  {B : Set l'}
  (f : (x :{♭} A) → B){x y :{♭} A}
  → ------------------------------
  (_ :{♭} x ≡ y) → f x ≡ f y
cong♭ _ refl = refl

----------------------------------------------------------------------
-- Postulating that the path object functor, Int → (_) , has a right
-- adjoint, √. This follows from the fact that the interval is tiny.
----------------------------------------------------------------------
-- The path object functor
℘ :{♭}
  {l : Level}
  (Γ : Set l)
  → ---------
  Set l
℘ A = Int → A

-- The functorial action of ℘
℘` :{♭}
  {l m : Level}
  {Γ : Set l}
  {Δ : Set m}
  (γ : Δ → Γ)
  → -----------
  ℘ Δ → ℘ Γ
℘` γ p i = γ (p i)

postulate
  -- the value of the right adjoint on objects
  √  :
    {l :{♭} Level}
    (A :{♭} Set l)
    → ------------
    Set l
  -- right transposition across the adjunction 
  R  :
    {l l' :{♭} Level}
    {A :{♭} Set l}
    {B :{♭} Set l'}
    (f :{♭} ℘ A → B)
    → ---------------
    A → √ B
  -- left transposition across the adjunction
  L  :
    {l l' :{♭} Level}
    {A :{♭} Set l}
    {B :{♭} Set l'}
    (g :{♭} A → √ B)
    → --------------
    ℘ A → B
  -- right and left transposition are mutually inverse
  LR :
    {l l' :{♭} Level}
    {A :{♭} Set l}
    {B :{♭} Set l'}
    {f :{♭} ℘ A → B}
    → ---------------
    L (R f) ≡ f
  RL :
    {l l' :{♭} Level}
    {A :{♭} Set l}
    {B :{♭} Set l'}
    {g :{♭} A → √ B}
    → ---------------
    R (L g) ≡ g
  -- one-sided naturality of right transposition
  R℘ :
    {l l' l'' :{♭} Level}
    {A :{♭} Set l}
    {B :{♭} Set l'}
    {C :{♭} Set l''}
    (g :{♭} A → B)
    (f :{♭} ℘ B → C)
    → --------------------
    R (f ∘ ℘` g) ≡ R f ∘ g

{-# REWRITE LR RL #-}
{- 
The use of these REWRITES is not necessary, but it does simplify
proofs of equality in the paper by making some of the steps
computational. The proof of L℘ below is an example.
-}

-- One-sided naturality of left transposition is derivable
L℘ :
  {l l' l'' :{♭} Level}
  {A :{♭} Set l}
  {B :{♭} Set l'}
  {C :{♭} Set l''}
  (f :{♭} B → √ C)
  (g :{♭} A → B)
  → --------------------
  L f ∘ ℘` g ≡ L (f ∘ g)
L℘ f g = cong♭ L (R℘ g (L f))
{- 
Here is the proof without declaring LR and RL to be REWRITES:
     proof
       (L f ∘ ℘` g)
     ≡[ symm LR  ]
       L (R (L f ∘ ℘` g))
     ≡[ cong♭ L (R℘ g (L f)) ]
       L (R (L f) ∘ g)
     ≡[ cong♭ (λ h → L (h ∘ g)) RL ]
       L (f ∘ g)
     qed
-}
  
-- Functoriality of √
√` :
  {l l' :{♭} Level}
  {A :{♭} Set l}
  {B :{♭} Set l'}
  (f :{♭} A → B)
  → ---------------
  √ A → √ B
√` f = R (f ∘ L id)

-- The other naturality property of right transposition
√R :
  {l l' l'' :{♭} Level}
  {A :{♭} Set l}
  {B :{♭} Set l'}
  {C :{♭} Set l''}
  (g :{♭} B → C)
  (f :{♭} ℘ A → B)
  → --------------------
  √` g ∘ R f ≡ R (g ∘ f)
√R g f =
  proof:
    R (g ∘ L id) ∘ R f
  ≡[ symm (R℘ (R f) (g ∘ L id)) ]≡
    R (g ∘ L id ∘ ℘`(R f))
  ≡[ cong♭ (λ h → R (g ∘ h)) (L℘ id (R f)) ]≡
    R (g ∘ f)
  qed

-- The other naturality property of left transposition
L√ :
  {l l' l'' :{♭} Level}
  {A :{♭} Set l}
  {B :{♭} Set l'}
  {C :{♭} Set l''}
  (g :{♭} B → C)
  (f :{♭} A → √ B)
  → ---------------------
  g ∘ L f  ≡ L (√` g ∘ f)
L√ g f = cong♭ L (symm (√R g (L f)))
