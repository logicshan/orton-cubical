----------------------------------------------------------------------
-- This Agda code is designed to accompany the thesis "Cubical models
-- of homotopy type theory - an internal approach" by Ian Orton.    
----------------------------------------------------------------------

{-# OPTIONS --rewriting #-}
module glueing.core where 

open import prelude
open import impredicative
open import interval
open import cof
open import fibrations
open import equivs
open import Data.paths
open import Data.products

----------------------------------------------------------------------
-- Glueing
----------------------------------------------------------------------
<_,id> : ∀{ℓ}{Γ : Set ℓ} → Γ → Int → Γ × Int
< x ,id> i = (x , i)

i=OI : ∀{ℓ}{Γ : Set ℓ} → Γ × Int → Cof
i=OI (x , i) = (i ≈O) ∨ (i ≈I)

Glue' :
  (Φ : Cof)
  (A : [ Φ ] → Set)
  (B : Set)
  (f : (u : [ Φ ]) → A u → B)
  → ---------------
  Set
Glue' Φ A B f = Σ a ∈ ((u : [ Φ ]) → A u) , ⟦ b ∈ B ∣ All u ∈ [ Φ ] , f u (a u) ≈ b ⟧

Glue :
  ∀{a}{Γ : Set a}
  (Φ : Γ → Cof)
  (A : res Γ Φ → Set)
  (B : Γ → Set)
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  Γ → Set
Glue Φ A B f x = Glue' (Φ x) (λ u → A (x , u)) (B x) (f x)

glue-ptwise :
  {Φ : Cof}
  {A : [ Φ ] → Set}
  {B : Set}
  (f : (u : [ Φ ]) → A u → B)
  → ---------------
  (u : [ Φ ]) → A u → Glue' Φ A B f
glue-ptwise {Φ} {A} {B} f u a = ((λ v → moveA v a) , (f u a , (λ v → cong (λ{(u , a) → f u a}) (symm (moveMove v))))) where
  moveA : (v : [ Φ ]) → A u → A v
  moveA v = subst A (eq (fst Φ))
  moveMove : (v : [ Φ ]) → (u , a) ≡ (v , moveA v a)
  moveMove v = Σext (eq (fst Φ)) refl

glue :
  ∀{a}{Γ : Set a}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (xu : res Γ Φ) → A xu → Glue Φ A B f (fst xu)
glue {a} {Γ} {Φ} {A} {B} f (x , u) = glue-ptwise {Φ x} (f x) u

unglue :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (x : Γ) → Glue Φ A B f x → B x
unglue _ _ (_ , b , _) = b

unglue' :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (x : Γ)(u : [ Φ x ]) → Glue Φ A B f x → A (x , u)
unglue' _ _ u (a , _ , _) = a u

unglueGlue :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (xu : res Γ Φ) → (unglue {Φ = Φ} f (fst xu)) ∘ (glue {Φ = Φ} f xu) ≡ f (fst xu) (snd xu)
unglueGlue f (x , u) = funext (λ a → refl)

glue' :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (x : Γ) → (a : (u : [ Φ x ]) → A (x , u)) → ⟦ b ∈ B x ∣ all [ Φ x ] (λ u → f x u (a u) ≈ b) ⟧ → Glue Φ A B f x
glue' f x a (b , bPrf) = (a , b , bPrf)

unglueGlue' :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (x : Γ) → (a : (u : [ Φ x ]) → A (x , u))
   → (unglue {Φ = Φ} f x) ∘ (glue' {Φ = Φ} f x a) ≡ fst
unglueGlue' f x a = refl

glueUnglue :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  → ---------------
  (x : Γ) → (g : Glue Φ A B f x)
   → glue' {Φ = Φ} f x (fst g) (unglue {Φ = Φ} f x g , snd (snd g)) ≡ g
glueUnglue f x g = refl

glueExt :
  {Φ : Cof}
  {A : [ Φ ] → Set}
  {B : Set}
  (f : (u : [ Φ ]) → A u → B)
  (g g' : Glue' Φ A B f)
  (p : fst g ≡ fst g')
  (q : fst (snd g) ≡ fst (snd g'))
  → ---------------
  g ≡ g'
glueExt _ (_ , _ , fa≡b) (_ , _ , fa≡b') refl refl =
  Σext refl (Σext refl (funext (λ u → uip (fa≡b u) (fa≡b' u))))

-- The fibration structure that we get for the fiber of f
-- regarded as a family over B
σ :
  ∀{ℓ}{Γ : Set ℓ}
  {Φ : Γ → Cof}
  {A : Fib (res Γ Φ)}
  {B : Fib Γ}
  (f : (x : Γ)(u : [ Φ x ]) → fst A (x , u) → fst B x)
  (x : Γ)
  (u : [ Φ x ])
  → ---------------
  isFib (Fiber (f x u))
σ {_} {Γ} {Φ} {A , α} {B , β} f x u =
  FibΣ {B = λ{ (b , a) → f x u a ~ b}}
    (reindex A α (λ _ → x , u))
    (reindex (Path B) (FibPath β) (λ{ (b , a) → (x , f x u a , b)}))

FibGlueId :
  {Φ : Int → Cof}
  {A : res Int Φ → Set}
  {B : Int → Set}
  (f : (x : Int)(u : [ Φ x ]) → A (x , u) → B x)
  (equiv : (x : Int)(v : [ Φ x ]) → Equiv' (f x v))
  → ---------------
  isFib A → isFib B → isFib (Glue Φ A B f)
abstract
 FibGlueId {Φ} {A} {B} f equiv α β e p ψ q ((a , b , fa↗b) , ext) = (g₁ , ext') where
  x : Int
  x = p ⟨ ! e ⟩
  ~a : [ ψ ] → (u : [ Φ x ]) → A (x , u)
  ~a v = fst (q v ⟨ ! e ⟩)
  ~b : [ ψ ] → B x
  ~b v = fst (snd (q v ⟨ ! e ⟩))
  f~a=~b : (v : [ ψ ])(u : [ Φ x ]) → f x u (~a v u) ≡ ~b v
  f~a=~b v = snd (snd (q v ⟨ ! e ⟩))
  
  qb : [ ψ ] → Π (B ∘ p)
  qb u i = fst (snd (q u i))
  b₁' : ⟦ b ∈ (B (p ⟨ ! e ⟩)) ∣ (ψ , qb) ∙ ⟨ ! e ⟩ ↗ b ⟧
  b₁' = β e p ψ qb (b , (λ u → cong (λ g → fst (snd g)) (ext u)))

  a₁'p' : (u : [ Φ x ])(v : [ ψ ]) → Fiber (f x u) (fst b₁')
  a₁'p' u v = (~a v u , reflPath' (trans (snd b₁' v) (f~a=~b v u)))

  ε : (u : [ Φ x ]) → Ext' (Fiber (f x u) (fst b₁'))
  ε u = contr2ext (σ {Φ = Φ} {A , α} {B , β} f x u) (equiv x u) (fst b₁')

  a₁p : (u : [ Φ x ]) → ⟦ ap ∈ Fiber (f x u) (fst b₁') ∣ (ψ , a₁'p' u) ↗ ap ⟧
  a₁p u = ε u ψ (a₁'p' u)

  a₁ : ⟦ a ∈ ((u : [ Φ x ]) → A (x , u)) ∣ (ψ , λ v → ~a v) ↗ a ⟧
  a₁ = (λ u → fst (fst (a₁p u))) , (λ v → (funext (λ u → cong fst (snd (a₁p u) v))))

  ~b-∪-fa₁ : [ ψ ∨ Φ x ] → Int → B (p ⟨ ! e ⟩)
  ~b-∪-fa₁ u i = _∪_ {φ = ψ} {ψ = Φ x} ~b (λ u → fst (snd (fst (a₁p u))) i) {agree} u where
    agree : prf ((ψ , ~b) ⌣ (Φ x , (λ u → fst (snd (fst (a₁p u))) i)))
    agree v u =
      let p≡refl = cong (λ ap → fst (snd ap) i) (snd (a₁p u) v) in
      let refl≡ = reflPathEval ((trans (snd b₁' v) (f~a=~b v u))) i in
      trans p≡refl (trans (symm refl≡) (snd b₁' v))
      
  b₁ : ⟦ b ∈ (B x) ∣ (ψ ∨ Φ x , ~b-∪-fa₁) ∙ O ↗ b ⟧
  b₁ = β I' (λ _ → x) (ψ ∨ Φ x) ~b-∪-fa₁
    ((fst b₁') , (λ u →
      or-elim-eq (λ u → ~b-∪-fa₁ u I)
        (fst b₁') (λ {l} → snd b₁' l) (λ {r} → snd (snd (snd (fst (a₁p r))))) u))

  g₁ : Glue Φ A B f x
  g₁ = (fst a₁ , fst b₁ , (λ u → trans (snd b₁ ∣ inr u ∣) (symm (fst (snd (snd (fst (a₁p u))))))))

  ext' : prf ((ψ , q) ∙ ⟨ ! e ⟩ ↗ g₁)
  ext' v = glueExt {Φ = Φ x} (f x) (q v ⟨ ! e ⟩) g₁ (snd a₁ v) (snd b₁ ∣ inl v ∣)

FibGlue-open :
  ∀{a}{Γ : Set a}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → ---------------
  isFib A → isFib B → isFib (Glue Φ A B f)
FibGlue-open {_} {Γ} {Φ} {A} {B} f equiv α β e p =
  FibGlueId {Φ ∘ p} (λ x → f (p x)) (λ x → equiv (p x))
    (reindex A α (λ xu → (p (fst xu)) , snd xu)) (reindex B β p) e id

FibGlue :
  ∀{a}{Γ : Set a}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  (f : (x : Γ)(u : [ Φ x ]) → A (x , u) → B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → ---------------
  isFib A → isFib B → isFib (Glue Φ A B f)
abstract
 FibGlue {_} {Γ} {Φ} {A} {B} f equiv α β e p =
  FibGlue-open {_} {Γ} {Φ} {A} {B} f equiv α β e p

FibGlue-unfold :
  ∀{a}{Γ : Set a}
  {Φ : Γ → Cof}
  {A : res Γ Φ → Set}
  {B : Γ → Set}
  → ---------------
  FibGlue-open {a} {Γ} {Φ} {A} {B} ≡ FibGlue {a} {Γ} {Φ} {A} {B}
abstract
 FibGlue-unfold = refl

GlueFib :
  ∀{ℓ}{Γ : Set ℓ}
  (Φ : Γ → Cof)
  (A : Fib (res Γ Φ))
  (B : Fib Γ)
  (f : (x : Γ)(u : [ Φ x ]) → fst A (x , u) → fst B x)
  (equiv : (x : Γ)(v : [ Φ x ]) → Equiv' (f x v))
  → ---------------
  Fib Γ
GlueFib Φ (A , α) (B , β) f equiv = (Glue Φ A B f , FibGlue {Φ = Φ} f equiv α β)

fstσFalse :
  ∀{ℓ}{Γ : Set ℓ}
  (A : Fib (res (Γ × Int) i=OI))
  (B : Fib (Γ × Int))
  (f : (x : Γ × Int)(u : [ i=OI x ]) → fst A (x , u) → fst B x)
  (equiv : (x : Γ × Int)(v : [ i=OI x ]) → Equiv' (f x v))
  (x : Γ)
  (b : fst B (x , I))
  → ---------------
  fst (fst (contr2ext (σ {Φ = i=OI} {A} {B} f (x , I) ∣ inr refl ∣) (equiv (x , I) ∣ inr refl ∣) b cofFalse ∅-elim))
    ≡ trivComp A I' ((x , I) , ∣ inr refl ∣) (fst (fst (equiv (x , I) ∣ inr refl ∣ b)))
abstract
 fstσFalse A B f equiv x b =

  proof:
  
      fst (fst (contr2ext (σ {Φ = i=OI} {A} {B} f xI u) ctrFib b cofFalse ∅-elim))
    
    ≡[ cong fst (contr2extFalse (σ {Φ = i=OI} {A} {B} f xI u) ctrFib b) ]≡
      
      fst (trivComp (Fiber (f xI u) , σ {Φ = i=OI} {A} {B} f xI u) I' b (fst (ctrFib b)))
    
    ≡[ fstFibΣid
         (reindex (fst A) (snd A) (λ _ → xI , u))
         (reindex (Path (fst B)) (FibPath (snd B)) (λ{ (_ , a) → (xI , f xI u a , b)}))
         I' id cofFalse ∅-elim (fst (equiv (x , I) ∣ inr refl ∣ b) , (λ ()))
      ]≡
       
      fst (snd A I' (λ _ → xI , u) cofFalse h (fst (fst (ctrFib b)) , h'))
    
    ≡[ cong (λ hh' →
         fst (snd A I' (λ _ → xI , u) cofFalse (fst hh') ((fst (fst (ctrFib b))) , (snd hh'))))
           (Σext (funext (λ ())) (funext (λ ())))
      ]≡
      
      trivComp A I' ((x , I) , ∣ inr refl ∣) (fst (fst (equiv (x , I) ∣ inr refl ∣ b)))
    
  qed
  
    where
    
      xI = (x , I)
      u : [ i=OI xI ]
      u = ∣ inr refl ∣
      ctrFib : Contr (Fiber (f xI u))
      ctrFib = equiv xI u
      
      h : ∅ → Int → fst A (xI , u)
      h = λ u i → fst (∅-elim {A = Int → Σ a ∈ fst A ((x , I) , ∣ inr refl ∣) , (f (x , I) ∣ inr refl ∣ a ~ b)} u i)
      hb : (u : ∅)(i : Int) → f (x , I) ∣ inr refl ∣ (h u i) ~ b
      hb = λ u i → snd (∅-elim {A = Int → Σ a ∈ fst A ((x , I) , ∣ inr refl ∣) , (f (x , I) ∣ inr refl ∣ a ~ b)} u i)
      h'' : (u : ∅) → ((h u I) , hb u I) ≡ fst (equiv (x , I) ∣ inr refl ∣ b)
      h'' = λ ()
      h' : (u : ∅) → h u I ≡ fst (fst (equiv (x , I) ∣ inr refl ∣ b))
      h' = λ u → cong {A = Σ a ∈ fst A ((x , I) , ∣ inr refl ∣) , (f (x , I) ∣ inr refl ∣ a ~ b)} fst (h'' u)

-- Given a fibration over Γ × Int we can compose from (x,O) to (x,I)
compOI  :
  ∀{ℓ}{Γ : Set ℓ}
  (B : Fib (Γ × Int))
  (x : Γ)
  (b : fst B (x , O))
  →
  fst B (x , I)
compOI (_ , β) x b = fst (β O' < x ,id> cofFalse ∅-elim (b , λ ()))

-- Just convincing Agda that a series of maps ∅ → X are all equal. Final result is:
--
-- unglue (compOI-in-Glue (glue a)) ≡ fst (empty extension of (compOI-in-B (f a)))
--
uaβhelper3' :
  ∀{ℓ}{Γ : Set ℓ}
  (A : Fib (res (Γ × Int) i=OI))
  (B : Fib (Γ × Int))
  (f : (x : Γ × Int)(u : [ i=OI x ]) → fst A (x , u) → fst B x)
  (equiv : (x : Γ × Int)(v : [ i=OI x ]) → Equiv' (f x v))
  (x : Γ)
  (a : fst A ((x , O) , ∣ inl refl ∣))
  → ---------------
  unglue' {Φ = i=OI} f (x , I) ∣ inr refl ∣
    (compOI (GlueFib i=OI A B f equiv) x
      (glue {Φ = i=OI} f (((x , O) , ∣ inl refl ∣))  a))
    ≡ fst (fst (contr2ext (σ {Φ = i=OI} {A} {B} f (x , I) ∣ inr refl ∣) (equiv (x , I) ∣ inr refl ∣)
       (compOI B x (f (x , O) ∣ inl refl ∣ a)) cofFalse ∅-elim))
abstract
 uaβhelper3' {_} {Γ} (A , α) (B , β) f e x a =
   cong (λ hs → fst (fst (contr2ext (σ {Φ = i=OI} {A , α} {B , β} f (x , I) ∣ inr refl ∣) (e (x , I) ∣ inr refl ∣)
     (fst (β O' < x ,id> cofFalse (fst hs) ((f (x , O) ∣ inl refl ∣ a) , (fst (snd hs)))))
     cofFalse (snd (snd hs))))) equal
  where
  ~a : [ cofFalse ] → (u : [ i=OI (x , I) ]) → A ((x , I) , u)
  ~a v = fst (∅-elim {A = (i : Int) → Glue i=OI A B f (x , i)} v I)
  ~b : [ cofFalse ] → B (x , I)
  ~b v = fst (snd (∅-elim {A = (i : Int) → Glue i=OI A B f (x , i)} v I))
  f~a=~b : (v : [ cofFalse ])(u : [ i=OI (x , I) ]) → f (x , I) u (~a v u) ≡ ~b v
  f~a=~b v = snd (snd (∅-elim {A = (i : Int) → Glue i=OI A B f (x , i)} v I))
  
  qb : [ cofFalse ] → Π (B ∘ < x ,id>)
  qb u i = fst (snd (∅-elim {A = (i : Int) → Glue i=OI A B f (x , i)} u i))

  h'' : (u : ∅) → (∅-elim {A = (i : Int) → Glue i=OI A B f (x , i)} u O) ≡ (glue {Φ = i=OI} f ((x , O) , ∣ inl refl ∣) a)
  h'' = λ ()
  h' : prf ((cofFalse , qb) ∙ O ↗ (f (x , O) ∣ inl refl ∣ a))
  h' = λ u → cong (λ g → fst (snd g)) (h'' u)
  
  b₁' : ⟦ b ∈ (B (x , I)) ∣ (cofFalse , qb) ∙ I ↗ b ⟧
  b₁' = β O' < x ,id> cofFalse qb (f (x , O) ∣ inl refl ∣  a , h')

  a₁'p' : (v : [ cofFalse ]) → Fiber (f (x , I) ∣ inr refl ∣) (fst b₁')
  a₁'p' v = (~a v ∣ inr refl ∣ , reflPath' (trans (snd b₁' v) (f~a=~b v ∣ inr refl ∣)))
  equal : _≡_ {A = Σ qb ∈ ([ cofFalse ] → Π (B ∘ < x ,id>)) , Σ h' ∈ (prf ((cofFalse , qb) ∙ O ↗ (f (x , O) ∣ inl refl ∣ a))) , (∅ →
    Fiber (f (x , I) ∣ inr refl ∣) (fst (β O' < x ,id> cofFalse qb (f (x , O) ∣ inl refl ∣ a , h'))))} (qb , h' , a₁'p') (∅-elim , (λ ()) , ∅-elim)
  equal = Σext (funext (λ ())) (Σext (funext (λ ())) (funext (λ ())))

-- Composing from O to I in Glue i=OI is equal to a trivial comp
-- from the f^-1 applied to a comp through B. In the end f^-1
-- will be id and the inner comp will also be trivial.
--
-- unglue (compOI-in-Glue (glue a)) ≡ trivComp (f^-1 (compOI-in-B (f a)))
--
uaβhelper3 :
  ∀{ℓ}{Γ : Set ℓ}
  (A : Fib (res (Γ × Int) i=OI))
  (B : Fib (Γ × Int))
  (f : (x : Γ × Int)(u : [ i=OI x ]) → fst A (x , u) → fst B x)
  (equiv : (x : Γ × Int)(v : [ i=OI x ]) → Equiv' (f x v))
  (x : Γ)
  (a : fst A ((x , O) , ∣ inl refl ∣))
  → ---------------
  unglue' {Φ = i=OI} f (x , I) ∣ inr refl ∣
    (compOI (GlueFib i=OI A B f equiv) x
      (glue {Φ = i=OI} f (((x , O) , ∣ inl refl ∣))  a))
    ≡ fst ((snd A) I' (λ _ → (x , I) , ∣ inr refl ∣) cofFalse ∅-elim
        (fst (fst (equiv (x , I) ∣ inr refl ∣ (compOI B x (f (x , O) ∣ inl refl ∣ a)))), λ ()))
abstract
 uaβhelper3 A B f equiv x a =
  trans
    (fstσFalse A B f equiv x
      (fst (snd B O' < x ,id> cofFalse ∅-elim ((f (x , O) ∣ inl refl ∣ a) , (λ ())))))
    (uaβhelper3' A B f equiv x a)
