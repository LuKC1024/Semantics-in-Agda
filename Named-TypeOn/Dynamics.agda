open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax)

module Named-TypeOn.Dynamics
  where

open import Types
open import Identifiers
open import Named-TypeOn.Statics

data Value : Term → Set where

  sole : Value sole

  ⟨_,_⟩ : ∀ {M1 M2}
    → (V1 : Value M1)
    → (V2 : Value M2)
    -----
    → Value ⟨ M1 , M2 ⟩

  inl : ∀ {M}
    → (V : Value M)
    ----
    → Value (inl M)

  inr : ∀ {M}
    → (V : Value M)
    ----
    → Value (inr M)

  ƛ : ∀ B
    ---
    → Value (ƛ B)

unvalue : ∀ {M} → Value M → Term
unvalue {M} V = M

data Frame : Set where
  ⟨-□-,_⟩ : (M2 : Term) → Frame
  ⟨_,-□-⟩ : {M1 : Term} → (V1 : Value M1) → Frame
  car-□ : Frame
  cdr-□ : Frame
  inl-□ : Frame
  inr-□ : Frame
  case-□ : (B1 B2 : Bind) → Frame
  app-□  : (M : Term) → Frame
  bind-□ : (B : Bind) → Frame

embed : Term → Frame → Term
embed M ⟨-□-, M2 ⟩ = ⟨ M , M2 ⟩
embed M ⟨ V1 ,-□-⟩ = ⟨ unvalue V1 , M ⟩
embed M car-□ = car M
embed M cdr-□ = cdr M
embed M inl-□ = inl M
embed M inr-□ = inr M
embed M (case-□ B1 B2) = case M B1 B2
embed M (app-□ M2) = app M M2
embed M (bind-□ B) = bind M B

-- substitution, close terms only
mutual
  subst-b : Term → Id → Bind → Bind
  subst-b M' x' (x ⇒ M) with Id=? x x'
  subst-b M' x' (x ⇒ M) | yes p = x ⇒ M
  subst-b M' x' (x ⇒ M) | no ¬p = x ⇒ [ M' / x' ] M

  [_/_] : Term → Id → Term → Term
  [ M' / x' ] (var x) with Id=? x x'
  [ M' / x' ] (var x) | yes p = M'
  [ M' / x' ] (var x) | no ¬p = var x
  [ M' / x' ] sole = sole
  [ M' / x' ] ⟨ M1 , M2 ⟩ = ⟨ [ M' / x' ] M1 , [ M' / x' ] M2 ⟩
  [ M' / x' ] (car M) = car ([ M' / x' ] M)
  [ M' / x' ] (cdr M) = cdr ([ M' / x' ] M)
  [ M' / x' ] (inl M) = inl ([ M' / x' ] M)
  [ M' / x' ] (inr M) = inr ([ M' / x' ] M)
  [ M' / x' ] (case M B1 B2) = case ([ M' / x' ] M) (subst-b M' x' B1) (subst-b M' x' B2)
  [ M' / x' ] (ƛ B) = ƛ (subst-b M' x' B)
  [ M' / x' ] (app M1 M2) = app ([ M' / x' ] M1) ([ M' / x' ] M2)
  [ M' / x' ] (bind M B) = bind ([ M' / x' ] M) (subst-b M' x' B)

do-bind : Term → Bind → Term
do-bind M' (x ⇒ M) = [ M' / x ] M

-- reduction of redex
data _⟶_ : Term → Term → Set where
  car⟨_,_⟩ : ∀ {M1 M2}
    → (V1 : Value M1)
    → (V2 : Value M2)
    ----
    → (car ⟨ M1 , M2 ⟩) ⟶ M1
  cdr⟨_,_⟩ : ∀ {M1 M2}
    → (V1 : Value M1)
    → (V2 : Value M2)
    ----
    → (cdr ⟨ M1 , M2 ⟩) ⟶ M2

  case-inl : ∀ {M}
    → (V0 : Value M)
    → ∀ B1 B2
    → case (inl M) B1 B2 ⟶ (do-bind M B1)

  case-inr : ∀ {M}
    → (V0 : Value M)
    → ∀ B1 B2
    → case (inr M) B1 B2 ⟶ (do-bind M B2)

  app-ƛ : ∀ B M
    → app (ƛ B) M ⟶ bind M B

  bind : ∀ {M}
    → (V : Value M)
    → (B : Bind)
    ----
    → bind M B ⟶ (do-bind M B)

ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ []         = []
ext ρ (x≢y ∷ ∋x) = x≢y ∷ (ρ ∋x)

rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
    ----------------------------------
  → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
rename ρ (var i)     = var (ρ i)
rename ρ sole        = sole
rename ρ ⟨ M1 , M2 ⟩ = ⟨ rename ρ M1 , rename ρ M2 ⟩
rename ρ (car M) = car (rename ρ M)
rename ρ (cdr M) = cdr (rename ρ M)
rename ρ (inl M) = inl (rename ρ M)
rename ρ (inr M) = inr (rename ρ M)
rename ρ (case M (x1 ⇒ M1) (x2 ⇒ M2))
  = case (rename ρ M) (x1 ⇒ rename (ext ρ) M1) (x2 ⇒ rename (ext ρ) M2)
rename ρ (ƛ (x ⇒ M))      = ƛ (x ⇒ rename (ext ρ) M)
rename ρ (app M1 M2)      = app (rename ρ M1) (rename ρ M2)
rename ρ (bind N (x ⇒ M)) = bind (rename ρ N) (x ⇒ (rename (ext ρ) M))

weaken : ∀ {Γ M A}
  → ∅ ⊢ M ⦂ A
    ----------
  → Γ ⊢ M ⦂ A
weaken {Γ} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → ∅ ∋ z ⦂ C
      ---------
    → Γ ∋ z ⦂ C
  ρ ()

drop : ∀ {Γ x M A B C}
  → (Γ , x ⦂ A) , x ⦂ B ⊢ M ⦂ C
    --------------------------
  → Γ , x ⦂ B ⊢ M ⦂ C
drop {Γ} {x} {M} {A} {B} {C} ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → (Γ , x ⦂ A) , x ⦂ B ∋ z ⦂ C
      -------------------------
    → Γ , x ⦂ B ∋ z ⦂ C
  ρ []             = []
  ρ (x≢x ∷ [])     = ⊥-elim (x≢x refl)
  ρ (z≢x ∷ _ ∷ ∋z) = z≢x ∷ ∋z

swap : ∀ {Γ x y M A B C}
  → ¬ (x ≡ y)
  → (Γ , y ⦂ B) , x ⦂ A ⊢ M ⦂ C
    --------------------------
  → (Γ , x ⦂ A) , y ⦂ B ⊢ M ⦂ C
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → (Γ , y ⦂ B) , x ⦂ A ∋ z ⦂ C
      --------------------------
    → (Γ , x ⦂ A) , y ⦂ B ∋ z ⦂ C
  ρ []               = x≢y ∷ []
  ρ (z≢x ∷ [])       = []
  ρ (z≢x ∷ z≢y ∷ ∋z) = z≢y ∷ z≢x ∷ ∋z

mutual
  subst-b✓ : ∀ {Γ M' B T1 T2 T3}
    → ∅ ⊢ M' ⦂ T1
    → (x' : Id) 
    → TypeBind (Γ , x' ⦂ T1) B T2 T3
    → TypeBind Γ (subst-b M' x' B) T2 T3
  subst-b✓ M' x' (x ⇒ M) with Id=? x x'
  subst-b✓ M' x' (x ⇒ M) | yes refl = x ⇒ drop M
  subst-b✓ M' x' (x ⇒ M) | no ¬p    = x ⇒ subst✓ M' x' (swap ¬p M)
  
  subst✓ : ∀ {Γ M' M T1 T2}
    → ∅ ⊢ M' ⦂ T1
    → (x' : Id) 
    → Γ , x' ⦂ T1 ⊢ M             ⦂ T2
    → Γ  ⊢ [ M' / x' ] M ⦂ T2
  subst✓ M' x' (var {x = x} i) with Id=? x x'
  subst✓ M' x' (var {x = _} [])       | yes refl = weaken M'
  subst✓ M' x' (var {x = _} (¬p ∷ i)) | yes refl = ⊥-elim (¬p refl)
  subst✓ M' x' (var {x = _} [])       | no ¬p'   = ⊥-elim (¬p' refl)
  subst✓ M' x' (var {x = x} (¬p ∷ i)) | no ¬p'   = var i
  subst✓ M' x' sole        = sole
  subst✓ M' x' ⟨ M1 , M2 ⟩ = ⟨ subst✓ M' x' M1 , subst✓ M' x' M2 ⟩
  subst✓ M' x' (car M)     = car (subst✓ M' x' M)
  subst✓ M' x' (cdr M)     = cdr (subst✓ M' x' M)
  subst✓ M' x' (inl M)     = inl (subst✓ M' x' M)
  subst✓ M' x' (inr M)     = inr (subst✓ M' x' M)
  subst✓ M' x' (case M B1 B2)
    = case (subst✓ M' x' M) (subst-b✓ M' x' B1) (subst-b✓ M' x' B2)
  subst✓ M' x' (ƛ B)       = ƛ (subst-b✓ M' x' B)
  subst✓ M' x' (app M1 M2) = app (subst✓ M' x' M1) (subst✓ M' x' M2)
  subst✓ M' x' (bind M B)  = bind (subst✓ M' x' M) (subst-b✓ M' x' B)

do-bind-safe : ∀ {M B T1 T2}
  → ∅ ⊢ M ⦂ T1
  → TypeBind ∅ B T1 T2
  → ∅ ⊢ do-bind M B ⦂ T2
do-bind-safe M' (x' ⇒ M) = subst✓ M' x' M

-- reduction of program
data _⟼_ : Term → Term → Set where

  `_ : ∀ {M M'}
    → (p : M ⟶ M')
    → M ⟼ M'
  
  _[_] : ∀ {M M'}
    → (F : Frame)
    → (p : M ⟼ M')
    → (embed M F) ⟼ (embed M' F)

type-safety : ∀ {T} M
  → ∅ ⊢ M ⦂ T
  → (Value M) ⊎ ∃[ M' ](M ⟼ M' × ∅ ⊢ M' ⦂ T)
type-safety (var x) (var ())
type-safety sole sole = inj₁ sole
type-safety ⟨ M1 , M2 ⟩ ⟨ ✓M1 , ✓M2 ⟩
  with type-safety M1 ✓M1
...  | inj₂ (M1' , M1⟼M1' , ✓M1') = inj₂ (_ , ⟨-□-, M2 ⟩ [ M1⟼M1' ] , ⟨ ✓M1' , ✓M2 ⟩)
...  | inj₁ vM1
  with type-safety M2 ✓M2
...  | inj₁ vM2 = inj₁ ⟨ vM1 , vM2 ⟩
...  | inj₂ (M2' , M2⟼M2' , ✓M2') = inj₂ (_ , ⟨ vM1 ,-□-⟩ [ M2⟼M2' ] , ⟨ ✓M1 , ✓M2' ⟩)
type-safety (car M) (car ✓M)
  with type-safety M ✓M
...  | inj₂ (M' , M⟼M' , ✓M') = inj₂ (car M' , (car-□)[ M⟼M' ] , car ✓M')
...  | inj₁ vM
  with M           | vM            | ✓M
...  | sole        | sole          | ()
...  | ⟨ M1 , M2 ⟩ | ⟨ vM1 , vM2 ⟩ | ⟨ ✓M1 , ✓M2 ⟩ = inj₂ (M1 , (` car⟨ vM1 , vM2 ⟩) , ✓M1)
...  | inl _       | inl _         | ()
...  | inr _       | inr _         | ()
...  | ƛ _         | ƛ _           | ()
type-safety (cdr M) (cdr ✓M)
  with type-safety M ✓M
...  | inj₂ (M' , M⟼M' , ✓M') = inj₂ (cdr M' , (cdr-□)[ M⟼M' ] , cdr ✓M')
...  | inj₁ vM
  with M           | vM            | ✓M
...  | sole        | sole          | ()
...  | ⟨ M1 , M2 ⟩ | ⟨ vM1 , vM2 ⟩ | ⟨ ✓M1 , ✓M2 ⟩ = inj₂ (M2 , (` cdr⟨ vM1 , vM2 ⟩) , ✓M2)
...  | inl _       | inl _         | ()
...  | inr _       | inr _         | ()
...  | ƛ _         | ƛ _           | ()
type-safety (inl M) (inl ✓M)
  with type-safety M ✓M
...  | inj₁ vM = inj₁ (inl vM)
...  | inj₂ (M' , M⟼M' , ✓M') = inj₂ (inl M' , (inl-□ [ M⟼M' ]) , inl ✓M')
type-safety (inr M) (inr ✓M)
  with type-safety M ✓M
...  | inj₁ vM = inj₁ (inr vM)
...  | inj₂ (M' , M⟼M' , ✓M') = inj₂ (inr M' , (inr-□ [ M⟼M' ]) , inr ✓M')
type-safety (case M B1 B2) (case ✓M ✓B1 ✓B2) with type-safety M ✓M
type-safety (case M B1 B2) (case ✓M ✓B1 ✓B2) | inj₂ (M' , M⟼M' , ✓M') = inj₂ (case M' B1 B2 , (case-□ B1 B2)[ M⟼M' ] , case ✓M' ✓B1 ✓B2)
type-safety (case (var _) B1 B2)      (case (var i)  ✓B1 ✓B2)        | inj₁ ()
type-safety (case (car _) B1 B2)      (case (car ✓M) ✓B1 ✓B2)        | inj₁ ()
type-safety (case (cdr _) B1 B2)      (case (cdr ✓M) ✓B1 ✓B2)        | inj₁ ()
type-safety (case (inl M) B1 B2)      (case (inl ✓M) ✓B1 ✓B2)        | inj₁ (inl vM) = inj₂ (do-bind M B1 , (` case-inl vM B1 B2) , do-bind-safe ✓M ✓B1)
type-safety (case (inr M) B1 B2)      (case (inr ✓M) ✓B1 ✓B2)        | inj₁ (inr vM) = inj₂ (do-bind M B2 , (` case-inr vM B1 B2) , do-bind-safe ✓M ✓B2)
type-safety (case (case _ _ _) B1 B2) (case (case ✓M W1 W2) ✓B1 ✓B2) | inj₁ ()
type-safety (case (app _ _)    B1 B2) (case (app ✓M ✓M₁)    ✓B1 ✓B2) | inj₁ ()
type-safety (case (bind _ _)   B1 B2) (case (bind ✓M W2)    ✓B1 ✓B2) | inj₁ ()
type-safety (ƛ B) (ƛ ✓B) = inj₁ (ƛ B)
type-safety (app M1 M2) (app ✓M1 ✓M2) with type-safety M1 ✓M1
type-safety (app M1 M2) (app ✓M1 ✓M2) | inj₂ (M1' , M1⟼M1' , ✓M1') = inj₂ (app M1' M2 , (app-□ M2 [ M1⟼M1' ]) , app ✓M1' ✓M2)
type-safety (app .(var _) M2)      (app (var i)   ✓M2)        | inj₁ ()
type-safety (app .(car _) M2)      (app (car ✓M1) ✓M2)        | inj₁ ()
type-safety (app .(cdr _) M2)      (app (cdr ✓M1) ✓M2)        | inj₁ ()
type-safety (app .(case _ _ _) M2) (app (case ✓M1 W1 W2) ✓M2) | inj₁ ()
type-safety (app .(ƛ B) M2)        (app (ƛ ✓B)           ✓M2) | inj₁ (ƛ B) = inj₂ (bind M2 B , (` app-ƛ B M2) , bind ✓M2 ✓B)
type-safety (app .(app _ _) M2)    (app (app ✓M1 ✓M3)    ✓M2) | inj₁ ()
type-safety (app .(bind _ _) M2)   (app (bind ✓M1 W2)    ✓M2) | inj₁ ()
type-safety (bind M B) (bind ✓M ✓B)
  with type-safety M ✓M
...  | inj₁ vM = inj₂ (do-bind M B , (` bind vM B) , do-bind-safe ✓M ✓B)
...  | inj₂ (M' , M⟼M' , ✓M') = inj₂ (bind M' B , (bind-□ B)[ M⟼M' ] , bind ✓M' ✓B)
