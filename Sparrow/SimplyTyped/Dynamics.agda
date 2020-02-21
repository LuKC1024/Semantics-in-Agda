open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Chain

module Sparrow.SimplyTyped.Dynamics
  where

open import Types
open import Identifiers
open import Sparrow.Syntax
open import Sparrow.Semantics
open import Sparrow.SimplyTyped.Statics

ext : ∀ {Γ Δ}
  → (∀ {x A}     →         Γ ∋ x ⦂ A →         Δ ∋ x ⦂ A)
    -----------------------------------------------------
  → (∀ {x y A B} → Γ , y ⦂ B ∋ x ⦂ A → Δ , y ⦂ B ∋ x ⦂ A)
ext ρ []         = []
ext ρ (x≢y ∷ ∋x) = x≢y ∷ (ρ ∋x)

mutual
  renameB : ∀ {Γ Δ}
    → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
      ----------------------------------
    → (∀ {M A B} → TypeBind Γ M A B → TypeBind Δ M A B)
  renameB ρ (x ⇒ ⊢M) = x ⇒ rename (ext ρ) ⊢M
  
  rename : ∀ {Γ Δ}
    → (∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ x ⦂ A)
      ----------------------------------
    → (∀ {M A} → Γ ⊢ M ⦂ A → Δ ⊢ M ⦂ A)
  rename ρ `tt     = `tt
  rename ρ (var i) = var (ρ i)
  rename ρ (inl ⊢M) = inl (rename ρ ⊢M)
  rename ρ (inr ⊢M) = inr (rename ρ ⊢M)
  rename ρ (case ⊢M ⊢B1 ⊢B2) = case (rename ρ ⊢M) (renameB ρ ⊢B1) (renameB ρ ⊢B2)
  rename ρ (cons ⊢M1 ⊢M2) = cons (rename ρ ⊢M1) (rename ρ ⊢M2)
  rename ρ (car ⊢M) = car (rename ρ ⊢M)
  rename ρ (cdr ⊢M) = cdr (rename ρ ⊢M)
  rename ρ (lam ⊢B)      = lam (renameB ρ ⊢B)
  rename ρ (app ⊢M1 ⊢M2) = app (rename ρ ⊢M1) (rename ρ ⊢M2)

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
  ⊢[_/_]B_ : ∀ {Γ M' B T1 T2 T3}
    → ∅ ⊢ M' ⦂ T1
    → (x' : Id) 
    → TypeBind (Γ , x' ⦂ T1) B T2 T3
    → TypeBind Γ ([ M' / x' ]B B) T2 T3
  ⊢[ ⊢M' / x' ]B (x ⇒ M) with Id=? x x'
  ⊢[ ⊢M' / x' ]B (x ⇒ M) | yes refl = x ⇒ drop M
  ⊢[ ⊢M' / x' ]B (x ⇒ M) | no ¬p    = x ⇒ (⊢[ ⊢M' / x' ] swap ¬p M)
  
  ⊢[_/_]_ : ∀ {Γ M' M T1 T2}
    → ∅ ⊢ M' ⦂ T1
    → (x' : Id) 
    → Γ , x' ⦂ T1 ⊢ M             ⦂ T2
    → Γ  ⊢ [ M' / x' ] M ⦂ T2
  ⊢[ ⊢M' / x' ] `tt = `tt
  ⊢[ ⊢M' / x' ] (var {x = x} i) with Id=? x x'
  ⊢[ ⊢M' / x' ] (var {x = _} [])       | yes refl = weaken ⊢M'
  ⊢[ ⊢M' / x' ] (var {x = _} (¬p ∷ i)) | yes refl = ⊥-elim (¬p refl)
  ⊢[ ⊢M' / x' ] (var {x = _} [])       | no ¬p'   = ⊥-elim (¬p' refl)
  ⊢[ ⊢M' / x' ] (var {x = x} (¬p ∷ i)) | no ¬p'   = var i
  ⊢[ ⊢M' / x' ] (cons ⊢M1 ⊢M2) = cons (⊢[ ⊢M' / x' ] ⊢M1) (⊢[ ⊢M' / x' ] ⊢M2)
  ⊢[ ⊢M' / x' ] (car ⊢M) = car (⊢[ ⊢M' / x' ] ⊢M)
  ⊢[ ⊢M' / x' ] (cdr ⊢M) = cdr (⊢[ ⊢M' / x' ] ⊢M)
  ⊢[ ⊢M' / x' ] (inl ⊢M) = inl (⊢[ ⊢M' / x' ] ⊢M)
  ⊢[ ⊢M' / x' ] (inr ⊢M) = inr (⊢[ ⊢M' / x' ] ⊢M)
  ⊢[ ⊢M' / x' ] (case ⊢M ⊢B1 ⊢B2)
    = case (⊢[ ⊢M' / x' ] ⊢M) (⊢[ ⊢M' / x' ]B ⊢B1) (⊢[ ⊢M' / x' ]B ⊢B2)
  ⊢[ ⊢M' / x' ] (lam ⊢B)     = lam (⊢[ ⊢M' / x' ]B ⊢B)
  ⊢[ ⊢M' / x' ] (app ⊢M1 ⊢M2) = app (⊢[ ⊢M' / x' ] ⊢M1) (⊢[ ⊢M' / x' ] ⊢M2)

⊢do-bind : ∀ {M B T1 T2}
  → ∅ ⊢ M ⦂ T1
  → TypeBind ∅ B T1 T2
  → ∅ ⊢ do-bind M B ⦂ T2
⊢do-bind M' (x' ⇒ M) = ⊢[ M' / x' ] M


safety : ∀ {T} M
  → ∅ ⊢ M ⦂ T
  → ∃[ M' ](M ⟼ M' × ∅ ⊢ M' ⦂ T) ⊎ (Value M)
safety `tt `tt = inj₂ `tt
safety (cons M N) (cons ⊢M ⊢N) with safety M ⊢M
safety (cons M N) (cons ⊢M ⊢N) | inj₁ (M̂ , pM , ⊢M̂)          = inj₁ (cons M̂ N , ⟪ pM , [ cons-□ N ] ⟫ , cons ⊢M̂ ⊢N)
safety (cons M N) (cons ⊢M ⊢N) | inj₂ V with safety N ⊢N
safety (cons M N) (cons ⊢M ⊢N) | inj₂ V | inj₁ (N̂ , pN , ⊢N̂) = inj₁ (cons M N̂ , ⟪ pN , [ cons V □ ] ⟫ , cons ⊢M ⊢N̂)
safety (cons M N) (cons ⊢M ⊢N) | inj₂ V | inj₂ U             = inj₂ (cons V U)
safety (car M) (car ⊢M) with safety M ⊢M
safety (car M)            (car ⊢M)             | inj₁ (M̂ , pM , ⊢M̂) = inj₁ (car M̂ , ⟪ pM , [ car-□ ] ⟫   , car ⊢M̂)
safety (car (cons M1 M2)) (car (cons ⊢M1 ⊢M2)) | inj₂ (cons V1 V2)  = inj₁ (M1 , ⟨ ProjL V1 V2 , [] ⟩ , ⊢M1)
safety (cdr M) (cdr ⊢M) with safety M ⊢M
safety (cdr M)            (cdr ⊢M)             | inj₁ (M̂ , pM , ⊢M̂) = inj₁ (cdr M̂ , ⟪ pM , [ cdr-□ ] ⟫   , cdr ⊢M̂)
safety (cdr (cons M1 M2)) (cdr (cons ⊢M1 ⊢M2)) | inj₂ (cons V1 V2)  = inj₁ (M2 , ⟨ ProjR V1 V2 , [] ⟩ , ⊢M2)
safety (inl M) (inl ⊢M) with safety M ⊢M
safety (inl M) (inl ⊢M) | inj₁ (M̂ , pM , ⊢M̂) = inj₁ (inl M̂ , ⟪ pM , [ inl-□ ] ⟫ , inl ⊢M̂)
safety (inl M) (inl ⊢M) | inj₂ V             = inj₂ (inl V)
safety (inr M) (inr ⊢M) with safety M ⊢M
safety (inr M) (inr ⊢M) | inj₁ (M̂ , pM , ⊢M̂) = inj₁ (inr M̂ , ⟪ pM , [ inr-□ ] ⟫ , inr ⊢M̂)
safety (inr M) (inr ⊢M) | inj₂ V             = inj₂ (inr V)
safety (case M B1 B2) (case ⊢M ⊢B1 ⊢B2) with safety M ⊢M
safety (case M B1 B2) (case ⊢M ⊢B1 ⊢B2)             | inj₁ (M̂ , pM , ⊢M̂) = inj₁ (_ , ⟪ pM , [ case-□ B1 B2 ] ⟫ , case ⊢M̂ ⊢B1 ⊢B2)
safety (case (inl M) B1 B2) (case (inl ⊢M) ⊢B1 ⊢B2) | inj₂ (inl V)       = inj₁ (_ , ⟨ CaseL V , [] ⟩ , ⊢do-bind ⊢M ⊢B1)
safety (case (inr M) B1 B2) (case (inr ⊢M) ⊢B1 ⊢B2) | inj₂ (inr V)       = inj₁ (_ , ⟨ CaseR V , [] ⟩ , ⊢do-bind ⊢M ⊢B2)
safety (lam B) (lam ⊢B) = inj₂ (lam B)
safety (app M N) (app ⊢M ⊢N) with safety M ⊢M
safety (app M N) (app ⊢M ⊢N)             | inj₁ (M̂ , pM , ⊢M̂)                = inj₁ (_ , ⟪ pM , [ app-□ N ] ⟫  , (app ⊢M̂ ⊢N))
safety (app (lam B) N) (app (lam ⊢B) ⊢N) | inj₂ (lam B) with safety N ⊢N
safety (app (lam B) N) (app (lam ⊢B) ⊢N) | inj₂ (lam B) | inj₁ (N̂ , pN , ⊢N̂) = inj₁ (_ , ⟪ pN , [ app (lam B) □ ] ⟫ , (app (lam ⊢B) ⊢N̂))
safety (app (lam B) N) (app (lam ⊢B) ⊢N) | inj₂ (lam B) | inj₂ U             = inj₁ (_ , ⟨ Beta U , [] ⟩ , ⊢do-bind ⊢N ⊢B)
