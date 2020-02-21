module Sparrow.SimplyTyped.Statics
  where

-- This module defines what kinds of programs are well-formed statically.

open import Identifiers
open import Sparrow.Syntax
open import Types
open import Chain

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)

infixl 30 _,_⦂_
infixl 29 _⊢_⦂_
infixr 30 _∷_

Context : Set
Context = List (Id × Type)

-- alternative constructor of context

pattern ∅           = []
pattern _,_⦂_ Γ x T = (x , T) ∷ Γ

data _∋_⦂_ : Context → Id → Type → Set where
  [] : ∀ {Γ x T}
    -----
    → (Γ , x ⦂ T) ∋ x ⦂ T
  _∷_ : ∀ {Γ x x' T T'}
    → (¬p : ¬ x ≡ x')
    → (xs : Γ ∋ x ⦂ T)
    → (Γ , x' ⦂ T') ∋ x ⦂ T

lem-unique-lookup : ∀ {Γ x T1 T2}
  → Γ ∋ x ⦂ T1
  → Γ ∋ x ⦂ T2
  -----
  → T1 ≡ T2
lem-unique-lookup [] [] = refl
lem-unique-lookup [] (¬p ∷ ys) = ⊥-elim (¬p refl)
lem-unique-lookup (¬p ∷ xs) [] = ⊥-elim (¬p refl)
lem-unique-lookup (¬p ∷ xs) (¬q ∷ ys) = lem-unique-lookup xs ys

mutual
  data TypeBind : Context → Bind → Type → Type → Set where
    _⇒_ : ∀ {Γ S T M} x
      → (⊢M : (Γ , x ⦂ S) ⊢ M ⦂ T)
      → TypeBind Γ (x ⇒ M) S T

  data _⊢_⦂_ : Context → Term → Type → Set where
    var : ∀ {Γ x T}
      → (i : Γ ∋ x ⦂ T)
      -----
      → Γ ⊢ var x ⦂ T
  
    `tt : ∀ {Γ} 
      -----
      → Γ ⊢ `tt ⦂ `⊤
  
    cons : ∀ {Γ M1 M2 T1 T2}
      → (⊢M1 : Γ ⊢ M1 ⦂ T1)
      → (⊢M2 : Γ ⊢ M2 ⦂ T2)
      -----
      → Γ ⊢ cons M1 M2 ⦂ T1 `× T2
  
    car : ∀ {Γ M T1 T2}
      → (⊢M : Γ ⊢ M ⦂ T1 `× T2)
      ----
      → Γ ⊢ car M ⦂ T1
  
    cdr : ∀ {Γ M T1 T2}
      → (⊢M : Γ ⊢ M ⦂ T1 `× T2)
      ----
      → Γ ⊢ cdr M ⦂ T2
  
    inl : ∀ {Γ M T1 T2}
      → (⊢M : Γ ⊢ M ⦂ T1)
      ----
      → Γ ⊢ inl M ⦂ T1 `+ T2
  
    inr : ∀ {Γ M T1 T2}
      → (⊢M : Γ ⊢ M ⦂ T2)
      ----
      → Γ ⊢ inr M ⦂ T1 `+ T2
  
    case : ∀ {Γ M S1 S2 B1 B2 T}
      → (⊢M : Γ ⊢ M ⦂ S1 `+ S2)
      → (⊢B1 : TypeBind Γ B1 S1 T)
      → (⊢B2 : TypeBind Γ B2 S2 T)
      → Γ ⊢ case M B1 B2 ⦂ T
  
    lam : ∀ {Γ B S T}
      → (⊢M : TypeBind Γ B S T)
      ---
      → Γ ⊢ lam B ⦂ (S `→ T) 
  
    app : ∀ {Γ M1 T1 M2 T2}
      → (⊢M1 : Γ ⊢ M1 ⦂ (T1 `→ T2))
      → (⊢M2 : Γ ⊢ M2 ⦂ T1)
      ----
      → Γ ⊢ app M1 M2 ⦂ T2
