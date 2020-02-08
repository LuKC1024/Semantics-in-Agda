open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)

module Named-TypeOn.Statics
  where

open import Identifiers
open import Types

mutual
  record Bind : Set where
    inductive
    constructor _⇒_
    field
      x : Id
      M : Term

  data Term : Set where
    var : Id → Term
    sole : Term
    ⟨_,_⟩ : Term → Term → Term
    car : Term → Term
    cdr : Term → Term
    inl : Term → Term
    inr : Term → Term
    case : (M : Term) → (B1 B2 : Bind) → Term
    ƛ : Bind → Term
    app : Term → Term → Term
    bind : Term → Bind → Term

infixl 30 _,_⦂_
infixl 29 _⊢_⦂_
infixr 30 _∷_

data Context : Set where
  ∅ : Context
  _,_⦂_ : (Γ : Context) → (x : Id) → (T : Type) → Context

_⦂_,_ : Id → Type → Context → Context
x' ⦂ T' , ∅ = ∅ , x' ⦂ T'
x' ⦂ T' , (Γ , x ⦂ T) = (x' ⦂ T' , Γ) , x ⦂ T

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
    _⇒_ : ∀ {Γ S T M}
      → (x : Id)
      → (W : (Γ , x ⦂ S) ⊢ M ⦂ T)
      → TypeBind Γ (x ⇒ M) S T

  data _⊢_⦂_ : Context → Term → Type → Set where
    var : ∀ {Γ x T}
      → (i : Γ ∋ x ⦂ T)
      -----
      → Γ ⊢ var x ⦂ T
  
    sole : ∀ {Γ} 
      -----
      → Γ ⊢ sole ⦂ `U
  
    ⟨_,_⟩ : ∀ {Γ M1 M2 T1 T2}
      → (W1 : Γ ⊢ M1 ⦂ T1)
      → (W2 : Γ ⊢ M2 ⦂ T2)
      -----
      → Γ ⊢ ⟨ M1 , M2 ⟩ ⦂ T1 `× T2
  
    car : ∀ {Γ M T1 T2}
      → (W : Γ ⊢ M ⦂ T1 `× T2)
      ----
      → Γ ⊢ car M ⦂ T1
  
    cdr : ∀ {Γ M T1 T2}
      → (W : Γ ⊢ M ⦂ T1 `× T2)
      ----
      → Γ ⊢ cdr M ⦂ T2
  
    inl : ∀ {Γ M T1 T2}
      → (W : Γ ⊢ M ⦂ T1)
      ----
      → Γ ⊢ inl M ⦂ T1 `+ T2
  
    inr : ∀ {Γ M T1 T2}
      → (W : Γ ⊢ M ⦂ T2)
      ----
      → Γ ⊢ inr M ⦂ T1 `+ T2
  
    case : ∀ {Γ M0 S1 S2 B1 B2 T}
      → (W0 : Γ ⊢ M0 ⦂ S1 `+ S2)
      → (W1 : TypeBind Γ B1 S1 T)
      → (W2 : TypeBind Γ B2 S2 T)
      → Γ ⊢ case M0 B1 B2 ⦂ T
  
    ƛ : ∀ {Γ B S T}
      → (W : TypeBind Γ B S T)
      ---
      → Γ ⊢ ƛ B ⦂ (S `→ T) 
  
    app : ∀ {Γ M1 T1 M2 T2}
      → (W1 : Γ ⊢ M1 ⦂ (T1 `→ T2))
      → (W2 : Γ ⊢ M2 ⦂ T1)
      ----
      → Γ ⊢ app M1 M2 ⦂ T2

    bind : ∀ {Γ M T1 B T2}
      → (W1 : Γ ⊢ M ⦂ T1)
      → (W2 : TypeBind Γ B T1 T2)
      ----
      → Γ ⊢ bind M B ⦂ T2
