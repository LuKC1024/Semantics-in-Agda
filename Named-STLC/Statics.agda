open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)

module Named-STLC.Statics
  (Id : Set)
  (Id=? : (x y : Id) → Dec (x ≡ y))
  where

open import Types

data Context : Set where
  ∙ : Context
  _,_⦂_ : (Γ : Context) → (x : Id) → (A : Type) → Context

data _⦂_∈_ (x : Id) (A : Type) : Context → Set where
  nil : ∀ {Γ}
    -----
    → x ⦂ A ∈ (Γ , x ⦂ A)
  _∷_ : ∀ {Γ y B}
    → (¬p : ¬ x ≡ y)
    → (xs : x ⦂ A ∈ Γ)
    → x ⦂ A ∈ (Γ , y ⦂ B)

lem-unique-lookup : ∀ {Γ x A B}
  → x ⦂ A ∈ Γ
  → x ⦂ B ∈ Γ
  -----
  → A ≡ B
lem-unique-lookup nil nil = refl
lem-unique-lookup nil (¬p ∷ ys) = ⊥-elim (¬p refl)
lem-unique-lookup (¬p ∷ xs) nil = ⊥-elim (¬p refl)
lem-unique-lookup (¬p ∷ xs) (¬q ∷ ys) = lem-unique-lookup xs ys

data _⊢_ : Context → Type → Set where
  var : ∀ {Γ x A}
    → (i : x ⦂ A ∈ Γ)
    -----
    → Γ ⊢ A

  sole : ∀ {Γ}
    -----
    → Γ ⊢ Trivial

  cons : ∀ {Γ A1 A2}
    → (M1 : Γ ⊢ A1)
    → (M2 : Γ ⊢ A2)
    -----
    → Γ ⊢ Pair A1 A2

  car : ∀ {Γ A1 A2}
    → (M : Γ ⊢ Pair A1 A2)
    ----
    → Γ ⊢ A1

  cdr : ∀ {Γ A1 A2}
    → (M : Γ ⊢ Pair A1 A2)
    ----
    → Γ ⊢ A2

  left : ∀ {Γ A1 A2}
    → (M : Γ ⊢ A1)
    ----
    → Γ ⊢ Either A1 A2

  right : ∀ {Γ A1 A2}
    → (M : Γ ⊢ A2)
    ----
    → Γ ⊢ Either A1 A2

  match_[_⇒_][_⇒_] : ∀ {Γ A1 A2 A3}
    → (M0 : Γ ⊢ Either A1 A2)
    → (x1 : Id)
    → (M1 : (Γ , x1 ⦂ A1) ⊢ A3)
    → (x2 : Id)
    → (M2 : (Γ , x2 ⦂ A2) ⊢ A3)
    → Γ ⊢ A3

  lambda_⦂_∙_ : ∀ {Γ A2}
    → ∀ x A1
    → (Γ , x ⦂ A1) ⊢ A2
    ---
    → Γ ⊢ (A1 ⇒ A2)

  app : ∀ {Γ A1 A2}
    → (M1 : Γ ⊢ (A1 ⇒ A2))
    → (M2 : Γ ⊢ A1)
    ----
    → Γ ⊢ A2
