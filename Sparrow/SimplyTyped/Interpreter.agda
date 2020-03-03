module Sparrow.SimplyTyped.Interpreter
  where

open import Types
open import Identifiers
open import Sparrow.Syntax
open import Sparrow.Semantics
open import Sparrow.SimplyTyped.Statics

open import Data.Unit
open import Data.Sum
open import Data.Product

⟦_⟧T : Type → Set
⟦ `⊤ ⟧T = ⊤
⟦ T₁ `+ T₂ ⟧T = ⟦ T₁ ⟧T ⊎ ⟦ T₂ ⟧T
⟦ T₁ `× T₂ ⟧T = ⟦ T₁ ⟧T × ⟦ T₂ ⟧T
⟦ T₁ `→ T₂ ⟧T = ⟦ T₁ ⟧T → ⟦ T₂ ⟧T

data Env : Context → Set where
  []    : Env ∅
  _,_←_ : ∀ {Γ T}
    → Env Γ
    → ∀ x
    → ⟦ T ⟧T
    → Env (Γ , x ⦂ T)

lookup : ∀ {Γ x T} → Env Γ → Γ ∋ x ⦂ T → ⟦ T ⟧T
lookup (env , x ← v) []        = v
lookup (env , x ← v) (¬p ∷ ⊢y) = lookup env ⊢y

match : {A B C : Set} → A ⊎ B → (A → C) → (B → C) → C
match (inj₁ x) kl kr = kl x
match (inj₂ y) kl kr = kr y

mutual
  evalB : ∀ {Γ B T₁ T₂} → Env Γ → TypeBind Γ B T₁ T₂ → ⟦ T₁ ⟧T → ⟦ T₂ ⟧T
  evalB env (x ⇒ ⊢M) = λ v → eval (env , x ← v) ⊢M 
  
  eval : ∀ {Γ A M} → Env Γ → Γ ⊢ M ⦂ A → ⟦ A ⟧T
  eval env `tt = tt
  eval env (var x) = lookup env x
  eval env (cons M₁ M₂) = eval env M₁ , eval env M₂
  eval env (car M) = proj₁ (eval env M) 
  eval env (cdr M) = proj₂ (eval env M) 
  eval env (inl M) = inj₁ (eval env M)
  eval env (inr M) = inj₂ (eval env M)
  eval env (case M ⊢B1 ⊢B2) = match (eval env M) (evalB env ⊢B1) (evalB env ⊢B2)
  eval env (lam ⊢B) = evalB env ⊢B
  eval env (app M₁ M₂) = (eval env M₁) (eval env M₂)
