open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Chain

module Sparrow.Semantics
  where

open import Identifiers
open import Sparrow.Syntax

data Value : Term → Set where

  `tt : Value `tt

  cons : ∀ {M1 M2}
    → (V1 : Value M1)
    → (V2 : Value M2)
    -----
    → Value (cons M1 M2)

  inl : ∀ {M}
    → (V : Value M)
    ----
    → Value (inl M)

  inr : ∀ {M}
    → (V : Value M)
    ----
    → Value (inr M)

  lam : ∀ B
    ---
    → Value (lam B)

unvalue : ∀ {M} → Value M → Term
unvalue {M} V = M

data Frame : Set where
  cons-□ : (M2 : Term) → Frame
  cons_□ : {M1 : Term} → (V1 : Value M1) → Frame
  car-□ : Frame
  cdr-□ : Frame
  inl-□ : Frame
  inr-□ : Frame
  case-□ : (B1 B2 : Bind) → Frame
  app-□  : (M : Term) → Frame
  app_□  : ∀ {M} → (V : Value M) → Frame

plugF : Term → Frame → Term
plugF M (cons-□ N) = cons M N
plugF M (cons V □) = cons (unvalue V) M
plugF M (car-□) = car M
plugF M (cdr-□) = cdr M
plugF M (inl-□) = inl M
plugF M (inr-□) = inr M
plugF M (case-□ B1 B2) = case M B1 B2
plugF M (app-□ N) = app M N
plugF M (app V □) = app (unvalue V) M

EContext : Set
EContext = List Frame

plug : Term → EContext → Term
plug M []      = M
plug M (F ∷ Fs) = plug (plugF M F) Fs

lem-plug : ∀ M E1 E2
  → plug (plug M E1) E2 ≡ plug M (E1 ++ E2)
lem-plug M []       Gs = refl
lem-plug M (F ∷ Fs) Gs = lem-plug (plugF M F) Fs Gs

mutual
  [_/_]B : Term → Id → Bind → Bind
  [_/_]B M' x' (x ⇒ M) with Id=? x x'
  [_/_]B M' x' (x ⇒ M) | yes p = x ⇒ M
  [_/_]B M' x' (x ⇒ M) | no ¬p = x ⇒ [ M' / x' ] M

  [_/_] : Term → Id → Term → Term
  [ M' / x' ] (var x) with Id=? x x'
  [ M' / x' ] (var x) | yes p = M'
  [ M' / x' ] (var x) | no ¬p = var x
  [ M' / x' ] `tt = `tt
  [ M' / x' ] (cons M1 M2) = cons ([ M' / x' ] M1) ([ M' / x' ] M2)
  [ M' / x' ] (car M) = car ([ M' / x' ] M)
  [ M' / x' ] (cdr M) = cdr ([ M' / x' ] M)
  [ M' / x' ] (inl M) = inl ([ M' / x' ] M)
  [ M' / x' ] (inr M) = inr ([ M' / x' ] M)
  [ M' / x' ] (case M B1 B2) = case ([ M' / x' ] M) ([ M' / x' ]B B1) ([ M' / x' ]B B2)
  [ M' / x' ] (lam B) = lam ([ M' / x' ]B B)
  [ M' / x' ] (app M1 M2) = app ([ M' / x' ] M1) ([ M' / x' ] M2)

do-bind : Term → Bind → Term
do-bind M' (x ⇒ M) = [ M' / x ] M

-- reduction of redex
data _⟶_ : Term → Term → Set where
  ProjL : ∀ {M1 M2}
    → (V1 : Value M1)
    → (V2 : Value M2)
    ----
    → (car (cons M1 M2)) ⟶ M1
  ProjR : ∀ {M1 M2}
    → (V1 : Value M1)
    → (V2 : Value M2)
    ----
    → (cdr (cons M1 M2)) ⟶ M2

  CaseL : ∀ {M}
    → (V : Value M)
    → ∀ {B1 B2}
    → case (inl M) B1 B2 ⟶ (do-bind M B1)

  CaseR : ∀ {M}
    → (V : Value M)
    → ∀ {B1 B2}
    → case (inr M) B1 B2 ⟶ (do-bind M B2)

  Beta : ∀ {B M}
    → (V : Value M)
    → app (lam B) M ⟶ (do-bind M B)

⟶lft : ∀ {M N} → M ⟶ N → Term
⟶lft {M} {N} p = M

⟶rht : ∀ {M N} → M ⟶ N → Term
⟶rht {M} {N} p = N

data _⟼_ : Term → Term → Set where  
  ⟨_,_⟩ : ∀ {M M'}
    → (p : M ⟶ M')
    → (E : EContext)
    → (plug M E) ⟼ (plug M' E)

⟪_,_⟫ : ∀ {M M'}
  → M ⟼ M'
  → ∀ E
  → plug M E ⟼ plug M' E
⟪ ⟨ p , E' ⟩ , E ⟫
  rewrite lem-plug (⟶lft p) E' E | lem-plug (⟶rht p) E' E
  = ⟨ p , E' ++ E ⟩
