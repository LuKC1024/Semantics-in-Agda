open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)

module Named-STLC.Dynamics
  (Id : Set)
  (Id=? : (x y : Id) → Dec (x ≡ y))
  where

open import Types
open import Named-STLC.Statics Id Id=?

data Value : ∀ {A} → ∙ ⊢ A → Set where

  sole : Value sole

  cons : ∀ {A1 A2}
    → {M1 : ∙ ⊢ A1}
    → (V1 : Value M1)
    → {M2 : ∙ ⊢ A2}
    → (V2 : Value M2)
    -----
    → Value (cons M1 M2)

  left : ∀ {A1 A2}
    → {M : ∙ ⊢ A1}
    → (V : Value M)
    ----
    → Value (left {A2 = A2} M)

  right : ∀ {A1 A2}
    → {M : ∙ ⊢ A2}
    → (V : Value M)
    ----
    → Value (right {A1 = A1} M)

  lambda : ∀ {A2}
    → ∀ x A1
    → (M : (∙ , x ⦂ A1) ⊢ A2)
    ---
    → Value (lambda x ⦂ A1 ∙ M)

unvalue : ∀ {A} → {M : ∙ ⊢ A} → Value M → ∙ ⊢ A
unvalue {M = M} V = M

data ⊢_↣_ : Type → Type → Set where

  cons-□ : ∀ {A1 A2}
    → (M2 : ∙ ⊢ A2)
    -----
    → ⊢ A1 ↣ Pair A1 A2

  cons_□ : ∀ {A1 A2}
    → {M1 : ∙ ⊢ A1}
    → (V1 : Value M1)
    -----
    → ⊢ A2 ↣ Pair A1 A2

  car : ∀ {A1 A2}
    ----
    → ⊢ Pair A1 A2 ↣ A1

  cdr : ∀ {A1 A2}
    ----
    → ⊢ Pair A1 A2 ↣ A2

  left : ∀ {A1 A2}
    ----
    → ⊢ A1 ↣ Either A1 A2

  right : ∀ {A1 A2}
    ----
    → ⊢ A2 ↣ Either A1 A2

  match-□-[_⇒_][_⇒_] : ∀ {A1 A2 A3}
    → (x1 : Id)
    → (M1 : (∙ , x1 ⦂ A1) ⊢ A3)
    → (x2 : Id)
    → (M2 : (∙ , x2 ⦂ A2) ⊢ A3)
    → ⊢ Either A1 A2 ↣ A3

  app-□ : ∀ {A1 A2}
    → (M2 : ∙ ⊢ A1)
    ----
    → ⊢ (A1 ⇒ A2) ↣ A2

  app_□ : ∀ {A1 A2}
    → {M1 : ∙ ⊢ (A1 ⇒ A2)}
    → (V1 : Value M1)
    ----
    → ⊢ A1 ↣ A2

[_]_ : ∀ {A1 A2} → ∙ ⊢ A1 → ⊢ A1 ↣ A2 → ∙ ⊢ A2
[ M ] cons-□ M2 = cons M M2
[ M ] cons V1 □ = cons (unvalue V1) M
[ M ] car = car M
[ M ] cdr = cdr M
[ M ] left = left M
[ M ] right = right M
[ M ] match-□-[ x1 ⇒ M1 ][ x2 ⇒ M2 ] = match M [ x1 ⇒ M1 ][ x2 ⇒ M2 ]
[ M ] app-□ M2 = app M M2
[ M ] app V1 □ = app (unvalue V1) M

_⦂_,_ : Id → Type → Context → Context
x' ⦂ A' , ∙ = ∙ , x' ⦂ A'
x' ⦂ A' , (Γ , x ⦂ A) = (x' ⦂ A' , Γ) , x ⦂ A

embed-var : ∀ {Γ x A}
  → x ⦂ A ∈ Γ
  → ∀ {x' A'}
  → x ⦂ A ∈ (x' ⦂ A' , Γ)
embed-var nil = nil
embed-var (¬p ∷ i) = ¬p ∷ embed-var i

embed : ∀ {Γ A}
  → Γ ⊢ A
  → ∀ {x' A'}
  → (x' ⦂ A' , Γ) ⊢ A
embed (var i) = var (embed-var i)
embed sole = sole
embed (cons M1 M2) = cons (embed M1) (embed M2)
embed (car M) = car (embed M)
embed (cdr M) = cdr (embed M)
embed (left M) = left (embed M)
embed (right M) = right (embed M)
embed (match M0 [ x1 ⇒ M1 ][ x2 ⇒ M2 ]) = match embed M0 [ x1 ⇒ embed M1 ][ x2 ⇒ embed M2 ]
embed (lambda x ⦂ A1 ∙ M) = lambda x ⦂ A1 ∙ (embed M)
embed (app M1 M2) = app (embed M1) (embed M2)

_++_ : Context → Context → Context
∙ ++ ys = ys
(xs , x ⦂ A) ++ ys = xs ++ (x ⦂ A , ys)

lem-++-right-cons : ∀ Γ1 Γ2 x A →
  (Γ1 ++ (Γ2 , x ⦂ A)) ≡ ((Γ1 ++ Γ2) , x ⦂ A)
lem-++-right-cons ∙ Γ2 x A = refl
lem-++-right-cons (Γ1 , x₁ ⦂ A₁) Γ2 x A = lem-++-right-cons Γ1 (x₁ ⦂ A₁ , Γ2) x A

lem-++-∙ : ∀ Γ → (Γ ++ ∙) ≡ Γ
lem-++-∙ ∙ = refl
lem-++-∙ (Γ , x ⦂ A) with lem-++-∙ Γ
... | rr
  rewrite lem-++-right-cons Γ ∙ x A | lem-++-∙ Γ
  = refl

embed* : ∀ {Γ1 A}
  → Γ1 ⊢ A
  → ∀ Γ2
  → (Γ2 ++ Γ1) ⊢ A
embed* M ∙ = M
embed* M (Γ2 , x ⦂ A) = embed* (embed M) Γ2

subst-var : ∀ {x' A' Γ x A}
  → (i : x ⦂ A ∈ (x' ⦂ A' , Γ))
  → (A ≡ A') ⊎ (x ⦂ A ∈ Γ)
subst-var {Γ = ∙} nil = inj₁ refl
subst-var {Γ = ∙} (¬p ∷ ()) 
subst-var {Γ = Γ , x ⦂ A} nil = inj₂ nil
subst-var {Γ = Γ , x ⦂ A} (¬p ∷ i) with subst-var i
... | inj₁ refl = inj₁ refl
... | inj₂ j = inj₂ (¬p ∷ j)

[_/_]_ : ∀ {A B}
  → (M' : ∙ ⊢ A)
  → (x : Id)
  → ∀ {Γ}
  → (x ⦂ A , Γ) ⊢ B
  → Γ ⊢ B
[_/_]_ M' x' {Γ} (var i) with subst-var i
... | inj₁ refl rewrite sym (lem-++-∙ Γ) = embed* M' Γ
... | inj₂ j = var j 
[ M' / x' ] sole = sole
[ M' / x' ] cons M1 M2 = cons ([ M' / x' ] M1) ([ M' / x' ] M2)
[ M' / x' ] car M = car ([ M' / x' ] M)
[ M' / x' ] cdr M = cdr ([ M' / x' ] M)
[ M' / x' ] left M = left ([ M' / x' ] M)
[ M' / x' ] right M = right ([ M' / x' ] M)
[ M' / x' ] match M [ x1 ⇒ M₁ ][ x2 ⇒ M₂ ]
  = match [ M' / x' ] M [ x1 ⇒ [ M' / x' ] M₁ ][ x2 ⇒ [ M' / x' ] M₂ ]
[ M' / x' ] lambda x ⦂ A1 ∙  M = lambda x ⦂ A1 ∙ ([ M' / x' ] M)
[ M' / x' ] app M1 M2 = app ([ M' / x' ] M1) ([ M' / x' ] M2)

data _⟶_ : ∀ {A} → ∙ ⊢ A → ∙ ⊢ A → Set where

  car-[cons_-_] : ∀ {A1 A2}
    → {M1 : ∙ ⊢ A1}
    → (V1 : Value M1)
    → {M2 : ∙ ⊢ A2}
    → (V2 : Value M2)
    ----
    → (car (cons M1 M2)) ⟶ M1
    
  cdr-[cons_-_] : ∀ {A1 A2}
    → {M1 : ∙ ⊢ A1}
    → (V1 : Value M1)
    → {M2 : ∙ ⊢ A2}
    → (V2 : Value M2)
    ----
    → (cdr (cons M1 M2)) ⟶ M2

  match-[left_][_⇒_][_⇒_] : ∀ {A1 A2 A3}
    → {M0 : ∙ ⊢ A1}
    → (V0 : Value M0)
    → (x1 : Id)
    → (M1 : (∙ , x1 ⦂ A1) ⊢ A3)
    → (x2 : Id)
    → (M2 : (∙ , x2 ⦂ A2) ⊢ A3)
    → match (left M0) [ x1 ⇒ M1 ][ x2 ⇒ M2 ] ⟶ ([ M0 / x1 ] M1)

  match-[right_][_⇒_][_⇒_] : ∀ {A1 A2 A3}
    → {M0 : ∙ ⊢ A2}
    → (V0 : Value M0)
    → (x1 : Id)
    → (M1 : (∙ , x1 ⦂ A1) ⊢ A3)
    → (x2 : Id)
    → (M2 : (∙ , x2 ⦂ A2) ⊢ A3)
    → match (right M0) [ x1 ⇒ M1 ][ x2 ⇒ M2 ] ⟶ ([ M0 / x2 ] M2)

  app-[lambda_⦂_∙_]_ : ∀ {A2}
    → ∀ x A1
    → (M : (∙ , x ⦂ A1) ⊢ A2)
    → {M2 : ∙ ⊢ A1}
    → (V2 : Value M2)
    ----
    → app (lambda x ⦂ A1 ∙ M) M2 ⟶ ([ M2 / x ] M)

data _⟼_ : {A : Type} → ∙ ⊢ A → ∙ ⊢ A → Set where
  nil : ∀ {A}
    → {M M' : ∙ ⊢ A}
    → {prf : M ⟶ M'}
    → M ⟼ M'

  _∷_ : ∀ {A B}
    → (F : ⊢ A ↣ B)
    → {M M' : ∙ ⊢ A}
    → M ⟼ M'
    → ([ M ] F) ⟼ ([ M' ] F)

