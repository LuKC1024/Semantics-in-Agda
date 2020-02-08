open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; ∃-syntax)

module Named-STLC.Dynamics1
  (Id : Set)
  (Id=? : (x y : Id) → Dec (x ≡ y))
  where

open import Types
open import Named-STLC.Statics Id Id=?

data Value : ∀ {A} → ∙ ⊢ A → Set where

  sole : Value sole

  ⟨_,_⟩ : ∀ {A1 A2}
    → {M1 : ∙ ⊢ A1}
    → (V1 : Value M1)
    → {M2 : ∙ ⊢ A2}
    → (V2 : Value M2)
    -----
    → Value ⟨ M1 , M2 ⟩

  inl : ∀ {A1 A2}
    → {M : ∙ ⊢ A1}
    → (V : Value M)
    ----
    → Value (inl {A2 = A2} M)

  inr : ∀ {A1 A2}
    → {M : ∙ ⊢ A2}
    → (V : Value M)
    ----
    → Value (inr {A1 = A1} M)

  lambda_⦂_∙_ : ∀ {A2}
    → ∀ x A1
    → (M : (∙ , x ⦂ A1) ⊢ A2)
    ---
    → Value (lambda x ⦂ A1 ∙ M)

` : ∀ {A} → {M : ∙ ⊢ A} → Value M → ∙ ⊢ A
` {M = M} V = M

-- Frame of evaluation context
data ⊢_↣_ : Type → Type → Set where

  ⟨-□-,_⟩ : ∀ {A1 A2}
    → (M2 : ∙ ⊢ A2)
    -----
    → ⊢ A1 ↣ Pair A1 A2

  ⟨_,-□-⟩ : ∀ {A1 A2}
    → {M1 : ∙ ⊢ A1}
    → (V1 : Value M1)
    -----
    → ⊢ A2 ↣ Pair A1 A2

  car-□ : ∀ {A1 A2}
    ----
    → ⊢ Pair A1 A2 ↣ A1

  cdr-□ : ∀ {A1 A2}
    ----
    → ⊢ Pair A1 A2 ↣ A2

  inl-□ : ∀ {A1 A2}
    ----
    → ⊢ A1 ↣ Either A1 A2

  inr-□ : ∀ {A1 A2}
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

-- put term into frame
[_]_ : ∀ {A1 A2} → ∙ ⊢ A1 → ⊢ A1 ↣ A2 → ∙ ⊢ A2
[ M ] ⟨-□-, M2 ⟩ = ⟨ M , M2 ⟩
[ M ] ⟨ V1 ,-□-⟩ = ⟨ ` V1 , M ⟩
[ M ] car-□ = car M
[ M ] cdr-□ = cdr M
[ M ] inl-□ = inl M
[ M ] inr-□ = inr M
[ M ] match-□-[ x1 ⇒ M1 ][ x2 ⇒ M2 ] = match M [ x1 ⇒ M1 ][ x2 ⇒ M2 ]
[ M ] app-□ M2 = app M M2
[ M ] app V1 □ = app (` V1) M

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
embed ⟨ M1 , M2 ⟩ = ⟨ embed M1 , embed M2 ⟩
embed (car M) = car (embed M)
embed (cdr M) = cdr (embed M)
embed (inl M) = inl (embed M)
embed (inr M) = inr (embed M)
embed (match M0 [ x1 ⇒ M1 ][ x2 ⇒ M2 ]) = match embed M0 [ x1 ⇒ embed M1 ][ x2 ⇒ embed M2 ]
embed (lambda x ⦂ A1 ∙ M) = lambda x ⦂ A1 ∙ (embed M)
embed (app M1 M2) = app (embed M1) (embed M2)

_++_ : Context → Context → Context
∙ ++ ys = ys
(xs , x ⦂ A) ++ ys = xs ++ (x ⦂ A , ys)

lem-++-inr-cons : ∀ Γ1 Γ2 x A →
  (Γ1 ++ (Γ2 , x ⦂ A)) ≡ ((Γ1 ++ Γ2) , x ⦂ A)
lem-++-inr-cons ∙ Γ2 x A = refl
lem-++-inr-cons (Γ1 , x₁ ⦂ A₁) Γ2 x A = lem-++-inr-cons Γ1 (x₁ ⦂ A₁ , Γ2) x A

lem-++-∙ : ∀ Γ → (Γ ++ ∙) ≡ Γ
lem-++-∙ ∙ = refl
lem-++-∙ (Γ , x ⦂ A) with lem-++-∙ Γ
... | rr
  rewrite lem-++-inr-cons Γ ∙ x A | lem-++-∙ Γ
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

-- substitution, close terms only
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
[ M' / x' ] ⟨ M1 , M2 ⟩ = ⟨ [ M' / x' ] M1 , [ M' / x' ] M2 ⟩
[ M' / x' ] car M = car ([ M' / x' ] M)
[ M' / x' ] cdr M = cdr ([ M' / x' ] M)
[ M' / x' ] inl M = inl ([ M' / x' ] M)
[ M' / x' ] inr M = inr ([ M' / x' ] M)
[ M' / x' ] match M [ x1 ⇒ M₁ ][ x2 ⇒ M₂ ]
  = match [ M' / x' ] M [ x1 ⇒ [ M' / x' ] M₁ ][ x2 ⇒ [ M' / x' ] M₂ ]
[ M' / x' ] lambda x ⦂ A1 ∙ M = lambda x ⦂ A1 ∙ ([ M' / x' ] M)
[ M' / x' ] app M1 M2 = app ([ M' / x' ] M1) ([ M' / x' ] M2)

-- reduction of redex
data _⟶_ : ∀ {A} → ∙ ⊢ A → ∙ ⊢ A → Set where

  car⟨_,_⟩ : ∀ {A1 A2}
    → {M1 : ∙ ⊢ A1}
    → (V1 : Value M1)
    → {M2 : ∙ ⊢ A2}
    → (V2 : Value M2)
    ----
    → (car ⟨ M1 , M2 ⟩) ⟶ M1
    
  cdr⟨_,_⟩ : ∀ {A1 A2}
    → {M1 : ∙ ⊢ A1}
    → (V1 : Value M1)
    → {M2 : ∙ ⊢ A2}
    → (V2 : Value M2)
    ----
    → (cdr ⟨ M1 , M2 ⟩) ⟶ M2

  match[-inl_][_⇒_][_⇒_] : ∀ {A1 A2 A3}
    → {M0 : ∙ ⊢ A1}
    → (V0 : Value M0)
    → (x1 : Id)
    → (M1 : (∙ , x1 ⦂ A1) ⊢ A3)
    → (x2 : Id)
    → (M2 : (∙ , x2 ⦂ A2) ⊢ A3)
    → match (inl M0) [ x1 ⇒ M1 ][ x2 ⇒ M2 ] ⟶ ([ M0 / x1 ] M1)

  match[-inr_][_⇒_][_⇒_] : ∀ {A1 A2 A3}
    → {M0 : ∙ ⊢ A2}
    → (V0 : Value M0)
    → (x1 : Id)
    → (M1 : (∙ , x1 ⦂ A1) ⊢ A3)
    → (x2 : Id)
    → (M2 : (∙ , x2 ⦂ A2) ⊢ A3)
    → match (inr M0) [ x1 ⇒ M1 ][ x2 ⇒ M2 ] ⟶ ([ M0 / x2 ] M2)

  app[-lambda_⦂_∙_]_ : ∀ {A2}
    → ∀ x A1
    → (M : (∙ , x ⦂ A1) ⊢ A2)
    → {M2 : ∙ ⊢ A1}
    → (V2 : Value M2)
    ----
    → app (lambda x ⦂ A1 ∙ M) M2 ⟶ ([ M2 / x ] M)

-- reduction of program
data _⟼_ : {A : Type} → ∙ ⊢ A → ∙ ⊢ A → Set where
  nil : ∀ {A}
    → {M M' : ∙ ⊢ A}
    → (prf : M ⟶ M')
    → M ⟼ M'

  _∷_ : ∀ {A B}
    → (F : ⊢ A ↣ B)
    → {M M' : ∙ ⊢ A}
    → M ⟼ M'
    → ([ M ] F) ⟼ ([ M' ] F)

thm-type-safety : ∀ {A}
  → (M : ∙ ⊢ A)
  → (∃[ M' ] (M ⟼ M')) ⊎ (Value M)
thm-type-safety (var ()) 
thm-type-safety sole = inj₂ sole
thm-type-safety ⟨ M1 , M2 ⟩ with thm-type-safety M1
... | inj₁ (M1' , M1⟼M1') = inj₁ (_ , (⟨-□-, M2 ⟩ ∷ M1⟼M1'))
... | inj₂ V1 with thm-type-safety M2
...   | inj₁ (M2' , M2⟼M2') = inj₁ (_ , (⟨ V1 ,-□-⟩ ∷ M2⟼M2'))
...   | inj₂ V2 = inj₂ ⟨ V1 , V2 ⟩
thm-type-safety (car M) with thm-type-safety M
... | inj₁ (M' , M⟼M') = inj₁ (_ , (car-□ ∷ M⟼M'))
... | inj₂ ⟨ V1 , V2 ⟩ = inj₁ (_ , nil car⟨ V1 , V2 ⟩)
thm-type-safety (cdr M) with thm-type-safety M
... | inj₁ (M' , M⟼M') = inj₁ (_ , (cdr-□ ∷ M⟼M'))
... | inj₂ ⟨ V1 , V2 ⟩ = inj₁ (` V2 , nil cdr⟨ V1 , V2 ⟩)
thm-type-safety (inl M) with thm-type-safety M
... | inj₁ (M' , M⟼M') = inj₁ (_ , (inl-□ ∷ M⟼M'))
... | inj₂ V1 = inj₂ (inl V1)
thm-type-safety (inr M) with thm-type-safety M
... | inj₁ (M' , M⟼M') = inj₁ (_ , (inr-□ ∷ M⟼M'))
... | inj₂ V1 = inj₂ (inr V1)
thm-type-safety (match M [ x1 ⇒ M1 ][ x2 ⇒ M2 ]) with thm-type-safety M
... | inj₁ (M' , M⟼M') = inj₁ (_ , (match-□-[ x1 ⇒ M1 ][ x2 ⇒ M2 ] ∷ M⟼M'))
... | inj₂ (inl V1)  = inj₁ (_ , nil match[-inl V1 ][ x1 ⇒ M1 ][ x2 ⇒ M2 ])
... | inj₂ (inr V1) = inj₁ (_ , nil match[-inr V1 ][ x1 ⇒ M1 ][ x2 ⇒ M2 ])
thm-type-safety (lambda x ⦂ A1 ∙ M) = inj₂ (lambda x ⦂ A1 ∙ M)
thm-type-safety (app M1 M2) with thm-type-safety M1
... | inj₁ (M1' , M1⟼M1') = inj₁ (_ , (app-□ M2) ∷ M1⟼M1')
... | inj₂ V1 with thm-type-safety M2
...   | inj₁ (M2' , M2⟼M2') = inj₁ (_ , (app V1 □) ∷ M2⟼M2')
...   | inj₂ V2 with V1
...     | lambda x ⦂ A ∙ M = inj₁ (_ , nil (app[-lambda x ⦂ A ∙ M ] V2) )
