module STLC where
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Maybe
open import Data.Sum
  
data Env (A : Set) : Set where
  ∅   : Env A
  _,_ : Env A → A → Env A

extL : ∀ {A} -> A -> Env A -> Env A
extL a ∅ = ∅ , a
extL a (E , x) = extL a E , x

data Type : Set where
  Unit : Type
  Either : Type -> Type -> Type
  Pair : Type → Type → Type
  Fun  : Type → Type → Type
  
data _∈_ (A : Type) : Env Type → Set where
  zero : ∀ {Γ} → A ∈ (Γ , A)
  suc  : ∀ {Γ} → A ∈ Γ → ∀ {B} -> A ∈ (Γ , B)

mutual
  data Val : Type -> Set where
    sol : Val Unit
    inj₁ : {A : Type} -> Val A -> (B : Type) -> Val (Either A B)
    inj₂ : (A : Type) -> {B : Type} -> Val B -> Val (Either A B)
    cons : {A B : Type} -> Val A -> Val B -> Val (Pair A B)
    lam : (A : Type){B : Type} -> Exp (∅ , A) B -> Val (Fun A B)

  data Exp : Env Type -> Type -> Set where
    quo : ∀ {Γ A} -> Val A -> Exp Γ A
    var : ∀ {Γ A} -> A ∈ Γ -> Exp Γ A
    lam : ∀ {Γ} -> (A : Type){B : Type} -> Exp (Γ , A) B -> Exp Γ (Fun A B)
    app : ∀ {Γ} -> {A B : Type} -> Exp Γ (Fun A B) -> Exp Γ A -> Exp Γ B
    cons : ∀ {Γ} -> {A B : Type} -> Exp Γ A -> Exp Γ B -> Exp Γ (Pair A B)
    car : ∀ {Γ} -> {A B : Type} -> Exp Γ (Pair A B) -> Exp Γ A
    cdr : ∀ {Γ} -> {A B : Type} -> Exp Γ (Pair A B) -> Exp Γ B
    inj₁ : ∀ {Γ} -> {A : Type} -> Exp Γ A -> (B : Type) -> Exp Γ (Either A B)
    inj₂ : ∀ {Γ} -> (A : Type) -> {B : Type} -> Exp Γ B -> Exp Γ (Either A B)
    case : ∀ {Γ A B C} -> Exp Γ (Either A B) -> Exp Γ (Fun A C) -> Exp Γ (Fun B C) -> Exp Γ C
    sol : ∀ {Γ} -> Exp Γ Unit
    err : ∀ {Γ A} -> Exp Γ A

var? : ∀ {A B Γ} -> B ∈ (extL A Γ) -> (B ∈ Γ) ⊎ (B ≡ A)
var? {Γ = ∅} zero = inj₂ refl
var? {Γ = ∅} (suc ())
var? {Γ = Γ , x} zero = inj₁ zero
var? {Γ = Γ , x} (suc v) with var? v
var? {B = _} {Γ , x} (suc v) | inj₁ x₁ = inj₁ (suc x₁)
var? {B = _} {Γ , x} (suc v) | inj₂ refl = inj₂ refl

bind : ∀ {Γ A B} -> Val A -> Exp (extL A Γ) B -> Exp Γ B
bind v (quo x) = quo x
bind v (var x) with var? x
bind v (var x) | inj₁ x₁ = var x₁
bind v (var x) | inj₂ refl = quo v
bind v (lam A e) = lam A (bind v e)
bind v (app e e₁) = app (bind v e) (bind v e₁)
bind v (cons e e₁) = cons (bind v e) (bind v e₁)
bind v (car e) = car (bind v e)
bind v (cdr e) = cdr (bind v e)
bind v (inj₁ e B) = inj₁ (bind v e) B
bind v (inj₂ A e) = inj₂ A (bind v e)
bind v (case e e₁ e₂) = case (bind v e) (bind v e₁) (bind v e₂)
bind v sol = sol
bind v err = err

data Progress (A : Type) : Set where
  step : Exp ∅ A -> Progress A
  done : Val A -> Progress A
  exit : Progress A

reduce : ∀ {A} -> Exp ∅ A -> Progress A
reduce (quo x) = done x
reduce (var ())
reduce (lam A e) = done (lam A e)
reduce (app e e₁) with reduce e
reduce (app e e₁) | step x = step (app x e₁)
reduce (app e e₁) | done x with reduce e₁
reduce (app e e₁) | done x | step x₁ = step (app (quo x) x₁)
reduce (app e e₁) | done (lam A x) | done x₁ = step (bind x₁ x)
reduce (app e e₁) | done x | exit = exit
reduce (app e e₁) | exit = exit
reduce (cons e e₁) with reduce e
reduce (cons e e₁) | step x = step (cons x e₁)
reduce (cons e e₁) | done x with reduce e₁
reduce (cons e e₁) | done x | step x₁ = step (cons (quo x) x₁)
reduce (cons e e₁) | done x | done x₁ = done (cons x x₁)
reduce (cons e e₁) | done x | exit = exit
reduce (cons e e₁) | exit = exit
reduce (car e) with reduce e
reduce (car e) | step x = step (car x)
reduce (car e) | done (cons x x₁) = done x
reduce (car e) | exit = exit
reduce (cdr e) with reduce e
reduce (cdr e) | step x = step (cdr x)
reduce (cdr e) | done (cons x x₁) = done x₁
reduce (cdr e) | exit = exit
reduce (inj₁ e B) with reduce e
reduce (inj₁ e B) | step x = step (inj₁ x B)
reduce (inj₁ e B) | done x = done (inj₁ x B)
reduce (inj₁ e B) | exit = exit
reduce (inj₂ A e) with reduce e
reduce (inj₂ A e) | step x = step (inj₂ A x)
reduce (inj₂ A e) | done x = done (inj₂ A x)
reduce (inj₂ A e) | exit = exit
reduce (case e e₁ e₂) with reduce e
reduce (case e e₁ e₂) | step x = step (case x e₁ e₂)
reduce (case e e₁ e₂) | done x with reduce e₁
reduce (case e e₁ e₂) | done x | step x₁ = step (case (quo x) x₁ e₂)
reduce (case e e₁ e₂) | done x | done x₁ with reduce e₂
reduce (case e e₁ e₂) | done x | done x₁ | step x₂ = step (case (quo x) (quo x₁) x₂)
reduce (case e e₁ e₂) | done (inj₁ x B) | done (lam A x₁) | done (lam .B x₂) = step (bind x x₁)
reduce (case e e₁ e₂) | done (inj₂ A x) | done (lam .A x₁) | done (lam B x₂) = step (bind x x₂)
reduce (case e e₁ e₂) | done x | done x₁ | exit = exit
reduce (case e e₁ e₂) | done x | exit = exit
reduce (case e e₁ e₂) | exit = exit
reduce sol = done sol
reduce err = exit
