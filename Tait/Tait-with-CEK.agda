module Tait-with-CEK where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit  using (⊤; tt)
open import Data.Empty using (⊥)

infixr 5 _∷_
infixr 5 _++_

data Chain {Index : Set} (Link : Index → Index → Set) : Index → Index → Set where
  []  : ∀ {I} → Chain Link I I
  _∷_ : ∀ {I J K}
    → Link I J
    → Chain Link J K
    → Chain Link I K

List : Set → Set
List A = Chain (λ _ _ → A) tt tt

_++_ : ∀ {Index} {Link : Index → Index → Set} {I J K : Index}
  → Chain Link I J
  → Chain Link J K
  → Chain Link I K
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infix  3 _∋_
infix  3 _⊢_

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `⊤  : Type

-- contexts are lists of types

Context : Set
Context = List Type

data _∋_ : Context → Type → Set where

  zero : ∀ {Γ A}
      ---------
    → A ∷ Γ ∋ A

  suc : ∀ {Γ A B}
    →     Γ ∋ A
      ---------
    → B ∷ Γ ∋ A

data _⊢_ : Context → Type → Set where

  `tt : ∀ {Γ}
      ---------
    → Γ ⊢ `⊤

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ  : ∀ {Γ} A {B}
    → A ∷ Γ ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

mutual
  
  data Value : Type → Set where

    `tt :
      --------
        Value (`⊤)
   
    ƛ : ∀ {Γ} T1 {T2}
      → (M : T1 ∷ Γ ⊢ T2)
      → (ρ : Env Γ)
      -------------
      → Value (T1 ⇒ T2)

  data Env : Context → Set where
    []  : Env []
    _∷_ : ∀ {Γ T}
      → (v : Value T)
      → Env Γ
      → Env (T ∷ Γ)

lookup : ∀ {Γ A}
  → Env Γ
  → Γ ∋ A
  ---------
  → Value A
lookup (v ∷ vs) zero    = v
lookup (v ∷ vs) (suc n) = lookup vs n

data Closure (A : Type) : Set where
  _,_ : ∀ {Γ}
    → Γ ⊢ A
    → Env Γ → Closure A

-- continuations are chains of frames

data Frame : Type → Type → Set where

  □-·_ : ∀ {S T}
    → (c : Closure S)
    --------
    → Frame (S ⇒ T) T
                          
  _·-□ : ∀ {S T}
    → (v : Value (S ⇒ T))
    --------
    → Frame S T

Cont : Type → Type → Set
Cont = Chain Frame

data State (Z : Type) : Set where 
  expr : ∀ {A}
    → (c : Closure A)
    → (κ : Cont A Z)
    ------------
    → State Z
    
  cont : ∀ {A}
    → (v : Value A)
    → (κ : Cont A Z)
    ------------
    → State Z
      
data Progressing {Z : Type} : State Z →  Set where
  P-expr : ∀ {A}
    → {c : Closure A}
    → {k : Cont A Z}
    ------------
    → Progressing (expr c k)
    
  P-cont : ∀ {A B}
    → {v : Value A}
    → {F : Frame A B}
    → {k : Cont  B Z}
    ------------
    → Progressing (cont v (F ∷ k))

load : ∀ {T} → [] ⊢ T → State T
load M = (expr (M , []) [])

do-app : ∀ {T1 T2 Z}
  → Value (T1 ⇒ T2)
  → Value T1
  → Cont T2 Z
  → State Z
do-app (ƛ A e E) u k = (expr (e , (u ∷ E)) k)

progress : ∀ {Z} → (s : State Z) → Progressing s → State Z
progress (expr (`tt   , ρ) κ) P-expr = (cont `tt κ)
progress (expr (` x   , ρ) κ) P-expr = (cont (lookup ρ x) κ)
progress (expr (ƛ A M , ρ) κ) P-expr = (cont (ƛ A M ρ) κ)
progress (expr (L · N , ρ) κ) P-expr = (expr (L , ρ) (□-· (N , ρ) ∷ κ))
progress (cont v (□-· c ∷ k)) P-cont = (expr c (v ·-□ ∷ k))
progress (cont u (v ·-□ ∷ k)) P-cont = do-app v u k

data _⟶_ {T : Type} : State T → State T → Set where
  it : ∀ {s}
    → (sp : Progressing s)
    → s ⟶ progress s sp

_⟶*_ : {T : Type} → State T → State T → Set
_⟶*_ {T} = Chain (_⟶_ {T})

mutual
  -- a closure is good if it reduces to the same good value under any continuation.
  𝒞 : ∀ A → Closure A → Set
  𝒞 A (M , ρ)
    = ∃[ v ](𝒱 A v × ({B : Type}(k : Cont A B) → ((expr (M , ρ) k ⟶* cont v k))))

  -- a value is good if
  --   * it is the tt, or
  --   * it is a function and the body and a well-extended closure constitute a
  --     good closure
  𝒱 : ∀ A → Value A → Set
  𝒱 (A ⇒ B) (ƛ A M ρ) = ∀ v → 𝒱 A v → 𝒞 B (M , (v ∷ ρ))
  𝒱 `⊤      `tt       = ⊤

-- an environment is good if all its values are good
ℛ : ∀ {Γ} → Env Γ → Set
ℛ {Γ} ρ = ∀ {A} → (x : Γ ∋ A) → 𝒱 A (lookup ρ x)

-- a term is good if when combining with any good environment the resulting
-- closure is good
𝒯 : ∀ {Γ} A → (M : Γ ⊢ A) → Set
𝒯 A M = ∀ ρ → ℛ ρ → 𝒞 A (M , ρ)

abs-good : ∀ {Γ B} A
  → (M : A ∷ Γ ⊢ B)
  → 𝒯 B M
    ----------
  → 𝒯 (A ⇒ B) (ƛ A M)
abs-good B M M-good ρ ρ-good
  = ƛ B M ρ
  , G
  , λ k → it P-expr ∷ []
  where
  G : 𝒱 (B ⇒ _) (ƛ B M ρ)
  G v 𝒱-v = M-good (v ∷ ρ) λ { zero → 𝒱-v ; (suc x) → ρ-good x }

app-good : ∀ {Γ B A}
  → (M : Γ ⊢ A ⇒ B)
  → 𝒯 (A ⇒ B) M
  → (N : Γ ⊢ A)
  → 𝒯 A N
    ------------
  → 𝒯 B (M · N)
app-good M M-good N N-good ρ ρ-good
  with M-good ρ ρ-good
... | 𝒞-M
  with 𝒞-M
... | ƛ A L E' , 𝒱-ƛBLE' , M⟶*vM
  with N-good ρ ρ-good
... | 𝒞-N
  with 𝒞-N
... | vN , 𝒱-vN , N⟶*vN
  with 𝒱-ƛBLE' vN 𝒱-vN
... | 𝒞-L-vN∷E'
  with 𝒞-L-vN∷E'
... | vL , 𝒱-vL , L⟶*vL
  = vL
  , 𝒱-vL
  , λ k → it P-expr
        ∷ M⟶*vM (□-· (N , ρ) ∷ k)
       ++ it P-cont
        ∷ N⟶*vN (ƛ A L E' ·-□ ∷ k)
       ++ it P-cont
        ∷ L⟶*vL k

fundamental-property : ∀ {Γ A}
  → (M : Γ ⊢ A)
    -----------
  → 𝒯 A M
fundamental-property `tt
  = λ ρ ρ-good → `tt ,        tt       , λ k → it P-expr ∷ []
fundamental-property (` x)
  = λ ρ ρ-good → lookup ρ x , ρ-good x , λ k → it P-expr ∷ []
fundamental-property (ƛ A M)
  = abs-good A M (fundamental-property M)
fundamental-property (L · N)
  = app-good L (fundamental-property L) N (fundamental-property N) 

terminate : ∀ {A}
  → (M : [] ⊢ A)
  → ∃[ v ](load M ⟶* cont v [])
terminate M
  with fundamental-property M
... | M-good
  with M-good [] (λ ())
... | vM , 𝒱-Mv , M⟶*vM
  = vM , (M⟶*vM [])
