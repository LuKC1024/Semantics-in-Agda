module Tait-with-CEK where

open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit  using (⊤; tt)

infixr 5 _∷_
infixr 5 _++_

-- A chain is like a list with extra checks.
-- I define list on top of chain later

data Chain {Index : Set} (Link : Index → Index → Set) : Index → Index → Set where
  []  : ∀ {I} → Chain Link I I
  _∷_ : ∀ {I J K}
    → Link I J
    → Chain Link J K
    → Chain Link I K

_++_ : ∀ {Index} {Link : Index → Index → Set} {I J K : Index}
  → Chain Link I J
  → Chain Link J K
  → Chain Link I K
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

List : Set → Set
List A = Chain (λ _ _ → A) tt tt

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

  ƛ  : ∀ {Γ B} A
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

data _—→_ {T : Type} : State T → State T → Set where
  it : ∀ {s}
    → (sp : Progressing s)
    → s —→ progress s sp

_—→*_ : {T : Type} → State T → State T → Set
_—→*_ {T} = Chain (_—→_ {T})

mutual
  -- a closure is good if it always reduce to a value and the value is good
  -- and this reduction happens under any continuation.
  𝒞 : ∀ A → Closure A → Set
  𝒞 A c
    = ∃[ v ](𝒱 A v × ({B : Type}(k : Cont A B) → (expr c k —→* cont v k)))

  -- a value is good if
  --   * it is the tt, or
  --   * it is a function and returns a good closure when applied to a good value
  𝒱 : ∀ A → Value A → Set
  𝒱 (A ⇒ B) (ƛ A M ρ) = ∀ v → 𝒱 A v → 𝒞 B (M , (v ∷ ρ))
  𝒱 `⊤      `tt       = ⊤

-- an environment is good if all its values are good
ℛ : ∀ {Γ} → Env Γ → Set
ℛ {Γ} ρ = ∀ {A} → (x : Γ ∋ A) → 𝒱 A (lookup ρ x)

-- a term is good if when combined with any good environment the resulting
-- closure is good
𝒯 : ∀ {Γ} A → (M : Γ ⊢ A) → Set
-- 𝒯 A M = ∀ {ρ} → ℛ ρ → 𝒞 A (M , ρ)
𝒯 A M = ∀ {ρ}
  → ℛ ρ
  → ∃[ v ](𝒱 A v × ({B : Type}(k : Cont A B) → (expr (M , ρ) k —→* cont v k)))

ƛ̂ : ∀ {Γ} A {B}
  → {M : A ∷ Γ ⊢ B}
  → 𝒯 B M
    ----------
  → 𝒯 (A ⇒ B) (ƛ A M)
ƛ̂ A {B} 𝒯-M ℛ-ρ
  = _
  , (λ v 𝒱-v → 𝒯-M λ { zero → 𝒱-v ; (suc x) → ℛ-ρ x })
  , (λ k → it P-expr ∷ [])

_·̂_ : ∀ {Γ B A}
  → {M : Γ ⊢ A ⇒ B}
  → 𝒯 (A ⇒ B) M
  → {N : Γ ⊢ A}
  → 𝒯 A N
    ------------
  → 𝒯 B (M · N)
(𝒯-M ·̂ 𝒯-N) ℛ-ρ
  with 𝒯-M ℛ-ρ
... | 𝒞-M
  with 𝒞-M
... | ƛ A L ρ̂ , 𝒱-ƛBLρ̂ , M—→*vM
  with 𝒯-N ℛ-ρ
... | 𝒞-N
  with 𝒞-N
... | vN , 𝒱-vN , N—→*vN
  with 𝒱-ƛBLρ̂ vN 𝒱-vN
... | 𝒞-L-vN∷ρ̂
  with 𝒞-L-vN∷ρ̂
... | vL , 𝒱-vL , L—→*vL
  = vL
  , 𝒱-vL
  , (λ k → it P-expr              -- focus on M
         ∷ M—→*vM ((□-· _) ∷ k)   -- reduce M to value
        ++ it P-cont              -- focus on N
         ∷ N—→*vN ((_ ·-□) ∷ k)   -- reduce N to value
        ++ it P-cont              -- application
         ∷ L—→*vL k)              -- reduce the body (L) to value

fundamental-property : ∀ {Γ A}
  → (M : Γ ⊢ A)
    -----------
  → 𝒯 A M
fundamental-property `tt   = λ ℛ-ρ → _ , tt    , λ k → it P-expr ∷ []
fundamental-property (` x) = λ ℛ-ρ → _ , ℛ-ρ x , λ k → it P-expr ∷ []
fundamental-property (ƛ A M) = ƛ̂ A (fundamental-property M)
fundamental-property (L · N) = (fundamental-property L) ·̂ (fundamental-property N) 

terminate : ∀ {A}
  → (M : [] ⊢ A)
  → ∃[ v ](load M —→* cont v [])
terminate M
  with fundamental-property M
... | 𝒯-M
  with 𝒯-M (λ ())
... | vM , 𝒱-Mv , M—→*vM
  = vM , (M—→*vM [])
