module Chain where

open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

data Chain {Index : Set} (Link : Index → Index → Set) : Index → Index → Set where
  []  : ∀ {I} → Chain Link I I
  _∷_ : ∀ {I J K}
    → Link I J
    → Chain Link J K
    → Chain Link I K

pattern [_] x = x ∷ []

_++_ : ∀ {Index} {Link : Index → Index → Set} {I J K : Index}
  → Chain Link I J
  → Chain Link J K
  → Chain Link I K
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

List : Set → Set
List A = Chain (λ _ _ → A) tt tt

++-identity-l : ∀ {Index} {Link : Index → Index → Set} {I J : Index}
  → (xs : Chain Link I J)
  → [] ++ xs ≡ xs
++-identity-l xs = refl

++-identity-r : ∀ {Index} {Link : Index → Index → Set} {I J : Index}
  → (xs : Chain Link I J)
  → xs ++ [] ≡ xs
++-identity-r [] = refl
++-identity-r (x ∷ xs) = cong (x ∷_) (++-identity-r xs)
