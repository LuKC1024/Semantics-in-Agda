module Identifiers where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)

postulate Id : Set
postulate Id=? : (x y : Id) → Dec (x ≡ y)
