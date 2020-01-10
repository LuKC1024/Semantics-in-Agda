module Types where

data Type : Set where
  Trivial : Type
  Either : Type -> Type -> Type
  Pair : Type → Type → Type
  _⇒_ : Type → Type → Type

