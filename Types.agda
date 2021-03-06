module Types where

data Type : Set where
  `⊤ : Type
  _`+_ : Type -> Type -> Type
  _`×_ : Type → Type → Type
  _`→_ : Type → Type → Type

infix 30 _`+_
infix 30 _`×_
infix 30 _`→_
