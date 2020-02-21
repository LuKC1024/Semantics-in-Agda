module Sparrow.Syntax where

open import Identifiers

mutual
  record Bind : Set where
    inductive
    constructor _⇒_
    field
      x : Id
      M : Term

  data Term : Set where
    var : Id → Term
    `tt : Term
    cons : Term → Term → Term
    car : Term → Term
    cdr : Term → Term
    inl : Term → Term
    inr : Term → Term
    case : (M : Term) → (B1 B2 : Bind) → Term
    lam : Bind → Term
    app : Term → Term → Term
