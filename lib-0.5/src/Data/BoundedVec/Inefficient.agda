------------------------------------------------------------------------
-- Bounded vectors (inefficient, concrete implementation)
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

-- Vectors of a specified maximum length.

module Data.BoundedVec.Inefficient where

open import Data.Nat
open import Data.List

------------------------------------------------------------------------
-- The type

infixr 5 _∷_

data BoundedVec {a} (A : Set a) : ℕ → Set a where
  []  : ∀ {n} → BoundedVec A n
  _∷_ : ∀ {n} (x : A) (xs : BoundedVec A n) → BoundedVec A (suc n)

------------------------------------------------------------------------
-- Increasing the bound

-- Note that this operation is linear in the length of the list.

↑ : ∀ {a n} {A : Set a} → BoundedVec A n → BoundedVec A (suc n)
↑ []       = []
↑ (x ∷ xs) = x ∷ ↑ xs

------------------------------------------------------------------------
-- Conversions

fromList : ∀ {a} {A : Set a} → (xs : List A) → BoundedVec A (length xs)
fromList []       = []
fromList (x ∷ xs) = x ∷ fromList xs

toList : ∀ {a n} {A : Set a} → BoundedVec A n → List A
toList []       = []
toList (x ∷ xs) = x ∷ toList xs
