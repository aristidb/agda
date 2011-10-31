module embmax where

open import Data.Nat
open import Data.Fin

emb : ∀ {n} -> Fin n -> Fin (suc n)
emb zero = zero
emb (suc i) = suc (emb i)

max : (n : ℕ) -> Fin (suc n)
max zero = zero
max (suc n) = suc (max n)

