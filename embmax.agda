module embmax where

open import Data.Nat renaming (_+_ to _ℕ+_)
open import Data.Fin

emb : ∀ {n} -> Fin n -> Fin (suc n)
emb zero = zero
emb (suc i) = suc (emb i)

max : {n : ℕ} -> Fin (suc n)
max {zero} = zero
max {suc n} = suc (max {n})

emb' : {n k : ℕ} -> Fin n -> Fin (n ℕ+ k)
emb' zero = zero
emb' (suc i) = suc (emb' i)

view : ∀ {n k} -> Fin n -> Fin (suc k)
view zero = zero
view {k = zero} (suc i) = max
view {k = suc k'} (suc i) = suc (view i)

data View (k : ℕ) : Set where
  vin : Fin (suc k) -> View k
  vmax : View k

vsuc : ∀ {k} -> View k -> View (suc k)
vsuc (vin i) = vin (suc i)
vsuc vmax = vmax

vtofin : ∀ {k} -> View k -> Fin (suc k)
vtofin (vin i) = i
vtofin vmax = max

view' : ∀ {n k} -> Fin n -> View k
view' zero = vin zero
view' {k = zero} (suc i) = vmax
view' {k = suc _} (suc i) = vsuc (view' i)


