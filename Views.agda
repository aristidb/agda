module Views where

open import Data.Nat

data Parity : ℕ -> Set where
  even : (k : ℕ) -> Parity (k * 2)
  odd : (k : ℕ) -> Parity (1 + k * 2)

parity : (n : ℕ) -> Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(1 + k * 2)) | odd k = even (suc k)

half : ℕ -> ℕ
half n with parity n
half .(k * 2) | even k = k
half .(1 + k * 2) | odd k = k

open import Function
open import Data.List
open import Data.Bool

infixr 30 _:all:_
data All {A : Set}(P : A -> Set) : List A -> Set where
  all[] : All P []
  _:all:_ : forall {x xs} -> P x -> All P xs -> All P (x ∷ xs)

satisfies : {A : Set} -> (A -> Bool) -> A -> Set
satisfies p x = T (p x)


