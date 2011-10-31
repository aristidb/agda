module Reverse where

open import Data.List

revOn : {A : Set} -> List A -> List A -> List A
revOn [] ys = ys
revOn (x ∷ xs) ys = revOn xs (x ∷ ys)

rev : {A : Set} -> List A -> List A
rev xs = revOn xs []
