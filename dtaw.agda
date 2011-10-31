-- Dependent Types At Work!
module dtaw where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

equiv : Bool -> Bool -> Bool
equiv true true = true
equiv true false = false
equiv false true = false
equiv false false = true

_||_ : Bool -> Bool -> Bool
true || _ = true
false || b = b

_&&_ : Bool -> Bool -> Bool
true && b = b
false && _ = false

_=>_ : Bool -> Bool -> Bool
true => b = b
false => _ = true

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

pred : Nat -> Nat
pred zero = zero
pred (succ n) = n

_+_ : Nat -> Nat -> Nat
zero + b = b
succ a + b = succ (a + b)

_*_ : Nat -> Nat -> Nat
zero * _ = zero
succ a * b = (a * b) + b

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC succ #-}
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}

_-_ : Nat -> Nat -> Nat
a - zero = a
a - succ b = pred (a - b)

_≤_ : Nat -> Nat -> Bool
zero ≤ b = true
succ a ≤ zero = false
succ a ≤ succ b = a ≤ b

_<_ : Nat -> Nat -> Bool
a < b = not (b ≤ a)
