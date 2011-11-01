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

id : {A : Set} -> A -> A
id x = x

K : (A B : Set) -> A -> B -> A
K _ _ x _ = x

S : (A B C : Set) -> (A -> B -> C) -> (A -> B) -> A -> C
S _ _ _ f g x = f x (g x)

if_then_else_ : {C : Set} -> Bool -> C -> C -> C
if true then a else b = a
if false then a else b = b

natrec : {C : Set} -> C -> (Nat -> C -> C) -> Nat -> C
natrec p h zero = p
natrec p h (succ n) = h n (natrec p h n)

plus : Nat -> Nat -> Nat
plus n m = natrec m (\x y -> succ y) n

mult : Nat -> Nat -> Nat
mult n m = natrec zero (\x y -> plus y m) n

_^_ : Nat -> Nat -> Nat
n ^ e = natrec 1 (\x y -> mult y n) e

isZero : Nat -> Bool
isZero = natrec true (\x y -> false)

pred' : Nat -> Nat
pred' = natrec 0 (\x y -> if isZero x then y else succ y)

subtract : Nat -> Nat -> Nat
subtract a b = natrec a (\x y -> pred' y) b

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] = []
map f (x :: xs) = f x :: map f xs

foldl : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldl f s [] = s
foldl f s (x :: xs) = foldl f (f x s) xs

listrec : {A B : Set} -> B -> (A -> List A -> B -> B) -> List A -> B
listrec p h [] = p
listrec p h (x :: xs) = h x xs (listrec p h xs)

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (x :: xs) = if p x then x :: filter p xs else filter p xs

data _X_ (A B : Set) : Set where
  <_,_> : A -> B -> A X B

fst : {A B : Set} -> A X B -> A
fst < a , b > = a

snd : {A B : Set} -> A X B -> B
snd < a , b > = b

zip : {A B : Set} -> List A -> List B -> List (A X B)
zip (x :: xs) (y :: ys) = < x , y > :: zip xs ys
zip _ _ = []

data _⊎_ (A B : Set) : Set where
  inl : A -> A ⊎ B
  inr : B -> A ⊎ B

case : {A B C : Set} -> (A -> C) -> (B -> C) -> A ⊎ B -> C
case f g (inl x) = f x
case f g (inr y) = g y

{-
div : Nat -> Nat -> Nat
div m n = if (m < n) then zero else succ (div (m - n) n)
-}

div : Nat -> Nat -> Nat
div m zero = zero
div m (succ n) = helper (m - n)
  where helper : Nat -> Nat
        helper zero = zero
        helper (succ d) = succ (div d (succ n))
