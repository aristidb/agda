module AgdaBasics where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + m = m
suc n + m = suc (n + m)

_*_ : Nat -> Nat -> Nat
zero * m = zero
suc n * m = m + (n * m)

_or_ : Bool -> Bool -> Bool
true or _ = true
false or x = x

_and_ : Bool -> Bool -> Bool
false and _ = false
true and x = x

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else _ = x
if false then _ else y = y

infixl 60 _*_
infixl 40 _+_
infixr 20 _or_
infix 5 if_then_else_

infixr 40 _::_
data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

data _⋆ (α : Set) : Set where
  ε : α ⋆
  _◃_ : α -> α ⋆ -> α ⋆

identity : (A : Set) -> A -> A
identity A x = x

zero' : Nat
zero' = identity Nat zero

apply : (A : Set)(B : A -> Set) -> ((x : A) -> B x) -> (a : A) -> B a
apply A B f a = f a

identity₂ : (A : Set) -> A -> A
identity₂ = \A x -> x

identity₃ : (A : Set) -> A -> A
identity₃ = \(A : Set)(x : A) -> x

identity₄ : (A : Set) -> A -> A
identity₄ = \(A : Set) x -> x

id : {A : Set} -> A -> A
id x = x

true' : Bool
true' = id true

silly : {A : Set}{x : A} -> A
silly {_}{x} = x

false' : Bool
false' = silly {x = false}

one : Nat
one = identity _ (suc zero)

_∘_ : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set}
      (f : {x : A}(y : B x) -> C x y)
      (g : (x : A) -> B x)
      (x : A) -> C x (g x)
(f ∘ g) x = f (g x)

plus-two = suc ∘ suc

data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

head : {A : Set}{n : Nat} -> Vec A (suc n) -> A
head (x :: _) = x

tail : {A : Set}{n : Nat} -> Vec A (suc n) -> Vec A n
tail (_ :: xs) = xs

vmap : {A B : Set}{n : Nat} -> (A -> B) -> Vec A n -> Vec B n
vmap f [] = []
vmap f (x :: xs) = f x :: vmap f xs

data Vec₂ (A : Set) : Nat -> Set where
  nil : Vec₂ A zero
  cons : (n : Nat) -> A -> Vec₂ A n -> Vec₂ A (suc n)

vmap₂ : {A B : Set}(n : Nat) -> (A -> B) -> Vec₂ A n -> Vec₂ B n
vmap₂ .zero f nil = nil
vmap₂ .(suc n) f (cons n x xs) = cons n (f x) (vmap₂ n f xs)

vmap₃ : {A B : Set}(n : Nat) -> (A -> B) -> Vec₂ A n -> Vec₂ B n
vmap₃ zero f nil = nil
vmap₃ (suc n) f (cons .n x xs) = cons n (f x) (vmap₃ n f xs)

data Image_∋_ {A B : Set}(f : A -> B) : B -> Set where
  im : (x : A) -> Image f ∋ f x

inv : {A B : Set}(f : A -> B)(y : B) -> Image f ∋ y -> A
inv f .(f x) (im x) = x

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)

magic : {A : Set} -> Fin zero -> A
magic ()

data Empty : Set where
  empty : Fin zero -> Empty

magic' : {A : Set} -> Empty -> A
magic' (empty ())

_!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
[] ! ()
(x :: xs) ! fzero = x
(x :: xs) ! (fsuc i) = xs ! i

tabulate : {n : Nat}{A : Set} -> (Fin n -> A) -> Vec A n
tabulate {zero} f = []
tabulate {suc n} f = f fzero :: tabulate (f ∘ fsuc)

data False : Set where
record True : Set where

trivial : True
trivial = _

isTrue : Bool -> Set
isTrue true = True
isTrue false = False

_<_ : Nat -> Nat -> Bool
_ < zero = false
zero < suc n = true
suc m < suc n = m < n

length : {A : Set} -> List A -> Nat
length [] = zero
length (x :: xs) = suc (length xs)

lookup : {A : Set}(xs : List A)(n : Nat) -> isTrue (n < length xs) -> A
lookup [] n ()
lookup (x :: xs) zero p = x
lookup (x :: xs) (suc n) p = lookup xs n p

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data _≤_ : Nat -> Nat -> Set where
  leq-zero : {n : Nat} -> zero ≤ n
  leq-suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

leq-trans : {l m n : Nat} -> l ≤ m -> m ≤ n -> l ≤ n
leq-trans leq-zero _ = leq-zero
leq-trans (leq-suc p) (leq-suc q) = leq-suc (leq-trans p q)

min : Nat -> Nat -> Nat
min x y with x < y
min x y | true = x
min x y | false = y

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (x :: xs) with p x
... | true = x :: filter p xs
... | false = filter p xs

data _≠_ : Nat -> Nat -> Set where
  z≠s : {n : Nat} -> zero ≠ suc n
  s≠z : {n : Nat} -> suc n ≠ zero
  s≠s : {m n : Nat} -> m ≠ n -> suc m ≠ suc n

data Equal? (n m : Nat) : Set where
  eq : n == m -> Equal? n m
  neq : n ≠ m -> Equal? n m

equal? : (n m : Nat) -> Equal? n m
equal? zero zero = eq refl
equal? zero (suc m) = neq z≠s
equal? (suc n) zero = neq s≠z
equal? (suc n) (suc m) with equal? n m
equal? (suc n) (suc .n) | eq refl = eq refl
equal? (suc n) (suc m) | neq p = neq (s≠s p)

infix 20 _⊆_
data _⊆_ {A : Set} : List A -> List A -> Set where
  stop : [] ⊆ []
  drop : forall {xs y ys} -> xs ⊆ ys -> xs ⊆ y :: ys
  keep : forall {x xs ys} -> xs ⊆ ys -> x :: xs ⊆ x :: ys

lem-filter : {A : Set}(p : A -> Bool)(xs : List A) -> filter p xs ⊆ xs
lem-filter p [] = stop
lem-filter p (x :: xs) with p x
... | true = keep (lem-filter p xs)
... | false = drop (lem-filter p xs)

{-
lem-t : (p : Nat -> Bool)(xs : List Nat) -> (zero :: filter p xs) ⊆ xs
lem-t p [] = stop
lem-t p (x :: xs) with p x
... | true = keep (lem-filter p xs)
... | false = drop (lem-filter p xs)
-}

lem-plus-zero : (n : Nat) -> n + zero == n
lem-plus-zero zero = refl
lem-plus-zero (suc n) with n + zero | lem-plus-zero n
... | .n | refl = refl

module MayBe where
  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A -> Maybe A

  maybe : {A B : Set} -> B -> (A -> B) -> Maybe A -> B
  maybe z f nothing = z
  maybe z f (just x) = f x

module A where
  private
    internal : Nat
    internal = zero

  exported : Nat -> Nat
  exported n = n + internal

mapMaybe₁ : {A B : Set} -> (A -> B) -> MayBe.Maybe A -> MayBe.Maybe B
mapMaybe₁ f MayBe.nothing = MayBe.nothing
mapMaybe₁ f (MayBe.just x) = MayBe.just (f x)

mapMaybe₂ : {A B : Set} -> (A -> B) -> MayBe.Maybe A -> MayBe.Maybe B
mapMaybe₂ f m = let open MayBe in maybe nothing (just ∘ f) m

open MayBe

mapMaybe₃ : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
mapMaybe₃ f = maybe nothing (just ∘ f)

open MayBe
  hiding (maybe)
  renaming (Maybe to _option; nothing to none; just to some)

mapOption : {A B : Set} -> (A -> B) -> A option -> B option
mapOption f none = none
mapOption f (some x) = some (f x)

mtrue : Maybe Bool
mtrue = mapOption not (just false)

module Sort (A : Set)(_<_ : A -> A -> Bool) where
  insert : A -> List A -> List A
  insert y [] = y :: []
  insert y (x :: xs) with x < y
  ... | true = x :: insert y xs
  ... | false = y :: x :: xs

  sort : List A -> List A
  sort [] = []
  sort (x :: xs) = insert x (sort xs)

sort₁ : (A : Set)(_<_ : A -> A -> Bool) -> List A -> List A
sort₁ = Sort.sort

module SortNat = Sort Nat _<_

sort₂ : List Nat -> List Nat
sort₂ = SortNat.sort

open Sort Nat _<_ renaming (insert to insertNat; sort to sortNat)

module Lists (A : Set)(_<_ : A -> A -> Bool) where
  open Sort A _<_ public

  minimum : List A -> Maybe A
  minimum xs with sort xs
  ... | [] = nothing
  ... | y :: ys = just y

-- import Logic using (_∧_; _∨_)

record Point : Set where
  field x : Nat
        y : Nat

mkPoint : Nat -> Nat -> Point
mkPoint a b = record { x = a; y = b }

getX : Point -> Nat
getX = Point.x

abs² : Point -> Nat
abs² p = let open Point p in x * x + y * y
