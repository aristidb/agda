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

infixr 30 _::_
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

isFalse : Bool -> Set
isFalse true = False
isFalse false = True

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

  data SameLength : List A -> List A -> Set where
    nil : SameLength [] []
    cons : forall {xs ys} -> (x : A)(y : A) -> SameLength xs ys -> SameLength (x :: xs) (y :: ys)
    eqv : (xs : List A) -> SameLength xs xs

  sl-commut : {xs ys : List A} -> SameLength xs ys -> SameLength ys xs
  sl-commut nil = nil
  sl-commut (cons x y p) = cons y x (sl-commut p)
  sl-commut (eqv xs) = (eqv xs)

  {-
  sl-assoc : {xs ys zs : List A} -> SameLength xs ys -> SameLength ys zs -> SameLength xs zs
  sl-assoc nil nil = nil
  sl-assoc (eqv xs) (eqv xs) = eqv xs
  -}

  {-
  lem-insert-pres : (y : A)(xs : List A) -> SameLength (y :: xs) (insert y xs)
  lem-insert-pres y [] = cons y y nil
  lem-insert-pres y (x :: xs) with x < y
  lem-insert-pres y (x :: xs) | false = cons y y (eqv (x :: xs))
  lem-insert-pres y (x :: xs) | true = cons x x (lem-insert-pres y xs)
  -}

  data Sorted : List A -> Set where
    snil : Sorted []
    sone : (x : A) -> Sorted (x :: [])
    smult : (x : A) -> (y : A) -> (ys : List A) -> isFalse (y < x) -> Sorted (y :: ys) -> Sorted (x :: y :: ys)

  {-
  lem-insert : (x : A) -> (ys : List A) -> Sorted ys -> Sorted (insert x ys)
  lem-insert x [] p = sone x
  lem-insert x (y :: ys) p with y < x
  lem-insert x (y :: ys) p | false = smult x y ys _ p
  lem-insert x (y :: []) p | true = smult y x [] _ (sone x)
  lem-insert x (y :: ys) p | true = let zs = insert x ys
                                    in  
  -}

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

record Monad (M : Set -> Set) : Set1 where
  field
    return : {A : Set} -> A -> M A
    _>>=_ : {A B : Set} -> M A -> (A -> M B) -> M B

  mapM : {A B : Set} -> (A -> M B) -> List A -> M (List B)
  mapM f [] = return []
  mapM f (x :: xs) = f x >>= \y -> mapM f xs >>= \ys -> return (y :: ys)

mapM' : {M : Set -> Set} -> Monad M -> {A B : Set} -> (A -> M B) -> List A -> M (List B)
mapM' Mon f xs = Monad.mapM Mon f xs

Matrix : Set -> Nat -> Nat -> Set
Matrix A n m = Vec (Vec A n) m

vec : {n : Nat}{A : Set} -> A -> Vec A n
vec {zero} x = []
vec {suc n} x = x :: vec x

infixl 90 _$_
_$_ : {n : Nat}{A B : Set} -> Vec (A -> B) n -> Vec A n -> Vec B n
[] $ [] = []
(f :: fs) $ (x :: xs) = f x :: (fs $ xs)

transpose : forall {A n m} -> Matrix A n m -> Matrix A m n
transpose [] = vec []
transpose ([] :: y') = []
transpose ((y :: y') :: y0) = (y :: vec head $ y0) :: transpose (y' :: vec tail $ y0)

lem-!-tab : forall {A n} -> (f : Fin n -> A)(i : Fin n) -> (tabulate f ! i) == f i
lem-!-tab f fzero = refl
lem-!-tab f (fsuc j) = lem-!-tab (f ∘ fsuc) j

cong : forall {A B}{x y}(f : A -> B) -> x == y -> f x == f y
cong f refl = refl

comm : {A : Set}{x y : A} -> x == y -> y == x
comm refl = refl

comm-plus : (x y : Nat) -> x + y == y + x
comm-plus zero zero = refl
comm-plus zero (suc m) with m + zero | comm-plus zero m
... | .m | refl = refl
comm-plus (suc n) zero with n + zero | comm-plus zero n
... | .n | refl = refl
comm-plus (suc n) (suc m) with n + m | n + suc m | m + suc n | comm-plus n m | comm-plus n (suc m) | comm-plus (suc n) m
... | .(m + n) | .(suc (m + n)) | .(suc (m + n)) | refl | refl | refl = cong suc refl

with-plus : {A : Set}{n : Nat} -> (k : Nat) -> (f : Fin (k + n) -> A) -> (Fin n -> A)
with-plus zero f = f
with-plus (suc k) f = with-plus k (f ∘ fsuc)

vdrop : {A : Set}{n : Nat} -> (k : Nat) -> Vec A (k + n) -> Vec A n
vdrop zero v = v
vdrop (suc k) v = vdrop k (tail v)

lem-vdrop-empty : {A : Set}(n : Nat) -> (xs : Vec A (n + zero)) -> vdrop n xs == []
lem-vdrop-empty zero [] = refl
lem-vdrop-empty (suc n) (x :: xs) = lem-vdrop-empty n xs

-- courtesy of dschoepe
lem-tab-! : forall {A n} (xs : Vec A n) -> tabulate (_!_ xs) == xs
lem-tab-! [] = refl
lem-tab-! (x :: xs) = cong (_::_ x) (aux x xs)
  where aux : {A : Set}{n : Nat}(x : A)(xs : Vec A n) -> tabulate (_!_ (x :: xs) ∘ fsuc) == xs
        aux x [] = refl
        aux x (x' :: xs) = cong (_::_ x') (aux x' xs)

⊆-refl : {A : Set}{xs : List A} -> xs ⊆ xs
⊆-refl {A} {[]} = stop
⊆-refl {A} {y :: y'} = keep ⊆-refl

⊆-trans : {A : Set}{xs ys zs : List A} -> xs ⊆ ys -> ys ⊆ zs -> xs ⊆ zs
⊆-trans stop stop = stop
⊆-trans stop (drop p) = drop p
⊆-trans (drop p) (drop q) = drop (⊆-trans (drop p) q) 
⊆-trans (drop p) (keep q) = drop (⊆-trans p q)
⊆-trans (keep p) (drop q) = drop (⊆-trans (keep p) q)
⊆-trans (keep p) (keep q) = keep (⊆-trans p q)

--infixr 30 _::_
data SubList {A : Set} : List A -> Set where
  [] : SubList []
  _::_ : forall x {xs} -> SubList xs -> SubList (x :: xs)
  skip : forall {x xs} -> SubList xs -> SubList (x :: xs)

forget : {A : Set}{xs : List A} -> SubList xs -> List A
forget [] = []
forget (x :: y) = x :: forget y
forget (skip y) = forget y

lem-forget : {A : Set}{xs : List A}(zs : SubList xs) -> forget zs ⊆ xs
lem-forget [] = stop
lem-forget (x :: y) = keep (lem-forget y)
lem-forget (skip y) = drop (lem-forget y)

filter' : {A : Set} -> (A -> Bool) -> (xs : List A) -> SubList xs
filter' p [] = []
filter' p (y :: ys) with p y
... | true = y :: filter' p ys
... | false = skip (filter' p ys)

complement : {A : Set}{xs : List A} -> SubList xs -> SubList xs
complement [] = []
complement (x :: y) = skip y
complement {xs = x :: _} (skip y) = x :: y

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
x :: xs ++ ys = x :: (xs ++ ys) 

concatMap : {A : Set}{B : Set} -> (f : A -> List B) -> List A -> List B
concatMap f [] = []
concatMap f (x :: xs) = f x ++ concatMap f xs

sublists : {A : Set}(xs : List A) -> List (SubList xs)
sublists [] = [] :: []
sublists (x :: xs) = concatMap (λ ys → (x :: ys) :: skip ys :: []) (sublists xs)
