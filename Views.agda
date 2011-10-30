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

data Find {A : Set}(p : A -> Bool) : List A -> Set where
  found : (xs : List A)(y : A) -> satisfies p y -> (ys : List A) -> Find p (xs ++ y ∷ ys)
  not-found : forall {xs} -> All (satisfies (not ∘ p)) xs -> Find p xs

find₁ : {A : Set}(p : A -> Bool)(xs : List A) -> Find p xs
find₁ p [] = not-found all[]
find₁ p (x ∷ xs) with p x
... | true = found [] x {! !} xs
... | false = {! !}

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data Inspect {A : Set}(x : A) : Set where
  it : (y : A) -> x == y -> Inspect x

inspect : {A : Set}(x : A) -> Inspect x
inspect x = it x refl

trueIsTrue : {x : Bool} -> x == true -> T x
trueIsTrue refl = _

falseIsFalse : {x : Bool} -> x == false -> T (not x)
falseIsFalse refl = _

find : {A : Set}(p : A -> Bool)(xs : List A) -> Find p xs
find p [] = not-found all[]
find p (x ∷ xs) with inspect (p x)
... | it true prf = found [] x (trueIsTrue prf) xs
... | it false prf with find p xs
find p (x ∷ ._) | it false _ | found xs y py ys = found (x ∷ xs) y py ys
find p (x ∷ xs) | it false prf | not-found npxs = not-found (falseIsFalse prf :all: npxs)

data _∈_ {A : Set}(x : A) : List A -> Set where
  hd : forall {xs} -> x ∈ (x ∷ xs)
  tl : forall {xs y ys} -> x ∈ xs -> x ∈ (y ∷ ys)

index : {A : _}{x : A}{xs : _} -> x ∈ xs -> ℕ
index hd = zero
index (tl p) = suc (index p)

data Lookup {A : Set}(xs : List A) : ℕ -> Set where
  inside : (x : A)(p : x ∈ xs) -> Lookup xs (index p)
  outside : (m : ℕ) -> Lookup xs (length xs + m)

_!_ : {A : Set}(xs : List A)(n : ℕ) -> Lookup xs n
[] ! n = outside n
(x ∷ xs) ! zero = inside x hd
(x ∷ xs) ! suc n with xs ! n
(x ∷ xs) ! suc .(index p) | inside y p = inside y (tl p)
(x ∷ xs) ! suc .(length xs + n) | outside n = outside n

infixr 30 _⟶_
data Type : Set where
  ı : Type
  _⟶_ : Type -> Type -> Type

data Equal? : Type -> Type -> Set where
  yes : forall {τ} -> Equal? τ τ
  no : forall {σ τ} -> Equal? σ τ

_=?=_ : (σ τ : Type) -> Equal? σ τ
ı =?= ı = yes
ı =?= (_ ⟶ _) = no
(_ ⟶ _) =?= ı = no
(σ₁ ⟶ τ₁) =?= (σ₂ ⟶ τ₂) with σ₁ =?= σ₂ | τ₁ =?= τ₂
(σ ⟶ τ) =?= (.σ ⟶ .τ) | yes | yes = yes
(σ₁ ⟶ τ₁) =?= (σ₂ ⟶ τ₂) | _ | _ = no

infixl 80 _$$_
data Raw : Set where
  var : ℕ -> Raw
  _$$_ : Raw -> Raw -> Raw
  lam : Type -> Raw -> Raw

Cxt = List Type

data Term (Γ : Cxt) : Type -> Set where
  var : forall {τ} -> τ ∈ Γ -> Term Γ τ
  _$$_ : forall {σ τ} -> Term Γ (σ ⟶ τ) -> Term Γ σ -> Term Γ τ
  lam : forall σ {τ} -> Term (σ ∷ Γ) τ -> Term Γ (σ ⟶ τ)

erase : forall {Γ τ} -> Term Γ τ -> Raw
erase (var x) = var (index x)
erase (t $$ u) = erase t $$ erase u
erase (lam σ τ) = lam σ (erase τ)

data Infer (Γ : Cxt) : Raw -> Set where
  ok : (τ : Type)(t : Term Γ τ) -> Infer Γ (erase t)
  bad : {e : Raw} -> Infer Γ e

infer : (Γ : Cxt)(e : Raw) -> Infer Γ e
infer Γ (var n) with Γ ! n
infer Γ (var .(length Γ + n)) | outside n = bad
infer Γ (var .(index x)) | inside σ x = ok σ (var x)
infer Γ (e₁ $$ e₂) with infer Γ e₁
infer Γ (e₁ $$ e₂) | bad = bad
infer Γ (.(erase t₁) $$ e₂) | ok ı t₁ = bad
infer Γ (.(erase t₁) $$ e₂) | ok (σ ⟶ τ) t₁ with infer Γ e₂
infer Γ (.(erase t₁) $$ e₂) | ok (σ ⟶ τ) t₁ | bad = bad
infer Γ (.(erase t₁) $$ .(erase t₂)) | ok (σ ⟶ τ) t₁ | ok σ' t₂ with σ =?= σ'
infer Γ (.(erase t₁) $$ .(erase t₂))
  | ok (σ ⟶ τ) t₁ | ok .σ t₂ | yes = ok τ (t₁ $$ t₂)
infer Γ (.(erase t₁) $$ .(erase t₂))
  | ok (σ ⟶ τ) t₁ | ok σ' t₂ | no = bad
infer Γ (lam σ e) with infer (σ ∷ Γ) e
infer Γ (lam σ .(erase t)) | ok τ t = ok (σ ⟶ τ) (lam σ t)
infer Γ (lam σ e) | bad = bad
