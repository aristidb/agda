module XML where

open import Data.String
open import Data.List hiding (_++_)
open import Data.Nat

Tag = String

mutual
  data Schema : Set where
    tag : Tag -> List Child -> Schema

  data Child : Set where
    text : Child
    elem : ℕ -> ℕ -> Schema -> Child

data BList (A : Set) : ℕ -> Set where
  [] : forall {n} -> BList A n
  _::_ : forall {n} -> A -> BList A n -> BList A (suc n)

data Cons (A B : Set) : Set where
  _::_ : A -> B -> Cons A B

data False : Set where

FList : Set -> ℕ -> ℕ -> Set
FList A zero m = BList A m
FList A (suc n) zero = False
FList A (suc n) (suc m) = Cons A (FList A n m)

infixr 30 _:all:_
data All {A : Set}(P : A -> Set) : List A -> Set where
  all[] : All P []
  _:all:_ : forall {x xs} -> P x -> All P xs -> All P (x ∷ xs)

mutual
  data XML : Schema -> Set where
    element : forall {kids}(t : Tag) -> All Element kids -> XML (tag t kids)

  Element : Child -> Set
  Element text = String
  Element (elem n m s) = FList (XML s) n m

mutual
  printXML : {s : Schema} -> XML s -> String
  printXML (element t xs) = "<" ++ t ++ ">" ++ printChildren xs ++ "</" ++ t ++ ">"

  printFirst : {kid : Child} -> Element kid -> String
  printFirst {text} x = x
  printFirst {elem zero m s} [] = ""
  printFirst {elem zero (suc m) s} (e :: es) = printXML e ++ printFirst es
  printFirst {elem (suc n) zero s} ()
  printFirst {elem (suc n) (suc m) s} (e :: es) = printXML e ++ printFirst es

  printChildren : {kids : List Child} -> All Element kids -> String
  printChildren all[] = ""
  printChildren (x :all: xs) = printFirst x ++ printChildren xs

schema : Schema
schema = tag "Root" (text ∷ [])

ex1 : XML schema
ex1 = element "Root" ("hallo" :all: all[])
