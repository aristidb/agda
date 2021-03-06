------------------------------------------------------------------------
-- Subsets of finite sets
------------------------------------------------------------------------

module Data.Fin.Subset where

open import Algebra
import Algebra.Props.BooleanAlgebra as BoolAlgProp
import Algebra.Props.BooleanAlgebra.Expression as BAExpr
import Data.Bool.Properties as BoolProp
open import Data.Fin
open import Data.List as List using (List)
open import Data.Nat
open import Data.Product
open import Data.Vec using (Vec; _∷_; _[_]=_)
import Relation.Binary.Vec.Pointwise as Pointwise
open import Relation.Nullary

infix 4 _∈_ _∉_ _⊆_ _⊈_

------------------------------------------------------------------------
-- Definitions

-- Sides.

open import Data.Bool public
  using () renaming (Bool to Side; true to inside; false to outside)

-- Partitions a finite set into two parts, the inside and the outside.

Subset : ℕ → Set
Subset = Vec Side

------------------------------------------------------------------------
-- Membership and subset predicates

_∈_ : ∀ {n} → Fin n → Subset n → Set
x ∈ p = p [ x ]= inside

_∉_ : ∀ {n} → Fin n → Subset n → Set
x ∉ p = ¬ (x ∈ p)

_⊆_ : ∀ {n} → Subset n → Subset n → Set
p₁ ⊆ p₂ = ∀ {x} → x ∈ p₁ → x ∈ p₂

_⊈_ : ∀ {n} → Subset n → Subset n → Set
p₁ ⊈ p₂ = ¬ (p₁ ⊆ p₂)

------------------------------------------------------------------------
-- Set operations

-- Pointwise lifting of the usual boolean algebra for booleans gives
-- us a boolean algebra for subsets.
--
-- The underlying equality of the returned boolean algebra is
-- propositional equality.

booleanAlgebra : ℕ → BooleanAlgebra _ _
booleanAlgebra n =
  BoolAlgProp.replace-equality
    (BAExpr.lift BoolProp.booleanAlgebra n)
    Pointwise.Pointwise-≡

private
  open module BA {n} = BooleanAlgebra (booleanAlgebra n) public
    using
      ( ⊥  -- The empty subset.
      ; ⊤  -- The subset containing all elements.
      )
    renaming
      ( _∨_ to _∪_  -- Binary union.
      ; _∧_ to _∩_  -- Binary intersection.
      ; ¬_  to ∁    -- Complement.
      )

-- A singleton subset, containing just the given element.

⁅_⁆ : ∀ {n} → Fin n → Subset n
⁅ zero  ⁆ = inside  ∷ ⊥
⁅ suc i ⁆ = outside ∷ ⁅ i ⁆

-- N-ary union.

⋃ : ∀ {n} → List (Subset n) → Subset n
⋃ = List.foldr _∪_ ⊥

-- N-ary intersection.

⋂ : ∀ {n} → List (Subset n) → Subset n
⋂ = List.foldr _∩_ ⊤

------------------------------------------------------------------------
-- Properties

Nonempty : ∀ {n} (p : Subset n) → Set
Nonempty p = ∃ λ f → f ∈ p

Empty : ∀ {n} (p : Subset n) → Set
Empty p = ¬ Nonempty p

-- Point-wise lifting of properties.

Lift : ∀ {n} → (Fin n → Set) → (Subset n → Set)
Lift P p = ∀ {x} → x ∈ p → P x
