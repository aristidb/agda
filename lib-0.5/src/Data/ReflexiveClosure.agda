------------------------------------------------------------------------
-- Reflexive closures
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Data.ReflexiveClosure where

open import Data.Unit
open import Level
open import Relation.Binary
open import Relation.Binary.Simple

------------------------------------------------------------------------
-- Reflexive closure

data Refl {a ℓ} {A : Set a} (_∼_ : Rel A ℓ) : Rel A (a ⊔ ℓ) where
  [_]  : ∀ {x y} (x∼y : x ∼ y) → Refl _∼_ x y
  refl : Reflexive (Refl _∼_)

-- Map.

map : ∀ {a a′ ℓ ℓ′} {A : Set a} {A′ : Set a′}
        {_R_ : Rel A ℓ} {_R′_ : Rel A′ ℓ′} {f : A → A′} →
      _R_ =[ f ]⇒ _R′_ → Refl _R_ =[ f ]⇒ Refl _R′_
map R⇒R′ [ xRy ] = [ R⇒R′ xRy ]
map R⇒R′ refl    = refl

-- The reflexive closure has no effect on reflexive relations.

drop-refl : ∀ {a ℓ} {A : Set a} {_R_ : Rel A ℓ} →
            Reflexive _R_ → Refl _R_ ⇒ _R_
drop-refl rfl [ x∼y ] = x∼y
drop-refl rfl refl    = rfl

------------------------------------------------------------------------
-- Example: Maybe

module Maybe where

  Maybe : ∀ {ℓ} → Set ℓ → Set ℓ
  Maybe A = Refl (Const A) tt tt

  nothing : ∀ {a} {A : Set a} → Maybe A
  nothing = refl

  just : ∀ {a} {A : Set a} → A → Maybe A
  just = [_]
