module peano where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + zero = zero
zero + n = n
suc n + n' = suc (n + n')

proof₁ : ℕ
proof₁ = suc (suc (suc (suc (suc zero))))

proof₂' : (A : Set) → A → A
proof₂' _ x = x

proof₂ : ℕ → ℕ
proof₂ = proof₂' ℕ

data _∧_ (P : Set) (Q : Set) : Set where
  ∧-intro : P → Q → (P ∧ Q)

proof₃ : {P Q : Set} → (P ∧ Q) → P
proof₃ (∧-intro p q) = p

_⇔_ : (P : Set) → (Q : Set) → Set
a ⇔ b = (a → b) ∧ (b → a)

∧-comm' : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
∧-comm' (∧-intro p q) = ∧-intro q p

∧-comm : {P Q : Set} → (P ∧ Q) ⇔ (Q ∧ P)
∧-comm = ∧-intro ∧-comm' ∧-comm'

∧-assoc₁ : {P Q R : Set} → ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))
∧-assoc₁ (∧-intro (∧-intro p q) r) = ∧-intro p (∧-intro q r)

∧-assoc₂ : {P Q R : Set} → (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
∧-assoc₂ (∧-intro p (∧-intro q r)) = ∧-intro (∧-intro p q) r

∧-assoc : {P Q R : Set} → ((P ∧ Q) ∧ R) ⇔ (P ∧ (Q ∧ R))
∧-assoc = ∧-intro ∧-assoc₁ ∧-assoc₂

data _∨_ (P Q : Set) : Set where
  ∨₁ : P -> P ∨ Q
  ∨₂ : Q -> P ∨ Q

∨-elim : {A B C : Set} → (A → C) → (B → C) → (A ∨ B) → C
∨-elim ac bc (∨₁ a) = ac a
∨-elim ac bc (∨₂ b) = bc b

∨-comm' : {P Q : Set} → (P ∨ Q) → (Q ∨ P)
∨-comm' (∨₁ p) = ∨₂ p
∨-comm' (∨₂ q) = ∨₁ q

∨-comm : {P Q : Set} → (P ∨ Q) ⇔ (Q ∨ P)
∨-comm = ∧-intro ∨-comm' ∨-comm'

∨-assoc₁ : {P Q R : Set} → ((P ∨ Q) ∨ R) → (P ∨ (Q ∨ R))
∨-assoc₁ (∨₁ (∨₁ p)) = ∨₁ p
∨-assoc₁ (∨₁ (∨₂ q)) = ∨₂ (∨₁ q)
∨-assoc₁ (∨₂ r) = ∨₂ (∨₂ r)

∨-assoc₂ : {P Q R : Set} → (P ∨ (Q ∨ R)) → ((P ∨ Q) ∨ R)
∨-assoc₂ (∨₁ p) = ∨₁ (∨₁ p)
∨-assoc₂ (∨₂ (∨₁ q)) = ∨₁ (∨₂ q)
∨-assoc₂ (∨₂ (∨₂ r)) = ∨₂ r

∨-assoc : {P Q R : Set} → ((P ∨ Q) ∨ R) ⇔ (P ∨ (Q ∨ R))
∨-assoc = ∧-intro ∨-assoc₁ ∨-assoc₂

data ⊥ : Set where -- nothing

¬ : Set → Set
¬ A = A → ⊥

