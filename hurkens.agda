{-# OPTIONS --type-in-type #-}

open import Data.Nat

-- The following turns on universe levels, so Set : Set

⊥ : Set -- not usual bot type, but ok its equivalent
⊥ = (A : Set) → A

¬_ : Set → Set --negation of a statement
¬ A = A → ⊥

P : Set → Set -- P x is the type of type families on x
P A = A → Set


U : Set
--   X           f              p → Set, where p = P X
U = (X : Set) → (P (P X) → X) → P (P X)
--let thingo X = P (P X) = (X → Set) → Set = a function which given a type family on X, outputs a type
-- then U is the type of functions which given a type X, and function thingo X ­→ X, outputs a thingo X

τ : P (P U) → U -- given a thingo U, output a U
τ t = λ X f p →         (t λ x → p (f (x X f)))
-- everything to right of first → is a type

-- here are types of things:
-- t is a thingo U
-- everything to right of = is U, as described above
-- X is a type, and f : thingo X → X, and p : P X
-- to right of first →, we must produce a type
-- we do so by applying t to a function. Remember, t : thingo X, so given P X returns type
-- So we must give a P X = X → Type
-- the λ x creates function, and then the Type is p (f (x X f))
-- p is X → Set, and f : thingo X → X,


-- I give up for now, just copying...

σ : U -> P (P U)
σ s = s U \t -> τ t

Δ : P U
Δ = \y -> ¬ ((p : P U) -> σ y p -> p (τ (σ y)))

Ω : U
Ω = τ \p -> (x : U) -> σ x p -> p x

D : Set
D = (p : P U) -> σ Ω p -> p (τ (σ Ω))

lem₁ : (p : P U) -> ((x : U) -> σ x p -> p x) -> p Ω
lem₁ p H1 = H1 Ω \x -> H1 (τ (σ x))

lem₂ : ¬ D
lem₂ = lem₁ Δ \x H2 H3 -> H3 Δ H2 \p -> H3 \y -> p (τ (σ y))

lem₃ : D
lem₃ p = lem₁ \y -> p (τ (σ y))
loop : ⊥
loop = lem₂ lem₃

data Nothing : Set where

thing1 : ℕ
thing1 = 6

thing2 : Nothing
thing2 = loop Nothing
