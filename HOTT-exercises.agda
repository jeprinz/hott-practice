module HOTT-exercises where

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary

--------------------------------------------------------------------------------
-- Exercise 1.1

-- define composition - is this in stdlib?
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x → f (g x)

proof1 : {A B C D : Set} {f : C → D} {g : B → C} {h : A → B} → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
proof1 = refl

-- Ok in agda the proof is refl, but what does this mean in the context of what the HOTT book says?
--------------------------------------------------------------------------------
-- Exercise 1.2

--define product type (can't figure out how to use stdlib)
data _∧_ (A B : Set) : Set where
  _×_ : A → B → A ∧ B

pr1 : {A B : Set} → A ∧ B → A -- projection functions
pr1 (a × b) = a

pr2 : {A B : Set} → A ∧ B → B
pr2 (a × b) = b

rec× : {A B C : Set} → (A → B → C) → A ∧ B → C
rec× g and = g (pr1 and) (pr2 and)

rec×-verify : {A B C : Set} → (g : A → B → C) → (a : A) → (b : B) →
  rec× g (a × b) ≡ g a b
rec×-verify g a b = refl
--------------------------------------------------------------------------------
-- Exercise 1.11
-- Show that for any type A, we have ¬¬¬ A → ¬ A.

proof11 : {A : Set} → ¬ (¬ (¬ A)) → ¬ A
proof11 notNotNotA a = notNotNotA (λ notA → notA a)

--------------------------------------------------------------------------------

-- Couldnt find the coproduct type in stdlib
data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B


-- Exercise 1.12

-- (i) If A, then (if B then A).
proof12i : {A B : Set} → A → (B → A)
proof12i a = λ b → a
-- (ii) If A, then not (not A).
proof12ii : {A B : Set} → A → ¬ (¬ A)
proof12ii a = λ f → f a
-- (iii) If (not A or not B), then not (A and B).
proof12iii : {A B : Set} → ((¬ A) ∨ (¬ B)) → ¬ (A ∧ B)
proof12iii (left notA) (a × b) = notA a
proof12iii (right notB) (a × b) = notB b
--------------------------------------------------------------------------------

-- Exercise 1.13
--prove not (not (P or not P)).

proof13 : {P : Set} → ¬ ¬ (P ∨ (¬ P))
proof13 notPOrNotP = notPOrNotP (right (λ p → (notPOrNotP (left   p))))
--------------------------------------------------------------------------------
-- Exercise 1.14

f : (x : Set) → (p : x ≡ x) → p ≡ refl
f x refl = refl

--------------------------------------------------------------------------------
