open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product

module ch2sec2 where


transport : {A : Set} → {P : A → Set} → {x y : A} → (p : x ≡ y) → P(x) → P(y)
transport refl Px = Px

-- lift-u-p1  : {A : Set} → {P : A → Set} → {x y : A} → (p : x ≡ y) → (u : P x) → (x , y) ≡ (y , transport p u)
-- lift-u-p1 = {!   !}

module Lemma232 {A : Set} (P : A → Set) (x y : A) (u : P x) (p : x ≡ y) where
  p* : P(x) → P(y)
  p* = transport p

  type : Set
  type = left ≡ right
   where left : Σ A P
         left = (x , u)
         right : Σ A P
         right = (y , p* u)

  l : Σ A P
  l = (x , u)
  r : Σ A P
  r = (y , p* u)

  lemma : (x ≡ y) → l ≡ r
  lemma refl = {!   !}

  lift-u-p : type
  lift-u-p = lemma p

  -- test : (x ≡ y) → u ≡ p* u
  -- test = ?
