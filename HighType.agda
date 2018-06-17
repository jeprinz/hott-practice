
open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Level

module HighType where --need better names

assertType : ∀ {i} → (A : Set i) → A → A
assertType _ x = x

module _ {i : Level} (A : Set i) where

  data HIType (path : A × A) : Set i where
    elmt : A → HIType path

data _≈_ {i} : {A : Set i} → A → A → Set (Level.suc i) where
  refl : {A : Set i} → {x : A} → x ≈ x
  path : {A : Set i} → (path : A × A) → ℕ →  (assertType (HIType A path) (elmt (proj₁ path))) ≈ elmt (proj₂ path)

-- prove some things

-- an example

data 𝟙 : Set where
  ⋆ : 𝟙

S¹ : Set
S¹ = HIType 𝟙 (⋆ , ⋆)

base : S¹
base = elmt ⋆

reflbase : base ≈ base
reflbase = refl
