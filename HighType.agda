
open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Product
open import Level

module HighType where --need better names

assertType : ∀ {i} → (A : Set i) → A → A
assertType _ x = x

module _ {i : Level} (A : Set i) where

  data HIType (path : A × A) : Set i where
    elmt : A → HIType path

data eq {i : Level} : {A : Set i} → ℕ → A → A → Set (Level.suc i) where
  refl : {A : Set i} → {x : A} → eq 0 x x
  path : {A : Set i} → (path : A × A) → eq 0 (assertType (HIType A path) (elmt (proj₁ path))) (elmt (proj₂ path))
  sym : {n : ℕ} → {A : Set i} → {x y : A} → eq n x y → eq n y x
  tran : {n : ℕ} → {A : Set i} → {x y z : A} → eq n x y → eq n y z → eq n x z


  -- higher order
  cancelsym : {n : ℕ} → {A : Set i} → {x y : A} → {p : eq n x y} → (assertType {!   !} {!   !}) -- eq (n + 1) p (sym (sym p))
  -- cancelts : {n : ℕ} → {A : Set i} → {x y z : A} →

-- suffice to say, the above will not work

-- prove some things

-- symet : ∀ {i} → {A : Set i} → {x y : A} → x ≈ y → y ≈ x
-- symet refl = refl
-- symet (path (a , b)) = {!   !}

-- an example

data 𝟙 : Set where
  ⋆ : 𝟙

S¹ : Set
S¹ = HIType 𝟙 (⋆ , ⋆)

base : S¹
base = elmt ⋆

-- reflbase : base ≈ base
-- reflbase = refl
