open import Function
open import Relation.Binary.PropositionalEquality
open import Level
open import Data.Product
open import Data.Nat hiding (_⊔_)


module univalence where

-- homotopy, taken from robert rose's code. Replaced symbol with '~', previously looked like '~' but secretly was different
module _ {i j} {X : Set i} {P : X → Set j} where
  infix 4 _~_
  _~_ : (f g : (x : X) → P x) → Set (i ⊔ j)
  f ~ g = (x : X) → f x ≡ g x

module _ {i j} {A : Set i} {B : Set j} where
  isequiv : (f : A → B) → Set (i ⊔ j)
  isequiv f = (Σ (B → A) (λ g → f ∘ g ~ id)) × (Σ (B → A) (λ h → h ∘ f ~ id))
