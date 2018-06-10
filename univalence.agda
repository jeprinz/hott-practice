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

module _ {i j} {A : Set i} {B : Set j} where --define an equivalence between types
  isequiv : (f : A → B) → Set (i ⊔ j)
  isequiv f = (Σ (B → A) (λ g → f ∘ g ~ id)) × (Σ (B → A) (λ h → h ∘ f ~ id))

module _ {i j} (A : Set i) (B : Set j) where -- define the type of equivalences A≃B. BTW, for '≃' type '\~-'
  _≃_ : Set (i ⊔ j)
  _≃_ = Σ (A → B) (λ f → isequiv f)

--Practice using equivalences by coding up some lemmas
--Lemma 2.4.12
module Lemma2412 {A B C : Set} where
  idA : A → A
  idA x = x

  lemma1 : idA ∘ idA ~ idA
  lemma1 x = refl

  parti : A ≃ A
  parti = (idA , ((idA , lemma1) , (idA , lemma1)))
  --      (f   , ((g   , proof)  , (h   ,  proof)))

  partii : A ≃ B → B ≃ A
  partii (f , ((g , proofg) , (h , proofh))) = {!   !}

-- again from robert rose code
module _ {i j} {A : Set i} {P : A → Set j} {- I would leave P explicit -} where
  transport : {x y : A} → (p : x ≡ y) → P(x) → P(y)
  transport refl Px = Px
