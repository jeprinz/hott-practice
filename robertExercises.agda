open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product

P : {X : Set} → X × X → Set
P (x , y) = x ≡ y

ex1 : {X : Set} → Σ (X × X) P ≡ X
ex1 = ?
