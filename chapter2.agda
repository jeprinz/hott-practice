open import Relation.Binary.PropositionalEquality
open import path-induction

module chapter2 where

_∙_ : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl ∙ refl = refl

module lemma214 (A : Set) (x y z w : A) (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) where
  lemmai1 : p ≡ p ∙ refl
  lemmai1 = ind A ? ?
  lemmai2 : p ≡ refl ∙ p
  lemmai2 = {!   !}



module loopSpace (A : Set) (a : A) where


  path : Set
  path = a ≡ a

  2path : Set
  2path = refla ≡ refla
    where refla : a ≡ a
          refla = refl

  2pathcommute : (α β : 2path) → α ∙ β ≡ β ∙ α
  2pathcommute refl refl = refl

only1eq : {A : Set} → {a b : A} → (p : a ≡ b) → (q : a ≡ b) → p ≡ q
only1eq refl refl = refl
-- given the fact that I can define the above, I really dont understand what all of this means.
-- This proves there is only one element of a ≡ b, so why are we bothering with all of this nonsense?
