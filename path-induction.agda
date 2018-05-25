-- here I will attempt to derive path induction, not sure if actually possible or what

open import Relation.Binary.PropositionalEquality
open import Data.Nat


-- indicernability of identicals
ioi : (A : Set) → (C : (A → Set)) → (x : A) → (y : A) → (p : x ≡ y) → (C x) → (C y)
ioi a C x y refl Cx = Cx
-- ioi a C x y p = subst C p
-- The above is also equivalent, So
-- this means that indicernability of identicals is the same thing as subst


-- mytrans : ∀ A → ∀ B → ∀ C → A ≡ B → B ≡ C → A ≡ C
-- mytrans a b c p1 p2 = {!   !}


-- path induction
-- First, define some things to make this easier...
-- refer to page 64 in hott book
CType : Set → Set₁ -- This is the type of C in the definition of path induction
CType A = (x : A) → (y : A) → x ≡ y → Set

cType : (A : Set) → CType A → Set -- The type of lower case c in definition
cType A C = (x : A) → C x x refl

fType : (A : Set) → CType A → Set -- This is the output type f in the function
fType A C = (x : A) → (y : A) → (p : x ≡ y) → C x y p


ind : (A : Set) → (C : CType A) → (c : cType A C) → fType A C
ind A C c x y refl = c x
