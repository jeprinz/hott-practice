-- here I will attempt to derive path induction, not sure if actually possible or what

open import Relation.Binary.PropositionalEquality
open import Data.Nat

module path-induction where

-- indicernability of identicals
ioi : (A : Set) → (C : (A → Set)) → (x : A) → (y : A) → (p : x ≡ y) → (C x) → (C y)
ioi a C x y refl Cx = Cx
-- ioi a C x y p = subst C p
-- The above is also equivalent, So
-- this means that indicernability of identicals is the same thing as subst


-- This is how to define trans in terms of pattern matching
mytrans : (A : Set) → (B : Set) → (C : Set) → A ≡ B → B ≡ C → A ≡ C
mytrans a b c refl refl = refl


-- path induction
-- First, define some things to make this easier...
-- refer to page 64 in hott book
CType : Set → Set₁ -- This is the type of C in the definition of path induction
CType A = (x : A) → (y : A) → x ≡ y → Set

cType : (A : Set) → CType A → Set -- The type of lower case c in definition
cType A C = (x : A) → C x x refl

fType : (A : Set) → CType A → Set -- This is the output type f in the function
fType A C = (x : A) → (y : A) → (p : x ≡ y) → C x y p

indType : Set₁
indType = (A : Set) → (C : CType A) → (c : cType A C) → fType A C

ind : indType
ind A C c x y refl = c x

-- based path induction

CType' : (A : Set) → (a : A) → Set₁
CType' A a = (x : A) → a ≡ x → Set

cType' : (A : Set) → (a : A) → CType' A a → Set
cType' A a C = C a refl

fType' : (A : Set) → (a : A) → (C : CType' A a) → (c : cType' A a C) → Set
fType' A a C c = (x : A) → (p : a ≡ x) → C x p

indType' : Set₁
indType' = (A : Set) → (a : A) → (C : CType' A a) → (c : cType' A a C) → fType' A a C c

ind' : indType'
ind' A a C c x refl = c


--- Now, for the grand finaly: showing path induction and based path induction are same
--- IMPORTANT NoTE: WE ARE NOT ALLOWED TO USE PATTERN MATCHING HERE, THAT
--- WOULD DEFEAT THE POINT OF THIS EXERCISE

--Use ind' to derive something of type indType

regularFromBased : indType
regularFromBased A C c x y p = ind' A x (C x) (c x) y p

--Use ind to derive something of type indType'

-- basedFromRegular : indType'
-- basedFromRegular A a C c x p = {!   !}


-- Proof of Lemma 2.1.1 (aka construction of my own version of the 'sym' function)
mysym1 : {A : Set} → {x y : A} → x ≡ y → y ≡ x
mysym1 refl = refl -- with pattern matching, everthing is trivial. But hott wants us to do.....

-- mysym2 : {A : Set} → {x y : A} → x ≡ y → y ≡ x

-- first define
-- D : (A : Set) → CType A
-- D A x y p = y ≡ x
--
-- d : (A : Set) → (C : CType A) → cType A C
-- d A C x = {!   !}
--
--
-- mysym2 p = {!   !}
