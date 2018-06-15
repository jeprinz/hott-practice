open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Empty -- for ⊥
open import univalence
open import Data.Product
open import Relation.Nullary
open import Data.Nat

module encodeDecode where

-- transport : {A : Set} → {P : A → Set} → {x y : A} → (p : x ≡ y) → P(x) → P(y)
-- transport refl Px = Px

contradiction : {A : Set} → ⊥ → A
contradiction ()

module theorem2-12-5 (A B : Set) (a₀ : A) where
  -- a : A ⊎ B
  -- a = inj₁ {!   !}

  code : A ⊎ B → Set
  code (inj₁ a) = a₀ ≡ a
  code (inj₂ b) = ⊥

  encode : (x : A ⊎ B) → (p : inj₁(a₀) ≡ x) → code x
  encode x refl = refl --this works in agda

  decode : (x : A ⊎ B) → code x → (inj₁ a₀ ≡ x)
  decode (inj₁ a) refl = refl
  decode (inj₂ b) bot = contradiction bot
  -- decode (inj₁ a) b = ?

  qinv1 : (x : A ⊎ B) → (p : (inj₁ a₀) ≡ x) → decode x (encode x p) ≡ p
  qinv1 x refl = refl

  -- this helper is needed below so that I can do path induction after coproduct induction
  helper : {a : A} → (p : a₀ ≡ a) → encode (inj₁ a) (decode (inj₁ a) p) ≡ p
  helper refl = refl

  qinv2 : (x : A ⊎ B) → (c : code x) → encode x (decode x c) ≡ c
  qinv2 (inj₁ a) c = helper c -- agda really really needs a way to do pattern matching inline......
  qinv2 (inj₂ b) c = contradiction c

  fact : (x : A ⊎ B) → isequiv (encode x)
  -- fact x = ((decode x , qinv2 x) , (decode x, qinv1 x)) -- why doesnt this line compile
  fact (inj₁ a) = ((decode (inj₁ a) , qinv2 (inj₁ a)) , (decode (inj₁ a), qinv1 (inj₁ a)))
  fact (inj₂ b) = ((decode (inj₂ b) , qinv2 (inj₂ b)) , (decode (inj₂ b), qinv1 (inj₂ b)))



  -- fact2 : (b : B) → isequiv ()

  theorem : (x : A ⊎ B) → (inj₁(a₀) ≡ x) ≃ code x
  theorem x = (encode x , fact x)

  -- in Agda, this doesnt even actually require the above theorem.
  result : {a : A} → {b : B} → ¬ (inj₁ a ≡ inj₂ b)
  result ()

  -- it seems really bizzare that this is the only way to prove 0 ~= 1
  -- is there another way? is the problem with how path induction works?
