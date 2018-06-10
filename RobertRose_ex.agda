{-# OPTIONS --without-K #-}


open import Level
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Function

module RobertRose_ex where

infix 4 _==_
_==_ = _≡_
{- for consistency with the book
   (also, consider renaming Set to Type... -}

module _ {i j} {X : Set i} {P : X → Set j} where
  infix 4 _∼_
  _∼_ : (f g : (x : X) → P x) → Set (i ⊔ j)
  f ∼ g = (x : X) → f x == g x

module _ {i j} {A : Set i} {P : A → Set j} {- I would leave P explicit -} where
  transport : {x y : A} → (p : x ≡ y) → P(x) → P(y)
  transport refl Px = Px

-- lift-u-p1  : {A : Set} → {P : A → Set} → {x y : A} → (p : x ≡ y) → (u : P x) → (x , y) ≡ (y , transport p u)
-- lift-u-p1 = {!   !}

module Lemma232' {i j} {A : Set i} (P : A → Set j) where

  lemma : {x y : A} → (p : x == y) → (ux : P x)
          → (x , ux) == (y , transport {P = P} p ux)
  lemma refl ux = refl

------

module _ {i} (X : Set i) where
  P : Set i
  P = Σ X (λ x → Σ X (λ y → x == y))

module _ {i} {X : Set i} (x₀ : X) where
  P* : Set i
  P* = Σ X (λ x → x == x₀)

module Ex1 {i} (X : Set i) where
  f : X → P X
  f x = (x , (x , refl)) -- was a hole

  g : P X → X
  g (x , (x' , refl)) = x -- was a hole. Is this right?

  η : g ∘ f ∼ id
  η x = refl -- was a hole

  ε : f ∘ g ∼ id
  ε (x , (_ , refl)) = refl -- was a hole


data 𝟙 : Set where
  ⋆ : 𝟙

module Ex2 {i} (X : Set i) (x₀ : X) where
  f : 𝟙 → P* x₀
  f ⋆ = (x₀ , refl) -- was hole

  g : P* x₀ → 𝟙
  g (x₀ , refl) = ⋆ -- was hole

  η : g ∘ f ∼ id
  η ⋆ = refl -- was hole

  ε : f ∘ g ∼ id
  ε (x₀ , refl) = refl -- was hole

module _ {i j} {X : Set i} {P : X → Set j} {f g : (x : X) → P x} where
  postulate
    funext : f ∼ g → f == g

module Ex3 {i j} {X : Set i} {Y : Set j} where
  fib-repl : (X → Y) → (P X → Y)
  fib-repl f (x , (_ , refl)) = f x -- was hole

  fib-repl-inv : (P X → Y) → (X → Y)
  fib-repl-inv f x = f (x , (x , refl)) --was hole

  fib-repl-η : fib-repl-inv ∘ fib-repl ∼ id
  fib-repl-η f = refl -- was hole

  ------------------------------------------------

  -- f : (P X → Y)
  -- need to show fib-repl fib-repl-inv f = id f, but these are both functions
  -- so I will use funext, and then I only need to produce fib-repl fib-repl-inv f ~ id f, but this is equivalent to
  -- a functoion : PX → fib-repl fib-repl-inv f PX = f PX -- where PX : P X

  impl : (f : P X → Y) → (PX : P X) → (fib-repl (fib-repl-inv f)) PX == f PX
  impl f (x , (_ , refl)) = refl

  fib-repl-ε : fib-repl ∘ fib-repl-inv ∼ id
  fib-repl-ε f = funext (λ PX → impl f PX) --was hole

  -- QUESTION: did I need to use funext to solve the above?

  fib-repl-htpy : (f : X → Y) → f == fib-repl f ∘ Ex1.f X
  fib-repl-htpy f = refl -- was hole

  -- Ex1.f does x -> (x , (x , refl))

{- For any f : X → Y, you also get a factorization through
           Σ X (λ x → Σ Y (λ y → f x == y))
   which corresponds to the inverse images glued back together to
   get the domain of f -}
