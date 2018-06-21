open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import univalence
open import Function

isContra : Set → Set
isContra(A) = Σ A (λ a → (x : A) → (a ≡ x))

module _ (A : Set) (a : A) where
  lemma : (x : Σ A (λ x₁ → a ≡ x₁)) → (a , refl) ≡ x
  lemma (x1 , refl) = refl

  Fact : isContra (Σ A (λ x → a ≡ x))
  Fact = ((a , refl) , lemma)

-- prove a proposition about transporting on pointed types
module _ (A : Set) (* : A) (P : A → Set) (a : A) (x : P *) (contractible : isContra (Σ A P)) where
  center : Σ A P
  center = proj₁ contractible

  pathToCenter : (point : Σ A P) → (center ≡ point)
  pathToCenter = proj₂ contractible

  pathTox : (point : Σ A P) → ((* , x) ≡ point)
  pathTox point = trans (sym (pathToCenter (* , x))) (pathToCenter point)

  -- I am pretty sure the following might be true with some kind of transport
  allPathSame : {point1 point2 : Σ A P} → (path1 : point1 ≡ point2) → (path2 : point1 ≡ point2) → path1 ≡ path2
  allPathSame refl refl = refl

  equiv : (* ≡ a) → P a -- the equivalence between paths and points that were trying to prove is indeed an equivalence
  equiv arg = transport arg x

  firstPath : {a b : Σ A P} → a ≡ b → proj₁ a ≡ proj₁ b -- used in next definition
  firstPath refl = refl

  inverse : P a → * ≡ a -- supposed inverse of purported equivelence
  inverse point = firstPath (pathTox (a , point))

  -- proof1 : inverse ∘ equiv ~ id
  -- proof1 path = firstPath (allPathSame ? ?)

  -- proposition : isequiv equiv
  -- proposition = ((inverse , {!   !}) , (inverse , {!   !}))

module _ {A : Set} {P : A → Set} {Q : A → Set} (f : (x : A) → P x → Q x) where -- Theorem 4.7.7
  total : Σ A P → Σ A Q
  total (a , pa) = (a , f a pa)

  theorem' : ((x : A) → (isequiv (f x))) → isequiv total
  theorem' = {!   !}

  -- if total preserves first element (x,-) → (x,-) , then so does inverse of total
  -- intuitively, prove this by composing below with proj₁ on both sides
  -- lemma2 : (inv : Σ A Q → Σ A P) → (total ∘ inv ~ id) → (x : A) → (proj₁ ∘ inv ~ proj₁)
  -- lemma2 inv proof x elt = {!   !}

  -- theorem477 : isequiv total → ((x : A) → (isequiv (f x)))
  -- theorem477 ((inv1 , proof1) , (inv2 , proof2)) x = (({!   !} , {!   !}) , ({!   !} , {!   !}))
