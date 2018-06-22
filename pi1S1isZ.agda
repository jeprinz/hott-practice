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
module _ (A : Set) (* : A) (P : A → Set) (contractible : isContra (Σ A P)) (a : A) (x : P *) where
  center : Σ A P
  center = proj₁ contractible

  pathToCenter : (point : Σ A P) → (center ≡ point)
  pathToCenter = proj₂ contractible

  pathTox : (point : Σ A P) → ((* , x) ≡ point)
  pathTox point = trans (sym (pathToCenter (* , x))) (pathToCenter point)

  equiv : (* ≡ a) → P a -- the equivalence between paths and points that were trying to prove is indeed an equivalence
  equiv arg = transport arg x

  -- to prove its an equivalence, we have P() already, define Q(point) = (point ≡ a)
  -- next, show Σ A P ≃ Σ A Q by showing latter is contractible, and two contractible spaces are equivalent
  -- and apply theorem 4.7.7 below

  Q : A → Set
  Q point = point ≡ a

  tidbit : (value : Σ A Q) → (a , refl) ≡ value -- this is necessary for proving contractibility of Q below, need sep-
  tidbit (eltA , refl) = refl -- arate function in order to do path induction

  QisContractible : isContra (Σ A Q)
  QisContractible = ((a , refl) , tidbit)

  bigequiv : Σ A P → Σ A Q -- this function is an equivalence between Σ A P and Σ A Q
  bigequiv _ = (a , refl)

  biginverse : Σ A Q → Σ A P -- this is (homotopic) inverse bigequiv above
  biginverse _ = center

  -- we now have our equivalences , but need to prove that they actually are equivalences
  direction1 : bigequiv ∘ biginverse ~ id
  direction1 value = tidbit value
  direction2 : biginverse ∘ bigequiv ~ id
  direction2 value = pathToCenter value

  totalequivalence : isequiv bigequiv
  totalequivalence = ((biginverse , direction1) , (biginverse , direction2))

  -- so to sum up, bigequiv and biginverse, together with the above two directional proofs, constitute an equivalence of total spaces
  -- next, we need to prove that given a point, P(point) and Q(point) are also equivalent. So apply theorem477


module _ {A : Set} {P : A → Set} {Q : A → Set} (f : (x : A) → P x → Q x) where -- Theorem 4.7.7
  total : Σ A P → Σ A Q
  total (a , pa) = (a , f a pa)

  theorem' : ((x : A) → (isequiv (f x))) → isequiv total
  theorem' = {!   !}

  -- if total preserves first element (x,-) → (x,-) , then so does inverse of total
  -- intuitively, prove this by composing below with proj₁ on both sides
  -- lemma2 : (inv : Σ A Q → Σ A P) → (total ∘ inv ~ id) → (x : A) → (proj₁ ∘ inv ~ proj₁)
  -- lemma2 inv proof x elt = {!   !}

  theorem477 : isequiv total → ((x : A) → (isequiv (f x)))
  theorem477 ((inv1 , proof1) , (inv2 , proof2)) x = {!   !}
