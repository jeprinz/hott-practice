--open import Data.Nat
open import Data.Product
open import Data.Nat
open import Relation.Binary.PropositionalEquality

-------------------------------------------------------------------------------
-- Exercise 1.3 - derive induction principle for products using only the projections
-- and the propositional uniqueness principle uniq_axb. Verify definitional equalities are valid.

ind : {A : Set} → {B : Set} → (c : A × B → Set) → (g : (x : A) → (y : B) → c (x , y)) → (pair : A × B) → c pair
ind c g pair = g (proj₁ pair) (proj₂ pair)

-- f : {A : Set} → {B : Set} → (a : A × A -> Set) → A
-- f = {!   !}

-- Exercise 1.16 - show for all i, j, i + j = j + i
-- NOTE: cong applies something to both sides, so if p is proof a = b, then cong f p is f a = f b

plusZeroRight : ∀ n → n + 0 ≡ n
plusZeroRight zero = refl
plusZeroRight (suc n) = cong suc (plusZeroRight n)

plusZeroLeft : ∀ n → n ≡ n + 0
plusZeroLeft n = sym (plusZeroRight n)

zeroPlusRight : ∀ n → 0 + n ≡ n
zeroPlusRight zero = refl
zeroPlusRight (suc n) = cong suc (zeroPlusRight n)

lemma1 : ∀ i → ∀ j → (suc i) + j ≡ suc (i + j)
lemma1 i j = refl

lemma2 : ∀ i → ∀ j → i + (suc j) ≡ suc (i + j)
lemma2 0 j = refl
lemma2 (suc i) j = trans (lemma1 i (suc j)) (cong suc (lemma2 i j))

-- Finally, assoiativity
assoc : (i : ℕ) → (j : ℕ) → i + j ≡ j + i
assoc 0 j = trans (zeroPlusRight j) (plusZeroLeft j)
assoc (suc i) j = trans (lemma1 i j) (
  trans (cong suc (assoc i j)) (sym (lemma2 j i))
  )

-- My only question after doing this excercise is how would I define "trans" on my own?
-- More generally, can path induction be derived from pattern matching in agda?
-- Can path induction be used to derive trans?
