open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import univalence
open import Function

-- Exercise 2.4 ------------------------------------------------
npath : ∀ {i} → Set i → ℕ → Set _
npath A 0 = A
npath A (suc n) = Σ (npath A n × npath A n) λ {(p1 , p2) → p1 ≡ p2}

-- Exercise 2.11 -----------------------------------------------

module _ (A B C : Set) (f : A → C) (g : B → C) where
  -- first, define pullback as in 2.15.11 in HoTT book
  P : Set -- the pullback of A B C
  P = Σ A (λ a → Σ B (λ b → f(a) ≡ g(b)))
  -- Next, we need the top and left of the square, which are simply inclusion maps
  h : P → A
  h (a , (b , p)) = a
  k : P → B
  k (a , (b , p)) = b
  -- just for fun, prove it commutes
  commutes : f ∘ h ~ g ∘ k
  commutes (a , (b , p)) = p


  -- Next, we prove the universal property
  module _ (X : Set) where -- given any other type (object of category) X
    pullcross : Set -- represents × X → C
    pullcross = Σ A (λ a → Σ B (λ b → ))

    equiv : (X → P) → (X → A) × (X → B)
    equiv q = ((λ x → proj₁ (q x)) , (λ x →  proj₁ (proj₂ (q x))))

    equivinv : (X → A) × (X → B) → (X → P)
    equivinv (a , b) = λ x → {!   !}

    theorem : (X → P) ≃ (X → A) × (X → B)
    theorem = {!   !}
