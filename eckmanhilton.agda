open import Relation.Binary.PropositionalEquality

module eckmanhilton where

assertType : ∀ {i} → (A : Set i) → A → A
assertType _ x = x

_⋆_ = trans
ru : {A : Set} → {a b : A} → (p : a ≡ b) → p ≡ p ⋆ refl
ru refl = refl

lu : {A : Set} → {a b : A} → (p : a ≡ b) → refl ⋆ p ≡ p
lu refl = refl

module _ {A : Set} {a b x : A} {p q : a ≡ b} (α : p ≡ q) where
  rwhisk' : (r : b ≡ x) → p ⋆ r ≡ q ⋆ r
  rwhisk' refl = ((sym (ru p)) ⋆ α) ⋆ (ru q)

  _rwhisk_ = rwhisk'

  lwhisk' : (r : x ≡ a) → r ⋆ p ≡ r ⋆ q
  -- lwhisk' refl = (lu p) ⋆ (α ⋆ (sym (lu q))) --old
  lwhisk' refl = ((sym (lu p)) ⋆ α) ⋆ (lu q) --more like book


_lwhisk_ : {A : Set} → {a b x : A} → {p q : a ≡ b} → (r : x ≡ a) → (β : p ≡ q) → r ⋆ p ≡ r ⋆ q
onepath lwhisk twopath = lwhisk' twopath onepath

module _ {A : Set} {a b c : A} {p q : a ≡ b} {r s : b ≡ c} (α : p ≡ q) (β : r ≡ s) where
  _*_ : p ⋆ r ≡ q ⋆ s
  _*_ = (α rwhisk r) ⋆ (q lwhisk β)
  _*'_ : p ⋆ r ≡ q ⋆ s
  _*'_ = (p lwhisk β) ⋆ (α rwhisk s)


-- Now lets prove some things

same : {A : Set} → {a b c : A} → (p q : a ≡ b) → (r s : b ≡ c) → (α : p ≡ q) → (β : r ≡ s) → α * β ≡ α *' β
same refl refl refl refl refl refl = refl


reflof : {A : Set} → (a : A) → (a ≡ a)
reflof a = refl

squarelemma1 : {A : Set} → {a : A} → (reflof a) ⋆ (reflof a) ≡ reflof a
squarelemma1 = refl

squarelemma2 : {A : Set} → {a b c : A} → (p : a ≡ b) → (q : b ≡ c) → (reflof p) * (reflof q) ≡ (reflof (p ⋆ q))
squarelemma2 refl refl = refl

square' : {a : Set} → {a b c : a} → (p q r : a ≡ b) → (s t u : b ≡ c) → (α : p ≡ q) →
  (β : s ≡ t) → (α' : q ≡ r) → (β' : t ≡ u) → (α * β) ⋆ (α' * β') ≡ (α ⋆ α') * (β ⋆ β')
square' refl refl refl refl refl refl refl refl refl refl = refl

module _ {a : Set} {a b c : a} {p q r : a ≡ b} {s t u : b ≡ c} (α : p ≡ q) (β : s ≡ t) (α' : q ≡ r) (β' : t ≡ u) where
  square : (α * β) ⋆ (α' * β') ≡ (α ⋆ α') * (β ⋆ β')
  square = square' p q r s t u α β α' β'

  -- now, we deduce commutativity


-- try using a noah-style proof of commutativity with the square
module _ {A : Set} {a : A} (α β : (reflof a) ≡ (reflof a)) where
  reflrefla = reflof (reflof a)


  commutestep1 : α ⋆ β ≡ ((α * reflrefla) ⋆ (reflrefla * β))
  commutestep1 = {!   !}

  commute : α ⋆ β ≡ β ⋆ α
  commute = {!   !}

module _ {A : Set} {a : A} (α : (reflof a) ≡ (reflof a)) (β : (reflof a) ≡ (reflof a)) where

  starequivalent : α * β ≡ α *' β
  starequivalent = same refl refl refl refl α β

  step1 : α * β ≡ ((refl ⋆ α) ⋆ refl) ⋆ ((refl ⋆ β) ⋆ refl)
  step1 = refl

  step2' : (refl ⋆ α) ≡ α → (refl ⋆ β) ≡ β → ((refl ⋆ α) ⋆ refl) ⋆ ((refl ⋆ β) ⋆ refl) ≡ (α ⋆ refl) ⋆ (β ⋆ refl)
  step2' refl refl = refl
  step2 = step2' (lu α) (lu β)

  lemma1 : {α' β' : (reflof a) ≡ (reflof a)} → (α ≡ α') → (β ≡ β') → α' ⋆ β' ≡ α ⋆ β
  lemma1 refl refl = refl -- this lemma is only necessary because agda is trying to reduce α ⋆ refl when it shouldn't, and
  -- this means i need to write in terms of generic α' so that agda can't try to reduce it
  step3' : α ≡ (α ⋆ refl) → β ≡ (β ⋆ refl) → (α ⋆ refl) ⋆ (β ⋆ refl) ≡ α ⋆ β
  step3' p q = lemma1 p q
  step3 = step3' (ru α) (ru β)

  lemma : refl ⋆ α ≡ α
  lemma = refl

  composeSame : α * β ≡ α ⋆ β
  composeSame = (step1 ⋆ step2) ⋆ step3
