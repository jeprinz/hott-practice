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

module _ {A : Set} {a : A} (α : (reflof a) ≡ (reflof a)) (β : (reflof a) ≡ (reflof a)) where

  starequivalent : α * β ≡ α *' β
  starequivalent = same refl refl refl refl α β

  -- step1 : α * β ≡ (α rwhisk refl) ⋆ (refl lwhisk β)
  -- step1 = refl
  --
  -- step2 : (α rwhisk refl) ⋆ (refl lwhisk β) ≡ (((sym (ru refl)) ⋆ α) ⋆ (ru refl)) ⋆ (((sym (lu refl)) ⋆ β) ⋆ (lu refl))
  -- step2 = refl
  --
  -- step3 : (((sym (ru refl)) ⋆ α) ⋆ (ru refl)) ⋆ (((sym (lu refl)) ⋆ β) ⋆ (lu refl)) ≡
  --   (((sym refl) ⋆ α) ⋆ refl) ⋆ (((sym refl) ⋆ β) ⋆ refl)
  -- step3 = refl
  --
  -- step4 : (((sym refl) ⋆ α) ⋆ refl) ⋆ (((sym refl) ⋆ β) ⋆ refl) ≡ ((refl ⋆ α) ⋆ refl) ⋆ ((refl ⋆ β) ⋆ refl)
  -- step4 = refl

  step : α * β ≡ ((refl ⋆ α) ⋆ refl) ⋆ ((refl ⋆ β) ⋆ refl)
  step = refl

  lemma : refl ⋆ α ≡ α
  lemma = refl

  composeSame : α * β ≡ α ⋆ β
  composeSame = {!   !}

  composeSame' : {!   !} ≡ α ⋆ β
  composeSame' = {!   !}
