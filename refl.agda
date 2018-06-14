open import Data.Nat

data _≡_ {a} {A : Set a} (x : A) : A → Set where --stuff before the : is usable everywhere
  refl : x ≡ x -- First is x, second is A
  -- so refl is an element of eqs x x
  -- so although 0 ≡ 1 is a valid type, there are no elements of it

data test (x : ℕ) : ℕ → Set where
  testInstance : test x (suc x)

trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p refl = p

double : ℕ → ℕ
double n = 2 * n

data _IsHalf_ (x : ℕ) : ℕ → Set where
  isHalf : x IsHalf (double x)

theorem : {x y : ℕ} → x IsHalf y → (2 * x) ≡ y
theorem isHalf = refl
