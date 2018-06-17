open import Data.Nat
open import Data.List
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality

module EquivRel where

-- data Prop : Set where -- why cant I define a type like: this thing is ≡ true, without need for identity type?
  -- asType true : true → Prop

record equivrel (A : Set) (_~_ : A → A → Set) : Set where
  field
    reflex : (a : A) → a ~ a
    symetry : {a b : A} → a ~ b → b ~ a
    transi : {a b c : A} → a ~ b → b ~ c → a ~ c


module Equivalence (A : Set) (~ : A → A → Set) (eq : equivrel A ~) where
  data Quot : Set where
    quot : A → Quot -- hide this externally

  makeQuot : A → Quot
  makeQuot a = quot a

  -- data Equiv (a : Quot) (b : Quot) : Set₁ where
    -- a ~ b : Equiv


  -- given function A → B, and proof that the function respects equivalence, can get function Quot → B
  rec : {B : Set} → (f : A → B) → ({a b : A} → ~ a b → f(a) ≡ f(b)) → (Quot → B)
  rec f _ (quot a) = f a

  -- eh kinda works

-- For example
-- define numbers mod 4 type

data _~_ : ℕ → ℕ → Set where
  refl : (a : ℕ) → a ~ a -- this corresponds to regular constructor
  base : 0 ~ 4 -- this corresponds to path constructor

  symetry : {a b : ℕ} → a ~ b → b ~ a --these two correspond to facts about equality
  transi : {a b c : ℕ} → a ~ b → b ~ c → a ~ c --these freely generate the remaining things that are equal

  next : {a b : ℕ} → a ~ b → suc a ~ suc b --this one has to do with the constructors of ℕ
  -- maybe we can generalize the above with a constructor which
  -- takes any function f : ℕ → ℕ, and if a ~ b then f(a) ~ f(b)
  -- guarunteeing a lot of the behavior that were trying to prove here...
  -- TODO: TODO: READ THE ABOVE LATER!!!

eq : equivrel ℕ (_~_)
eq = record {
  reflex = refl;
  symetry = symetry;
  transi = transi}

ℤ/4 : Set
ℤ/4 = Equivalence.Quot ℕ (_~_) eq

impl : ℕ → ℕ -- wait how would i write this with the ℕ recursor?
impl 0 = 0
impl (suc (suc (suc (suc n)))) = impl n
impl n = n

lemma2 : (a : ℕ) → impl (suc (suc (suc (suc a)))) ≡ impl a
lemma2 a = refl

lemma1 : (a : ℕ) → impl a ≡ impl (impl a)
lemma1 0 = refl
lemma1 (suc (suc (suc (suc n)))) = trans (lemma2 n) (lemma1 n)
lemma1 (suc (suc (suc zero))) = refl
lemma1 (suc (suc zero)) = refl
lemma1 (suc zero) = refl

lemma : (a b : ℕ) → impl a ≡ impl b → impl (suc a) ≡ impl (suc b)
lemma a b p = {!   !}

proof : {a b : ℕ} → a ~ b → impl a ≡ impl b
proof (refl a) = refl
proof base = refl
proof (symetry eq) = sym (proof eq)
proof (transi eq1 eq2) = trans (proof eq1) (proof eq2)
proof (next eq) = {!   !}
  -- next : {a b : ℕ} → a ~ b → suc a ~ suc b

func : ℤ/4 → ℕ
func = Equivalence.rec ℕ (_~_) eq impl proof

--the following is where problems will arise... solution: define new equality which respects Quot!
func2 : ℤ/4 → ℤ/4
func2 = {!   !}
