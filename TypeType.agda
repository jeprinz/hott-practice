-- The goal is to implement the concept of a type as a ttype to show it can be done, and eveentually the same with higher types

open import Level
open import Data.List
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Nat hiding (suc)

module TypeType where

HVec : ∀ {n} → List (Set n) → Set n
HVec [] = Lift ⊤
HVec (A ∷ As) = A × HVec As

HCo : ∀ {n} → List (Set n) → Set n
HCo [] = Lift ⊤
HCo (A ∷ As) = A ⊎ HVec As

module _ {i : Level} where
  TypeList : Set (suc i) --represents the arguments to a constructor for a type
  TypeList = List (Set i)

  Constructors : Set (suc i) --represents the list of all constructors for a type
  Constructors = List TypeList -- so list of lists of sets

  -- Type that is passed to a given constructor
  SingleArgType : TypeList → Set i -- given type list, return product type of all of them
  SingleArgType = HVec

  -- Type which is coproduct of all constructor types, one of these will let you instantiate an object
  MultiArgType : Constructors → Set i -- type which will be arg to just one of the constructors
  MultiArgType constructors = HCo (Data.List.map SingleArgType constructors)

  data TypeImpl (constructors : Constructors) : Set i where
    construct : (MultiArgType constructors) → TypeImpl constructors

-- a : List ℕ
-- a = 1 ∷ 0 ∷ []

-- mutual
  -- ctrs : Constructors
  -- ctrs = ([]) ∷ (Wrapper ∷ []) ∷ []

  -- data Wrapper : Set where

-- the following is the real problem here.....
myN : Set
myN = MultiArgType (([]) ∷ (myN ∷ []) ∷ [])
