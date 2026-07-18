open import Data.Product using (∃; Σ; map-Σ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import Real using (ℝ∞; +∞; -∞)
open import Relation.Nullary.Negation.Core using (¬_)
open import Level using (Level) renaming (suc to lsuc; zero to lzero)

module Types
  {ℓ : Level}
  (complexExtension : Bool)
  (customTypes : Set)
  (isBQNNum : ℝ∞ {ℓ} → Set) -- Spec allows implementation defined numbers to be a subset of reals
  (rounding :
-- TODO Complex extension
--    if complexExtension then
--      ((ℝ∞ × ℝ∞) → Σ (ℝ∞ × ℝ∞) (map-Σ isBQNNum isBQNNum) )
--    else
      ℝ∞ {ℓ} → Σ ℝ∞ isBQNNum
  )
  where

open import grammer
open import examples
open import Data.Maybe using (just) renaming (nothing to ignore)
open import Data.List using ([])

data type : Set (lsuc ℓ)

data Character  : Set
data Number     : Set (lsuc ℓ)
data Array      : Set (lsuc ℓ)
data Function   : Set
data 1-Modifier : Set
data 2-Modifier : Set
data Namespace  : Set

-- https://mlochbaum.github.io/BQN/spec/types.html
data type where
  CharacterAsType  : Character   → type
  NumberAsType     : Number      → type
  ArrayAsType      : Array       → type
  FunctionAsType   : Function    → type
  1-ModifierAsType : 1-Modifier  → type
  2-ModifierAsType : 2-Modifier  → type
  NamespaceAsType  : Namespace   → type
  custom           : customTypes → type -- The spec allows any amount of custom types. If I undertand correctly, only system values can return these.

open import Data.Fin using (Fin; suc; zero)
unicodeMax = 1114111


data Character where
  char : Fin unicodeMax → Character

-- TODO Complex extension idea
-- ℝ∞orℂ∞ = if complexExtension then ℝ∞ {ℓ} × ℝ∞ {ℓ} else ℝ∞

data Number where
  num : Σ ℝ∞ isBQNNum → Number

open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)
open import Data.Nat.ListAction using (product)

data Array where
  arr : (shape : List ℕ) → (ravel : Vec type (product shape)) → Array

-- inputs and the result are values of any type

-- TODO figure out what code should be represented as, and place it here.
-- Keep in mind the option that funcs, 1-mod, and 2-mod could have different Code types
data Code : Set where

data Function where
  monadic : Code → Function
  dyadic : Code → Function

data 1-Modifier where
  1mod : Code → 1-Modifier

data 2-Modifier where
  1mod : Code → 2-Modifier

data Namespace where
-- A namespace holds the variables
-- used to evaluate a block or program,
-- as defined in the scoping rules.
-- The observable aspects of a namespace
-- are that it can be compared for equality
-- with other namespaces and that it exposes
-- variables associated with certain names, whose values can be queried or set.

  -- TODO

-- Uncomment if this ever becomes useful
-- data Operation : Set where
--   func : Function → Operation
--   1mod : 1-Modifier → Operation
--   2mod : 2-Modifier → Operation
--
-- data Data : Set (lsuc ℓ) where
--   char : Character → Data
--   num : Number → Data
--   arr : Array → Data
