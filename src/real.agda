open import Data.Product using (∃; _,_)
open import Function using (_∘_)
open import Data.Product using (_×_)
import Data.Rational as R using (ℚ; _<_; _+_; 0ℚ; 1ℚ)
open R using (ℚ) renaming (_<_ to _<ℚ_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

open import Data.Rational using () renaming (
  *<* to ℤ<ℤ→ℚ<ℚ )

open import Data.Integer using () renaming (
  +<+ to ℕ<ℕ→ℤ<ℤ )

open import Data.Nat using () renaming (
  s≤s to ℕ<ℕ→1+ℕ<1+ℕ;
  z≤n to 0<1+ℕ )

open import Relation.Binary.PropositionalEquality using () renaming (
  sym to x≡y→y≡x )

import Data.Rational.Properties as ℚp using () renaming (
  ≤-reflexive to x≡y→x≤y;
  ≤-<-trans to x≤y→y<z→x<z;
  +-monoʳ-< to x∊ℚ→y<z→x+y<x+z;
  +-identityʳ to x∊ℚ→x+0≡x )

-- https://en.wikipedia.org/wiki/Construction_of_the_real_numbers#Construction_by_Dedekind_cuts
data ℝ∞ : Set₁ where
  real  : (A : ℚ → Set)
        → ( ∀{x y : ℚ}
          → x <ℚ y
          → A y
          → A x
        ) → (
          ∀ x → A x → ∃ λ y → A y × x <ℚ y
        ) → ℝ∞

-∞ : ℝ∞
-∞ = real (λ z → ⊥) (λ p2 ()) λ x ()

0<1 = ℤ<ℤ→ℚ<ℚ {0ℚ} {1ℚ}(ℕ<ℕ→ℤ<ℤ (ℕ<ℕ→1+ℕ<1+ℕ (0<1+ℕ)))
  where
    open R

+∞ : ℝ∞
+∞ = real (λ x → ⊤) (λ p2 p3 → tt) λ x tt → (x + 1ℚ) , tt ,
  x≤y→y<z→x<z
    (x≡y→x≤y (x≡y→y≡x (x∊ℚ→x+0≡x x)))
    (x∊ℚ→y<z→x+y<x+z x 0<1)
  where
    open ℚp
    open R
