module Real where

open import Data.Product using (∃; ∃₂; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Relation.Nullary.Negation.Core using (¬_)
open import Data.Nat.Coprimality using (1-coprimeTo)
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary using (yes; no)

open import Data.Rational
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality

import Level
import Data.Integer as ℤ; open ℤ using (ℤ)
import Data.Nat     as ℕ; open ℕ using (ℕ)

-- TODO
-- the basic arithmetic operations add, subtract, multiply, divide, and natural exponent (base e)

-- https://en.wikipedia.org/wiki/Construction_of_the_real_numbers#Construction_by_Dedekind_cuts
-- Extended to infinities by ignoring that Ax≢⊥∧Ax≢⊤
record ℝ∞ {ℓ} : Set (Level.suc ℓ) where
  constructor real∞
  field
    LeftOfCut  : ℚ → Set
    leftFilled : ∀ x y → x < y → LeftOfCut y → LeftOfCut x
    noMax      : ∀ x → LeftOfCut x → ∃ λ y → LeftOfCut y × x < y

0<1 : 0ℚ < 1ℚ
0<1 = *<* (ℤ.+<+ (ℕ.s≤s (ℕ.z≤n)))

¬1<0 : 1ℚ < 0ℚ → ⊥
¬1<0 (*<* (ℤ.+<+ ()))

∞ -∞ : ∀ {ℓ} → ℝ∞ {ℓ}
-∞ = real∞ (λ z → ⊥) (λ a b p2 ()) λ x ()
∞  = real∞ (λ x → ⊤) _ λ x y → (x + 1ℚ) , y ,
  ≤-<-trans
    (≤-reflexive (sym (+-identityʳ x)))
    (+-monoʳ-< x 0<1)

data _<ℝ∞_ {ℓ} : Rel (ℝ∞ {ℓ}) (Level.suc ℓ) where
  *<ℝ∞* : {A a : ℚ → Set}
      → ∀ {F f G g}
      → (∀ x → A x → a x)
      → (∃ λ x → A x → ¬ a x)
      → real∞ A F G <ℝ∞ real∞ a f g

x≡x*½+x*½ : ∀ {x} → x ≡ x * ½ + x * ½
x≡x*½+x*½ {x} =
  x ≡⟨ sym (+-identityʳ x) ⟩
  x + 0ℚ ≡⟨ cong (_+_ x) (sym (+-inverseˡ (x * ½))) ⟩
  x + (- (x * ½) + x * ½) ≡⟨ sym (+-assoc x (- (x * ½)) (x * ½)) ⟩
  x - x * ½ + x * ½ ≡⟨ cong (λ y → y - x * ½ + x * ½) (sym (*-identityʳ x)) ⟩
  x * 1ℚ - x * ½ + x * ½ ≡⟨ cong (λ y → x * 1ℚ + y + x * ½) (neg-distribʳ-* x ½) ⟩
  x * 1ℚ + x * -½ + x * ½ ≡⟨ cong (_+ x * ½) (sym (*-distribˡ-+ x 1ℚ -½)) ⟩
  x * ½ + x * ½ ∎
  where open ≡-Reasoning

midpoint : (x y : ℚ) → x < y → ∃ λ z → z < y × x < z
midpoint x y x<y = x * ½ + y * ½
  , (begin-strict
    x * ½ + y * ½ <⟨ +-monoˡ-< (y * ½) (*-monoˡ-<-pos ½ x<y) ⟩
    y * ½ + y * ½ ≡⟨ sym x≡x*½+x*½ ⟩
    y ∎
  ) , (begin-strict
    x ≡⟨ x≡x*½+x*½ ⟩
    x * ½ + x * ½ <⟨ +-monoʳ-< (x * ½) (*-monoˡ-<-pos ½ x<y) ⟩
    x * ½ + y * ½ ∎
  )
  where open ≤-Reasoning

ℚ→ℝ∞ : ∀ {ℓ} → ℚ → ℝ∞ {ℓ}
ℚ→ℝ∞ y = real∞
  (_< y) (λ xx yy → <-trans) (λ x → midpoint x y)

1/⟨1+_⟩ : ℕ → ℚ
1/⟨1+ n ⟩ = mkℚ+ 1 (ℕ.suc n) (1-coprimeTo (ℕ.suc n))

Series : ℕ → ℚ
Series ℕ.zero = 0ℚ
Series (ℕ.suc n) = Series n + 1/⟨1+ n ⟩ * 1/⟨1+ n ⟩

π*π÷6 : ∀ {ℓ} → ℝ∞ {ℓ}
π*π÷6 = real∞
  π*π÷6→Set
  f
  g
  where
    data π*π÷6→Set (x : ℚ) : Set where
      constr : ∀ n → x < Series n → π*π÷6→Set x

    f : (x y : ℚ) → x < y → π*π÷6→Set y → π*π÷6→Set x
    f _ _ x₁ (constr n x₂) = constr n (<-trans x₁ x₂)

    monotone : (n : ℕ) → Series n < Series (ℕ.suc n)
    monotone n = begin-strict
      Series n ≡⟨ sym (+-identityʳ (Series n)) ⟩
      Series n + 0ℚ ≡⟨ cong (_+_ (Series n)) (sym (*-zeroˡ 1/⟨1+ n ⟩)) ⟩
      Series n + 0ℚ * 1/⟨1+ n ⟩ <⟨ +-monoʳ-< (Series n) (*-monoˡ-<-pos 1/⟨1+ n ⟩ (positive⁻¹ 1/⟨1+ n ⟩)) ⟩
      Series (ℕ.suc n) ∎
      where open ≤-Reasoning

    g : (x : ℚ) → π*π÷6→Set x → ∃ λ y → π*π÷6→Set y × x < y
    g x (constr n x₁) =
      Series (ℕ.suc n)
      , constr (ℕ.suc (ℕ.suc n)) (monotone (ℕ.suc n))
      , <-trans x₁ (monotone n)
