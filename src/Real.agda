module Real where

open import Data.Product using (Σ; ∃; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Level using () renaming (suc to lsuc)
open import Data.Nat.Coprimality using (Coprime; 1-coprimeTo)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary.Core using (Rel)

import Data.Rational as ℚ; open ℚ using (ℚ)
import Data.Rational.Properties as ℚ
import Data.Rational.Unnormalised as ℚᵘ; open ℚᵘ using (ℚᵘ)
import Data.Rational.Unnormalised.Properties as ℚᵘ

import Data.Integer as ℤ; open ℤ using (ℤ; +_) renaming (
  +<+ to ℕ<ℕ→ℤ<ℤ)

import Data.Nat as ℕ; open ℕ using (ℕ) renaming (
  s≤s to ℕ<ℕ→1+ℕ<1+ℕ;
  z≤n to 0<1+ℕ )

-- TODO
-- the basic arithmetic operations add, subtract, multiply, divide, and natural exponent (base e)

-- https://en.wikipedia.org/wiki/Construction_of_the_real_numbers#Construction_by_Dedekind_cuts
-- Extended to infinities by ignoring that Ax≢⊥∧Ax≢⊤
record ℝ∞ {ℓ} : Set (lsuc ℓ) where
  constructor real∞
  field
    LeftOfCut  : ℚ → Set ℓ
    leftFilled : ∀ x y → x ℚ.< y → LeftOfCut y → LeftOfCut x
    noMax      : ∀ x → LeftOfCut x → ∃ λ y → LeftOfCut y × x ℚ.< y

-∞ : ℝ∞
-∞ = real∞ (λ z → ⊥) (λ a b p2 ()) λ x ()

0<1 = ℚ.*<* {ℚ.0ℚ} {ℚ.1ℚ} (ℕ<ℕ→ℤ<ℤ (ℕ<ℕ→1+ℕ<1+ℕ (0<1+ℕ)))

+∞ : ℝ∞
+∞ = real∞ (λ x → ⊤) (λ a b p2 p3 → tt) λ x tt → (x ℚ.+ ℚ.1ℚ) , tt ,
  ℚ.≤-<-trans
    (ℚ.≤-reflexive (sym (ℚ.+-identityʳ x)))
    (ℚ.+-monoʳ-< x 0<1)

data _<ℝ∞_ {ℓ} : Rel ℝ∞ (lsuc ℓ) where
  *<ℝ∞* : {A a : ℚ → Set ℓ}
      → ∀ {F f G g}
      → (∀ x → A x → a x)
      → (∃ λ x → A x → ¬ a x)
      → real∞ A F G <ℝ∞ real∞ a f g


x<y→x*½+y*½<y : {x y : ℚ} → (x<y : x ℚ.< y) → x ℚ.* ℚ.½ ℚ.+ y ℚ.* ℚ.½ ℚ.< y
x<y→x*½+y*½<y {x} {y} x<y =
  begin-strict
    x * ½ + y * ½ <⟨
      +-monoˡ-< (y * ½)
        (begin-strict
          x * ½ <⟨ *-monoˡ-<-pos ½ x<y ⟩
          y * ½ ≡⟨ *-distribˡ-+ y 1ℚ -½ ⟩
          y * 1ℚ + y * -½ ≡⟨ cong (y * 1ℚ ℚ.+_) (sym (neg-distribʳ-* y ½)) ⟩
          y * 1ℚ - (y * ½) ≡⟨ cong (_+ - (y * ½)) (*-identityʳ y) ⟩
          y - y * ½
        ∎)
    ⟩
    y - y * ½ + y * ½ ≡⟨ +-assoc y (- (y * ½)) (y * ½) ⟩
    y + (- (y * ½) + y * ½) ≡⟨ cong (_+_ y) (+-inverseˡ (y * ½)) ⟩
    y + 0ℚ ≡⟨ +-identityʳ y ⟩
    y ∎
    where
      open import Data.Rational
      open import Data.Rational.Properties
      open ℚ.≤-Reasoning

x<y→x<x*½+y*½ : {x y : ℚ} → (x<y : x ℚ.< y) → x ℚ.< x ℚ.* ℚ.½ ℚ.+ y ℚ.* ℚ.½
x<y→x<x*½+y*½ {x} {y} x<y =
  begin-strict
    x ≡⟨ sym (+-identityʳ x) ⟩
    x + 0ℚ ≡⟨ sym (cong (_+_ x) (+-inverseˡ (x * ½))) ⟩
    x + (- (x * ½) + x * ½) ≡⟨ sym (+-assoc x (- (x * ½)) (x * ½)) ⟩
    x - x * ½ + x * ½
    <⟨
      +-monoˡ-< (x * ½) (begin-strict
        x - x * ½ ≡⟨ sym (cong (_+ - (x * ½)) (*-identityʳ x)) ⟩
        x * 1ℚ - x * ½ ≡⟨ sym (cong (x * 1ℚ ℚ.+_) (sym (neg-distribʳ-* x ½))) ⟩
        x * 1ℚ + x * -½ ≡⟨ sym (*-distribˡ-+ x 1ℚ -½) ⟩
        x * ½ <⟨ *-monoˡ-<-pos ½ x<y ⟩
        y * ½
      ∎)
    ⟩
    y * ½ + x * ½ ≡⟨ +-comm (y * ½) (x * ½) ⟩
    x * ½ + y * ½ ∎
    where
      open import Data.Rational
      open import Data.Rational.Properties
      open ℚ.≤-Reasoning

midpoint : (x y : ℚ) → x ℚ.< y → ∃ λ z → z ℚ.< y × x ℚ.< z
midpoint x y x<y = x ℚ.* ℚ.½ ℚ.+ y ℚ.* ℚ.½ , x<y→x*½+y*½<y x<y , x<y→x<x*½+y*½ x<y

ℚ→ℝ∞ : ℚ → ℝ∞
ℚ→ℝ∞ x = real∞
  (ℚ._< x) (λ xx yy → ℚ.<-trans) (λ a → midpoint a x)


-- I'll define √ when i need it
--√_ : ℝ∞ → ℝ∞
--√ r = real∞
--    LeftOfCut
--    f
--    {!   !}
--  where
--    LeftOfCut = λ q → ℚ.0ℚ ℚ.> q ⊎ ℚ→ℝ∞ (q ℚ.* q) <ℝ∞ r
--    f : ∀ x y → x ℚ.< y → LeftOfCut y → LeftOfCut x
--    f x y x₁ x₂ = {!   !}

Series : ℕ → ℚ
Series ℕ.zero = ℚ.0ℚ
Series (ℕ.suc n) = Series n ℚ.+ (+ 1 ℚ./ ℕ.suc n) ℚ.* (+ 1 ℚ./ ℕ.suc n)

normalize-≤ : (x : ℚ) → ℚᵘ.0ℚᵘ ℚᵘ.< ℚ.toℚᵘ x → ℚ.0ℚ ℚ.< x
normalize-≤ x x₁ = ℚ.toℚᵘ-cancel-< x₁

π*π÷6 : ℝ∞
π*π÷6 = real∞
  π*π÷6→Set
  f
  g
  where

    data π*π÷6→Set (x : ℚ) : Set where
      constr : ∀ n → x ℚ.< Series n → π*π÷6→Set x

    f : (x y : ℚ) → x ℚ.< y → π*π÷6→Set y → π*π÷6→Set x
    f _ _ x₁ (constr n x₂) = constr n (ℚ.≤-<-trans (ℚ.<⇒≤ x₁) x₂)

    ppp3 : (n : ℕ) → ℚ.0ℚ ℚ.< ℚ.normalize 1 (ℕ.suc n)
    ppp3 n = ℚ.<-≤-trans (ℚ.positive⁻¹ (ℚ.mkℚ (+ 1) n (1-coprimeTo (ℕ.suc n)))) (ℚ.≤-reflexive (sym (ℚ.normalize-coprime (1-coprimeTo (ℕ.suc n)))))

    i : ∀ n → Series (ℕ.suc n) ℚ.< Series (ℕ.suc (ℕ.suc n))
    i n = ℚ.≤-<-trans
      {j = Series (ℕ.suc n) ℚ.+ ℚ.0ℚ}
      {k = Series (ℕ.suc n) ℚ.+ ℚ.normalize 1 (ℕ.suc (ℕ.suc n)) ℚ.* ℚ.normalize 1 (ℕ.suc (ℕ.suc n))}
      (ℚ.≤-reflexive (sym (ℚ.+-identityʳ (Series (ℕ.suc n)))))
      (ℚ.+-mono-≤-< {x = Series (ℕ.suc n)}
         (ℚ.≤-reflexive refl)
         (ℚ.toℚᵘ-cancel-< (ℚᵘ.≤-<-trans (ℚᵘ.≤-reflexive (ℚᵘ.≃-sym ( ℚᵘ.*-zeroˡ (ℚ.toℚᵘ (+ 1 ℚ./ (ℕ.suc (ℕ.suc n)))))))
          (begin-strict
            ℚᵘ.0ℚᵘ ℚᵘ.* ℚ.toℚᵘ (+ 1 ℚ./ (ℕ.suc (ℕ.suc n)))
              <⟨
                ℚᵘ.*-monoˡ-<-pos (ℚ.toℚᵘ (+ 1 ℚ./ ℕ.suc (ℕ.suc n))) ⦃ ℚ.positive (ppp3 (ℕ.suc n)) ⦄ {ℚᵘ.0ℚᵘ} {ℚ.toℚᵘ (+ 1 ℚ./ (ℕ.suc (ℕ.suc n)))} (ℚ.toℚᵘ-mono-< (ppp3 (ℕ.suc n)))
              ⟩
            ℚ.toℚᵘ (+ 1 ℚ./ (ℕ.suc (ℕ.suc n))) ℚᵘ.* ℚ.toℚᵘ (+ 1 ℚ./ (ℕ.suc (ℕ.suc n)))
              ≃⟨ ℚᵘ.≃-sym (ℚ.toℚᵘ-homo-* ((+ 1 ℚ./ ℕ.suc (ℕ.suc n))) ((+ 1 ℚ./ ℕ.suc (ℕ.suc n)))) ⟩
            ℚ.toℚᵘ ((+ 1 ℚ./ ℕ.suc (ℕ.suc n)) ℚ.* (+ 1 ℚ./ ℕ.suc (ℕ.suc n))) ∎
          )
         ))
      )
        where open ℚᵘ.≤-Reasoning

    open import Data.Unit using (tt)

    g : (x : ℚ) → π*π÷6→Set x → ∃ λ y → π*π÷6→Set y × x ℚ.< y
    g _ (constr n x₁) =
      Series (ℕ.suc n) ,
      constr (ℕ.suc (ℕ.suc n)) (i n) ,
      ℚ.<-trans x₁ (ℚ.≤-<-trans (ℚ.≤-reflexive (sym (ℚ.+-identityʳ (Series n))))
        (ℚ.+-monoʳ-<
          (Series n)
          (ℚ.≤-<-trans (ℚ.≤-reflexive refl)
            (ℚ.toℚᵘ-cancel-< (begin-strict_ (
              ℚᵘ.0ℚᵘ ≃⟨ ℚᵘ.≃-sym ( ℚᵘ.*-zeroˡ (ℚ.toℚᵘ (+ 1 ℚ./ (ℕ.suc n)))) ⟩
              ℚᵘ.0ℚᵘ ℚᵘ.* (ℚ.toℚᵘ (+ 1 ℚ./ (ℕ.suc n))) <⟨
                ℚᵘ.*-monoˡ-<-pos (ℚ.toℚᵘ (+ 1 ℚ./ ℕ.suc n)) {{ ℚ.positive (ppp3 n) }} {ℚᵘ.0ℚᵘ} {ℚ.toℚᵘ (+ 1 ℚ./ (ℕ.suc n))} (ℚ.toℚᵘ-mono-< (ppp3 n))
              ⟩
                ℚ.toℚᵘ (+ 1 ℚ./ (ℕ.suc n)) ℚᵘ.* ℚ.toℚᵘ (+ 1 ℚ./ (ℕ.suc n))
                  ≃⟨ ℚᵘ.≃-sym (ℚ.toℚᵘ-homo-* ((+ 1 ℚ./ ℕ.suc n)) ((+ 1 ℚ./ ℕ.suc n))) ⟩
                ℚ.toℚᵘ ((+ 1 ℚ./ ℕ.suc n) ℚ.* (+ 1 ℚ./ ℕ.suc n)) ∎)
              )
            )
          )
        )
      )
      where open ℚᵘ.≤-Reasoning
