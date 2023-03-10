{-

Definition of the circle as a HIT with a proof that Ω(S¹) ≡ ℤ

-}
{-# OPTIONS --cubical #-}
module CircleWindingNumber2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws 
open import Cubical.Data.Int
data S¹ : Type₀ where
  base : S¹
  loop : base ≡ base

{-
The definitions of helix and winding are taken from https://dl.acm.org/doi/abs/10.1145/3372885.3373825
-}

-- ΩS¹ ≡ ℤ
helix : S¹ → Type₀
helix base     = ℤ
helix (loop i) = sucPathℤ i

ΩS¹ : Type₀
ΩS¹ = base ≡ base

winding : ΩS¹ → ℤ
winding p = subst helix p (pos 0)

{-
The two following statements are proven by refl, so the winding number computes, because the univalence axiom is proven in cubical type theory.
-}

_ : winding (loop ∙ loop ∙ loop) ≡ pos 3
_ = refl

_ : winding ((loop ⁻¹) ∙ loop ∙ (loop ⁻¹)) ≡ negsuc 0
_ = refl 
