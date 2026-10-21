/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.Dealer.Coeffs

/-!
# The crowding operator is affine in the law

The crowding operator `A_λ(u) = ∫ ∇V(u − v) λ(dv)` of Example 5.5 of the well-posedness paper is
affine in the law: `A_{s λ₁ + (1 − s) λ₂} = s A_{λ₁} + (1 − s) A_{λ₂}` for finite measures
`λ₁, λ₂` and `s ∈ [0, 1]`.

## Main statements

* `Dissertation.Law.crowdOp_smul_add_smul` — the crowding operator is affine in the law.
-/

open MeasureTheory Filter Dissertation.Law
open scoped RealInnerProductSpace

namespace Dissertation.Law

/-! ### The crowding operator is affine in the law -/

section Affine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [CompleteSpace F] in
/-- **The crowding operator is affine in the law**: for finite measures `Λ₁, Λ₂` on `F` and
`s ∈ [0, 1]`, `A_{s Λ₁ + (1 − s) Λ₂}(u) = s A_{Λ₁}(u) + (1 − s) A_{Λ₂}(u)`. -/
theorem crowdOp_smul_add_smul (Λ₁ Λ₂ : Measure F) [IsFiniteMeasure Λ₁] [IsFiniteMeasure Λ₂]
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (u : F) :
    crowdOp (ENNReal.ofReal s • Λ₁ + ENNReal.ofReal (1 - s) • Λ₂) u
      = s • crowdOp Λ₁ u + (1 - s) • crowdOp Λ₂ u := by
  rw [crowdOp, integral_add_measure
    ((integrable_crowdGrad_sub Λ₁ u).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_crowdGrad_sub Λ₂ u).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hs.1,
    ENNReal.toReal_ofReal (by linarith [hs.2])]
  rfl

end Affine

end Dissertation.Law
