/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec5Sharp
import MVFBSDEJ.WellPosedness.Spec.Bridge25

/-!
# Example 5.1(i) of the well-posedness paper: sharpness, proof

## Main statements

* `MVFBSDEJ.Acceptance.ex_concrete_i_sharp` — (2.7) for the coefficients of Example 5.1(i)
  with constants `β₁', β₂'` forces `β₁' ≤ β₁` and `β₂' ≤ β₂`, by the deterministic test tuples of
  `not_diagonalMonotone_affine_of_lt`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Matrix

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.Law

universe u v w

/-- Example 5.1(i), sharpness. -/
theorem ex_concrete_i_sharp : PaperSpec.ex_concrete_i_sharp.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ _ T hT β₁ β₂ _ _ σc hc β₁' β₂' h
  have hM : DiagonalMonotone (enlJoint 𝒢₀ D h𝒢₀) P T (1 : Matrix (Fin 1) (Fin 1) ℝ) β₁' β₂'
      (affineCoeffs β₁ β₂ σc hc) := by
    filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
    have key := (ht (Θ, lawP2 P Θ) (mk_mem_diagonalInputs hΘ hΘ2) (Θ', lawP2 P Θ')
      (mk_mem_diagonalInputs hΘ' hΘ2')).2
    rw [integral_dissipation_eq hΘ2 hΘ2']
    simpa only [pairing27_eq] using key
  by_contra hne
  rw [not_and_or, not_le, not_le] at hne
  exact not_diagonalMonotone_affine_of_lt one_pos hT hne hM

end MVFBSDEJ.Acceptance
