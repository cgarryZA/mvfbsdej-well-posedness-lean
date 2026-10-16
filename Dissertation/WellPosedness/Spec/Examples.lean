/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Spec.Thm35
import Dissertation.WellPosedness.Examples.MeanFieldWP

/-!
# Example 5.1(i) under the printed assumptions

The affine system of Example 5.1(i) of the well-posedness paper, for `n = m`, any `d`,
`β₁, β₂ > 0`, `σ_c ∈ ℝ^{n×d}` and `h_c ∈ L²(ν; ℝⁿ)`,

`b = −β₁ y`, `σ = σ_c − β₁ z`, `h = h_c − β₁ u`, `f = β₂ x`, `g(x, ρ) = x`,

satisfies the printed assumptions together, over any filtered probability space and for any
deterministic initial datum `x₀`: the measurability (2.3), Assumption 2.2, Assumption 2.3 with
`L = max(β₁, β₂, 1)`, Assumption 2.4 with `G = 1` and Assumption 2.5 with `G = 1`, `α = 1` and its
own `β₁, β₂`.

## Main statements

* `affine_assumptions` — (2.3) and Assumptions 2.2–2.5 for Example 5.1(i).
-/

open MeasureTheory Filter ProbabilityTheory Dissertation.Law Matrix
open scoped ENNReal

namespace Dissertation.WellPosedness.Spec

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged LevyStochCalc

section Assumptions

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {n d : ℕ} {β₁ β₂ : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}
  {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **Example 5.1(i) satisfies the printed assumptions together**: for `β₁, β₂ > 0` and a
deterministic initial datum `x₀`, (2.3), Assumption 2.2, Assumption 2.3 with
`L = max(β₁, β₂, 1)`, Assumption 2.4 with `G = 1` and Assumption 2.5 with `G = 1`, `α = 1` and
`β₁, β₂`. -/
theorem affine_assumptions (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (x₀ : EuclideanSpace ℝ (Fin n)) :
    JointBorel T (affineCoeffs β₁ β₂ σc hc)
      ∧ Assumption22 ℱ P T (affineCoeffs β₁ β₂ σc hc) (fun _ => x₀)
      ∧ Assumption23 ℱ P T (max (max β₁ β₂) 1) (affineCoeffs β₁ β₂ σc hc)
      ∧ (1 : Matrix (Fin n) (Fin n) ℝ).rank = min n n
      ∧ Assumption25 ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) 1 β₁ β₂
          (affineCoeffs β₁ β₂ σc hc) := by
  have hJ : JointBorel T (affineCoeffs β₁ β₂ σc hc) :=
    jointBorel_iff.mpr ⟨coeffBorelW2_affine T, continuous_fst.borel_measurable⟩
  have h23 : Assumption23 ℱ P T (max (max β₁ β₂) 1) (affineCoeffs β₁ β₂ σc hc) :=
    ⟨le_trans zero_le_one (le_max_right _ _),
      LipInterior.of_diagonalLipschitz
        (diagonalLipschitz_affine hβ₁.le hβ₂.le (le_max_left _ _)),
      terminalLipschitz_affine (le_max_right _ _)⟩
  exact ⟨hJ, ⟨stronglyMeasurable_const, memLp_const x₀,
      originValues_iff_coeffOrigin.mpr (coeffOrigin_affine T)⟩, h23, rank_one_eq_min,
    Assumption25.of_monotone hJ h23 (constants_affine hβ₁ hβ₂) diagonalMonotone_affine
      terminalMonotone_affine⟩

end Assumptions

universe u v w

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {n d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {T β₁ β₂ : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}

end Dissertation.WellPosedness.Spec
