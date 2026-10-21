/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Spec.Bridge22
import Dissertation.WellPosedness.Spec.Bridge25
import Dissertation.WellPosedness.Remarks.LiMinSystem
import Dissertation.WellPosedness.Robustness.JumpMargin
import Dissertation.WellPosedness.Examples.MeanFieldWP

/-!
# A system failing Assumption 2.5: Example 3.2 of Li and Min

The linear mean-field system of Li and Min, `liMinCoeffs`, with `n = m = d = 1`,

`b = m_Y(μ)`, `σ = 1`, `h = u`, `f = m_X(μ)`, `g(x, ρ) = −𝔟(ρ)`,

satisfies the measurability (2.3), Assumption 2.2 with any deterministic initial datum and
Assumption 2.3 with `L = 2`, and `G = 1` satisfies Assumption 2.4. Its terminal map is Borel
measurable in the law since the barycentre `𝔟` is `1`-Lipschitz on the 2-Wasserstein space
`P₂(ℝ¹)`. Assumption 2.5 fails for every coupling matrix `G = (c) ∈ ℝ^{1×1}` of full rank, so
`c ≠ 0`, and all constants `α, β₁, β₂`, over any filtered probability space and at every horizon
`T > 0`: its interior inequality (2.7) fails at a pair of deterministic inputs, whose laws are
Dirac masses with means their points. For `c > 0` the inputs `(0, 1, 0, 0)` and `0` turn (2.7)
into `c ≤ −β₁ c²`, and for `c < 0` the inputs `(1, 0, 0, 0)` and `0` turn it into `−c ≤ −β₂ c²`;
both fail for `β₁, β₂ ≥ 0`.

This shows a failure of Assumption 2.5 while the other assumptions hold; it says nothing about
whether Assumption 2.5 is necessary for well-posedness.

## Main statements

* `GX_fin_one_apply`, `entry_ne_zero_of_rank_eq_one` — a `1 × 1` coupling matrix.
* `lipschitzWith_barycentre_toP2` — the barycentre is `1`-Lipschitz on `P₂(ℝ¹)`.
* `jointBorel_liMin`, `assumption22_liMin`, `assumption23_liMin` — (2.3), Assumption 2.2 and
  Assumption 2.3 for the system of Li and Min.
* `not_diagonalMonotone_liMin` — (2.7) fails for every `G ≠ 0` and all `β₁, β₂ ≥ 0`.
* `not_assumption25_liMin` — Assumption 2.5 fails for every full-rank `G` and all constants.
* `liMin_fails_assumption25` — the bundle: (2.3), Assumptions 2.2, 2.3 and 2.4 hold, and
  Assumption 2.5 fails.
-/

open MeasureTheory Filter Dissertation.Law Matrix

namespace Dissertation.WellPosedness.Spec

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence

/-! ### A `1 × 1` coupling matrix -/

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E]

/-! ### The assumptions that hold -/

/-- The barycentre is `1`-Lipschitz on the 2-Wasserstein space `P₂(ℝ¹)`. -/
theorem lipschitzWith_barycentre_toP2 :
    LipschitzWith 1 fun ρ : P2W (EuclideanSpace ℝ (Fin 1)) => barycentre ρ.toP2 :=
  LipschitzWith.of_dist_le_mul fun ρ ρ' => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm]
    exact norm_barycentre_sub_le _ _

/-- **(2.3) for the system of Li and Min.** -/
theorem jointBorel_liMin (T : ℝ) : JointBorel T (liMinCoeffs ν) :=
  jointBorel_iff.mpr ⟨coeffBorelW2_liMin T,
    ((lipschitzWith_barycentre_toP2.continuous.comp continuous_snd).neg).borel_measurable⟩

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **Assumption 2.2 for the system of Li and Min**, with a deterministic initial datum. -/
theorem assumption22_liMin (x₀ : EuclideanSpace ℝ (Fin 1)) :
    Assumption22 ℱ P T (liMinCoeffs ν) (fun _ => x₀) :=
  ⟨stronglyMeasurable_const, memLp_const x₀, originValues_iff_coeffOrigin.mpr (coeffOrigin_liMin T)⟩

/-- **Assumption 2.3 for the system of Li and Min**, with `L = 2`. -/
theorem assumption23_liMin : Assumption23 ℱ P T 2 (liMinCoeffs ν) :=
  assumption23_iff.mpr ⟨zero_le_two, diagonalLipschitzH_liMin, terminalLipschitz_liMin one_le_two⟩

/-! ### Assumption 2.5 fails -/

end Dissertation.WellPosedness.Spec
