/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Spec.Bridge22
import MVFBSDEJ.WellPosedness.Spec.Bridge25
import MVFBSDEJ.WellPosedness.Remarks.LiMinSystem
import MVFBSDEJ.WellPosedness.Robustness.JumpMargin
import MVFBSDEJ.WellPosedness.Examples.MeanFieldMonotone
import MVFBSDEJ.WellPosedness.Existence.GlobalEnl
import MVFBSDEJ.WellPosedness.System.PaperUniquenessInt
import LevyStochCalc.Driver.GaussianInitial

/-!
# Example 3.2 of Li and Min: the measurability and Assumptions 2.2 and 2.3

The linear mean-field system of Li and Min, `MVFBSDEJ.WellPosedness.System.liMinCoeffs`, with
`n = m = d = 1`,

`b = m_Y(μ)`, `σ = 1`, `h = u`, `f = m_X(μ)`, `g(x, ρ) = −𝔟(ρ)`,

satisfies the measurability (2.3), Assumption 2.2 with any deterministic initial datum and
Assumption 2.3 with `L = 2`. Its terminal map is Borel measurable in the law since the barycentre
`𝔟` is `1`-Lipschitz on the 2-Wasserstein space `P₂(ℝ¹)`.

## Main statements

* `lipschitzWith_barycentre_toP2` — the barycentre is `1`-Lipschitz on `P₂(ℝ¹)`.
* `jointBorel_liMin`, `assumption22_liMin`, `assumption23_liMin` — (2.3), Assumption 2.2 and
  Assumption 2.3 for the system of Li and Min.
-/

open MeasureTheory Filter MVFBSDEJ.Law Matrix

namespace MVFBSDEJ.WellPosedness.Spec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E]

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

end MVFBSDEJ.WellPosedness.Spec
