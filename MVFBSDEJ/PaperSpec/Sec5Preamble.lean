/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Setting
import MVFBSDEJ.WellPosedness.Spec.Assumptions
import MVFBSDEJ.WellPosedness.Remarks.LiMinSystem

/-!
# The preamble of Section 5 of the well-posedness paper

Statement numbers refer to the well-posedness paper at `1f67672`, in the standing setting of §2.
The dissipativity of Assumption 2.5 cannot be traded for Lipschitz continuity: the linear jump
system of Example 3.2 of Li and Min (`liMinCoeffs`, `n = m = d = 1`) is Lipschitz and has no
adapted solution on the horizon `T = 3π/4`.

## Main definitions

* `MVFBSDEJ.PaperSpec.sec5_limin` — the preamble's example.
-/

open MeasureTheory Filter ProbabilityTheory

namespace MVFBSDEJ.PaperSpec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Enlarged
  MVFBSDEJ.WellPosedness.Spec

universe u v w

/-- The preamble of §5. In the standing setting with `d = 1`, on the horizon `T = 3π/4`, the
system of Example 3.2 of Li and Min satisfies (2.3), Assumption 2.2 with every deterministic
initial datum and Assumption 2.3 with some constant, and from an initial datum `ξ₀` with
`𝔼 ξ₀ ≠ 0` it has no tuple of `ℍ_weak` satisfying (1.1), so no solution. -/
def sec5_limin : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    JointBorel (3 * Real.pi / 4) (liMinCoeffs ν)
    ∧ (∀ x₀ : EuclideanSpace ℝ (Fin 1),
      Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P (3 * Real.pi / 4) (liMinCoeffs ν) (fun _ => x₀))
    ∧ (∃ L : ℝ, Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P (3 * Real.pi / 4) L (liMinCoeffs ν))
    ∧ ∀ ξ₀ : Ω → EuclideanSpace ℝ (Fin 1), (∫ ω, ξ₀ ω 0 ∂P) ≠ 0 →
      ¬ ∃ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
        (U : Fin 1 → ℝ → Ω → E → ℝ),
        WeakSolution D h𝒢₀ hind₀ (3 * Real.pi / 4) (liMinCoeffs ν) ξ₀ X Y Z U

end MVFBSDEJ.PaperSpec
