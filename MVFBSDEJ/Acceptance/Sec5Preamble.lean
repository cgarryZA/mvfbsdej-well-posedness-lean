/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec5Preamble
import MVFBSDEJ.WellPosedness.Remarks.NoSolution
import MVFBSDEJ.WellPosedness.Spec.NotAssumption25
import LevyStochCalc.Driver.Existence

/-!
# The preamble of Section 5 of the well-posedness paper: proofs

## Main statements

* `MVFBSDEJ.Acceptance.sec5_limin` — the system of Example 3.2 of Li and Min is Lipschitz
  and has no solution on the horizon `T = 3π/4` from an initial datum of nonzero mean.
* `MVFBSDEJ.Acceptance.sec5_limin_hypotheses` — the standing setting with `d = 1` and an
  initial datum of nonzero mean exist.
-/

open MeasureTheory ProbabilityTheory

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Enlarged
  MVFBSDEJ.WellPosedness.Spec

universe u v w

/-- The preamble of §5. -/
theorem sec5_limin : PaperSpec.sec5_limin.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ hind₀
  refine ⟨jointBorel_liMin _, fun x₀ => assumption22_liMin x₀, ⟨2, assumption23_liMin⟩,
    fun ξ₀ hξ => ?_⟩
  rintro ⟨X, Y, Z, U, ⟨γ, h⟩, -, -⟩
  exact not_paperWeakSolutionInt_liMin hξ h

/-- **The hypotheses of the preamble of §5 can be met.** There is a probability space carrying a
Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥` independent of it, and an initial
datum `ξ₀ ≡ 1` of nonzero mean. -/
theorem sec5_limin_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (_ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)
      (ξ₀ : Ω → EuclideanSpace ℝ (Fin 1)), (∫ ω, ξ₀ ω 0 ∂P) ≠ 0 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  refine ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _,
    fun _ => EuclideanSpace.single 0 1, ?_⟩
  simp

end MVFBSDEJ.Acceptance
