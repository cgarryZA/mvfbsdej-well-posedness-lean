/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec5Sharp
import MVFBSDEJ.Acceptance.Sec5

/-!
# Example 5.1(i) of the well-posedness paper: sharpness, proof

## Main statements

* `MVFBSDEJ.Acceptance.ex_concrete_i_sharp` — (2.7) for the coefficients of Example 5.1(i)
  with constants `β₁', β₂'` forces `β₁' ≤ β₁` and `β₂' ≤ β₂`, by the deterministic test tuples of
  `MVFBSDEJ.WellPosedness.Existence.not_diagonalMonotone_affine_of_lt`.
* `MVFBSDEJ.Acceptance.ex_concrete_i_sharp_hypotheses` — its hypotheses hold at an instance of
  Example 5.1(i), with `β₁' = β₁` and `β₂' = β₂`.
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

/-- **The hypotheses of the sharpness of Example 5.1(i) hold.** Over a probability space carrying
a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥` independent of the driver, for
`T = 1`, `β₁ = β₂ = 1`, `σ_c = 0` and `h_c = 0`, the interior inequality (2.7) holds for the
coefficients of Example 5.1(i) with `G = 1` and the constants `β₁' = β₂' = 1` at almost every
`t ∈ [0, 1]`, by Assumption 2.5 of `ex_concrete_i`. -/
theorem ex_concrete_i_sharp_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ))),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P
      ∧ ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        Mono27At (enlJoint ⊥ D bot_le) P t (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 1 1 0 0) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  refine ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, ?_⟩
  exact (ex_concrete_i ⊥ (Measure.dirac (0 : ℝ)) P D bot_le (indep_bot_left _) 1 one_pos 1 1
    one_pos one_pos 0 0 (fun _ => 0) stronglyMeasurable_const
    (memLp_const _)).2.2.2.2.2.interior

end MVFBSDEJ.Acceptance
