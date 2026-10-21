/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Acceptance.A.Witness

/-!
# An instance of the hypotheses of Lemma 4.4 of the well-posedness paper

Statement numbers refer to the well-posedness paper at `1f67672`. The instance is that of
`Dissertation.Acceptance.A.thm_cwp_hypotheses`: a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`,
`𝒢₀ = ⊥`, `n = m = 1`, `T = 1`, and the system of Example 5.1(i) with `β₁ = β₂ = 1`,
`σ_c = h_c = 0`.

## Main statements

* `Dissertation.Acceptance.A.lem_cont_hypotheses` — the hypotheses of Lemma 4.4 together with
  `WP(λ₀)` at `λ* = λ₀`, the constant of Lemma 4.2.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.PaperSpec.A
  Dissertation.WellPosedness.Stability LevyStochCalc

universe w

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = β`, `σ_c = 0` and
`h_c = 0`. -/
local notation "sys " β:max =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) β β 0 0

/-- **The hypotheses of Lemma 4.4 hold at Example 5.1(i), with `WP(λ₀)`.** At the instance of
`thm_cwp_hypotheses`, the system with initial datum `0` satisfies (2.3) and Assumptions 2.2–2.5;
and for `λ*` and `λ₀` both equal to the constant `λ*(1, 1) ∈ (0, 1]` of Lemma 4.2, `WP(λ₀)`
holds. -/
theorem lem_cont_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 (sys 1)
      ∧ Assumption22 (enlJoint ⊥ D bot_le) P 1 (sys 1) (fun _ => 0)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 (sys 1)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 (sys 1)
      ∧ ∃ lamStar lam0 : ℝ, 0 < lamStar ∧ lamStar ≤ 1 ∧ lamStar ≤ lam0 ∧ lam0 ≤ 1
          ∧ WP D bot_le hind₀ 1 lam0 (sys 1) (fun _ => 0) := by
  obtain ⟨Ω, _, P, _, D, hind₀, hJ, h22, h23, hG, h25⟩ := thm_cwp_hypotheses.{w}
  obtain ⟨lamStar, hsmall⟩ := lem_small.{0, 0, w}
  obtain ⟨hpos, hle, hwp⟩ := hsmall ⊥ (Measure.dirac (0 : ℝ)) 1 1 1 P D bot_le hind₀ one_pos
    one_pos one_pos 1 one_pos 1 (sys 1) (fun _ => 0) hJ h22 h23
  exact ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hJ, h22, h23, hG, h25, lamStar 1 1,
    lamStar 1 1, hpos, hle, le_rfl, hle, hwp _ hpos.le le_rfl⟩

end Dissertation.Acceptance.A
