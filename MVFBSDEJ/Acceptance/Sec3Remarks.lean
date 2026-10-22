/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec3Remarks
import MVFBSDEJ.PaperSpec.Sec2Measurability
import MVFBSDEJ.Acceptance.Sec3
import MVFBSDEJ.WellPosedness.Spec.Examples

/-!
# The measurability (2.5) and Remark 3.2 of the well-posedness paper: proofs

The measurability (2.5) is a consequence of the joint Borel measurability (2.3), through
`MVFBSDEJ.WellPosedness.Spec.JointBorel.coeffRegular` and
`MVFBSDEJ.WellPosedness.Spec.JointBorel.predictable_jump`. For Remark 3.2, along a tuple of `ℍ²`
satisfying (1.1), (2.5) and Assumptions 2.2–2.3 bound the energy of the drift and driver processes
by (4.2), so the tuple satisfies (1.1) with square-integrable coefficient processes; the `S²` bounds
of `𝕊` then follow from the forward form of both equations.

## Main statements

* `MVFBSDEJ.Acceptance.eq_coefmeas`, `eq_coefmeas_jump` — (2.5).
* `MVFBSDEJ.Acceptance.rem_cwp_class` — Remark 3.2, and `rem_cwp_class_hypotheses` — its
  hypotheses hold at Example 5.1(i).
-/

open MeasureTheory ProbabilityTheory

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Enlarged
  MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.WellPosedness.Existence MVFBSDEJ.PaperSpec

universe u v w

/-- (2.5), the first line: along a progressive tuple the drift, diffusion and driver evaluations
are progressively measurable, and the jump coefficient has a marked progressive representative. -/
theorem eq_coefmeas : PaperSpec.eq_coefmeas.{u, v} := by
  intro Ω mΩ ℱ P _ E _ ν _ _ n m d T C hJ
  exact hJ.coeffRegular ℱ P

/-- (2.5), the second line: the jump coefficient along a predictable tuple and a Borel law flow is
predictable. -/
theorem eq_coefmeas_jump : PaperSpec.eq_coefmeas_jump.{u, v} := by
  intro Ω mΩ ℱ E _ ν _ _ n m d T C Θ ρ hJ hΘ hρ
  exact hJ.predictable_jump hΘ hρ

/-- Remark 3.2: under (2.3) and Assumptions 2.2–2.3, a tuple of `ℍ²` satisfying (1.1) solves
(1.1) in `𝕊`. -/
theorem rem_cwp_class : PaperSpec.rem_cwp_class.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ T hT L C ξ₀ hJ h22 h23 X Y Z U hW
  obtain ⟨γ, hw⟩ := hW.1
  obtain ⟨γ', hadm⟩ := hw.toPaperWeakTuple.exists_paperAdmissible hT.le
    (eq_coefmeas _ P ν n m d T C hJ) (originValues_iff_coeffOrigin.mp h22.origin)
    h23.interior.diagonalLipschitz_two_mul
  have hpw : PaperWeakSolution D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T C (fun i ω => ξ₀ ω i) X Y Z U γ :=
    { toPaperWeakTuple := hw.toPaperWeakTuple
      toPaperAdmissible := { hw.toPaperAdmissibleInt with b_sq := hadm.b_sq, f_sq := hadm.f_sq }
      fwd := hw.fwd
      bwd := hw.bwd }
  have hs := hpw.toPaperSolution (crossWitnessEnl D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT
  exact ⟨hW, hs.X_sup, hs.Y_sup⟩

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = β`, `σ_c = 0` and
`h_c = 0`. -/
local notation "sys " β:max =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) β β 0 0

/-- **The hypotheses of Remark 3.2 hold at Example 5.1(i).** Over a probability space carrying a
Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`, `n = m = 1` and `T = 1`, the system
of Example 5.1(i) with `β₁ = β₂ = 1`, `σ_c = 0`, `h_c = 0` and initial datum `0` satisfies (2.3),
Assumption 2.2 and Assumption 2.3 with `L = 1`, and a tuple of `ℍ²` satisfies (1.1) (the
solution of Theorem 3.5). -/
theorem rem_cwp_class_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 (sys 1)
      ∧ Assumption22 (enlJoint ⊥ D bot_le) P 1 (sys 1) (fun _ => 0)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 (sys 1)
      ∧ ∃ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
          (U : Fin 1 → ℝ → Ω → ℝ → ℝ),
          WeakSolution D bot_le hind₀ 1 (sys 1) (fun _ => 0) X Y Z U := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨hJ, h22, h23, hG, h25⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (0 : EuclideanSpace ℝ (Fin 1))
  have e₁ : max (max (1 : ℝ) 1) 1 = 1 := by norm_num
  rw [e₁] at h23
  obtain ⟨X, Y, Z, U, hW, -, -⟩ := (thm_cwp ⊥ _ 1 1 1 P D bot_le hind₀ one_pos one_pos
    one_pos 1 one_pos 1 1 1 1 1 _ _ hJ h22 h23 hG h25).1
  exact ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hJ, h22, h23, X, Y, Z, U, hW⟩

end MVFBSDEJ.Acceptance
