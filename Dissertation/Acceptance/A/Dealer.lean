/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec5
import Dissertation.Acceptance.A.Sec3
import Dissertation.Law.CrowdTwoPoint
import Dissertation.WellPosedness.BrownianPoisson.FrozenCell
import Dissertation.WellPosedness.Examples.LinearGenerator
import Dissertation.WellPosedness.Enlarged.Bot
import Dissertation.WellPosedness.Examples.MeanFieldMonotone
import Dissertation.WellPosedness.Remarks.LinearMean
import Dissertation.Acceptance.A.Sec4
import Dissertation.WellPosedness.Stability.LinearCongr

/-!
# Example 5.5 of the well-posedness paper: proofs

## Main statements

* `Dissertation.Acceptance.A.ex55Crowd_eq` — the crowding correction of Example 5.5 is
  `Dissertation.Law.crowdOp`.
* `Dissertation.Acceptance.A.ex_dealer_potential`, `ex_dealer_crowd` — the potential, and the
  Lipschitz bound of the crowding correction.
* `Dissertation.Acceptance.A.ex_dealer_twopoint`, `ex_dealer_not_mean_corr`, `ex_dealer_affine` —
  beyond the mean.
* `Dissertation.Acceptance.A.ex_dealer_marks` — the mark measure.
* `Dissertation.Acceptance.A.ex_dealer_unit_hypotheses`, `ex_dealer_marks_hypotheses` — the
  hypotheses hold on the mark space of the example.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.Law
  Dissertation.WellPosedness.Stability

universe u v w

/-- The crowding correction of Example 5.5 is `crowdOp`. -/
theorem ex55Crowd_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] (Λ : Measure F) (u : F) :
    PaperSpec.A.ex55Crowd Λ u = crowdOp Λ u :=
  rfl

/-- Example 5.5, the potential. -/
theorem ex_dealer_potential : PaperSpec.A.ex_dealer_potential.{v} := by
  intro E _ ν
  exact ⟨crowdPot_neg, convexOn_crowdPot, hasGradientAt_crowdPot, norm_crowdGrad_le_one,
    norm_crowdGrad_sub_le⟩

/-- Example 5.5, the crowding correction is jointly Lipschitz. -/
theorem ex_dealer_crowd : PaperSpec.A.ex_dealer_crowd.{v} := by
  intro E _ ν _ _ Λ Λ' u u'
  exact norm_crowdOp_sub_le Λ Λ' u u'

/-- The symmetric two-point law `½ (δ_{−a} + δ_a)` as a measure. -/
theorem twoPoint_law_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (a : F) :
    (P2.twoPoint a).law = (1 / 2 : ℝ≥0∞) • (Measure.dirac (-a) + Measure.dirac a) := by
  have hlaw : (P2.twoPoint a).law
      = ENNReal.ofReal (1 - 1 / 2) • Measure.dirac (-a)
        + ENNReal.ofReal (1 / 2) • Measure.dirac a :=
    rfl
  have h : ENNReal.ofReal (1 / 2) = 1 / 2 := by
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rw [hlaw, smul_add, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, h]

/-- Example 5.5, the two-point laws. -/
theorem ex_dealer_twopoint : PaperSpec.A.ex_dealer_twopoint.{v} := by
  intro E _ ν _ _ w hw
  simp only
  rw [← twoPoint_law_eq, ← twoPoint_law_eq, integral_id_twoPoint, integral_id_twoPoint,
    ex55Crowd_eq, ex55Crowd_eq, crowdOp_twoPoint_one hw, crowdOp_twoPoint_two hw]
  refine ⟨rfl, rfl, ?_⟩
  congr 1
  ring

/-- The crowding gradient is not homogeneous: `∇V(2 w) ≠ 2 ∇V(w)` for a unit vector `w`. -/
theorem crowdGrad_two_smul_ne {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {w : F} (hw : ‖w‖ = 1) : crowdGrad ((2 : ℝ) • w) ≠ (2 : ℝ) • crowdGrad w := by
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; exact one_ne_zero)
  have h1 : crowdGrad w = (1 / Real.sqrt (1 + 1 ^ 2)) • w := by
    rw [← crowdGrad_smul_of_norm_eq_one hw, one_smul]
  rw [crowdGrad_smul_of_norm_eq_one hw, h1, smul_smul]
  intro h
  have h' := smul_left_injective ℝ hw0 h
  have h5 : Real.sqrt 2 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2p : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  norm_num at h'
  rw [← div_eq_mul_inv] at h'
  linarith [div_lt_div_of_pos_left two_pos h2p h5]

/-- Example 5.5, the crowding correction is no function of the mean and is nonlinear in the
valuation curve when `L²(ν) ≠ 0`. -/
theorem ex_dealer_not_mean_corr : PaperSpec.A.ex_dealer_not_mean_corr.{v} := by
  intro E _ ν _ _ ⟨u, hu⟩
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hw : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  refine ⟨fun ⟨Φ, hΦ⟩ => crowdOp_not_mean_function hw
    ⟨fun m => Φ m (‖u‖⁻¹ • u), fun Λ => hΦ Λ _⟩, P2.dirac 0, fun ⟨A, c, hA⟩ => ?_⟩
  have h0 := hA 0
  have h1 := hA (‖u‖⁻¹ • u)
  have h2 := hA ((2 : ℝ) • ‖u‖⁻¹ • u)
  change crowdOp (Measure.dirac 0) _ = _ at h0 h1 h2
  rw [crowdOp_dirac, sub_zero, crowdGrad_zero, map_zero, zero_add] at h0
  rw [crowdOp_dirac, sub_zero, ← h0, add_zero] at h1 h2
  rw [map_smul, ← h1] at h2
  exact crowdGrad_two_smul_ne hw h2

/-- Example 5.5, the crowding correction is affine in the law and an expectation kernel. -/
theorem ex_dealer_affine : PaperSpec.A.ex_dealer_affine.{v} := by
  intro E _ ν _ _
  refine ⟨fun Λ₁ Λ₂ s hs u => crowdOp_smul_add_smul Λ₁.law Λ₂.law hs u, fun μ u => ?_,
    fun θ₁ θ₁' θ₂ θ₂' => ?_⟩
  · rw [ex55Crowd_eq, crowdOp, margU_law, integral_map measurable_projUH.aemeasurable
      (stronglyMeasurable_crowdGrad_sub u).aestronglyMeasurable]
    rfl
  · have h := norm_crowdGrad_sub_le (θ₁.2.2.2 - θ₁'.2.2.2) (θ₂.2.2.2 - θ₂'.2.2.2)
    have e : θ₁.2.2.2 - θ₁'.2.2.2 - (θ₂.2.2.2 - θ₂'.2.2.2)
        = projUH (θ₁ - θ₂) - projUH (θ₁' - θ₂') := by
      rw [map_sub, map_sub]
      simp only [projUH_apply]
      abel
    have h₁ := norm_projUH_le_norm_toL2 (θ₁ - θ₂)
    have h₂ := norm_projUH_le_norm_toL2 (θ₁' - θ₂')
    rw [toL2_sub] at h₁ h₂
    calc _ = ‖crowdGrad (θ₁.2.2.2 - θ₁'.2.2.2) - crowdGrad (θ₂.2.2.2 - θ₂'.2.2.2)‖ := rfl
      _ ≤ ‖projUH (θ₁ - θ₂) - projUH (θ₁' - θ₂')‖ := e ▸ h
      _ ≤ ‖projUH (θ₁ - θ₂)‖ + ‖projUH (θ₁' - θ₂')‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add h₁ h₂

/-- Example 5.5, the mark measure. -/
theorem ex_dealer_marks : PaperSpec.A.ex_dealer_marks := by
  intro c hc ϱ hϱ0 hϱ2
  have e : (fun e : Bool × Set.Ioc (0 : ℝ) 1 => (if e.1 then 1 else -1) * (e.2 : ℝ))
      = signedSize := rfl
  exact ⟨dealerMarks_univ hc hϱ0.le, lintegral_sq_dealerMarks_lt_top c hϱ2,
    e ▸ memLp_signedSize c hϱ2⟩

/-! ### The hypotheses on the mark space of the example -/

/-- **A unit vector of `L²(ν)` on the mark space of the example.** With `c_{±1} = 1/2` and
`ϱ = 1`, the signed size `h_c(ς, q) = ς q` has `‖h_c‖_{L²(ν)} = 1`, so it is nonzero. -/
theorem ex_dealer_unit_hypotheses :
    ∃ w : Lp (EuclideanSpace ℝ (Fin 1)) 2 (dealerMarks (fun _ => 1 / 2) 1), ‖w‖ = 1 ∧ w ≠ 0 := by
  have hc : ∀ b : Bool, (fun _ : Bool => (1 / 2 : ℝ)) b = (2 - 1) / 2 := fun _ => by norm_num
  have hw := norm_dealerJump_eq_one (by norm_num : (1 : ℝ) < 2) hc
  exact ⟨_, hw, fun h => by rw [h, norm_zero] at hw; exact zero_ne_one hw⟩

/-- **The hypotheses of the mark measure of Example 5.5 hold**: `c_{±1} = 1/2 > 0` and
`0 < ϱ = 1 < 2`. -/
theorem ex_dealer_marks_hypotheses :
    (∀ b : Bool, 0 < (fun _ : Bool => (1 / 2 : ℝ)) b) ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) < 2 :=
  ⟨fun _ => one_half_pos, one_pos, one_lt_two⟩

end Dissertation.Acceptance.A
