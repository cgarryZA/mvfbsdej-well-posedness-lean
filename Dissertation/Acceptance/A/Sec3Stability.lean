/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3Stability
import Dissertation.Acceptance.A.Sec3

/-!
# The paragraph after Theorem 3.1 of the well-posedness paper: proofs

## Main statements

* `Dissertation.Acceptance.A.thm_stab_companion` — the companion bound, from Theorem 3.1 with
  the roles of the two systems exchanged.
* `Dissertation.Acceptance.A.thm_stab_data` — continuous dependence on the data, from
  Theorem 3.1 with the interior coefficient differences equal to zero.
* `Dissertation.Acceptance.A.thm_stab_minimal` — the estimate (3.1) using only (2.3) on the
  second system, with `C_stab = aprioriConst T (10 (2L)²) (4 (2L)²) ‖G‖ c_G α β₁ β₂ 1`.
-/

open MeasureTheory ProbabilityTheory

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Stability Dissertation.WellPosedness.Spec
  Dissertation.WellPosedness.Enlarged

universe u v w

/-- `‖a − b‖₊ = ‖b − a‖₊` on `ℝ`. -/
theorem nnnorm_real_sub_comm (a b : ℝ) : ‖a - b‖₊ = ‖b - a‖₊ := NNReal.eq (norm_sub_rev a b)

/-- `supSize` of a difference is symmetric in the two tuples. -/
theorem supSize_sub_comm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Type*}
    [MeasurableSpace E] {ν : Measure E} {n m d : ℕ} {T : ℝ}
    (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
    (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ) :
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      = supSize P ν T (fun i t ω => X₂ i t ω - X₁ i t ω) (fun k t ω => Y₂ k t ω - Y₁ k t ω)
        (fun k t ω j => Z₂ k t ω j - Z₁ k t ω j) (fun k t ω e => U₂ k t ω e - U₁ k t ω e) := by
  simp only [supSize, esq, LevyStochCalc.Brownian.Ito.energy,
    LevyStochCalc.Poisson.Compensated.markedEnergy, nnnorm_real_sub_comm]

/-- The companion bound after Theorem 3.1. -/
theorem thm_stab_companion : PaperSpec.A.thm_stab_companion.{u, v, w} := by
  obtain ⟨Cst, hC⟩ := thm_stab.{u, v, w}
  refine ⟨Cst, ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L₁ L α β₁ β₂ G C₁ C₂ ξ₁ ξ₂
    hJ₁ h22₁ h23₁ hJ₂ h22₂ h23₂ hG h25₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hS₁ hS₂
  have h := hC 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L L₁ α β₁ β₂ G C₂ C₁ ξ₂ ξ₁ hJ₂ h22₂ h23₂
    hG h25₂ hJ₁ h22₁ h23₁ X₂ X₁ Y₂ Y₁ Z₂ Z₁ U₂ U₁ hS₂ hS₁
  rw [supSize_sub_comm] at h
  refine h.trans_eq ?_
  congr 1
  simp only [dataSize, esq, LevyStochCalc.Brownian.Ito.energy,
    LevyStochCalc.Poisson.Compensated.markedEnergy, nnnorm_real_sub_comm]

/-- Continuous dependence on the data after Theorem 3.1. -/
theorem thm_stab_data : PaperSpec.A.thm_stab_data.{u, v, w} := by
  obtain ⟨Cst, hC⟩ := thm_stab.{u, v, w}
  refine ⟨Cst, ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L L₂ α β₁ β₂ G C₁ C₂ ξ₁ ξ₂
    hJ₁ h22₁ h23₁ hG h25₁ hJ₂ h22₂ h23₂ hb hσ hh hf X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hS₁ hS₂
  refine (hC 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L L₂ α β₁ β₂ G C₁ C₂ ξ₁ ξ₂ hJ₁ h22₁ h23₁
    hG h25₁ hJ₂ h22₂ h23₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hS₁ hS₂).trans_eq ?_
  congr 1
  have hcj : coeffJump P T C₂ (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂
      = coeffJump P T C₁ (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂ := by
    funext i s ω e
    simp only [coeffJump, hh]
  simp only [dataSize, driftProc, diffusionProc, driverProc, hcj, hb, hσ, hf, sub_self,
    LevyStochCalc.Brownian.Ito.energy, LevyStochCalc.Poisson.Compensated.markedEnergy]
  simp

/-- The estimate (3.1) without the hypotheses on the second system after Theorem 3.1. -/
theorem thm_stab_minimal : PaperSpec.A.thm_stab_minimal.{u, v, w} := by
  refine ⟨fun T L g c α β₁ β₂ =>
    aprioriConst T (10 * (2 * L) ^ 2) (4 * (2 * L) ^ 2) g c α β₁ β₂ 1, ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C₁ C₂ ξ₁ ξ₂
    hJ₁ h22₁ h23₁ hG h25₁ hJ₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hS₁ hS₂
  obtain ⟨⟨γ₁, h₁⟩, -, -⟩ := hS₁
  obtain ⟨⟨γ₂, h₂⟩, hX₂l, hY₂l⟩ := hS₂
  have key := PaperSolution.supSize_sub_le_of_coeffBorel
    (h₁ := h₁)
    (h₂ := h₂)
    (hmeas₁ := (jointBorel_iff.mp hJ₁).1.toCoeffBorel)
    (hg₁ := hJ₁.measurable_g_section)
    (hg₂ := hJ₂.measurable_g_section)
    (𝒲 := crossWitnessEnl D h𝒢₀ hind₀)
    (hℱ0 := hF0_enlJoint D h𝒢₀)
    (hnull := fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (hT := hT)
    (hL := h23₁.interior.diagonalLipschitz_two_mul)
    (hLT := (lipTerminal_iff_terminalLipschitz.mp h23₁.terminal).two_mul)
    (hcG := inv_nonneg.mpr (sq_nonneg (sMin G)))
    (hGf := gCoerciveForward_of_rank hG)
    (hGb := gCoerciveBackward_of_rank hG)
    (hconst := h25₁.constants)
    (hM := h25₁.diagonalMonotone)
    (hMT := h25₁.terminalMonotone)
  have hj : ∀ i, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => jumpProc T (coeffJump P T C₁ X₂ Y₂ Z₂ U₂) i s ω e - jumpProc T γ₂ i s ω e)
      = LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
        jumpProc T (coeffJump P T C₁ (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e
          - jumpProc T (coeffJump P T C₂ (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e) :=
    fun i => PaperSolution.markedEnergy_coeffJump_sub_eq_leftLim h₂ hT hX₂l hY₂l
      (jointBorel_iff.mp hJ₁).1.toCoeffBorel (jointBorel_iff.mp hJ₂).1.toCoeffBorel i
  refine key.trans_eq ?_
  simp only [dataSize, hj]

end Dissertation.Acceptance.A
