/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec3Stability
import MVFBSDEJ.Acceptance.Sec3
import MVFBSDEJ.WellPosedness.Existence.CoeffPredictable
import MVFBSDEJ.WellPosedness.Existence.PaperAdmissible

/-!
# The paragraph after Theorem 3.1 of the well-posedness paper: proofs

## Main statements

* `MVFBSDEJ.Acceptance.thm_stab_companion` — the companion bound, from Theorem 3.1 with
  the roles of the two systems exchanged.
* `MVFBSDEJ.Acceptance.thm_stab_data` — continuous dependence on the data, from
  Theorem 3.1 with the interior coefficient differences equal to zero.
* `MVFBSDEJ.Acceptance.thm_stab_minimal` — the estimate (3.1) using only (2.3) on the
  second system, with `C_stab = aprioriConst T (10 (2L)²) (4 (2L)²) ‖G‖ c_G α β₁ β₂ 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Stability MVFBSDEJ.WellPosedness.Spec
  MVFBSDEJ.WellPosedness.Enlarged

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
theorem thm_stab_companion : PaperSpec.thm_stab_companion.{u, v, w} := by
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
theorem thm_stab_data : PaperSpec.thm_stab_data.{u, v, w} := by
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

/-- A bound `a ≤ c b` in `[0, ∞]` with `c ≠ 0` holds once it holds for finite `b`. -/
theorem le_mul_of_ne_top_imp {a b c : ℝ≥0∞} (hc : c ≠ 0) (h : b ≠ ⊤ → a ≤ c * b) :
    a ≤ c * b := by
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp [ENNReal.mul_top hc]
  · exact h hb

/-- The estimate (3.1) without the hypotheses on the second system after Theorem 3.1. If the
right side is finite, the drift and driver differences have finite energy, and so do the drift and
driver of the second system along its solution, the first system's being finite by (4.2). -/
theorem thm_stab_minimal : PaperSpec.thm_stab_minimal.{u, v, w} := by
  refine ⟨fun T L g c α β₁ β₂ =>
    aprioriConst T (10 * (2 * L) ^ 2) (4 * (2 * L) ^ 2) g c α β₁ β₂ 1, ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C₁ C₂ ξ₁ ξ₂
    hJ₁ h22₁ h23₁ hG h25₁ hJ₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hS₁ hS₂
  have hcG : 0 ≤ (sMin G ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg (sMin G))
  have hC : 0 < aprioriConst T (10 * (2 * L) ^ 2) (4 * (2 * L) ^ 2) ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁
      β₂ 1 :=
    aprioriConst_pos hT.le (by positivity) (by positivity) hcG h25₁.constants.α_nonneg
      h25₁.constants.β₁_nonneg h25₁.constants.β₂_nonneg one_pos
  refine le_mul_of_ne_top_imp (ENNReal.ofReal_pos.mpr hC).ne' fun hfin => ?_
  obtain ⟨⟨⟨⟨⟨-, -⟩, hbs⟩, -⟩, -⟩, hfs⟩ := by simpa only [dataSize, ENNReal.add_ne_top] using hfin
  obtain ⟨⟨γ₁, h₁⟩, -, -⟩ := Solution.paperSolutionEnl hT.le hJ₁ h22₁.origin h23₁ hS₁
  obtain ⟨⟨⟨γ₂, hw₂⟩, hX₂l, hY₂l⟩, hX₂s, hY₂s⟩ := hS₂
  obtain ⟨γ', hadm⟩ := hw₂.toPaperWeakTuple.exists_paperAdmissible hT.le (hJ₁.coeffRegular _ P)
    (originValues_iff_coeffOrigin.mp h22₁.origin) h23₁.interior.diagonalLipschitz_two_mul
  have hb₂ : ∀ i, LevyStochCalc.Brownian.Ito.energy P T (driftProc P T C₂ X₂ Y₂ Z₂ U₂ i) ≠ ⊤ :=
    fun i => by
      have e : driftProc P T C₂ X₂ Y₂ Z₂ U₂ i = fun ω s => driftProc P T C₁ X₂ Y₂ Z₂ U₂ i ω s
          - (driftProc P T C₁ X₂ Y₂ Z₂ U₂ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s) := by
        funext ω s
        ring
      rw [e]
      exact LevyStochCalc.BSDEJ.Solves.energy_sub_ne_top (hadm.b_meas i)
        ((hadm.b_meas i).sub (hw₂.b_meas i)) (hadm.b_sq i)
        (ENNReal.sum_ne_top.mp hbs i (Finset.mem_univ i))
  have hf₂ : ∀ k, LevyStochCalc.Brownian.Ito.energy P T (driverProc P T C₂ X₂ Y₂ Z₂ U₂ k) ≠ ⊤ :=
    fun k => by
      have e : driverProc P T C₂ X₂ Y₂ Z₂ U₂ k = fun ω s => driverProc P T C₁ X₂ Y₂ Z₂ U₂ k ω s
          - (driverProc P T C₁ X₂ Y₂ Z₂ U₂ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s) := by
        funext ω s
        ring
      rw [e]
      exact LevyStochCalc.BSDEJ.Solves.energy_sub_ne_top (hadm.f_meas k)
        ((hadm.f_meas k).sub (hw₂.f_meas k)) (hadm.f_sq k)
        (ENNReal.sum_ne_top.mp hfs k (Finset.mem_univ k))
  have hpw₂ : PaperWeakSolution D (enlJoint 𝒢₀ D h𝒢₀)
      (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T
      C₂ (fun i ω => ξ₂ ω i) X₂ Y₂ Z₂ U₂ γ₂ :=
    { toPaperWeakTuple := hw₂.toPaperWeakTuple
      toPaperAdmissible := { hw₂.toPaperAdmissibleInt with b_sq := hb₂, f_sq := hf₂ }
      fwd := hw₂.fwd
      bwd := hw₂.bwd }
  have h₂ := hpw₂.paperSolution hX₂s hY₂s
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

end MVFBSDEJ.Acceptance
