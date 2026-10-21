/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3UniquenessLip
import Dissertation.WellPosedness.System.WeakPairDiffLip
import Dissertation.WellPosedness.System.SolvesS2
import Dissertation.WellPosedness.Stability.SupUpgrade
import Dissertation.WellPosedness.BrownianPoisson.Estimate
import Dissertation.Acceptance.A.Sec3Uniqueness

/-!
# The proof of Theorem 3.3 under the Lipschitz condition alone: proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`. Two solutions of
(1.1) in `ℍ_weak` solve the `λ`-forced system (4.1) at `λ = 1` with zero forcing
(`paperWeakSolutionForcedInt_one_zero_iff`); extended off `[0, T]`, their difference is the
difference system of the implementation with the coupling matrix `0`
(`PaperWeakSolutionForcedInt.exists_pairDiff_lip`), which needs Assumption 2.3 along the diagonal
and no monotonicity. Its Lipschitz field is the bound at almost every time, its integrands have
finite energy, which is (3.2), its forward coordinates obey the supremum bound of the difference
system (`PairDiff.lintegral_biSup_fwd_le`), its backward coordinates the estimate of Lemma 4.1
(`LinearBSDEJ.brownianPoisson_estimate`), and the whole difference has finite `ℍ`-norm
(`supSize_lt_top_of_linear`). The terminal bound is (2.6) with (2.9) at the square-integrable
`ℱ_T`-measurable terminal values (`TerminalLipschitz.lipT_pair`). The jump coefficient at the
predictable tuples agrees with the solutions' representatives almost everywhere
(`PaperWeakSolutionForcedInt.ae_forcedJump_sub_leftLim_eq`).

## Main statements

* `Dissertation.Acceptance.A.eq_uniq_coeff_ae` — the bound at almost every time, `K(L) = 40 L²`.
* `Dissertation.Acceptance.A.eq_uniq_coeff_lip` — (3.2).
* `Dissertation.Acceptance.A.eq_uniq_fwd` — the forward difference, `K(T) = 3T + 12`.
* `Dissertation.Acceptance.A.eq_uniq_bwd_eq` — the backward difference.
* `Dissertation.Acceptance.A.eq_uniq_bwd_terminal` — the terminal bound before (3.3),
  `K(L) = 4 L²`.
* `Dissertation.Acceptance.A.eq_uniq_bwd_lip` — (3.3), with `C_BP(T) = 13 e^T + 3T`.
* `Dissertation.Acceptance.A.rem_uniq_lip_mem` — `Θ¹ − Θ² ∈ ℍ`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.WellPosedness.BrownianPoisson
  Dissertation.PaperSpec.A LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

/-- The bound before (3.2) at almost every time, with `K(L) = 10 (2L)²`. -/
theorem eq_uniq_coeff_ae : PaperSpec.A.eq_uniq_coeff_ae.{u, v, w} := by
  refine ⟨fun L => 10 * (2 * L) ^ 2, ?_⟩
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L C hJ h23 ξ₀
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, hXl₁, hYl₁⟩ ⟨⟨γ₂, h₂⟩, hXl₂, hYl₂⟩
  have h₁' := paperWeakSolutionForcedInt_one_zero_iff.mpr h₁
  have h₂' := paperWeakSolutionForcedInt_one_zero_iff.mpr h₂
  obtain ⟨X₁', X₂', Y₁', Y₂', hXe, hYe, hD⟩ := h₁'.exists_pairDiff_lip h₂' hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul
  have hj := h₁'.ae_forcedJump_sub_leftLim_eq h₂' hT.le (jointBorel_iff.mp hJ).1.toCoeffBorel
    hXl₁ hYl₁ hXl₂ hYl₂
  have hj' := ae_time_ae_of_ae_markedEnergyMeasure hj
  filter_upwards [hD.lip, hj', ae_restrict_mem measurableSet_Icc] with s hs hjs hsI
  have hL : ∀ᵐ ω ∂P, ∀ i, ∫⁻ e, (‖jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁)
        Z₁ U₁) i s ω e - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
        s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      = ∫⁻ e, (‖jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
    filter_upwards [hjs] with ω hω i
    refine lintegral_congr_ae ?_
    filter_upwards [hω] with e he
    have := he i
    simp only [one_mul, Pi.zero_apply, sub_self, add_zero] at this
    rw [this]
  have hX : ∀ i ω, X₁' i s ω - X₂' i s ω = X₁ i s ω - X₂ i s ω := fun i ω => by
    rw [congrFun (hXe i s hsI).1 ω, congrFun (hXe i s hsI).2 ω]
  have hY : ∀ k ω, Y₁' k s ω - Y₂' k s ω = Y₁ k s ω - Y₂ k s ω := fun k ω => by
    rw [congrFun (hYe k s hsI).1 ω, congrFun (hYe k s hsI).2 ω]
  refine le_of_eq_of_le (lintegral_congr_ae ?_) (hs.trans_eq ?_)
  · filter_upwards [hL] with ω hω
    simp only [hω]
  · congr 1
    refine lintegral_congr fun ω => ?_
    simp only [hX, hY]

/-- (3.2) under the Lipschitz condition. -/
theorem eq_uniq_coeff_lip : PaperSpec.A.eq_uniq_coeff_lip.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L C hJ h23 ξ₀
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, hXl₁, hYl₁⟩ ⟨⟨γ₂, h₂⟩, hXl₂, hYl₂⟩
  obtain ⟨X₁', X₂', Y₁', Y₂', -, -, hD⟩ :=
    (paperWeakSolutionForcedInt_one_zero_iff.mpr h₁).exists_pairDiff_lip
    (paperWeakSolutionForcedInt_one_zero_iff.mpr h₂) hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul
  have hb : ∀ i, Brownian.Ito.energy P T
      (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s) ≠ ⊤ :=
    fun i => by simpa only [one_mul, Pi.zero_apply, sub_self, add_zero] using (hD.fwd i).b_sq
  have hσ : ∀ i j, Brownian.Ito.energy P T (fun ω s => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
      - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) ≠ ⊤ :=
    fun i j => by simpa only [one_mul, Pi.zero_apply, sub_self, add_zero] using (hD.fwd i).σ_sq j
  have hh : ∀ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
      jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i s ω e
        - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e) ≠ ⊤ :=
    fun i => by
      rw [h₁.markedEnergy_coeffJump_sub_leftLim_eq h₂ hT.le
        (jointBorel_iff.mp hJ).1.toCoeffBorel hXl₁ hYl₁ hXl₂ hYl₂ i]
      simpa only [one_mul, Pi.zero_apply, sub_self, add_zero] using (hD.fwd i).γ_sq
  have hf : ∀ k, Brownian.Ito.energy P T
      (fun ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) ≠ ⊤ :=
    fun k => by simpa only [one_mul, Pi.zero_apply, sub_self, add_zero] using (hD.bwd k).φ_sq
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨ENNReal.sum_lt_top.mpr fun i _ => (hb i).lt_top,
      ENNReal.sum_lt_top.mpr fun i _ => ENNReal.sum_lt_top.mpr fun j _ => (hσ i j).lt_top⟩,
    ENNReal.sum_lt_top.mpr fun i _ => (hh i).lt_top⟩,
    ENNReal.sum_lt_top.mpr fun k _ => (hf k).lt_top⟩

/-- The forward difference in the proof of Theorem 3.3 and its supremum bound, with
`K(T) = 3T + 12`. -/
theorem eq_uniq_fwd : PaperSpec.A.eq_uniq_fwd.{u, v, w} := by
  refine ⟨fun T => 3 * T + 12, ?_⟩
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L C hJ h23 ξ₀
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hw₁ hw₂
  have hfin := eq_uniq_coeff_lip.{u, v, w} 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L C hJ h23 ξ₀
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hw₁ hw₂
  obtain ⟨⟨γ₁, h₁⟩, hXl₁, hYl₁⟩ := hw₁
  obtain ⟨⟨γ₂, h₂⟩, hXl₂, hYl₂⟩ := hw₂
  have h₁' := paperWeakSolutionForcedInt_one_zero_iff.mpr h₁
  have h₂' := paperWeakSolutionForcedInt_one_zero_iff.mpr h₂
  obtain ⟨X₁', X₂', Y₁', Y₂', hXe, -, hD⟩ := h₁'.exists_pairDiff_lip h₂' hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul
  have hj := h₁'.ae_forcedJump_sub_leftLim_eq h₂' hT.le (jointBorel_iff.mp hJ).1.toCoeffBorel
    hXl₁ hYl₁ hXl₂ hYl₂
  have hE := h₁.markedEnergy_coeffJump_sub_leftLim_eq h₂ hT.le
    (jointBorel_iff.mp hJ).1.toCoeffBorel hXl₁ hYl₁ hXl₂ hYl₂
  refine ⟨fun i => ?_, ?_, ?_⟩
  -- the forward difference
  · have hF := hD.fwd i
    simp only [one_mul, Pi.zero_apply, sub_self, add_zero] at hF
    have hq₀ := marked_sq_int_global_of_vanishing hF.γ_vanish hF.γ_sq
    refine ⟨?_, hF.σ_meas, hF.σ_prog, sq_int_global_of_vanishing hF.σ_vanish hF.σ_sq,
      ⟨_, hF.γ_meas, hF.γ_prog, hq₀, ?_⟩, fun H hHm hHp hHq hH t ht => ?_⟩
    · filter_upwards [h₁.b_int i, h₂.b_int i] with ω e₁ e₂
      exact (e₁.sub e₂).congr_fun (fun s _ => by simp only [Pi.sub_apply]) measurableSet_Icc
    · filter_upwards [hj] with q hq
      have := hq i
      simp only [one_mul, Pi.zero_apply, sub_self, add_zero] at this
      exact this.symm
    · have hE' := markedEnergy_sub_eq_zero_of_ae_eq (φ₂ := fun ω s e =>
        jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e) hHm hF.γ_meas (by
          filter_upwards [hH, hj] with q e₁ e₂
          have := e₂ i
          simp only [one_mul, Pi.zero_apply, sub_self, add_zero] at this
          rw [e₁, this])
      filter_upwards [hF.eqn t ht, compensatedIntegral_congr_of_markedEnergy (φ₂ := fun ω s e =>
        jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e) D.N
        (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) hHm hHp hHq hF.γ_meas hF.γ_prog hq₀ hE' ht.2]
        with ω e₁ e₂
      rw [← congrFun (hXe i t ht).1 ω, ← congrFun (hXe i t ht).2 ω, e₁, e₂, zero_add]
  -- the supremum bound
  · have hSX := hD.lintegral_biSup_fwd_le (crossWitnessEnl D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
      (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT
    simp only [one_mul, Pi.zero_apply, sub_self, add_zero] at hSX
    have h0 : ∫⁻ ω, esq (fun _ : Fin n => (0 : ℝ)) ∂P = 0 := by simp [esq]
    have hsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁ i t ω - X₂ i t ω)) ∂P
        = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁' i t ω - X₂' i t ω)) ∂P := by
      refine lintegral_congr fun ω => iSup_congr fun t => iSup_congr fun ht => ?_
      simp only [congrFun (hXe _ t ht).1 ω, congrFun (hXe _ t ht).2 ω]
    simp only [← hE] at hSX ⊢
    rw [hsup]
    refine hSX.trans ?_
    rw [h0, mul_zero, zero_add]
    set A := ∑ i, Brownian.Ito.energy P T
      (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
    set B := ∑ i, ∑ j, Brownian.Ito.energy P T
      (fun ω s => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
    set Cj := ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
      jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i s ω e
        - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e)
    have hK : ENNReal.ofReal (3 * T + 12) = 3 * ENNReal.ofReal T + 12 := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    rw [hK]
    calc 3 * (ENNReal.ofReal T * A) + 12 * (B + Cj)
        ≤ 3 * ENNReal.ofReal T * (A + B + Cj) + 12 * (A + B + Cj) := by
          rw [mul_assoc]
          gcongr
          · exact le_self_add.trans le_self_add
          · exact le_add_self
      _ = (3 * ENNReal.ofReal T + 12) * (A + B + Cj) := by ring
  -- finiteness
  · exact (le_self_add.trans_lt hfin)

/-- The backward difference in the proof of Theorem 3.3. -/
theorem eq_uniq_bwd_eq : PaperSpec.A.eq_uniq_bwd_eq.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L C hJ h23 ξ₀
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ k
  obtain ⟨X₁', X₂', Y₁', Y₂', -, hYe, hD⟩ :=
    (paperWeakSolutionForcedInt_one_zero_iff.mpr h₁).exists_pairDiff_lip
    (paperWeakSolutionForcedInt_one_zero_iff.mpr h₂) hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul
  have hB := hD.bwd k
  simp only [one_mul, Pi.zero_apply, sub_self, add_zero] at hB
  refine ⟨?_, hB.Z_meas, hB.Z_prog, sq_int_global_of_vanishing hB.Z_vanish hB.Z_sq,
    hB.U_meas, hB.U_prog, marked_sq_int_global_of_vanishing hB.U_vanish hB.U_sq,
    fun t ht => ?_⟩
  · filter_upwards [h₁.f_int k, h₂.f_int k] with ω e₁ e₂
    exact (e₁.sub e₂).congr_fun (fun s _ => by simp only [Pi.sub_apply]) measurableSet_Icc
  · filter_upwards [hB.eqn t ht] with ω e
    rw [← congrFun (hYe k t ht).1 ω, ← congrFun (hYe k t ht).2 ω]
    exact e

/-- The terminal bound before (3.3), with `K(L) = 4 L²`. -/
theorem eq_uniq_bwd_terminal : PaperSpec.A.eq_uniq_bwd_terminal.{u, v, w} := by
  refine ⟨fun L => 4 * L ^ 2, ?_⟩
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L C hJ h23 ξ₀
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩
  have hT' : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  exact ⟨fun i => ⟨h₁.XT_sq i, h₂.XT_sq i⟩,
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).lipT_pair
      (fun i => h₁.X_adapted i T hT') (fun i => h₂.X_adapted i T hT') h₁.XT_sq h₂.XT_sq,
    lintegral_esq_lt_top (x := fun i ω => X₁ i T ω - X₂ i T ω)
      fun i => (h₁.XT_sq i).sub (h₂.XT_sq i)⟩

/-- (3.3) under the Lipschitz condition, with `C_BP(T) = 13 e^T + 3T`. -/
theorem eq_uniq_bwd_lip : PaperSpec.A.eq_uniq_bwd_lip.{u, v, w} := by
  refine ⟨fun T => 13 * Real.exp T + 3 * T, ?_⟩
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L C hJ h23 ξ₀
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩
  obtain ⟨X₁', X₂', Y₁', Y₂', -, hYe, hD⟩ :=
    (paperWeakSolutionForcedInt_one_zero_iff.mpr h₁).exists_pairDiff_lip
    (paperWeakSolutionForcedInt_one_zero_iff.mpr h₂) hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul
  have 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  have hℱ0 := hF0_enlJoint D h𝒢₀
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0
  have hξ : ∀ k, MemLp (fun ω => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) 2 P :=
    fun k => by simpa only [one_mul, Pi.zero_apply, sub_self, add_zero] using (hD.bwd k).ξ_sq
  have hφ : ∀ k, Brownian.Ito.energy P T
      (fun ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) ≠ ⊤ :=
    fun k => by simpa only [one_mul, Pi.zero_apply, sub_self, add_zero] using (hD.bwd k).φ_sq
  have hest : ∀ k, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y₁' k t ω - Y₂' k t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
      ≤ ENNReal.ofReal (13 * Real.exp T + 3 * T)
        * (∫⁻ ω, (‖terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω‖₊ : ℝ≥0∞) ^ 2 ∂P
          + Brownian.Ito.energy P T (fun ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
            - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)) := fun k => by
    have h := (hD.bwd k).brownianPoisson_estimate 𝒲 hℱ0 hnull hT
    simp only [one_mul, Pi.zero_apply, sub_self, add_zero] at h
    exact le_trans (le_self_add.trans le_self_add) h
  have hsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω)) ∂P
      = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁' k t ω - Y₂' k t ω)) ∂P := by
    refine lintegral_congr fun ω => iSup_congr fun t => iSup_congr fun ht => ?_
    simp only [congrFun (hYe _ t ht).1 ω, congrFun (hYe _ t ht).2 ω]
  have hesq : ∫⁻ ω, esq (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) ∂P
      = ∑ k, ∫⁻ ω, (‖terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    unfold esq
    exact lintegral_finsetSum' _ fun k _ =>
      ((hξ k).aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  refine ⟨?_, ENNReal.add_lt_top.mpr ⟨lintegral_esq_lt_top hξ,
    ENNReal.sum_lt_top.mpr fun k _ => (hφ k).lt_top⟩⟩
  rw [hsup, hesq, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine (lintegral_biSup_esq_le hT.le
    (fun k t => ((hD.bwd k).Y_adapted t).mono ((enlJoint 𝒢₀ D h𝒢₀).le t) le_rfl)
    fun k => (hD.bwd k).Y_rightCont).trans (Finset.sum_le_sum fun k _ => hest k)

/-- `Θ¹ − Θ² ∈ ℍ` under the Lipschitz condition. -/
theorem rem_uniq_lip_mem : PaperSpec.A.rem_uniq_lip_mem.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L C hJ h23 ξ₀
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩
  obtain ⟨X₁', X₂', Y₁', Y₂', hXe, hYe, hD⟩ :=
    (paperWeakSolutionForcedInt_one_zero_iff.mpr h₁).exists_pairDiff_lip
    (paperWeakSolutionForcedInt_one_zero_iff.mpr h₂) hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul
  have h := supSize_lt_top_of_linear (ν := ν) hD.fwd hD.bwd (crossWitnessEnl D h𝒢₀ hind₀)
    (hF0_enlJoint D h𝒢₀) (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT
  refine lt_of_eq_of_lt ?_ h
  unfold supSize
  congr 3
  · refine lintegral_congr fun ω => iSup_congr fun t => iSup_congr fun ht => ?_
    simp only [congrFun (hXe _ t ht).1 ω, congrFun (hXe _ t ht).2 ω]
  · refine lintegral_congr fun ω => iSup_congr fun t => iSup_congr fun ht => ?_
    simp only [congrFun (hYe _ t ht).1 ω, congrFun (hYe _ t ht).2 ω]

end Dissertation.Acceptance.A
