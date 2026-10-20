/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4ProofSteps
import Dissertation.Acceptance.A.Sec4BrownianPoisson
import Dissertation.Acceptance.A.Sec4Frozen
import Dissertation.Acceptance.A.Sec4Contraction
import Dissertation.Acceptance.A.Sec4Estimates
import Dissertation.WellPosedness.BrownianPoisson.EnergyAtWeighted
import Dissertation.WellPosedness.Stability.RateEnergy

/-!
# Further steps of the proofs of Lemmas 4.1–4.3: proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The weighted
inequality of Lemma 4.1 is the difference of the weighted second-moment identities at the
horizons `t` and `T` with Young's inequality (`brownianPoisson_weighted_at_vec_of_measurable`).
The bound before (4.9) is the first link of (4.9) before integration in time. The backward
difference before (4.12) is the difference of the linear backward equations of the two frozen
steps (`LinearBSDEJ.sub`). The contraction by `1/2` is (4.13) at `λ ≤ λ_*`, where
`C_Φ λ² ≤ C_Φ λ_*² = 1/4`. The first two links of the chain before (4.27) are the `S²` bound of
the backward coordinates of the difference system (`LinearBSDEJ.lintegral_biSup_sq_le`) and the
rate bound (3.2) at the pair (`PairDiff.rateEnergy_le`).

## Main statements

* `Dissertation.Acceptance.A.eq_supE_weighted` — the weighted inequality.
* `Dissertation.Acceptance.A.eq_coeffdiff_ae` — the bound before (4.9).
* `Dissertation.Acceptance.A.eq_bwddiff_identity` — the backward difference before (4.12).
* `Dissertation.Acceptance.A.eq_contract_half` — `λ_*` and the contraction by `1/2`.
* `Dissertation.Acceptance.A.eq_bwd_chain` — the first two links before (4.27), with
  `K₁ = 3T + 12` and `K₂ = (3T + 12)(2 · 10 (2L)² + 2)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.WellPosedness.BrownianPoisson
  Dissertation.PaperSpec.A Dissertation.Law LevyStochCalc

universe u v w

/-- The weighted inequality in the proof of Lemma 4.1. -/
theorem eq_supE_weighted : PaperSpec.A.eq_supE_weighted.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ hind₀ _ _ T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs
    _ hξ hφm hφs hYa hYr _ heq t ht
  have hξk : ∀ k, MemLp (fun ω => δξ ω k) 2 P := memLp_iff_forall_coord.mp hξ
  exact brownianPoisson_weighted_at_vec_of_measurable (crossWitnessEnl D h𝒢₀ hind₀)
    (hF0_enlJoint D h𝒢₀) (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT
    (ξ := fun k ω => δξ ω k)
    (fun k j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
    (fun k => progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k)) hZv hZs
    (fun k => (hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
    (fun k => (hU k).markedProgressivelyMeasurable) hUv hUs hφm hφs hξk hYa hYr heq ht

/-- The bound before (4.9), at almost every time. -/
theorem eq_coeffdiff_ae : PaperSpec.A.eq_coeffdiff_ae.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ _ _ _ _ T hT L C ξ₀ _ _ h23 X₁ X₂ Y₁ Y₂ Z₁ Z₂
    U₁ U₂ ⟨hw₁, -, -, -, -⟩ ⟨hw₂, -, -, -, -⟩
  filter_upwards [h23.interior, hw₁.ae_memLp_tupleAt hT.le, hw₂.ae_memLp_tupleAt hT.le,
    hw₁.ae_ae_memLp_jump, hw₂.ae_ae_memLp_jump, ae_restrict_mem measurableSet_Icc]
    with s hLs hm₁ hm₂ hU₁ hU₂ hs
  refine (hLs.lintegral_sq_coeffDiff_le (hw₁.stronglyMeasurable_tupleAt hs) hm₁
    (hw₂.stronglyMeasurable_tupleAt hs) hm₂).trans ?_
  gcongr ENNReal.ofReal (10 * L ^ 2) * ?_
  refine lintegral_mono_ae ?_
  filter_upwards [hU₁, hU₂] with ω h₁ h₂
  rw [tupleAt_sub h₁ h₂]
  exact ofReal_channelSq_tupleAt_le s ω

/-- The backward difference before (4.12). -/
theorem eq_bwddiff_identity : PaperSpec.A.eq_bwddiff_identity.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L C ξ₀ _ _ _ lam _ _
    qb qσ qh qf qg _ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ _ _ X₁' X₂' Y₁' Y₂' Z₁' Z₂' U₁' U₂' hS₁ hS₂ k
  have h := (hS₁.2.1 k).sub (hS₂.2.1 k)
  have e₁ : (fun ω => lam * terminalVal P T C X₁' k ω + qg k ω
      - (lam * terminalVal P T C X₂' k ω + qg k ω))
      = fun ω => lam * (terminalVal P T C X₁' k ω - terminalVal P T C X₂' k ω) :=
    funext fun ω => by ring
  have e₂ : (fun ω s => lam * driverProc P T C X₁ Y₁ Z₁ U₁ k ω s + qf k ω s
      - (lam * driverProc P T C X₂ Y₂ Z₂ U₂ k ω s + qf k ω s))
      = fun ω s => lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
        - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) :=
    funext fun ω => funext fun s => by ring
  rw [e₁, e₂] at h
  exact h

/-- `λ_*` and the contraction by `1/2`, after (4.13). -/
theorem eq_contract_half : PaperSpec.A.eq_contract_half.{u, v, w} := by
  obtain ⟨c₀, hc₀, hC⟩ := eq_contract.{u, v, w}
  refine ⟨c₀, hc₀, fun c hc => ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L C ξ₀ hJ h22 h23 CΦ lamStar
    hCΦ hlam
  have hC1 : 1 ≤ CΦ := hCΦ ▸ le_max_left _ _
  have hsq1 : 1 ≤ Real.sqrt CΦ := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hC1
  have hl0 : 0 < lamStar := by
    rw [hlam]
    exact inv_pos.mpr (by linarith)
  have hlhalf : lamStar ≤ 1 / 2 := by
    rw [hlam, one_div]
    exact inv_anti₀ (by norm_num) (by linarith)
  have hstar : CΦ * lamStar ^ 2 = 1 / 4 := by
    rw [hlam, inv_pow, mul_pow, Real.sq_sqrt (by linarith)]
    field_simp
    ring
  refine ⟨⟨hl0, hlhalf⟩, fun lam hl0' hll => ?_⟩
  have hl1 : lam ≤ 1 := hll.trans (hlhalf.trans (by norm_num))
  have hCl : CΦ * lam ^ 2 ≤ 1 / 4 := by
    rw [← hstar]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0' hll 2) (by linarith)
  refine ⟨hCl, fun qb qσ qh qf qg hq X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hΘ₁ hΘ₂ X₁' X₂' Y₁' Y₂' Z₁' Z₂'
    U₁' U₂' hS₁ hS₂ => ?_⟩
  obtain ⟨-, h2, h3⟩ := hC c hc 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L C ξ₀ hJ h22 h23 lam
    hl0' hl1 qb qσ qh qf qg hq X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hΘ₁ hΘ₂ X₁' X₂' Y₁' Y₂' Z₁' Z₂' U₁' U₂' hS₁
    hS₂
  rw [← hCΦ] at h3
  have h4 := (h2.trans h3).trans (by gcongr; exact hCl)
  have hq : ((1 / 4 : ℝ) ^ (1 / 2 : ℝ)) = 1 / 2 := by
    rw [← Real.sqrt_eq_rpow, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  calc _ ≤ (ENNReal.ofReal (1 / 4) * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω)
          (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
          (fun k t ω e => U₁ k t ω e - U₂ k t ω e)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow h4 (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num), hq]

/-- The first two links of the chain before (4.27). -/
theorem eq_bwd_chain : PaperSpec.A.eq_bwd_chain.{u, v, w} := by
  refine ⟨fun T _ _ _ _ _ _ => 3 * T + 12,
    fun T L _ _ _ _ _ => (3 * T + 12) * (2 * (10 * (2 * L) ^ 2) + 2), ?_⟩
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ _
  obtain ⟨X₁', X₂', Y₁', Y₂', hXe, hYe, hD⟩ := h₁.exists_pairDiff h₂ hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone
  have 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  have hℱ0 := hF0_enlJoint D h𝒢₀
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0
  have h0m : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  -- the extensions agree with the solutions on `[0, T]`
  have hsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω)) ∂P
      = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁' k t ω - Y₂' k t ω)) ∂P := by
    refine lintegral_congr fun ω => iSup_congr fun t => iSup_congr fun ht => ?_
    simp only [congrFun (hYe _ t ht).1 ω, congrFun (hYe _ t ht).2 ω]
  have hY0 : ∫⁻ ω, esq (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P
      = ∑ k, ∫⁻ ω, (‖Y₁' k 0 ω - Y₂' k 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    unfold esq
    simp only [← congrFun (hYe _ 0 h0m).1, ← congrFun (hYe _ 0 h0m).2]
    exact lintegral_finsetSum' _ fun k _ =>
      (((hD.bwd k).memLp_initial hT.le).aestronglyMeasurable.aemeasurable.nnnorm
        |>.coe_nnreal_ennreal).pow_const 2
  have heX : ∀ i, Brownian.Ito.energy P T (fun ω s => X₁' i s ω - X₂' i s ω)
      = Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω) := fun i =>
    energy_eq_of_eqOn fun t ht => funext fun ω => by
      simp only [congrFun (hXe i t ht).1 ω, congrFun (hXe i t ht).2 ω]
  have heY : ∀ k, Brownian.Ito.energy P T (fun ω s => Y₁' k s ω - Y₂' k s ω)
      = Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω) := fun k =>
    energy_eq_of_eqOn fun t ht => funext fun ω => by
      simp only [congrFun (hYe k t ht).1 ω, congrFun (hYe k t ht).2 ω]
  set a := ∑ k, ∫⁻ ω, (‖Y₁' k 0 ω - Y₂' k 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P with ha
  set r := ∑ k, Brownian.Ito.energy P T (fun ω s => lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
    - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) + (qf₁ k ω s - qf₂ k ω s)) with hr
  set jz := ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) with hjz
  set ju := ∑ k, Poisson.Compensated.markedEnergy P ν T
    (fun ω s e => U₁ k s ω e - U₂ k s ω e) with hju
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hK₁ : ENNReal.ofReal (3 * T + 12) = 3 * ENNReal.ofReal T + 12 := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  refine ⟨?_, ?_⟩
  -- the forward-form bound
  · rw [hsup, hY0]
    refine (lintegral_biSup_esq_le hT.le
      (fun k t => ((hD.bwd k).Y_adapted t).mono ((enlJoint 𝒢₀ D h𝒢₀).le t) le_rfl)
      fun k => (hD.bwd k).Y_rightCont).trans ?_
    have hk : ∀ k, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
        (‖Y₁' k t ω - Y₂' k t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
        ≤ 3 * ∫⁻ ω, (‖Y₁' k 0 ω - Y₂' k 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P
          + 3 * (ENNReal.ofReal T * Brownian.Ito.energy P T (fun ω s =>
            lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
              + (qf₁ k ω s - qf₂ k ω s)))
          + 12 * ((∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j))
            + Poisson.Compensated.markedEnergy P ν T
              (fun ω s e => U₁ k s ω e - U₂ k s ω e)) := fun k =>
      (hD.bwd k).lintegral_biSup_sq_le 𝒲 hℱ0 hnull hT
    refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, hK₁]
    rw [← ha, ← hr, ← hjz, ← hju]
    have h1 : 3 * a ≤ (3 * ENNReal.ofReal T + 12) * a := by
      gcongr
      exact le_add_left (by norm_num)
    have h2 : 3 * (ENNReal.ofReal T * r) ≤ (3 * ENNReal.ofReal T + 12) * r := by
      rw [← mul_assoc]
      gcongr
      exact le_self_add
    have h3 : 12 * (jz + ju) ≤ (3 * ENNReal.ofReal T + 12) * (jz + ju) := by
      gcongr
      exact le_add_self
    calc 3 * a + 3 * (ENNReal.ofReal T * r) + 12 * (jz + ju)
        ≤ (3 * ENNReal.ofReal T + 12) * a + (3 * ENNReal.ofReal T + 12) * r
          + (3 * ENNReal.ofReal T + 12) * (jz + ju) := add_le_add (add_le_add h1 h2) h3
      _ = (3 * ENNReal.ofReal T + 12) * (a + r + (jz + ju)) := by ring
  -- the Lipschitz step
  · have hR := hD.rateEnergy_le hT.le (hlow.le.trans hlam) hlam1
    have hP := PairDiff.dataSize_eq_add P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i)
      (fun i ω s => qb₁ i ω s - qb₂ i ω s) (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
      (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
      (fun k ω => qg₁ k ω - qg₂ k ω)
    simp only [heX, heY] at hR
    set dS := dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
      (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
      (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω) with hdS
    set I := ∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω) with hI
    set J := ∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω) + jz + ju with hJd
    set k := ENNReal.ofReal (10 * (2 * L) ^ 2) with hk
    have hr' : r ≤ 2 * k * (I + J) + 2 * dS := by
      refine (le_add_self.trans hR).trans ?_
      gcongr
      rw [hP]
      exact le_add_self
    have hz : jz + ju ≤ J := by
      rw [hJd, add_assoc]
      exact le_add_self
    have hKe : ENNReal.ofReal ((3 * T + 12) * (2 * (10 * (2 * L) ^ 2) + 2))
        = ENNReal.ofReal (3 * T + 12) * (2 * k + 2) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by norm_num),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    have e : I + ∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω) + jz + ju
        = I + J := by
      rw [hJd]
      ring
    rw [hKe, e, mul_assoc]
    gcongr ENNReal.ofReal (3 * T + 12) * ?_
    generalize ∫⁻ ω, esq (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P = y
    clear_value I J k dS r jz ju
    have hexp : (2 * k + 2) * (y + (I + J) + dS)
        = y + (2 * k * (I + J) + 2 * dS) + J + (2 * k * y + y + I + (I + J) + 2 * k * dS) := by
      ring
    rw [hexp]
    refine le_trans ?_ le_self_add
    gcongr

end Dissertation.Acceptance.A
