/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec4ProofSteps
import MVFBSDEJ.Acceptance.Sec4BrownianPoisson
import MVFBSDEJ.Acceptance.Sec4Contraction
import MVFBSDEJ.Acceptance.Sec4Estimates
import MVFBSDEJ.WellPosedness.BrownianPoisson.EnergyAtWeighted
import MVFBSDEJ.WellPosedness.Stability.ForwardSupAt
import MVFBSDEJ.WellPosedness.Stability.WeightedYoung

/-!
# Further steps of the proofs of Lemmas 4.1–4.3: proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The weighted
inequality of Lemma 4.1 is the difference of the weighted second-moment identities at the horizons
`t` and `T` with Young's inequality
(`MVFBSDEJ.WellPosedness.BrownianPoisson.brownianPoisson_weighted_at_vec_of_measurable`). The
bound before (4.9) is the first link of (4.9) before integration in time. The backward difference
before (4.12) is the difference of the linear backward equations of the two frozen steps
(`MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.sub`). The contraction by `1/2` is (4.13)
at `λ ≤ λ_*`, where `C_Φ λ² ≤ C_Φ λ_*² = 1/4`. The chain before (4.23) at a time `t ≤ T` is the `S²`
bound on `[0, t]` of the forward coordinates of the difference system
(`MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ.lintegral_biSup_sq_le_at`), the expected
Lipschitz bound (3.2) integrated over `[0, t]`
(`MVFBSDEJ.WellPosedness.Stability.PairDiff.coeffEnergy_le_at`) and
`|δX_s|² ≤ sup_{r ≤ s} |δX_r|²`. The display inserting (4.25) in (4.24) and the backward bound at
every time are `MVFBSDEJ.WellPosedness.Stability.PairDiff.weighted_window_le` and
`MVFBSDEJ.WellPosedness.Stability.PairDiff.window_le`; the terminal bound is (2.6) with (2.9) at
the square-integrable terminal values. The first two links of the chain before (4.27) are the `S²`
bound of the backward coordinates of the difference system
(`MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.lintegral_biSup_sq_le`) and the rate bound
(3.2) at the pair (`MVFBSDEJ.WellPosedness.Stability.PairDiff.rateEnergy_le`).

## Main statements

* `MVFBSDEJ.Acceptance.eq_supE_weighted` — the weighted inequality.
* `MVFBSDEJ.Acceptance.eq_coeffdiff_ae` — the bound before (4.9).
* `MVFBSDEJ.Acceptance.eq_bwddiff_identity` — the backward difference before (4.12).
* `MVFBSDEJ.Acceptance.eq_contract_half` — `λ_*` and the contraction by `1/2`.
* `MVFBSDEJ.Acceptance.eq_fwd_chain` — the chain before (4.23), with
  `K₁ = 2(3T + 12) + 3`, `K₂ = K₁ (10 (2L)² + 1)` and `K₃ = 2 K₂`.
* `MVFBSDEJ.Acceptance.eq_wgt_insert` — (4.25) inserted in (4.24), with
  `C = 2 · 10 (2L)² + 3`, and the backward bound at every time, with
  `C' = e^{κT} max(1, C/ε) / (1 − ε)`.
* `MVFBSDEJ.Acceptance.eq_wgt_terminal` — the terminal bound before (4.26), with
  `C = 4L²`.
* `MVFBSDEJ.Acceptance.eq_bwd_chain` — the first two links before (4.27), with
  `K₁ = 3T + 12` and `K₂ = (3T + 12)(2 · 10 (2L)² + 2)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.WellPosedness.BrownianPoisson
  MVFBSDEJ.PaperSpec MVFBSDEJ.Law LevyStochCalc

universe u v w

/-- The weighted inequality in the proof of Lemma 4.1. -/
theorem eq_supE_weighted : PaperSpec.eq_supE_weighted.{u, v, w} := by
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
theorem eq_coeffdiff_ae : PaperSpec.eq_coeffdiff_ae.{u, v, w} := by
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
theorem eq_bwddiff_identity : PaperSpec.eq_bwddiff_identity.{u, v, w} := by
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
theorem eq_contract_half : PaperSpec.eq_contract_half.{u, v, w} := by
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
  have h4 := (h2.trans h3).trans
    (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hCl) zero_le)
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

/-- The chain before (4.23), at every time. -/
theorem eq_fwd_chain : PaperSpec.eq_fwd_chain.{u, v, w} := by
  refine ⟨fun T _ _ _ _ _ _ => 2 * (3 * T + 12) + 3,
    fun T L _ _ _ _ _ => (2 * (3 * T + 12) + 3) * (10 * (2 * L) ^ 2 + 1),
    fun T L _ _ _ _ _ => 2 * ((2 * (3 * T + 12) + 3) * (10 * (2 * L) ^ 2 + 1)), ?_⟩
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, hXl₁, hYl₁⟩ ⟨⟨γ₂, h₂⟩, hXl₂, hYl₂⟩ hS
  obtain ⟨X₁', X₂', Y₁', Y₂', hXe, hYe, hD⟩ := h₁.exists_pairDiff h₂ hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone
  have 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  have hℱ0 := hF0_enlJoint D h𝒢₀
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0
  have hlam0 : lam ≠ 0 := (hlow.trans_le hlam).ne'
  have hl : lam ^ 2 ≤ 1 := by nlinarith
  have hbm := hD.measurable_b hlam0
  have hσm := hD.measurable_σ hlam0
  have hhm := hD.measurable_h hlam0
  -- the jump coefficient at the predictable tuples
  have hj := h₁.ae_forcedJump_sub_leftLim_eq h₂ hT.le (jointBorel_iff.mp hJ).1.toCoeffBorel
    hXl₁ hYl₁ hXl₂ hYl₂
  have hjump : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      Poisson.Compensated.markedEnergy P ν t (fun ω s e =>
        jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i s ω e
          - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e)
      = Poisson.Compensated.markedEnergy P ν t
          (fun ω s e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e) := fun t ht i =>
    markedEnergy_congr_ae_of_le ht.2 (by
      filter_upwards [hj] with q hq
      exact mul_left_cancel₀ hlam0 (add_right_cancel (hq i)))
  -- the extensions agree with the solutions on `[0, T]`
  have eX : ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, X₁' i s ω - X₂' i s ω = X₁ i s ω - X₂ i s ω :=
    fun i s hs ω => by rw [congrFun (hXe i s hs).1 ω, congrFun (hXe i s hs).2 ω]
  have eY : ∀ k, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, Y₁' k s ω - Y₂' k s ω = Y₁ k s ω - Y₂ k s ω :=
    fun k s hs ω => by rw [congrFun (hYe k s hs).1 ω, congrFun (hYe k s hs).2 ω]
  have hsupX : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) t, esq (fun i => X₁ i s ω - X₂ i s ω)) ∂P
        = ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) t, esq (fun i => X₁' i s ω - X₂' i s ω)) ∂P :=
    fun t ht => lintegral_congr fun ω => iSup_congr fun s => iSup_congr fun hs => by
      simp only [eX _ s (Set.Icc_subset_Icc le_rfl ht.2 hs) ω]
  have heX : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      Brownian.Ito.energy P t (fun ω s => X₁' i s ω - X₂' i s ω)
        = Brownian.Ito.energy P t (fun ω s => X₁ i s ω - X₂ i s ω) := fun t ht i =>
    energy_eq_of_eqOn fun s hs => funext fun ω => eX i s (Set.Icc_subset_Icc le_rfl ht.2 hs) ω
  have heY : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k,
      Brownian.Ito.energy P t (fun ω s => Y₁' k s ω - Y₂' k s ω)
        = Brownian.Ito.energy P t (fun ω s => Y₁ k s ω - Y₂ k s ω) := fun t ht k =>
    energy_eq_of_eqOn fun s hs => funext fun ω => eY k s (Set.Icc_subset_Icc le_rfl ht.2 hs) ω
  -- the data size
  have hP := PairDiff.dataSize_eq_add P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i)
    (fun i ω s => qb₁ i ω s - qb₂ i ω s) (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
    (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
    (fun k ω => qg₁ k ω - qg₂ k ω)
  set dS := dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
    (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
    (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω) with hdS
  set a := ∫⁻ ω, esq (fun i => ξ₁ ω i - ξ₂ ω i) ∂P with ha
  have ha_le : a ≤ dS := by
    rw [hP]
    exact le_self_add.trans le_self_add
  have hQ_le : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∑ i, Brownian.Ito.energy P t (fun ω s => qb₁ i ω s - qb₂ i ω s)
        + ∑ i, ∑ j, Brownian.Ito.energy P t (fun ω s => qσ₁ i s ω j - qσ₂ i s ω j)
        + ∑ i, Poisson.Compensated.markedEnergy P ν t
          (fun ω s e => qh₁ i s ω e - qh₂ i s ω e) ≤ dS := fun t ht => by
    have hmono : ∀ H : Ω → ℝ → ℝ, Brownian.Ito.energy P t H ≤ Brownian.Ito.energy P T H :=
      fun H => lintegral_mono fun _ => lintegral_mono_set (Set.Icc_subset_Icc le_rfl ht.2)
    have hmono' : ∀ H : Ω → ℝ → E → ℝ, Poisson.Compensated.markedEnergy P ν t H
        ≤ Poisson.Compensated.markedEnergy P ν T H :=
      fun H => lintegral_mono fun _ => lintegral_mono_set (Set.Icc_subset_Icc le_rfl ht.2)
    rw [hP]
    refine le_trans ?_ (le_self_add.trans le_add_self)
    gcongr with i _ i _ j _ i _
    · exact hmono _
    · exact hmono _
    · exact hmono' _
  -- the supremum at `T` is finite
  have hfin : ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁ i s ω - X₂ i s ω)) ∂P < ⊤ := by
    refine lt_of_le_of_lt ?_ hS
    unfold supSize
    exact le_self_add.trans (le_self_add.trans le_self_add)
  have hsup_mono : MonotoneOn (fun t => ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) t,
      esq (fun i => X₁ i s ω - X₂ i s ω)) ∂P) (Set.Icc (0 : ℝ) T) :=
    fun t₁ _ t₂ _ h12 => lintegral_mono fun ω =>
      biSup_mono fun s hs => ⟨hs.1, hs.2.trans h12⟩
  refine ⟨fun t ht => ⟨?_, ?_, ?_⟩, hsup_mono, fun t ht =>
    (hsup_mono ht ⟨hT.le, le_rfl⟩ ht.2).trans_lt hfin⟩
  -- the BDG link
  · rw [hsupX t ht]
    have hS1 := lintegral_biSup_esq_le (P := P) ht.1
      (fun i s => ((hD.fwd i).X_adapted s).mono ((enlJoint 𝒢₀ D h𝒢₀).le s) le_rfl)
      fun i => (hD.fwd i).X_rightCont
    have hSi := fun i => (hD.fwd i).lintegral_biSup_sq_le_at 𝒲 hℱ0 hnull ht
    have hR := hD.realisedEnergy_le_at hbm hσm hhm hl t
    have hesq : ∑ i, ∫⁻ ω, (‖ξ₁ ω i - ξ₂ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P = a := by
      rw [ha]
      unfold esq
      exact (lintegral_finsetSum' _ fun i _ =>
        ((hD.fwd i).ξ₀_sq.aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const
          2).symm
    refine hS1.trans ((Finset.sum_le_sum fun i _ => hSi i).trans ?_)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hesq]
    simp only [hjump t ht]
    set Rb := ∑ i, Brownian.Ito.energy P t (fun ω s => lam * (driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
      - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s) + (qb₁ i ω s - qb₂ i ω s)) with hRb
    set Rσ := ∑ i, ∑ j, Brownian.Ito.energy P t (fun ω s => lam
      * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
        + (qσ₁ i s ω j - qσ₂ i s ω j)) with hRσ
    set Rh := ∑ i, Poisson.Compensated.markedEnergy P ν t (fun ω s e => lam
      * (jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e) + (qh₁ i s ω e - qh₂ i s ω e)) with hRh
    set B := ∑ i, Brownian.Ito.energy P t (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
        - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
      + ∑ i, ∑ j, Brownian.Ito.energy P t (fun ω s => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
      + ∑ i, Poisson.Compensated.markedEnergy P ν t
        (fun ω s e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e) with hB
    set Q := ∑ i, Brownian.Ito.energy P t (fun ω s => qb₁ i ω s - qb₂ i ω s)
      + ∑ i, ∑ j, Brownian.Ito.energy P t (fun ω s => qσ₁ i s ω j - qσ₂ i s ω j)
      + ∑ i, Poisson.Compensated.markedEnergy P ν t
        (fun ω s e => qh₁ i s ω e - qh₂ i s ω e) with hQ
    have hR' : Rb + Rσ + Rh ≤ 2 * B + 2 * dS :=
      hR.trans (by gcongr; exact hQ_le t ht)
    have htT : ENNReal.ofReal t ≤ ENNReal.ofReal T := ENNReal.ofReal_le_ofReal ht.2
    have hK₁ : ENNReal.ofReal (2 * (3 * T + 12) + 3) = 2 * (3 * ENNReal.ofReal T + 12) + 3 := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_mul (by norm_num)]
      simp only [ENNReal.ofReal_ofNat]
    rw [hK₁]
    clear_value Rb Rσ Rh B Q dS a
    calc 3 * a + 3 * (ENNReal.ofReal t * Rb) + 12 * (Rσ + Rh)
        ≤ 3 * a + 3 * (ENNReal.ofReal T * Rb) + 12 * (Rσ + Rh) := by gcongr
      _ ≤ 3 * a + (3 * ENNReal.ofReal T + 12) * (Rb + Rσ + Rh) := by
          have e : 3 * a + (3 * ENNReal.ofReal T + 12) * (Rb + Rσ + Rh)
              = 3 * a + 3 * (ENNReal.ofReal T * Rb) + 12 * (Rσ + Rh)
                + (3 * ENNReal.ofReal T * (Rσ + Rh) + 12 * Rb) := by ring
          rw [e]
          exact le_self_add
      _ ≤ 3 * a + (3 * ENNReal.ofReal T + 12) * (2 * B + 2 * dS) := by gcongr
      _ ≤ (2 * (3 * ENNReal.ofReal T + 12) + 3) * (a + B + dS) := by
          have e : (2 * (3 * ENNReal.ofReal T + 12) + 3) * (a + B + dS)
              = 3 * a + (3 * ENNReal.ofReal T + 12) * (2 * B + 2 * dS)
                + (2 * (3 * ENNReal.ofReal T + 12) * a + 3 * B + 3 * dS) := by ring
          rw [e]
          exact le_self_add
  -- the Lipschitz link
  · have hc := hD.coeffEnergy_le_at hbm hσm hhm hT.le ht
    simp only [heX t ht, heY t ht] at hc
    simp only [hjump t ht]
    set B := ∑ i, Brownian.Ito.energy P t (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
        - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
      + ∑ i, ∑ j, Brownian.Ito.energy P t (fun ω s => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
      + ∑ i, Poisson.Compensated.markedEnergy P ν t
        (fun ω s e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e) with hB
    set x := ∑ i, Brownian.Ito.energy P t (fun ω s => X₁ i s ω - X₂ i s ω) with hx
    set y := ∑ k, Brownian.Ito.energy P t (fun ω s => Y₁ k s ω - Y₂ k s ω) with hy
    set z := ∑ k, ∑ j, Brownian.Ito.energy P t (fun ω s => Z₁ k s ω j - Z₂ k s ω j) with hz
    set u := ∑ k, Poisson.Compensated.markedEnergy P ν t
      (fun ω s e => U₁ k s ω e - U₂ k s ω e) with hu
    set k := ENNReal.ofReal (10 * (2 * L) ^ 2) with hk
    set K₁ := ENNReal.ofReal (2 * (3 * T + 12) + 3) with hK₁
    have hK₂ : ENNReal.ofReal ((2 * (3 * T + 12) + 3) * (10 * (2 * L) ^ 2 + 1))
        = K₁ * (k + 1) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one,
        ENNReal.ofReal_one]
    rw [hK₂, mul_assoc]
    clear_value B x y z u k K₁ dS a
    gcongr K₁ * ?_
    have e : (k + 1) * (a + (x + y + z + u) + dS)
        = a + k * (x + (y + z + u)) + dS + (k * a + (x + y + z + u) + k * dS) := by ring
    rw [e]
    exact le_trans (by gcongr) le_self_add
  -- the integrated supremum
  · have hmono : ∀ H : Ω → ℝ → ℝ, Brownian.Ito.energy P t H ≤ Brownian.Ito.energy P T H :=
      fun H => lintegral_mono fun _ => lintegral_mono_set (Set.Icc_subset_Icc le_rfl ht.2)
    have hmono' : ∀ H : Ω → ℝ → E → ℝ, Poisson.Compensated.markedEnergy P ν t H
        ≤ Poisson.Compensated.markedEnergy P ν T H :=
      fun H => lintegral_mono fun _ => lintegral_mono_set (Set.Icc_subset_Icc le_rfl ht.2)
    have hI := hD.energy_le_lintegral_biSup hT.le t
    simp only [heX t ht] at hI
    have eI : ∫⁻ s in Set.Icc (0 : ℝ) t,
          ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) s, esq (fun i => X₁' i r ω - X₂' i r ω)) ∂P
        = ∫⁻ s in Set.Icc (0 : ℝ) t,
          ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) s, esq (fun i => X₁ i r ω - X₂ i r ω)) ∂P :=
      setLIntegral_congr_fun measurableSet_Icc fun s hs => lintegral_congr fun ω =>
        iSup_congr fun r => iSup_congr fun hr => by
          simp only [eX _ r ⟨hr.1, hr.2.trans (hs.2.trans ht.2)⟩ ω]
    rw [eI] at hI
    have hy : ∑ k, Brownian.Ito.energy P t (fun ω s => Y₁ k s ω - Y₂ k s ω)
        ≤ ∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω) :=
      Finset.sum_le_sum fun k _ => hmono _
    have hz : ∑ k, ∑ j, Brownian.Ito.energy P t (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
        ≤ ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) :=
      Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ => hmono _
    have hu : ∑ k, Poisson.Compensated.markedEnergy P ν t
          (fun ω s e => U₁ k s ω e - U₂ k s ω e)
        ≤ ∑ k, Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => U₁ k s ω e - U₂ k s ω e) :=
      Finset.sum_le_sum fun k _ => hmono' _
    set K₂ := ENNReal.ofReal ((2 * (3 * T + 12) + 3) * (10 * (2 * L) ^ 2 + 1)) with hK₂
    have hK₃ : ENNReal.ofReal (2 * ((2 * (3 * T + 12) + 3) * (10 * (2 * L) ^ 2 + 1)))
        = 2 * K₂ := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    rw [hK₃, mul_comm 2 K₂, mul_assoc]
    gcongr K₂ * ?_
    have key : ∀ {a x y z u dS I y' z' u' : ℝ≥0∞}, a ≤ dS → x ≤ I → y ≤ y' → z ≤ z' →
        u ≤ u' → a + (x + y + z + u) + dS ≤ 2 * (I + (y' + z' + u') + dS) := by
      intro a x y z u dS I y' z' u' ha hx hy hz hu
      calc a + (x + y + z + u) + dS ≤ dS + (I + (y' + z' + u')) + dS := by
            have e : x + y + z + u = x + (y + z + u) := by ring
            rw [e]
            gcongr
        _ ≤ dS + (I + (y' + z' + u')) + dS + (I + (y' + z' + u')) := le_self_add
        _ = 2 * (I + (y' + z' + u') + dS) := by ring
    exact key ha_le hI hy hz hu

/-- (4.25) inserted in (4.24), and the backward bound at every time. -/
theorem eq_wgt_insert : PaperSpec.eq_wgt_insert.{u, v, w} := by
  refine ⟨fun _ L _ _ _ _ _ => 2 * (10 * (2 * L) ^ 2) + 3,
    fun ε κ T L _ _ _ _ _ =>
      Real.exp (κ * T) * max 1 ((2 * (10 * (2 * L) ^ 2) + 3) / ε) / (1 - ε), ?_⟩
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ hq₁ hq₂
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ _
  obtain ⟨X₁', X₂', Y₁', Y₂', hXe, hYe, hD⟩ := h₁.exists_pairDiff h₂ hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone
  have 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  have hK : (0 : ℝ) ≤ 10 * (2 * L) ^ 2 := by positivity
  have hlam0 : 0 ≤ lam := hlow.le.trans hlam
  have hqf : ∀ k, Brownian.Ito.energy P T (fun ω s => qf₁ k ω s - qf₂ k ω s) ≠ ⊤ := fun k =>
    (hq₁.toForcing.sub hq₂.toForcing).qf_sq k
  have eX : ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, X₁' i s ω - X₂' i s ω = X₁ i s ω - X₂ i s ω :=
    fun i s hs ω => by rw [congrFun (hXe i s hs).1 ω, congrFun (hXe i s hs).2 ω]
  have eY : ∀ k, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, Y₁' k s ω - Y₂' k s ω = Y₁ k s ω - Y₂ k s ω :=
    fun k s hs ω => by rw [congrFun (hYe k s hs).1 ω, congrFun (hYe k s hs).2 ω]
  have hae : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc t T))),
      q.2 ∈ Set.Icc (0 : ℝ) T := fun t ht =>
    (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)).mono
      fun q hq => ⟨ht.1.trans hq.1, hq.2⟩
  have eYt : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ ω, ∑ k, (Y₁' k t ω - Y₂' k t ω) ^ 2 ∂P
      = ∫ ω, ∑ k, (Y₁ k t ω - Y₂ k t ω) ^ 2 ∂P := fun t ht =>
    integral_congr_ae (Eventually.of_forall fun ω => by simp only [eY _ t ht ω])
  -- the forward differences on the window
  have eXw : ∀ t ∈ Set.Icc (0 : ℝ) T,
      (fun q : Ω × ℝ => ∑ i, (X₁' i q.2 q.1 - X₂' i q.2 q.1) ^ 2
        + ∑ k, (qf₁ k q.1 q.2 - qf₂ k q.1 q.2) ^ 2)
      =ᵐ[P.prod (volume.restrict (Set.Icc t T))]
      fun q : Ω × ℝ => ∑ i, (X₁ i q.2 q.1 - X₂ i q.2 q.1) ^ 2
        + ∑ k, (qf₁ k q.1 q.2 - qf₂ k q.1 q.2) ^ 2 := fun t ht => by
    filter_upwards [hae t ht] with q hq
    simp only [eX _ q.2 hq q.1]
  refine ⟨fun ε hε hε1 κ hκ t ht => ?_, fun ε hε hε1 κ hκ t ht => ?_⟩
  -- the inserted display
  · obtain ⟨i1, i2, i3, i4, hle⟩ := hD.weighted_window_le 𝒲 hT hK hlam0 hlam1 hqf hε hε1 κ ht
    set c := (2 * (10 * (2 * L) ^ 2) + 3) / ε with hc
    have eD : (fun q : Ω × ℝ => Real.exp (κ * q.2)
        * ((κ - c) * ∑ k, (Y₁' k q.2 q.1 - Y₂' k q.2 q.1) ^ 2
          + (1 - ε) * ∑ k, (∑ j, (Z₁ k q.2 q.1 j - Z₂ k q.2 q.1 j) ^ 2
            + ∫ e, (U₁ k q.2 q.1 e - U₂ k q.2 q.1 e) ^ 2 ∂ν)))
        =ᵐ[P.prod (volume.restrict (Set.Icc t T))]
        fun q : Ω × ℝ => Real.exp (κ * q.2)
          * ((κ - c) * ∑ k, (Y₁ k q.2 q.1 - Y₂ k q.2 q.1) ^ 2
            + (1 - ε) * (∑ k, ∑ j, (Z₁ k q.2 q.1 j - Z₂ k q.2 q.1 j) ^ 2
              + ∑ k, ∫ e, (U₁ k q.2 q.1 e - U₂ k q.2 q.1 e) ^ 2 ∂ν)) := by
      filter_upwards [hae t ht] with q hq
      simp only [eY _ q.2 hq q.1, Finset.sum_add_distrib]
    have eXq : (fun q : Ω × ℝ => Real.exp (κ * q.2)
        * (∑ i, (X₁' i q.2 q.1 - X₂' i q.2 q.1) ^ 2 + ∑ k, (qf₁ k q.1 q.2 - qf₂ k q.1 q.2) ^ 2))
        =ᵐ[P.prod (volume.restrict (Set.Icc t T))]
        fun q : Ω × ℝ => Real.exp (κ * q.2)
          * (∑ i, (X₁ i q.2 q.1 - X₂ i q.2 q.1) ^ 2
            + ∑ k, (qf₁ k q.1 q.2 - qf₂ k q.1 q.2) ^ 2) := by
      filter_upwards [eXw t ht] with q hq
      rw [hq]
    have i3' := i3.congr eD
    have i4' := i4.congr eXq
    refine ⟨?_, i2, i3', i4', ?_⟩
    · exact i1.congr (Eventually.of_forall fun ω => by simp only [eY _ t ht ω])
    rw [eYt t ht, integral_congr_ae eD, integral_congr_ae eXq] at hle
    calc _ = Real.exp (κ * t) * ∫ ω, ∑ k, (Y₁ k t ω - Y₂ k t ω) ^ 2 ∂P
          + ∫ q, Real.exp (κ * q.2)
            * ((κ - c) * ∑ k, (Y₁ k q.2 q.1 - Y₂ k q.2 q.1) ^ 2
              + (1 - ε) * (∑ k, ∑ j, (Z₁ k q.2 q.1 j - Z₂ k q.2 q.1 j) ^ 2
                + ∑ k, ∫ e, (U₁ k q.2 q.1 e - U₂ k q.2 q.1 e) ^ 2 ∂ν))
            ∂(P.prod (volume.restrict (Set.Icc t T))) := by
          rw [integral_prod _ i3']
      _ ≤ _ := hle
      _ = _ := by rw [integral_prod _ i4']
  -- the backward bound at every time
  · obtain ⟨j1, j2, hle⟩ := hD.window_le 𝒲 hT hK hlam0 hlam1 hqf hε hε1 hκ ht
    have eZ : (fun q : Ω × ℝ => ∑ k, (∑ j, (Z₁ k q.2 q.1 j - Z₂ k q.2 q.1 j) ^ 2
          + ∫ e, (U₁ k q.2 q.1 e - U₂ k q.2 q.1 e) ^ 2 ∂ν))
        = fun q : Ω × ℝ => ∑ k, ∑ j, (Z₁ k q.2 q.1 j - Z₂ k q.2 q.1 j) ^ 2
          + ∑ k, ∫ e, (U₁ k q.2 q.1 e - U₂ k q.2 q.1 e) ^ 2 ∂ν := by
      funext q
      rw [Finset.sum_add_distrib]
    rw [eZ] at j1 hle
    have j2' := j2.congr (eXw t ht)
    refine ⟨j1, j2', ?_⟩
    rw [eYt t ht, integral_congr_ae (eXw t ht)] at hle
    calc _ = ∫ ω, ∑ k, (Y₁ k t ω - Y₂ k t ω) ^ 2 ∂P
          + ∫ q, (∑ k, ∑ j, (Z₁ k q.2 q.1 j - Z₂ k q.2 q.1 j) ^ 2
            + ∑ k, ∫ e, (U₁ k q.2 q.1 e - U₂ k q.2 q.1 e) ^ 2 ∂ν)
            ∂(P.prod (volume.restrict (Set.Icc t T))) := by
          rw [integral_prod _ j1]
      _ ≤ _ := hle
      _ = _ := by rw [integral_prod _ j2']

/-- The terminal bound before (4.26), with `C = 4L²`. -/
theorem eq_wgt_terminal : PaperSpec.eq_wgt_terminal.{u, v, w} := by
  refine ⟨fun _ L _ _ _ _ _ => 4 * L ^ 2, ?_⟩
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam _ _ _ _ ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ _
  have hT' : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  exact (lipTerminal_iff_terminalLipschitz.mp h23.terminal).lipT_pair
    (fun i => h₁.X_adapted i T hT') (fun i => h₂.X_adapted i T hT') h₁.XT_sq h₂.XT_sq

/-- The first two links of the chain before (4.27). -/
theorem eq_bwd_chain : PaperSpec.eq_bwd_chain.{u, v, w} := by
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
      rw [ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hk, ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat]
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

end MVFBSDEJ.Acceptance
