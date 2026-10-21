/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4LocalMartingales
import Dissertation.WellPosedness.BrownianPoisson.LocalMartingales
import Dissertation.WellPosedness.Martingale.DavisCompensated
import Dissertation.Acceptance.A.Sec4

/-!
# The local martingales `M^W` and `M¹` of the proof of Lemma 4.1: proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The weight
`w_s = e^s δY_{s−} 1_{(0, T]}(s)` is predictable, bounded by `e^T R` before `δY` leaves the ball of
radius `R`, and satisfies `|w_s|² ≤ e^{2T} sup_{t ≤ T} |δY_t|²`; with `𝔼 sup_{t ≤ T} |δY_t|² < ∞`
from Lemma 4.1, `Dissertation.WellPosedness.Martingale.localBrownian_weight` and
`Dissertation.WellPosedness.Martingale.localCompensated_weight` give the local integrals, their
bounds with `c₀ = 9`, and the zero means. The integrand of `M¹` is marked predictable and vanishes
at the nonpositive times, so the Burkholder–Davis–Gundy inequality in quadratic-variation form for
local compensated integrals
(`Dissertation.WellPosedness.Martingale.IsLocalCompensatedIntegral.lintegral_biSup_le_count`,
constant `24`) and the Cauchy–Schwarz inequality in `ℝᵐ` give the first link of its chain.

## Main statements

* `Dissertation.Acceptance.A.lem41_MW` — `M^W`.
* `Dissertation.Acceptance.A.lem41_M1` — `M¹`.
* `Dissertation.Acceptance.A.lem41_M1_bdg` — the first link of the chain for `M¹`, with
  `c₀ = 24`.
* `Dissertation.Acceptance.A.lem41_M1_chain` — the links of the chain for `M¹` after its first.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Martingale Dissertation.WellPosedness.Spec
  Dissertation.WellPosedness.BrownianPoisson LevyStochCalc

universe u v w

/-- **`M^W` in the proof of Lemma 4.1**, with `c₀ = 9`. -/
theorem lem41_MW : PaperSpec.A.lem41_MW.{u, v, w} := by
  refine ⟨9, by norm_num, fun c hc => ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ hind₀ hm hd T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs
    hξm hξ hφm hφs hYa hYr hYl heq
  obtain ⟨CBP, hCBP⟩ := lem_bpbsde.{u, v, w}
  have hS := (hCBP 𝒢₀ ν m d P D h𝒢₀ hind₀ hm hd T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs hξm
    hξ hφm hφs hYa hYr hYl heq).1
  obtain ⟨hwm, hwp, hwb, hwsq⟩ := expLeftLimWeight_props (ℱ := enlJoint 𝒢₀ D h𝒢₀) hT.le
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) hYa hYl
  have key := localBrownian_weight D.W (enlJoint 𝒢₀ D h𝒢₀)
    (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) hT hYa
    (fun i ω t ht => hYr i ω t ht) hS hwm hwp hwb (Real.exp_pos T).le hwsq
    (Z := δZ) (fun k j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
    (fun k j => progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k) j)
    (fun k j => BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k) j)
    (fun k ω s hs => Or.inr (hZv k ω s hs))
  rw [expLeftLim_integrand_eq hZv] at key
  have hfin : ENNReal.ofReal (c * Real.exp T)
      * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, esq (fun k => δY k t ω) ∂P) ^ (1 / 2 : ℝ)
      * (∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => δZ k s ω j)) ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hS.ne))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ENNReal.sum_lt_top.2 fun k _ => ENNReal.sum_lt_top.2 fun j _ => (hZs k j).lt_top).ne)
  refine ⟨key.1, fun MW hMW => ⟨?_, hfin, (key.2 MW hMW).2⟩⟩
  have hc9 : 9 * ENNReal.ofReal (Real.exp T) ≤ ENNReal.ofReal (c * Real.exp T) := by
    rw [show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc (Real.exp_pos T).le)
  calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖MW t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 9 * ENNReal.ofReal (Real.exp T)
          * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖δY i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)
          * (∑ k, ∑ j, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖δZ k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            ^ (1 / 2 : ℝ) := (key.2 MW hMW).1
    _ ≤ _ := mul_le_mul' (mul_le_mul' hc9 le_rfl) le_rfl

/-- **`M¹` in the proof of Lemma 4.1**, with `c₀ = 9`. -/
theorem lem41_M1 : PaperSpec.A.lem41_M1.{u, v, w} := by
  refine ⟨9, by norm_num, fun c hc => ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ hind₀ hm hd T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs
    hξm hξ hφm hφs hYa hYr hYl heq
  obtain ⟨CBP, hCBP⟩ := lem_bpbsde.{u, v, w}
  have hS := (hCBP 𝒢₀ ν m d P D h𝒢₀ hind₀ hm hd T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs hξm
    hξ hφm hφs hYa hYr hYl heq).1
  obtain ⟨hwm, hwp, hwb, hwsq⟩ := expLeftLimWeight_props (ℱ := enlJoint 𝒢₀ D h𝒢₀) hT.le
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) hYa hYl
  have key := localCompensated_weight D.N (enlJoint 𝒢₀ D h𝒢₀)
    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) hT hYa
    (fun i ω t ht => hYr i ω t ht) hS hwm hwp hwb (Real.exp_pos T).le hwsq
    (U := δU) (fun k => (hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
    (fun k => (hU k).markedProgressivelyMeasurable)
    (fun k => BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k))
    (fun k ω s hs => Or.inr fun e => hUv k ω s e hs)
  rw [expLeftLim_markedIntegrand_eq hUv] at key
  have hfin : ENNReal.ofReal (c * Real.exp T)
      * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, esq (fun k => δY k t ω) ∂P) ^ (1 / 2 : ℝ)
      * (∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e))
        ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hS.ne))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ENNReal.sum_lt_top.2 fun k _ => (hUs k).lt_top).ne)
  refine ⟨key.1, fun M1 hM1 => ⟨?_, hfin, (key.2 M1 hM1).2⟩⟩
  have hc9 : 9 * ENNReal.ofReal (Real.exp T) ≤ ENNReal.ofReal (c * Real.exp T) := by
    rw [show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc (Real.exp_pos T).le)
  calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M1 t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 9 * ENNReal.ofReal (Real.exp T)
          * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖δY i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)
          * (∑ k, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖δU k s ω e‖₊ : ℝ≥0∞) ^ 2
              ∂ν ∂volume ∂P) ^ (1 / 2 : ℝ) := (key.2 M1 hM1).1
    _ ≤ _ := mul_le_mul' (mul_le_mul' hc9 le_rfl) le_rfl

/-- **The first link of the chain for `M¹`**, with `c₀ = 24`: the Burkholder–Davis–Gundy
inequality in quadratic-variation form and the Cauchy–Schwarz inequality in `ℝᵐ`. -/
theorem lem41_M1_bdg : PaperSpec.A.lem41_M1_bdg.{u, v, w} := by
  refine ⟨24, by norm_num, fun c hc => ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ hind₀ hm hd T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs
    hξm hξ hφm hφs hYa hYr hYl heq M1 hM1
  set ℱ := enlJoint 𝒢₀ D h𝒢₀ with hℱdef
  set H : Ω → ℝ → E → ℝ := fun ω s e => Real.exp s
    * ∑ k, (if 0 < s then leftLimProc δY k s ω else 0) * δU k s ω e with hHdef
  -- the integrand is marked predictable
  have hY : ∀ k, Probability.Predictable ℱ fun ω s =>
      if s ∈ Ioc (0 : ℝ) T then leftLimProc δY k s ω else 0 := fun k =>
    predictable_leftLim_Ioc (hYa k) (hYl k)
  have hF : Measurable fun p : ℝ × ℝ × ℝ => Real.exp p.1 * p.2.1 * p.2.2 :=
    (Real.measurable_exp.comp measurable_fst).mul measurable_snd.fst |>.mul measurable_snd.snd
  have hterm : ∀ k, Probability.MarkedPredictable ℱ ν fun ω s e =>
      if 0 < s then Real.exp s * (if s ∈ Ioc (0 : ℝ) T then leftLimProc δY k s ω else 0)
        * δU k s ω e else 0 := fun k =>
    (hU k).comp_measurable hF (hY k).measurable
  have hHeq : (fun ω s e => ∑ k, (if 0 < s then Real.exp s
      * (if s ∈ Ioc (0 : ℝ) T then leftLimProc δY k s ω else 0) * δU k s ω e else 0)) = H := by
    rw [hHdef, ← expLeftLim_markedIntegrand_eq hUv]
    funext ω s e
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hs : 0 < s
    · simp only [if_pos hs, expLeftLimWeight]
    · simp [hs, expLeftLimWeight, show s ∉ Ioc (0 : ℝ) T from fun h => hs h.1]
  have hpred : Probability.MarkedPredictable ℱ ν H := by
    rw [← hHeq]
    exact Finset.measurable_sum Finset.univ fun k _ => hterm k
  have h0 : ∀ ω s e, s ≤ 0 → H ω s e = 0 := fun ω s e hs => by
    simp [hHdef, not_lt.mpr hs]
  have key := IsLocalCompensatedIntegral.lintegral_biSup_le_count D.N ℱ
    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT hpred h0 hM1
  refine key.trans ?_
  have hc24 : (24 : ℝ≥0∞) ≤ ENNReal.ofReal c := by
    rw [show (24 : ℝ≥0∞) = ENNReal.ofReal 24 by norm_num]
    exact ENNReal.ofReal_le_ofReal hc
  gcongr with ω x
  -- the Cauchy–Schwarz inequality in `ℝᵐ`
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [hHdef]
  rw [mul_pow, show Real.exp (2 * x.1) = Real.exp x.1 ^ 2 by
    rw [sq, ← Real.exp_add, two_mul], mul_assoc]
  gcongr
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- **The links of the chain for `M¹` after its first**: Cauchy–Schwarz, the compensation formula
(2.1) and the `L²(ν)` norm. -/
theorem lem41_M1_chain : PaperSpec.A.lem41_M1_chain.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ hind₀ hm hd T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs
    hξm hξ hφm hφs hYa hYr hYl heq
  have hN := isPoissonFiltration_enlJoint D h𝒢₀ hind₀
  obtain ⟨hJm, h3⟩ := poisson_sumSq_compensation (N := D.N) hN T hU
  have hUm : ∀ k, Measurable fun p : Ω × ℝ × E => δU k p.2.1 p.1 p.2.2 := fun k =>
    (hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl
  have hUω : ∀ ω, Measurable fun p : ℝ × E => ENNReal.ofReal (∑ k, δU k p.1 ω p.2 ^ 2) :=
    fun ω => ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun k _ =>
      ((hUm k).comp (measurable_const.prodMk measurable_id)).pow_const 2)
  have hSm : Measurable fun ω => ⨆ t ∈ Icc (0 : ℝ) T, ∑ k, (‖δY k t ω‖₊ : ℝ≥0∞) ^ 2 := by
    refine Dissertation.WellPosedness.Martingale.measurable_biSup_Icc_ennreal hT.le (fun t ht =>
      Finset.measurable_sum _ fun k _ =>
        ((hYa k t ht).mono ((enlJoint 𝒢₀ D h𝒢₀).le t) le_rfl).nnnorm.coe_nnreal_ennreal.pow_const
          2) fun ω t ht => ?_
    refine tendsto_finsetSum _ fun k _ => ?_
    exact ((ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp
      continuous_nnnorm)).continuousAt.tendsto.comp (hYr k ω t ht)
  refine ⟨?_, h3, lintegral_Ioc_sumSq_eq_markedEnergy hUm⟩
  exact (lintegral_mono fun ω => sqrt_setLIntegral_leftLim_le ω (fun k t ht => hYl k ω t ht)
    (D.N.N ω) (hUω ω)).trans (lintegral_mul_sqrt_le hSm.aemeasurable hJm _)

end Dissertation.Acceptance.A
