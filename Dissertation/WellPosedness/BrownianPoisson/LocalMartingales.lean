/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Martingale.LocalWeight
import Dissertation.WellPosedness.System.LawFlow
import Dissertation.WellPosedness.BrownianPoisson.Compensation
import LevyStochCalc.Probability.MarkedPredictableComp

/-!
# The weight `e^s δY_{s−}` of the local martingales of Lemma 4.1

The integrands `e^s ⟨δY_{s−}, δZ_s ·⟩` and `e^s ⟨δY_{s−}, δU_s(e)⟩` of the local martingales
`M^W` and `M¹` are weighted sums `∑_k w_k δZ_k`, `∑_k w_k δU_k` with the weight
`w_k(s) = e^s δY^k_{s−} 1_{(0, T]}(s)`. The weight is jointly and progressively measurable, at most
`e^T R` at a time before which `|δY| ≤ R`, and `|w_s|² ≤ e^{2T} sup_{t ≤ T} |δY_t|²`, as
`Martingale.localBrownian_weight` and `Martingale.localCompensated_weight` ask.

## Main definitions

* `Dissertation.WellPosedness.BrownianPoisson.expLeftLimWeight` — the weight.

## Main statements

* `Dissertation.WellPosedness.BrownianPoisson.expLeftLimWeight_props` — its properties.
* `Dissertation.WellPosedness.BrownianPoisson.expLeftLim_integrand_eq`,
  `Dissertation.WellPosedness.BrownianPoisson.expLeftLim_markedIntegrand_eq` — the integrands as
  weighted sums.
* `Dissertation.WellPosedness.BrownianPoisson.poisson_sq_chain` — the Cauchy–Schwarz and
  compensation links for the quadratic variation of `M¹`.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Dissertation.WellPosedness.BrownianPoisson

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Martingale LevyStochCalc

section Weight

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ} {m : ℕ}

/-- The weight `e^s δY_{s−}` of `M^W` and `M¹`, cut to `(0, T]`. -/
noncomputable def expLeftLimWeight (Y : Fin m → ℝ → Ω → ℝ) (T : ℝ) (k : Fin m) (s : ℝ)
    (ω : Ω) : ℝ :=
  Real.exp s * (if s ∈ Ioc (0 : ℝ) T then leftLimProc Y k s ω else 0)

/-- The properties of the weight `e^s δY_{s−}` that `localBrownian_weight` asks for. -/
theorem expLeftLimWeight_props (hT : 0 ≤ T) (hℱneg : ∀ r : ℝ, r ≤ 0 → ℱ 0 ≤ ℱ r)
    {Y : Fin m → ℝ → Ω → ℝ} (hYad : ∀ k, ∀ t ∈ Icc (0 : ℝ) T, Measurable[ℱ t] (Y k t))
    (hYl : ∀ k ω, ∀ t ∈ Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l)) :
    (∀ k, Measurable (Function.uncurry fun ω s => expLeftLimWeight Y T k s ω))
    ∧ (∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => expLeftLimWeight Y T k s ω)
    ∧ (∀ (R : ℝ), 0 ≤ R → ∀ k ω s, 0 ≤ s → s ≤ T →
        (∀ u, 0 ≤ u → u < s → ∀ i, |Y i u ω| ≤ R) →
          |expLeftLimWeight Y T k s ω| ≤ Real.exp T * R)
    ∧ ∀ ω, ∀ s ∈ Icc (0 : ℝ) T, ENNReal.ofReal (∑ k, expLeftLimWeight Y T k s ω ^ 2)
        ≤ ENNReal.ofReal (Real.exp T ^ 2)
          * ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2 := by
  have hL := fun k => progressive_leftLim_Ioc (T := T) hℱneg (hYad k) (hYl k)
  have hexpm : Measurable (Function.uncurry fun (_ : Ω) (s : ℝ) => Real.exp s) :=
    Real.measurable_exp.comp measurable_snd
  have hexpp : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (s : ℝ) => Real.exp s :=
    Probability.progressivelyMeasurable_of_rightContinuous (X := fun s (_ : Ω) => Real.exp s)
      (fun _ => measurable_const)
      (fun _ t => Real.continuous_exp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  refine ⟨fun k => hexpm.mul (hL k).1, fun k => hexpp.mul (hL k).2, ?_, ?_⟩
  · intro R hR k ω s hs0 hsT hb
    simp only [expLeftLimWeight]
    split_ifs with hs
    · rw [abs_mul, abs_of_pos (Real.exp_pos s)]
      obtain ⟨l, hl⟩ := hYl k ω s hs
      exact mul_le_mul (Real.exp_le_exp.mpr hsT)
        (abs_leftLim_le hs.1 hl fun u hu hus => hb u hu hus k) (abs_nonneg _)
        (Real.exp_pos T).le
    · simp only [mul_zero, abs_zero]
      positivity
  · intro ω s hs
    by_cases hs' : s ∈ Ioc (0 : ℝ) T
    · simp only [expLeftLimWeight, if_pos hs', mul_pow]
      rw [← Finset.mul_sum, ENNReal.ofReal_mul (by positivity)]
      gcongr
      · exact hs'.2
      · exact ofReal_sum_leftLim_sq_le hs' fun k => hYl k ω s hs'
    · simp only [expLeftLimWeight, if_neg hs', mul_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, Finset.sum_const_zero, ENNReal.ofReal_zero]
      exact bot_le

end Weight

/-- The integrand `e^s ⟨δY_{s−}, δZ_s ·⟩` as the weighted sum `∑_k w_k δZ_k`. -/
theorem expLeftLim_integrand_eq {Ω : Type*} {m d : ℕ} {T : ℝ} {Y : Fin m → ℝ → Ω → ℝ}
    {Z : Fin m → ℝ → Ω → Fin d → ℝ} (hZv : ∀ k ω s, s ∉ Icc (0 : ℝ) T → Z k s ω = 0) :
    (fun s ω j => ∑ k, expLeftLimWeight Y T k s ω * Z k s ω j)
      = fun s ω j => Real.exp s * ∑ k, (if 0 < s then leftLimProc Y k s ω else 0) * Z k s ω j := by
  funext s ω j
  by_cases hs : s ∈ Ioc (0 : ℝ) T
  · simp only [expLeftLimWeight, if_pos hs, if_pos hs.1, Finset.mul_sum, mul_assoc]
  · rcases le_or_gt s 0 with hs0 | hs0
    · simp [expLeftLimWeight, if_neg hs, not_lt.mpr hs0]
    · have hsT : s ∉ Icc (0 : ℝ) T := fun h => hs ⟨hs0, h.2⟩
      simp [expLeftLimWeight, hZv _ ω s hsT]

/-- The marked integrand `e^s ⟨δY_{s−}, δU_s(e)⟩` as the weighted sum `∑_k w_k δU_k`. -/
theorem expLeftLim_markedIntegrand_eq {Ω E : Type*} {m : ℕ} {T : ℝ} {Y : Fin m → ℝ → Ω → ℝ}
    {U : Fin m → ℝ → Ω → E → ℝ} (hUv : ∀ k ω s e, s ∉ Icc (0 : ℝ) T → U k s ω e = 0) :
    (fun ω s e => ∑ k, expLeftLimWeight Y T k s ω * U k s ω e)
      = fun ω s e => Real.exp s * ∑ k, (if 0 < s then leftLimProc Y k s ω else 0) * U k s ω e := by
  funext ω s e
  by_cases hs : s ∈ Ioc (0 : ℝ) T
  · simp only [expLeftLimWeight, if_pos hs, if_pos hs.1, Finset.mul_sum, mul_assoc]
  · rcases le_or_gt s 0 with hs0 | hs0
    · simp [expLeftLimWeight, if_neg hs, not_lt.mpr hs0]
    · have hsT : s ∉ Icc (0 : ℝ) T := fun h => hs ⟨hs0, h.2⟩
      simp [expLeftLimWeight, hUv _ ω s e hsT]

section Chain

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]

/-- The quadratic integrand `|U_s(e)|²`, cut to the positive times, is marked predictable. -/
theorem measurable_sumSq_pos {ν : Measure E} [SigmaFinite ν]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {m : ℕ} {U : Fin m → ℝ → Ω → E → ℝ}
    (hU : ∀ k, Probability.MarkedPredictable ℱ ν fun ω s e => U k s ω e) :
    Measurable[Probability.markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
      if 0 < p.2.1 then ENNReal.ofReal (∑ k, U k p.2.1 p.1 p.2.2 ^ 2) else 0 := by
  have hF : Measurable fun q : ℝ × ℝ × (Fin m → ℝ) => ENNReal.ofReal (∑ k, q.2.2 k ^ 2) :=
    ENNReal.measurable_ofReal.comp (Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp measurable_snd.snd).pow_const 2)
  have hΓ : Probability.MarkedPredictable ℱ ν fun ω s e => (fun k => U k s ω e : Fin m → ℝ) := by
    unfold Probability.MarkedPredictable
    letI : MeasurableSpace (Ω × ℝ × E) := Probability.markedPredictableSigma ℱ ν
    exact measurable_pi_lambda _ fun k => hU k
  have hcomp := Probability.MarkedPredictable.comp_measurable (ν := ν) hF
    (Y := fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) measurable_const hΓ
  exact hcomp

/-- The quadratic variation `∫_{(0, s]} ∫_E e^{2r} |Y_{r−}|² |U_r(e)|²` of `M¹` against any measure:
its square root is at most `e^T (sup_{t ≤ T} |Y_t|²)^{1/2} (∫∫ |U|²)^{1/2}`. -/
theorem sqrt_setLIntegral_leftLim_le {T : ℝ} {m : ℕ} {Y : Fin m → ℝ → Ω → ℝ}
    {U : Fin m → ℝ → Ω → E → ℝ} (ω : Ω)
    (hYl : ∀ k, ∀ t ∈ Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l))
    (μ : Measure (ℝ × E))
    (hUm : Measurable fun p : ℝ × E => ENNReal.ofReal (∑ k, U k p.1 ω p.2 ^ 2)) :
    (∫⁻ p in Ioc (0 : ℝ) T ×ˢ univ,
        ENNReal.ofReal (Real.exp (2 * p.1)
          * (∑ k, (if 0 < p.1 then leftLimProc Y k p.1 ω else 0) ^ 2)
          * ∑ k, U k p.1 ω p.2 ^ 2) ∂μ) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (Real.exp T)
        * (⨆ t ∈ Icc (0 : ℝ) T, ∑ k, (‖Y k t ω‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ)
        * (∫⁻ p in Ioc (0 : ℝ) T ×ˢ univ, ENNReal.ofReal (∑ k, U k p.1 ω p.2 ^ 2) ∂μ)
          ^ (1 / 2 : ℝ) := by
  set S : ℝ≥0∞ := ⨆ t ∈ Icc (0 : ℝ) T, ∑ k, (‖Y k t ω‖₊ : ℝ≥0∞) ^ 2 with hSdef
  have hle : ∫⁻ p in Ioc (0 : ℝ) T ×ˢ univ,
      ENNReal.ofReal (Real.exp (2 * p.1)
        * (∑ k, (if 0 < p.1 then leftLimProc Y k p.1 ω else 0) ^ 2)
        * ∑ k, U k p.1 ω p.2 ^ 2) ∂μ
      ≤ ∫⁻ p in Ioc (0 : ℝ) T ×ˢ univ, ENNReal.ofReal (Real.exp T ^ 2) * S
        * ENNReal.ofReal (∑ k, U k p.1 ω p.2 ^ 2) ∂μ := by
    refine setLIntegral_mono' (measurableSet_Ioc.prod MeasurableSet.univ) fun p hp => ?_
    have hp1 : p.1 ∈ Ioc (0 : ℝ) T := hp.1
    simp only [if_pos hp1.1]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    gcongr
    · rw [← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by push_cast; linarith [hp1.2])
    · exact ofReal_sum_leftLim_sq_le hp1 fun k => hYl k p.1 hp1
  calc (∫⁻ p in Ioc (0 : ℝ) T ×ˢ univ,
        ENNReal.ofReal (Real.exp (2 * p.1)
          * (∑ k, (if 0 < p.1 then leftLimProc Y k p.1 ω else 0) ^ 2)
          * ∑ k, U k p.1 ω p.2 ^ 2) ∂μ) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (Real.exp T ^ 2) * S * ∫⁻ p in Ioc (0 : ℝ) T ×ˢ univ,
          ENNReal.ofReal (∑ k, U k p.1 ω p.2 ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
        refine ENNReal.rpow_le_rpow (hle.trans_eq ?_) (by norm_num)
        exact lintegral_const_mul _ hUm
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ofReal_sq_rpow_half (Real.exp_pos T).le]

/-- `𝔼 ∫_{(0, T]} ∫_E |U|² ν(de) ds = ∑_k 𝔼 ∫_0^T ‖U_k‖²_{L²(ν)} ds`. -/
theorem lintegral_Ioc_sumSq_eq_markedEnergy {P : Measure Ω} {ν : Measure E} [SigmaFinite ν]
    {T : ℝ} {m : ℕ} {U : Fin m → ℝ → Ω → E → ℝ}
    (hUm : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2) :
    ∫⁻ ω, ∫⁻ s in Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (∑ k, U k s ω e ^ 2) ∂ν ∂volume ∂P
      = ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) := by
  have he : ∀ k ω s, Measurable fun e => (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 := fun k ω s =>
    ((hUm k).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).nnnorm
      |>.coe_nnreal_ennreal.pow_const 2
  have hs : ∀ k ω, Measurable fun s => ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := fun k ω => by
    have h3 : Measurable fun q : ℝ × E => (‖U k q.1 ω q.2‖₊ : ℝ≥0∞) ^ 2 :=
      ((hUm k).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).nnnorm
        |>.coe_nnreal_ennreal.pow_const 2
    exact h3.lintegral_prod_right'
  have hω : ∀ k, Measurable fun ω => ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
      (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := fun k => by
    have h3 : Measurable fun q : (Ω × ℝ) × E => (‖U k q.1.2 q.1.1 q.2‖₊ : ℝ≥0∞) ^ 2 :=
      ((hUm k).comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk
        measurable_snd))).nnnorm.coe_nnreal_ennreal.pow_const 2
    exact h3.lintegral_prod_right'.lintegral_prod_right'
  have hin : ∀ ω, ∫⁻ s in Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (∑ k, U k s ω e ^ 2) ∂ν
      = ∑ k, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
    intro ω
    rw [setLIntegral_congr Ioc_ae_eq_Icc, ← lintegral_finsetSum _ fun k _ => hs k ω]
    refine lintegral_congr fun s => ?_
    rw [← lintegral_finsetSum _ fun k _ => he k ω s]
    refine lintegral_congr fun e => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
    simp_rw [nnnorm_sq_eq_ofReal]
  simp_rw [hin]
  rw [lintegral_finsetSum _ fun k _ => hω k]
  rfl

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {N : Poisson.PoissonRandomMeasure P ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **The compensation formula (2.1) for `|U|²`.** -/
theorem poisson_sumSq_compensation (hℱN : Poisson.IsPoissonFiltration N ℱ) (T : ℝ) {m : ℕ}
    {U : Fin m → ℝ → Ω → E → ℝ}
    (hU : ∀ k, Probability.MarkedPredictable ℱ ν fun ω s e => U k s ω e) :
    AEMeasurable (fun ω => ∫⁻ p in Ioc (0 : ℝ) T ×ˢ univ,
      ENNReal.ofReal (∑ k, U k p.1 ω p.2 ^ 2) ∂(N.N ω)) P
    ∧ ∫⁻ ω, ∫⁻ p in Ioc (0 : ℝ) T ×ˢ univ,
          ENNReal.ofReal (∑ k, U k p.1 ω p.2 ^ 2) ∂(N.N ω) ∂P
        = ∫⁻ ω, ∫⁻ s in Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (∑ k, U k s ω e ^ 2)
            ∂ν ∂volume ∂P := by
  have hcomp := aemeasurable_and_lintegral_compensation (N := N) hℱN T
    (measurable_sumSq_pos (ν := ν) hU)
  have hNeq : ∀ ω, ∫⁻ p in Ioc (0 : ℝ) T ×ˢ univ, (fun p : Ω × ℝ × E =>
        if 0 < p.2.1 then ENNReal.ofReal (∑ k, U k p.2.1 p.1 p.2.2 ^ 2) else 0) (ω, p) ∂(N.N ω)
      = ∫⁻ p in Ioc (0 : ℝ) T ×ˢ univ, ENNReal.ofReal (∑ k, U k p.1 ω p.2 ^ 2) ∂(N.N ω) :=
    fun ω => setLIntegral_congr_fun (measurableSet_Ioc.prod MeasurableSet.univ)
      fun p hp => by simp only [if_pos hp.1.1]
  have hνeq : ∀ ω, ∫⁻ s in Ioc (0 : ℝ) T, ∫⁻ e, (fun p : Ω × ℝ × E =>
        if 0 < p.2.1 then ENNReal.ofReal (∑ k, U k p.2.1 p.1 p.2.2 ^ 2) else 0) (ω, s, e) ∂ν
      = ∫⁻ s in Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (∑ k, U k s ω e ^ 2) ∂ν :=
    fun ω => setLIntegral_congr_fun measurableSet_Ioc fun s hs => by
      simp only [if_pos hs.1]
  obtain ⟨h1, -, h3⟩ := hcomp
  refine ⟨?_, ?_⟩
  · rw [show (fun ω => ∫⁻ p in Ioc (0 : ℝ) T ×ˢ univ,
        ENNReal.ofReal (∑ k, U k p.1 ω p.2 ^ 2) ∂(N.N ω)) = _ from (funext hNeq).symm]
    exact h1
  · rw [show (fun ω => ∫⁻ p in Ioc (0 : ℝ) T ×ˢ univ,
        ENNReal.ofReal (∑ k, U k p.1 ω p.2 ^ 2) ∂(N.N ω)) = _ from (funext hNeq).symm,
      show (fun ω => ∫⁻ s in Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (∑ k, U k s ω e ^ 2) ∂ν)
        = _ from (funext hνeq).symm]
    exact h3

end Chain

end Dissertation.WellPosedness.BrownianPoisson
