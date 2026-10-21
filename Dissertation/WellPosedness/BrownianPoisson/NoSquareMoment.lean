/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.QuadraticIntegrand

/-!
# A marked integrand of finite energy whose square has infinite energy

For a Brownian motion `W`, a time `r > 0` and `c = 1_{(0, 1]}(W_r) W_r^{−1/4}`, the Gaussian law of
`W_r` gives `𝔼 c² = 𝔼 1_{(0, 1]}(W_r) W_r^{−1/2} < ∞` and `𝔼 c⁴ = 𝔼 1_{(0, 1]}(W_r) W_r^{−1} = ∞`,
since the Gaussian density is bounded above, and bounded below on `(0, 1]`, by positive
constants. For a mark set `A` with `0 < ν(A) < ∞` and `r < T`, the integrand
`U_s(e) = 1_{(r, T]}(s) 1_A(e) c` is marked predictable, vanishes off `[0, T]` and has finite
energy, while `e^s |U_s(e)|²` has infinite energy: membership in `H²_N` gives the quadratic
integrand of the Poisson martingale `M²` of the proof of Lemma 4.1 of the well-posedness paper no
square moment.

## Main statements

* `lintegral_quarterPow_sq_lt_top`, `lintegral_quarterPow_four_eq_top` — the two moments of `c`.
* `exists_markedPredictable_sq_markedEnergy_eq_top` — the integrand `U`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness.BrownianPoisson

open LevyStochCalc

/-- `x ↦ 1_{(0, 1]}(x) x^{−1/4}`. -/
noncomputable def quarterPow (x : ℝ) : ℝ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun x => x ^ (-(1 / 4 : ℝ))) x

/-- `x ↦ 1_{(0, 1]}(x) x^{−1/4}` is measurable. -/
theorem measurable_quarterPow : Measurable quarterPow :=
  (measurable_id.pow_const _).indicator measurableSet_Ioc

/-- `‖1_{(0, 1]}(x) x^{−1/4}‖² = 1_{(0, 1]}(x) x^{−1/2}`. -/
theorem coe_nnnorm_quarterPow_sq (x : ℝ) :
    (‖quarterPow x‖₊ : ℝ≥0∞) ^ 2
      = (Set.Ioc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (x ^ (-(1 / 2 : ℝ)))) x := by
  rw [coe_nnnorm_sq_eq_ofReal]
  by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
  · rw [quarterPow, Set.indicator_of_mem hx, Set.indicator_of_mem hx, ← Real.rpow_natCast,
      ← Real.rpow_mul hx.1.le]
    norm_num
  · rw [quarterPow, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-- `‖1_{(0, 1]}(x) x^{−1/4}‖⁴ = 1_{(0, 1]}(x) x^{−1}`. -/
theorem coe_nnnorm_quarterPow_four (x : ℝ) :
    (‖quarterPow x‖₊ : ℝ≥0∞) ^ 4
      = (Set.Ioc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (x ^ (-1 : ℝ))) x := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, coe_nnnorm_quarterPow_sq]
  by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      ← ENNReal.ofReal_pow (Real.rpow_nonneg hx.1.le _), ← Real.rpow_natCast,
      ← Real.rpow_mul hx.1.le]
    norm_num
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-- The Gaussian density is at most `(2πv)^{−1/2}`. -/
theorem gaussianPDF_le (v : ℝ≥0) (x : ℝ) :
    gaussianPDF 0 v x ≤ ENNReal.ofReal (√(2 * Real.pi * v))⁻¹ := by
  rw [gaussianPDF, gaussianPDFReal]
  refine ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (by positivity) ?_)
  rw [Real.exp_le_one_iff]
  have : 0 ≤ (x - 0) ^ 2 / (2 * (v : ℝ)) := by positivity
  linarith [neg_div (2 * (v : ℝ)) ((x - 0) ^ 2)]

/-- On `(0, 1]` the Gaussian density is at least `(2πv)^{−1/2} e^{−1/(2v)}`. -/
theorem le_gaussianPDF {v : ℝ≥0} (hv : v ≠ 0) {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    ENNReal.ofReal ((√(2 * Real.pi * v))⁻¹ * Real.exp (-1 / (2 * v))) ≤ gaussianPDF 0 v x := by
  rw [gaussianPDF, gaussianPDFReal]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine Real.exp_le_exp.mpr ?_
  have hv' : (0 : ℝ) < 2 * v := by positivity
  rw [div_le_div_iff_of_pos_right hv']
  have h1 : (x - 0) ^ 2 ≤ 1 := by
    rw [sub_zero]
    nlinarith [hx.1, hx.2]
  linarith

/-- `∫_{(0, 1]} x^{−1/2} dx < ∞`. -/
theorem lintegral_Ioc_rpow_neg_half_lt_top :
    ∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ (-(1 / 2 : ℝ))) < ⊤ := by
  have h : IntegrableOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Set.Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  exact h.lintegral_lt_top

/-- `∫_{(0, 1]} x^{−1} dx = ∞`. -/
theorem lintegral_Ioc_rpow_neg_one_eq_top :
    ∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ (-1 : ℝ)) = ⊤ := by
  by_contra hfin
  have hint : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Set.Ioc (0 : ℝ) 1) := by
    refine ⟨(measurable_id.pow_const _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact lt_top_iff_ne_top.mpr hfin
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact Real.rpow_nonneg hx.1.le _
  have h := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := (-1 : ℝ)) zero_lt_one).mp
    (hint.mono_set Set.Ioo_subset_Ioc_self)
  norm_num at h

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The law of a Brownian motion at a time `r > 0` is the centred Gaussian of variance `r`. -/
theorem map_brownian_eq_gaussianReal (W : Brownian.BrownianMotion P) {r : ℝ} (hr : 0 < r) :
    P.map (W.W r) = gaussianReal 0 ⟨r - 0, by linarith⟩ := by
  have h1 := W.increment_gaussian (le_refl 0) hr
  have h2 : (fun ω => W.W r ω - W.W 0 ω) =ᵐ[P] W.W r := by
    filter_upwards [W.initial_zero] with ω hω
    rw [hω, sub_zero]
  rw [Measure.map_congr h2] at h1
  exact h1

/-- The expectation of a measurable function of `W_r`, `r > 0`, against the Gaussian density. -/
theorem lintegral_comp_brownian (W : Brownian.BrownianMotion P) {r : ℝ} (hr : 0 < r)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (W.W r ω) ∂P = ∫⁻ x, gaussianPDF 0 ⟨r - 0, by linarith⟩ x * F x := by
  have hv : (⟨r - 0, by linarith⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have h' := congrArg NNReal.toReal h
    change r - 0 = 0 at h'
    linarith
  rw [← lintegral_map hF (W.measurable_eval r), map_brownian_eq_gaussianReal W hr,
    gaussianReal_of_var_ne_zero _ hv,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hF]
  rfl

/-- `𝔼 |1_{(0, 1]}(W_r) W_r^{−1/4}|² < ∞` for `r > 0`. -/
theorem lintegral_quarterPow_sq_lt_top (W : Brownian.BrownianMotion P) {r : ℝ} (hr : 0 < r) :
    ∫⁻ ω, (‖quarterPow (W.W r ω)‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
  have hF : Measurable fun x => (‖quarterPow x‖₊ : ℝ≥0∞) ^ 2 :=
    measurable_quarterPow.nnnorm.coe_nnreal_ennreal.pow_const 2
  rw [lintegral_comp_brownian W hr hF]
  simp only [coe_nnnorm_quarterPow_sq]
  have he : ∀ x, gaussianPDF 0 ⟨r - 0, by linarith⟩ x
      * (Set.Ioc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (x ^ (-(1 / 2 : ℝ)))) x
      = (Set.Ioc (0 : ℝ) 1).indicator (fun x => gaussianPDF 0 ⟨r - 0, by linarith⟩ x
          * ENNReal.ofReal (x ^ (-(1 / 2 : ℝ)))) x := fun x =>
    (Set.indicator_mul_right _ _ _).symm
  simp only [he]
  rw [lintegral_indicator measurableSet_Ioc]
  refine lt_of_le_of_lt (lintegral_mono fun x => mul_le_mul_left (gaussianPDF_le _ x) _) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top lintegral_Ioc_rpow_neg_half_lt_top

/-- `𝔼 |1_{(0, 1]}(W_r) W_r^{−1/4}|⁴ = ∞` for `r > 0`. -/
theorem lintegral_quarterPow_four_eq_top (W : Brownian.BrownianMotion P) {r : ℝ} (hr : 0 < r) :
    ∫⁻ ω, (‖quarterPow (W.W r ω)‖₊ : ℝ≥0∞) ^ 4 ∂P = ⊤ := by
  have hv : (⟨r - 0, by linarith⟩ : ℝ≥0) ≠ 0 := by
    intro h
    have h' := congrArg NNReal.toReal h
    change r - 0 = 0 at h'
    linarith
  have hF : Measurable fun x => (‖quarterPow x‖₊ : ℝ≥0∞) ^ 4 :=
    measurable_quarterPow.nnnorm.coe_nnreal_ennreal.pow_const 4
  rw [lintegral_comp_brownian W hr hF]
  simp only [coe_nnnorm_quarterPow_four]
  have he : ∀ x, gaussianPDF 0 ⟨r - 0, by linarith⟩ x
      * (Set.Ioc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (x ^ (-1 : ℝ))) x
      = (Set.Ioc (0 : ℝ) 1).indicator (fun x => gaussianPDF 0 ⟨r - 0, by linarith⟩ x
          * ENNReal.ofReal (x ^ (-1 : ℝ))) x := fun x =>
    (Set.indicator_mul_right _ _ _).symm
  simp only [he]
  rw [lintegral_indicator measurableSet_Ioc]
  have hc0 : 0 < (√(2 * Real.pi * ((⟨r - 0, by linarith⟩ : ℝ≥0) : ℝ)))⁻¹
      * Real.exp (-1 / (2 * ((⟨r - 0, by linarith⟩ : ℝ≥0) : ℝ))) := by
    refine mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr ?_)) (Real.exp_pos _)
    change 0 < 2 * Real.pi * (r - 0)
    have := Real.pi_pos
    positivity
  refine top_le_iff.mp (le_trans ?_ (setLIntegral_mono' measurableSet_Ioc fun x hx =>
    mul_le_mul_left (le_gaussianPDF hv hx) _))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_Ioc_rpow_neg_one_eq_top]
  exact (ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc0).ne').ge

end Moments

section Integrand

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type*} [MeasurableSpace E] {ν : Measure E}

/-- For a set `A` of marks and a constant `K`,
`∫_0^T ∫_E 1_{(r, T] × A}(s, e) K ν(de) ds = K ν(A) (T − r)⁺` for `r ≥ 0`. -/
theorem setLIntegral_lintegral_indicator_rect {r T : ℝ} (hr : 0 ≤ r)
    {A : Set E} (hA : MeasurableSet A) (K : ℝ≥0∞) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (Set.Ioc r T ×ˢ A).indicator (fun _ => K) (s, e) ∂ν
      = K * ν A * ENNReal.ofReal (T - r) := by
  have he : ∀ s, ∫⁻ e, (Set.Ioc r T ×ˢ A).indicator (fun _ => K) (s, e) ∂ν
      = (Set.Ioc r T).indicator (fun _ => K * ν A) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc r T
    · rw [Set.indicator_of_mem hs, ← lintegral_indicator_const hA]
      refine lintegral_congr fun e => ?_
      by_cases he : e ∈ A
      · rw [Set.indicator_of_mem (Set.mk_mem_prod hs he), Set.indicator_of_mem he]
      · rw [Set.indicator_of_notMem (fun h => he (Set.mem_prod.mp h).2),
          Set.indicator_of_notMem he]
    · rw [Set.indicator_of_notMem hs]
      refine (lintegral_congr fun e => ?_).trans lintegral_zero
      exact Set.indicator_of_notMem (fun h => hs (Set.mem_prod.mp h).1) _
  simp only [he]
  rw [lintegral_indicator_const measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr (show Set.Ioc r T ⊆ Set.Icc 0 T from fun s hs =>
      ⟨hr.trans hs.1.le, hs.2⟩), Real.volume_Ioc]

/-- **A marked integrand of finite energy whose quadratic integrand has infinite energy.** For a
Brownian motion `W` whose value at `r ∈ (0, T)` is `ℱ_r`-measurable, a mark set `A` with
`0 < ν(A) < ∞` and `m ≥ 1`, the integrand `U^k_s(e) = 1_{(r, T]}(s) 1_A(e) c`, `k < m`, with
`c = 1_{(0, 1]}(W_r) W_r^{−1/4}`, is marked predictable, vanishes off `[0, T]` and has finite
energy, while `𝔼 ∫_0^T ∫_E (e^s |U_s(e)|²)² ν(de) ds = ∞`. -/
theorem exists_markedPredictable_sq_markedEnergy_eq_top (W : Brownian.BrownianMotion P)
    {ℱ : Filtration ℝ mΩ} {r T : ℝ} (hr : 0 < r) (hrT : r < T) (hW : Measurable[ℱ r] (W.W r))
    {A : Set E} (hA : MeasurableSet A) (hA0 : ν A ≠ 0) (hAt : ν A ≠ ⊤) {m : ℕ} (hm : 0 < m) :
    ∃ δU : Fin m → ℝ → Ω → E → ℝ,
      (∀ k, Probability.MarkedPredictable ℱ ν fun ω s e => δU k s ω e)
      ∧ (∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → δU k s ω e = 0)
      ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e) ≠ ⊤)
      ∧ Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => Real.exp s * ∑ k, δU k s ω e ^ 2) = ⊤ := by
  classical
  set c : Ω → ℝ := fun ω => quarterPow (W.W r ω) with hcdef
  have hcm : Measurable[ℱ r] c := measurable_quarterPow.comp hW
  have hc2 := lintegral_quarterPow_sq_lt_top W hr (P := P)
  have hc4 := lintegral_quarterPow_four_eq_top W hr (P := P)
  refine ⟨fun _ s ω e => (Set.Ioc r T ×ˢ A).indicator (fun _ => c ω) (s, e), fun _ =>
    Probability.markedPredictable_rectIndicator hr.le hA hAt hcm, fun _ ω s e hs =>
    Set.indicator_of_notMem (fun h => hs ⟨hr.le.trans h.1.1.le, h.1.2⟩) _, fun _ => ?_, ?_⟩
  · have hpt : ∀ ω s e, (‖(Set.Ioc r T ×ˢ A).indicator (fun _ => c ω) (s, e)‖₊ : ℝ≥0∞) ^ 2
        = (Set.Ioc r T ×ˢ A).indicator (fun _ => (‖c ω‖₊ : ℝ≥0∞) ^ 2) (s, e) := by
      intro ω s e
      by_cases h : (s, e) ∈ Set.Ioc r T ×ˢ A
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
        simp
    simp only [Poisson.Compensated.markedEnergy, hpt]
    simp only [setLIntegral_lintegral_indicator_rect hr.le hA]
    rw [lintegral_mul_const' _ _ (ENNReal.ofReal_ne_top), lintegral_mul_const' _ _ hAt]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hc2.ne hAt) ENNReal.ofReal_ne_top
  · refine top_le_iff.mp ?_
    have hpt : ∀ ω, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e,
        (Set.Ioc r T ×ˢ A).indicator (fun _ => (‖c ω‖₊ : ℝ≥0∞) ^ 4) (s, e)
          ≤ (‖Real.exp s * ∑ _k : Fin m,
              (Set.Ioc r T ×ˢ A).indicator (fun _ => c ω) (s, e) ^ 2‖₊ : ℝ≥0∞) ^ 2 := by
      intro ω s hs e
      by_cases h : (s, e) ∈ Set.Ioc r T ×ˢ A
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, coe_nnnorm_sq_eq_ofReal,
          show (4 : ℕ) = 2 * 2 from rfl, pow_mul, coe_nnnorm_sq_eq_ofReal,
          ← ENNReal.ofReal_pow (sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hes : 1 ≤ Real.exp s := Real.one_le_exp (hr.le.trans h.1.1.le)
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
        have hc0 : 0 ≤ c ω ^ 2 := sq_nonneg _
        have hk : c ω ^ 2 ≤ Real.exp s * (m * c ω ^ 2) := by
          calc c ω ^ 2 = 1 * (1 * c ω ^ 2) := by ring
            _ ≤ Real.exp s * (m * c ω ^ 2) := by gcongr
        exact pow_le_pow_left₀ hc0 hk 2
      · rw [Set.indicator_of_notMem h]
        exact zero_le
    calc (⊤ : ℝ≥0∞) = (∫⁻ ω, (‖c ω‖₊ : ℝ≥0∞) ^ 4 ∂P) * ν A * ENNReal.ofReal (T - r) := by
          rw [hc4, ENNReal.top_mul hA0, ENNReal.top_mul (by simpa using hrT)]
      _ = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (Set.Ioc r T ×ˢ A).indicator (fun _ => (‖c ω‖₊ : ℝ≥0∞) ^ 4) (s, e) ∂ν ∂volume ∂P := by
          simp only [setLIntegral_lintegral_indicator_rect hr.le hA]
          rw [lintegral_mul_const' _ _ (ENNReal.ofReal_ne_top), lintegral_mul_const' _ _ hAt]
      _ ≤ _ := by
          refine lintegral_mono fun ω => setLIntegral_mono' measurableSet_Icc fun s hs => ?_
          exact lintegral_mono fun e => hpt ω s hs e

end Integrand

end Dissertation.WellPosedness.BrownianPoisson
