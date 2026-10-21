/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Lenglart's domination argument in integrated form

Let `S, A ≥ 0` be random variables such that for every level `δ > 0` some `S'` agrees with or
dominates `S` on `{A < δ}` and has `𝔼 S'² ≤ c 𝔼 (A ∧ δ)`. Then `𝔼 S ≤ (1 + 2c) 𝔼 A^{1/2}`.
For a martingale `M` with quadratic variation `A`, stopped when `A` reaches `δ`, Doob's `L²`
inequality supplies `S'` with `c = 4`, and this is the Burkholder–Davis–Gundy inequality at
`p = 1` with constant `9` (Lenglart's inequality, integrated over the levels).

The proof integrates the tail bound `P(S ≥ ε) ≤ P(A ≥ ε²) + c 𝔼 (A ∧ ε²) / ε²` over `ε > 0`,
using `∫_0^∞ (a ∧ ε²) / ε² dε ≤ 2 a^{1/2}`.

## Main statements

* `Dissertation.WellPosedness.Martingale.lintegral_eq_lintegral_meas_ofReal_le` — the layer-cake
  formula for an extended nonnegative function.
* `Dissertation.WellPosedness.Martingale.lintegral_le_of_good_lambda` — the integrated Lenglart
  bound.
* `Dissertation.WellPosedness.Martingale.integrable_and_integral_eq_zero_of_cauchy` — a limit
  in probability of mean-zero variables that is Cauchy in `L¹` has mean zero.

## References

* Lenglart, *Relation de domination entre deux processus*, Ann. IHP 13 (1977).
* Revuz–Yor, *Continuous Martingales and Brownian Motion*, Ch. IV, Prop. 4.7.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace Dissertation.WellPosedness.Martingale

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The layer-cake formula for an extended nonnegative function.**
`∫ S dP = ∫_0^∞ P(S ≥ t) dt`. -/
theorem lintegral_eq_lintegral_meas_ofReal_le {S : Ω → ℝ≥0∞} (hS : AEMeasurable S P) :
    ∫⁻ ω, S ω ∂P = ∫⁻ t in Ioi 0, P {ω | ENNReal.ofReal t ≤ S ω} := by
  by_cases htop : P {ω | S ω = ∞} = 0
  · have hae : ∀ᵐ ω ∂P, S ω ≠ ∞ := by
      rw [ae_iff]
      simpa using htop
    have h1 : ∫⁻ ω, S ω ∂P = ∫⁻ ω, ENNReal.ofReal (S ω).toReal ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with ω hω
      rw [ENNReal.ofReal_toReal hω]
    rw [h1, lintegral_eq_lintegral_meas_le P
      (Eventually.of_forall fun ω => ENNReal.toReal_nonneg) hS.ennreal_toReal]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    refine measure_congr ?_
    filter_upwards [hae] with ω hω
    change (t ≤ (S ω).toReal) = (ENNReal.ofReal t ≤ S ω)
    rw [ENNReal.ofReal_le_iff_le_toReal hω]
  · rw [lintegral_eq_top_of_measure_eq_top_ne_zero hS htop]
    symm
    refine eq_top_iff.mpr ?_
    calc (⊤ : ℝ≥0∞) = ∫⁻ _ in Ioi (0 : ℝ), P {ω | S ω = ∞} := by
          rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top htop]
      _ ≤ ∫⁻ t in Ioi 0, P {ω | ENNReal.ofReal t ≤ S ω} := by
          refine lintegral_mono fun t => measure_mono fun ω hω => ?_
          simp only [mem_setOf_eq] at hω ⊢
          rw [hω]
          exact le_top

/-- `∫_0^∞ (a ∧ ε²) / ε² dε ≤ 2 a^{1/2}` for `a ∈ [0, ∞]`. -/
theorem lintegral_min_div_sq_le (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), min a (ENNReal.ofReal (t ^ 2)) / ENNReal.ofReal (t ^ 2)
      ≤ 2 * a ^ (1 / 2 : ℝ) := by
  rcases eq_or_ne a ∞ with rfl | hatop
  · rw [ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top (by norm_num)]
    exact le_top
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  set r : ℝ := (a ^ (1 / 2 : ℝ)).toReal with hr
  have hrt : a ^ (1 / 2 : ℝ) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hatop
  have hr0 : 0 < r := by
    refine ENNReal.toReal_pos ?_ hrt
    exact (ENNReal.rpow_pos (pos_iff_ne_zero.mpr ha0) hatop).ne'
  have hrE : ENNReal.ofReal r = a ^ (1 / 2 : ℝ) := ENNReal.ofReal_toReal hrt
  have haE : a = ENNReal.ofReal (r ^ 2) := by
    rw [ENNReal.ofReal_pow hr0.le, hrE, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hsplit : Ioi (0 : ℝ) ⊆ Ioc 0 r ∪ Ioi r := by
    intro t ht
    by_cases htr : t ≤ r
    · exact Or.inl ⟨ht, htr⟩
    · exact Or.inr (not_le.mp htr)
  have h1 : ∫⁻ t in Ioc 0 r, min a (ENNReal.ofReal (t ^ 2)) / ENNReal.ofReal (t ^ 2)
      ≤ ENNReal.ofReal r := by
    calc ∫⁻ t in Ioc 0 r, min a (ENNReal.ofReal (t ^ 2)) / ENNReal.ofReal (t ^ 2)
        ≤ ∫⁻ _ in Ioc 0 r, (1 : ℝ≥0∞) :=
          setLIntegral_mono' measurableSet_Ioc fun t _ =>
            ENNReal.div_le_of_le_mul (by rw [one_mul]; exact min_le_right _ _)
      _ = ENNReal.ofReal r := by rw [setLIntegral_const, Real.volume_Ioc, one_mul, sub_zero]
  have hint : ∫ t in Ioi r, r ^ 2 * t ^ (-2 : ℝ) = r := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hr0]
    have : r ^ (-2 + 1 : ℝ) = r⁻¹ := by norm_num [Real.rpow_neg_one]
    rw [this]
    field_simp
    norm_num
  have h2 : ∫⁻ t in Ioi r, min a (ENNReal.ofReal (t ^ 2)) / ENNReal.ofReal (t ^ 2)
      ≤ ENNReal.ofReal r := by
    calc ∫⁻ t in Ioi r, min a (ENNReal.ofReal (t ^ 2)) / ENNReal.ofReal (t ^ 2)
        ≤ ∫⁻ t in Ioi r, ENNReal.ofReal (r ^ 2 * t ^ (-2 : ℝ)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          have ht0 : 0 < t := hr0.trans ht
          calc min a (ENNReal.ofReal (t ^ 2)) / ENNReal.ofReal (t ^ 2)
              ≤ a / ENNReal.ofReal (t ^ 2) := by gcongr; exact min_le_left _ _
            _ = ENNReal.ofReal (r ^ 2 * t ^ (-2 : ℝ)) := by
              rw [haE, ← ENNReal.ofReal_div_of_pos (by positivity), Real.rpow_neg ht0.le,
                div_eq_mul_inv]
              norm_num
      _ = ENNReal.ofReal r := by
          rw [← ofReal_integral_eq_lintegral_ofReal, hint]
          · exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hr0).const_mul _
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            have ht0 : 0 < t := hr0.trans ht
            positivity
  calc ∫⁻ t in Ioi (0 : ℝ), min a (ENNReal.ofReal (t ^ 2)) / ENNReal.ofReal (t ^ 2)
      ≤ ∫⁻ t in Ioc 0 r ∪ Ioi r, min a (ENNReal.ofReal (t ^ 2)) / ENNReal.ofReal (t ^ 2) :=
        lintegral_mono_set hsplit
    _ ≤ _ := lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := add_le_add h1 h2
    _ = 2 * a ^ (1 / 2 : ℝ) := by rw [← two_mul, hrE]

/-- **Lenglart's domination argument, integrated over the levels.** If for every `δ > 0` some
`S'` dominates `S` on `{A < δ}` almost surely and `𝔼 S'² ≤ c 𝔼 (A ∧ δ)`, then
`𝔼 S ≤ (1 + 2c) 𝔼 A^{1/2}`. -/
theorem lintegral_le_of_good_lambda [IsFiniteMeasure P] {S A : Ω → ℝ≥0∞}
    (hS : AEMeasurable S P) (hA : Measurable A) {c : ℝ≥0∞}
    (h : ∀ δ : ℝ, 0 < δ → ∃ S' : Ω → ℝ≥0∞, AEMeasurable S' P ∧
      (∀ᵐ ω ∂P, A ω < ENNReal.ofReal δ → S ω ≤ S' ω) ∧
      ∫⁻ ω, S' ω ^ 2 ∂P ≤ c * ∫⁻ ω, min (A ω) (ENNReal.ofReal δ) ∂P) :
    ∫⁻ ω, S ω ∂P ≤ (1 + 2 * c) * ∫⁻ ω, A ω ^ (1 / 2 : ℝ) ∂P := by
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ 2) with hg
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp (measurable_id.pow_const 2)
  have hhalf : ∀ x y : ℝ≥0∞, x ^ 2 ≤ y → x ≤ y ^ (1 / 2 : ℝ) := by
    intro x y hxy
    rw [one_div, ENNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast hxy
  -- the tail bound at each level
  have htail : ∀ t : ℝ, 0 < t → P {ω | ENNReal.ofReal t ≤ S ω}
      ≤ P {ω | ENNReal.ofReal t ≤ A ω ^ (1 / 2 : ℝ)}
        + c * (∫⁻ ω, min (A ω) (g t) ∂P) / g t := by
    intro t ht
    obtain ⟨S', hS'm, hS'le, hS'sq⟩ := h (t ^ 2) (by positivity)
    have hgt0 : g t ≠ 0 := by simp [hg]; positivity
    have hgtt : g t ≠ ∞ := ENNReal.ofReal_ne_top
    have hsub : {ω | ENNReal.ofReal t ≤ S ω} ≤ᵐ[P]
        ({ω | ENNReal.ofReal t ≤ A ω ^ (1 / 2 : ℝ)} ∪ {ω | g t ≤ S' ω ^ 2} : Set Ω) := by
      filter_upwards [hS'le] with ω hω hmem
      change ENNReal.ofReal t ≤ S ω at hmem
      by_cases hA' : A ω < g t
      · right
        have h1 : ENNReal.ofReal t ≤ S' ω := hmem.trans (hω hA')
        change ENNReal.ofReal (t ^ 2) ≤ S' ω ^ 2
        rw [ENNReal.ofReal_pow ht.le]
        exact pow_le_pow_left₀ bot_le h1 2
      · left
        push Not at hA'
        refine hhalf _ _ ?_
        rw [← ENNReal.ofReal_pow ht.le]
        exact hA'
    calc P {ω | ENNReal.ofReal t ≤ S ω}
        ≤ P ({ω | ENNReal.ofReal t ≤ A ω ^ (1 / 2 : ℝ)} ∪ {ω | g t ≤ S' ω ^ 2}) :=
          measure_mono_ae hsub
      _ ≤ P {ω | ENNReal.ofReal t ≤ A ω ^ (1 / 2 : ℝ)} + P {ω | g t ≤ S' ω ^ 2} :=
          measure_union_le _ _
      _ ≤ P {ω | ENNReal.ofReal t ≤ A ω ^ (1 / 2 : ℝ)} + (∫⁻ ω, S' ω ^ 2 ∂P) / g t := by
          gcongr
          exact meas_ge_le_lintegral_div (hS'm.pow_const 2) hgt0 hgtt
      _ ≤ _ := by gcongr
  -- the drift part, integrated over the levels
  have hmeas2 : Measurable fun t : ℝ => c * (∫⁻ ω, min (A ω) (g t) ∂P) / g t := by
    refine (Measurable.const_mul ?_ c).div hgm
    exact Measurable.lintegral_prod_right' (f := fun p : ℝ × Ω => min (A p.2) (g p.1))
      ((hA.comp measurable_snd).min (hgm.comp measurable_fst))
  have hswap : ∫⁻ t in Ioi (0 : ℝ), c * (∫⁻ ω, min (A ω) (g t) ∂P) / g t
      = c * ∫⁻ ω, (∫⁻ t in Ioi (0 : ℝ), min (A ω) (g t) / g t) ∂P := by
    have hin : ∀ t, c * (∫⁻ ω, min (A ω) (g t) ∂P) / g t
        = c * ∫⁻ ω, min (A ω) (g t) / g t ∂P := by
      intro t
      rw [mul_div_assoc, div_eq_mul_inv, ← lintegral_mul_const _ (hA.min measurable_const)]
      simp only [div_eq_mul_inv]
    simp_rw [hin]
    have hjm : Measurable (Function.uncurry fun (t : ℝ) (ω : Ω) => min (A ω) (g t) / g t) :=
      ((hA.comp measurable_snd).min (hgm.comp measurable_fst)).div (hgm.comp measurable_fst)
    have hm1 : Measurable fun t : ℝ => ∫⁻ ω, min (A ω) (g t) / g t ∂P :=
      Measurable.lintegral_prod_right' (f := fun p : ℝ × Ω => min (A p.2) (g p.1) / g p.1) hjm
    rw [lintegral_const_mul c hm1]
    congr 1
    exact lintegral_lintegral_swap (μ := volume.restrict (Ioi (0 : ℝ))) (ν := P)
      hjm.aemeasurable
  have hA2 : AEMeasurable (fun ω => A ω ^ (1 / 2 : ℝ)) P := (hA.pow_const _).aemeasurable
  calc ∫⁻ ω, S ω ∂P = ∫⁻ t in Ioi 0, P {ω | ENNReal.ofReal t ≤ S ω} :=
        lintegral_eq_lintegral_meas_ofReal_le hS
    _ ≤ ∫⁻ t in Ioi 0, (P {ω | ENNReal.ofReal t ≤ A ω ^ (1 / 2 : ℝ)}
          + c * (∫⁻ ω, min (A ω) (g t) ∂P) / g t) :=
        setLIntegral_mono' measurableSet_Ioi fun t ht => htail t ht
    _ = ∫⁻ ω, A ω ^ (1 / 2 : ℝ) ∂P
          + c * ∫⁻ ω, (∫⁻ t in Ioi (0 : ℝ), min (A ω) (g t) / g t) ∂P := by
        rw [lintegral_add_right _ hmeas2, hswap, ← lintegral_eq_lintegral_meas_ofReal_le hA2]
    _ ≤ ∫⁻ ω, A ω ^ (1 / 2 : ℝ) ∂P + c * ∫⁻ ω, 2 * A ω ^ (1 / 2 : ℝ) ∂P := by
        gcongr with ω
        exact lintegral_min_div_sq_le (A ω)
    _ = (1 + 2 * c) * ∫⁻ ω, A ω ^ (1 / 2 : ℝ) ∂P := by
        rw [lintegral_const_mul' _ _ (by norm_num)]
        ring

/-- **A limit of mean-zero variables that is Cauchy in `L¹` has mean zero.** If `X_k → Y`
almost surely, each `X_k` is integrable with mean zero, and `𝔼|X_k − X_{k'}| ≤ ε_k` for
`k ≤ k'` with `ε_k → 0`, then `Y` is integrable with mean zero. -/
theorem integrable_and_integral_eq_zero_of_cauchy [IsFiniteMeasure P] {X : ℕ → Ω → ℝ}
    {Y : Ω → ℝ} (hXi : ∀ k, Integrable (X k) P) (hX0 : ∀ k, ∫ ω, X k ω ∂P = 0)
    (hY : AEStronglyMeasurable Y P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun k => X k ω) atTop (𝓝 (Y ω)))
    {ε : ℕ → ℝ≥0∞} (hε : Tendsto ε atTop (𝓝 0))
    (hC : ∀ k k', k ≤ k' → ∫⁻ ω, ‖X k ω - X k' ω‖ₑ ∂P ≤ ε k) :
    Integrable Y P ∧ ∫ ω, Y ω ∂P = 0 := by
  have hk : ∀ k, ∫⁻ ω, ‖X k ω - Y ω‖ₑ ∂P ≤ ε k := by
    intro k
    calc ∫⁻ ω, ‖X k ω - Y ω‖ₑ ∂P
        = ∫⁻ ω, liminf (fun k' => ‖X k ω - X k' ω‖ₑ) atTop ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlim] with ω hω
          have : Tendsto (fun k' => ‖X k ω - X k' ω‖ₑ) atTop (𝓝 ‖X k ω - Y ω‖ₑ) :=
            (continuous_enorm.tendsto _).comp (tendsto_const_nhds.sub hω)
          exact this.liminf_eq.symm
      _ ≤ liminf (fun k' => ∫⁻ ω, ‖X k ω - X k' ω‖ₑ ∂P) atTop :=
          lintegral_liminf_le' fun k' =>
            ((hXi k).sub (hXi k')).aestronglyMeasurable.enorm
      _ ≤ ε k := by
          have hfr : ∃ᶠ k' in atTop, ∫⁻ ω, ‖X k ω - X k' ω‖ₑ ∂P ≤ ε k :=
            (eventually_ge_atTop k).mono (fun k' hk' => hC k k' hk') |>.frequently
          exact liminf_le_of_frequently_le' hfr
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, ε k₀ < ∞ := by
    have := (hε.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))).exists
    obtain ⟨k₀, h⟩ := this
    exact ⟨k₀, h.trans ENNReal.one_lt_top⟩
  have hdiff : Integrable (fun ω => X k₀ ω - Y ω) P :=
    ⟨(hXi k₀).aestronglyMeasurable.sub hY, (hk k₀).trans_lt hk₀⟩
  have hYi : Integrable Y P := by
    have := (hXi k₀).sub hdiff
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp
  refine ⟨hYi, ?_⟩
  have hbound : ∀ᶠ k in atTop, ‖∫ ω, Y ω ∂P‖ ≤ (ε k).toReal := by
    filter_upwards [hε.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))] with k hεk
    have hεk' : ε k ≠ ∞ := (hεk.trans ENNReal.one_lt_top).ne
    have hdk : Integrable (fun ω => X k ω - Y ω) P :=
      ⟨(hXi k).aestronglyMeasurable.sub hY, (hk k).trans_lt (lt_top_iff_ne_top.mpr hεk')⟩
    have heq : ∫ ω, Y ω ∂P = -∫ ω, (X k ω - Y ω) ∂P := by
      rw [integral_sub (hXi k) hYi, hX0 k]
      ring
    rw [heq, norm_neg]
    calc ‖∫ ω, (X k ω - Y ω) ∂P‖ ≤ (∫⁻ ω, ‖X k ω - Y ω‖ₑ ∂P).toReal := by
          have := norm_integral_le_lintegral_norm (μ := P) (fun ω => X k ω - Y ω)
          simpa only [ofReal_norm] using this
      _ ≤ (ε k).toReal := ENNReal.toReal_mono hεk' (hk k)
  have htend : Tendsto (fun k => (ε k).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hε
    rw [ENNReal.toReal_zero] at h
    exact h
  have := ge_of_tendsto htend hbound
  exact norm_le_zero_iff.mp this

end Dissertation.WellPosedness.Martingale
