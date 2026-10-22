/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The function `t ↦ t^{-1/2}` near `0`

The drift `t ↦ t^{-1/2}` is integrable on `[0, T]`, with primitive `2√t`, but not square
integrable: `t^{-1}` is not integrable on any `(0, ε)`. The defect survives any perturbation that
stays bounded near `0`: if `y` is right-continuous at `0`, then `t^{-1/2} − y(t)` is not square
integrable on `[0, T]` for any `T > 0`, since near `0` it is at least `t^{-1/2}/2`, whose square
is `1/(4t)`.

## Main statements

* `integral_inv_sqrt` — `∫_0^t s^{-1/2} ds = 2√t`.
* `integrableOn_inv_sqrt` — `t ↦ t^{-1/2}` is integrable on `[0, T]`.
* `lintegral_ofReal_inv_Ioo_eq_top` — `∫_0^ε s^{-1} ds = ∞`.
* `lintegral_sq_inv_sqrt_sub_eq_top` — for `y` right-continuous at `0` and `T > 0`,
  `∫_0^T |s^{-1/2} − y(s)|² ds = ∞`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

/-- `s^{-1}` has infinite integral on `(0, ε)`, for `ε > 0`. -/
theorem lintegral_ofReal_inv_Ioo_eq_top {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ s in Ioo (0 : ℝ) ε, ENNReal.ofReal s⁻¹ = ⊤ := by
  have hni : ¬ IntegrableOn (fun x : ℝ => x⁻¹) (Ioo (0 : ℝ) ε) := by
    intro h
    have hr : ¬ IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioo (0 : ℝ) ε) := by
      rw [intervalIntegral.integrableOn_Ioo_rpow_iff hε]
      norm_num
    exact hr (h.congr_fun (fun x _ => (Real.rpow_neg_one x).symm) measurableSet_Ioo)
  by_contra hne
  refine hni ⟨measurable_inv.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lt_top_iff_ne_top]
  convert hne using 1
  refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  rw [← ofReal_norm, Real.norm_of_nonneg (inv_nonneg.mpr hx.1.le)]

/-- `s^{-1/2} = (√s)⁻¹` for `s ≥ 0`. -/
theorem inv_sqrt_eq_rpow {s : ℝ} (hs : 0 ≤ s) : (Real.sqrt s)⁻¹ = s ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hs]

/-- `∫_0^t s^{-1/2} ds = 2√t`, for `t ≥ 0`. -/
theorem integral_inv_sqrt {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Icc (0 : ℝ) t, (Real.sqrt s)⁻¹ = 2 * Real.sqrt t := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_congr (g := fun s => s ^ (-(1 / 2 : ℝ))) fun s hs => by
      simp only [uIcc_of_le ht] at hs
      exact inv_sqrt_eq_rpow hs.1,
    integral_rpow (Or.inl (by norm_num)), Real.zero_rpow (by norm_num), Real.sqrt_eq_rpow]
  norm_num
  ring

/-- `s ↦ s^{-1/2}` is integrable on `[0, T]`. -/
theorem integrableOn_inv_sqrt (T : ℝ) :
    IntegrableOn (fun s => (Real.sqrt s)⁻¹) (Icc (0 : ℝ) T) := by
  rcases le_or_gt 0 T with hT | hT
  · rcases hT.eq_or_lt with h0 | h0
    · subst h0
      simp
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    have h := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -(1 / 2 : ℝ)) h0).mpr
      (by norm_num)
    exact h.congr_fun (fun s hs => (inv_sqrt_eq_rpow hs.1.le).symm) measurableSet_Ioo
  · rw [Icc_eq_empty (not_le.mpr hT)]
    exact integrableOn_empty

/-- **A perturbation of `t^{-1/2}` bounded near `0` is not square integrable**: for `y`
right-continuous at `0` and `T > 0`, `∫_0^T |s^{-1/2} − y(s)|² ds = ∞`. -/
theorem lintegral_sq_inv_sqrt_sub_eq_top {y : ℝ → ℝ} (hy : Tendsto y (𝓝[>] 0) (𝓝 (y 0)))
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ s in Icc (0 : ℝ) T, (‖(Real.sqrt s)⁻¹ - y s‖₊ : ℝ≥0∞) ^ 2 = ⊤ := by
  set M := |y 0| + 1 with hM
  have hMpos : 0 < M := by positivity
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), |y s| ≤ M := by
    filter_upwards [hy.eventually (Metric.closedBall_mem_nhds (y 0) one_pos)] with s hs
    rw [Real.dist_eq] at hs
    have := abs_sub_abs_le_abs_sub (y s) (y 0)
    linarith
  obtain ⟨δ, hδ, hδs⟩ : ∃ δ > 0, ∀ s ∈ Ioo (0 : ℝ) δ, |y s| ≤ M := by
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
    exact ⟨u, hu, fun s hs => hsub hs⟩
  set ε := min (min δ T) (1 / (4 * M ^ 2)) with hε
  have hεpos : 0 < ε := by positivity
  have hεT : ε ≤ T := (min_le_left _ _).trans (min_le_right _ _)
  have key : ∀ s ∈ Ioo (0 : ℝ) ε,
      ENNReal.ofReal (s⁻¹ / 4) ≤ (‖(Real.sqrt s)⁻¹ - y s‖₊ : ℝ≥0∞) ^ 2 := by
    intro s hs
    have hys := hδs s ⟨hs.1, hs.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))⟩
    have hs4 : s < 1 / (4 * M ^ 2) := hs.2.trans_le (min_le_right _ _)
    have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs.1
    have hq : (Real.sqrt s)⁻¹ ^ 2 = s⁻¹ := by rw [inv_pow, Real.sq_sqrt hs.1.le]
    have h2M : 2 * M ≤ (Real.sqrt s)⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hsq]
      have e : (2 * M)⁻¹ = Real.sqrt (1 / (4 * M ^ 2)) := by
        rw [show (1 : ℝ) / (4 * M ^ 2) = ((2 * M)⁻¹) ^ 2 by field_simp; ring,
          Real.sqrt_sq (by positivity)]
      rw [e]
      exact Real.sqrt_le_sqrt hs4.le
    have hlow : (Real.sqrt s)⁻¹ / 2 ≤ |(Real.sqrt s)⁻¹ - y s| := by
      have := abs_le.mp hys
      rw [le_abs]
      left
      linarith
    rw [← enorm_eq_nnnorm, ← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc s⁻¹ / 4 = ((Real.sqrt s)⁻¹ / 2) ^ 2 := by rw [div_pow, hq]; norm_num
      _ ≤ |(Real.sqrt s)⁻¹ - y s| ^ 2 := pow_le_pow_left₀ (by positivity) hlow 2
  refine eq_top_iff.mpr ?_
  calc ⊤ = ∫⁻ s in Ioo (0 : ℝ) ε, ENNReal.ofReal (s⁻¹ / 4) := by
        have e : ∀ s : ℝ,
            ENNReal.ofReal (s⁻¹ / 4) = ENNReal.ofReal (1 / 4) * ENNReal.ofReal s⁻¹ := fun s => by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          ring_nf
        simp_rw [e]
        rw [lintegral_const_mul _ measurable_inv.ennreal_ofReal,
          lintegral_ofReal_inv_Ioo_eq_top hεpos, ENNReal.mul_top (by norm_num)]
    _ ≤ ∫⁻ s in Ioo (0 : ℝ) ε, (‖(Real.sqrt s)⁻¹ - y s‖₊ : ℝ≥0∞) ^ 2 :=
        setLIntegral_mono' measurableSet_Ioo key
    _ ≤ ∫⁻ s in Icc (0 : ℝ) T, (‖(Real.sqrt s)⁻¹ - y s‖₊ : ℝ≥0∞) ^ 2 :=
        lintegral_mono_set fun s hs => ⟨hs.1.le, hs.2.le.trans hεT⟩

end MVFBSDEJ.WellPosedness.System
