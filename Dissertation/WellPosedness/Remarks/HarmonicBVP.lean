/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The harmonic two-point problem of Li and Min

The means `x(t) = 𝔼 x_t`, `y(t) = 𝔼 y_t` of a solution of the mean-field system of Example 3.2 of
Li and Min solve the two-point boundary problem

`ẋ = y`, `ẏ = −x`, `x(0) = c`, `y(T) = −x(T)`,

in the integral form `x(t) = c + ∫_0^t β`, `y(t) = −x(T) + ∫_t^T φ` with `β = y` and `φ = x`
almost everywhere on `[0, T]`. Both `x` and `y` are then continuous on `[0, T]` and differentiable
in its interior with `ẋ = y`, `ẏ = −x`, so `A(t) = x(t) cos t − y(t) sin t` has derivative `0`
and `A(T) = A(0) = c`. The terminal condition gives `A(T) = x(T) (cos T + sin T)`, hence

`x(T) (cos T + sin T) = c`.

At `T = 3π/4` the factor `cos T + sin T` vanishes.

## Main statements

* `mul_cos_add_sin_eq_of_integral` — along a solution of the integral form,
  `x(T) (cos T + sin T) = c`.
* `cos_add_sin_three_pi_div_four` — `cos (3π/4) + sin (3π/4) = 0`.
-/

open MeasureTheory Set Filter Topology

namespace Dissertation.WellPosedness.System

/-- **The harmonic invariant of the two-point problem.** Let `T > 0` and let `β, φ` be integrable
on `[0, T]`. If `x(t) = c + ∫_0^t β` and `y(t) = −x(T) + ∫_t^T φ` for `t ∈ [0, T]`, with `β = y`
and `φ = x` almost everywhere on `[0, T]`, then `x(T) (cos T + sin T) = c`. -/
theorem mul_cos_add_sin_eq_of_integral {T c : ℝ} {x y β φ : ℝ → ℝ} (hT : 0 < T)
    (hβ : IntegrableOn β (Icc 0 T)) (hφ : IntegrableOn φ (Icc 0 T))
    (hx : ∀ t ∈ Icc (0 : ℝ) T, x t = c + ∫ s in Icc 0 t, β s)
    (hy : ∀ t ∈ Icc (0 : ℝ) T, y t = -x T + ∫ s in Icc t T, φ s)
    (hβy : β =ᵐ[volume.restrict (Icc 0 T)] y) (hφx : φ =ᵐ[volume.restrict (Icc 0 T)] x) :
    x T * (Real.cos T + Real.sin T) = c := by
  have hTI : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hu : uIcc (0 : ℝ) T = Icc 0 T := uIcc_of_le hT.le
  -- the integral form with interval integrals
  have hx' : ∀ t ∈ Icc (0 : ℝ) T, x t = c + ∫ s in (0 : ℝ)..t, β s := fun t ht => by
    rw [hx t ht, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht.1]
  have hy' : ∀ t ∈ Icc (0 : ℝ) T, y t = -x T + ∫ s in t..T, φ s := fun t ht => by
    rw [hy t ht, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht.2]
  -- continuity on `[0, T]`
  have hxc : ContinuousOn x (Icc 0 T) := by
    have h := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := T)
      (hu ▸ hβ)
    rw [hu] at h
    exact (continuousOn_const.add h).congr hx'
  have hyc : ContinuousOn y (Icc 0 T) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left (a := (0 : ℝ)) (b := T)
      (hu ▸ hφ)
    rw [hu] at h
    exact (continuousOn_const.add h).congr hy'
  -- replace `β` by `y` and `φ` by `x`
  have hβy' : ∀ᵐ s, s ∈ Icc (0 : ℝ) T → β s = y s := (ae_restrict_iff' measurableSet_Icc).mp hβy
  have hφx' : ∀ᵐ s, s ∈ Icc (0 : ℝ) T → φ s = x s := (ae_restrict_iff' measurableSet_Icc).mp hφx
  have hx'' : ∀ t ∈ Icc (0 : ℝ) T, x t = c + ∫ s in (0 : ℝ)..t, y s := fun t ht => by
    rw [hx' t ht, intervalIntegral.integral_congr_ae]
    filter_upwards [hβy'] with s hs hst
    rw [uIoc_of_le ht.1] at hst
    exact hs ⟨hst.1.le, hst.2.trans ht.2⟩
  have hy'' : ∀ t ∈ Icc (0 : ℝ) T, y t = -x T + ∫ s in t..T, x s := fun t ht => by
    rw [hy' t ht, intervalIntegral.integral_congr_ae]
    filter_upwards [hφx'] with s hs hst
    rw [uIoc_of_le ht.2] at hst
    exact hs ⟨ht.1.trans hst.1.le, hst.2⟩
  -- derivatives in the interior
  have hIoo : ∀ t ∈ Ioo (0 : ℝ) T, Icc (0 : ℝ) T ∈ 𝓝 t := fun t ht => Icc_mem_nhds ht.1 ht.2
  have hxd : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt x (y t) t := fun t ht => by
    have h := (intervalIntegral.integral_hasDerivAt_right
      ((hyc.mono (Icc_subset_Icc le_rfl ht.2.le)).intervalIntegrable_of_Icc ht.1.le)
      ((hyc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hyc.continuousAt (hIoo t ht))).const_add c
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hIoo t ht] with u hu using hx'' u hu
  have hyd : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt y (-x t) t := fun t ht => by
    have h := (intervalIntegral.integral_hasDerivAt_left
      ((hxc.mono (Icc_subset_Icc ht.1.le le_rfl)).intervalIntegrable_of_Icc ht.2.le)
      ((hxc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hxc.continuousAt (hIoo t ht))).const_add (-x T)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hIoo t ht] with u hu using hy'' u hu
  -- the invariant `A = x cos − y sin` is constant
  set A : ℝ → ℝ := fun t => x t * Real.cos t - y t * Real.sin t with hA
  have hAc : ContinuousOn A (Icc 0 T) :=
    (hxc.mul Real.continuous_cos.continuousOn).sub (hyc.mul Real.continuous_sin.continuousOn)
  have hAd : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt A 0 t := fun t ht => by
    have h := ((hxd t ht).mul (Real.hasDerivAt_cos t)).sub ((hyd t ht).mul (Real.hasDerivAt_sin t))
    exact h.congr_deriv (by ring)
  obtain ⟨t₀, -, ht₀⟩ := exists_hasDerivAt_eq_slope A (fun _ => (0 : ℝ)) hT hAc hAd
  have hAT : A T = A 0 := by
    rw [sub_zero, eq_comm, div_eq_zero_iff] at ht₀
    rcases ht₀ with h | h
    · linarith
    · exact absurd h hT.ne'
  have hA0 : A 0 = c := by
    simp only [hA, Real.cos_zero, Real.sin_zero, mul_one, mul_zero, sub_zero]
    rw [hx'' 0 h0I, intervalIntegral.integral_same, add_zero]
  have hyT : y T = -x T := by
    rw [hy'' T hTI, intervalIntegral.integral_same, add_zero]
  rw [← hA0, ← hAT]
  simp only [hA, hyT]
  ring

/-- `cos (3π/4) + sin (3π/4) = 0`. -/
theorem cos_add_sin_three_pi_div_four :
    Real.cos (3 * Real.pi / 4) + Real.sin (3 * Real.pi / 4) = 0 := by
  have e : 3 * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
  rw [e, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
  ring

end Dissertation.WellPosedness.System
