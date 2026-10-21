/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.Dealer.Linear

/-!
# Example 5.5: the moments of the linear equation

For a solution `X` of the linear equation of the specialisation with
`∫ η_c² dν = ∫ η_x² dν = 1` and `∫ η_c η_x dν = 0`, the bilinear identity against the constant
solution `1` gives `m(t) = 𝔼 X_t = −∫_0^t m`, and against `X` itself
`v(t) = 𝔼 X_t² = ∫_0^t (−2 v + ¼ + ¼ (1 + v))`, the left limits meeting the path at almost every
time. Weighting by `e^t` and `e^{7t/4}`, `m = 0` and `v(t) = (2/7)(1 − e^{−7t/4})`. At a fixed
time `t ∈ (0, T]` the left limit `X_{t−}` has the same two moments, by dominated convergence along
`X_{s}`, `s ↑ t`, under the running supremum of `X²`.

## Main statements

* `linearFSDEJ_one` — the constant `1` solves the linear forward equation with zero integrands.
* `DealerLinear.expectation_eq_zero` — `𝔼 X_t = 0`.
* `DealerLinear.integral_sq_eq` — `𝔼 X_t² = (2/7)(1 − e^{−7t/4})`.
* `DealerLinear.hasDerivAt_integral_sq` — `v' = −(7/4) v + ½`.
* `DealerLinear.leftLim_moments` — the moments of `X_{t−}`.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped RealInnerProductSpace ENNReal NNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.BrownianPoisson LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

/-! ### The constant solution -/

section One

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

variable (D ℱ hℱW hℱN T) in
/-- **The constant `1` solves the linear forward equation** from `1` with zero integrands. -/
theorem linearFSDEJ_one :
    LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 1) (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => 0)
      (fun _ _ _ => 0) where
  σ_meas _ := measurable_const
  σ_prog _ := Probability.progressivelyMeasurable_const ℱ 0
  σ_vanish _ _ _ := rfl
  σ_sq _ := by simp [Brownian.Ito.energy]
  γ_meas := measurable_const
  γ_prog := Poisson.Compensated.markedProgressivelyMeasurable_zero ℱ
  γ_vanish _ _ _ _ := rfl
  γ_sq := by simp [Poisson.Compensated.markedEnergy]
  b_meas := measurable_const
  b_prog := Probability.progressivelyMeasurable_const ℱ 0
  b_vanish _ _ _ := rfl
  b_sq := by simp [Brownian.Ito.energy]
  ξ₀_sq := memLp_const 1
  X_adapted _ := measurable_const
  X_rightCont _ _ := tendsto_const_nhds
  eqn t ht := by
    have hB := fun i : Fin d => Brownian.Ito.stochasticIntegralBrownian_ae_zero (D.W.W i) ℱ
      (hℱW i) measurable_const (Probability.progressivelyMeasurable_const ℱ 0)
      (fun T _ => by simp) t
    have hN := Poisson.Compensated.stochasticIntegral_ae_zero_of_vanishing D.N hℱN
      (fun _ _ _ => (0 : ℝ)) measurable_const
      (Poisson.Compensated.markedProgressivelyMeasurable_zero ℱ)
      (fun T _ => by simp [Poisson.Compensated.markedEnergy]) ht.1 (fun _ _ _ _ => rfl)
    filter_upwards [ae_all_iff.mpr hB, hN] with ω hω hN
    simp only [Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral,
      Brownian.Ito.stochasticIntegral, Pi.zero_apply] at hω hN ⊢
    rw [Finset.sum_eq_zero fun i _ => hω i, hN]
    simp

end One

/-! ### The moments of the linear equation -/

section Moments

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {ηc ηx : E → ℝ}
  {X : ℝ → Ω → ℝ}

/-- **A linear relation `m(t) = m₀ + ∫_0^t (a m + c)` has the exponential solution.** For
`a ≠ 0`, `m` with `m(t) = m₀ + ∫_0^t (a m(s) + c) ds` on `[0, T]` and `s ↦ a m(s) + c` integrable
on `[0, T]`: `m(t) = (m₀ + c/a) e^{a t} − c/a` on `[0, T]`. -/
theorem eq_of_linear_integral {m : ℝ → ℝ} {m₀ a c : ℝ} (ha : a ≠ 0)
    (hg : MeasureTheory.IntegrableOn (fun s => a * m s + c) (Set.Icc (0 : ℝ) T))
    (hm : ∀ s ∈ Set.Icc (0 : ℝ) T, m s = m₀ + ∫ r in Set.Icc (0 : ℝ) s, (a * m r + c)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, m t = (m₀ + c / a) * Real.exp (a * t) - c / a := by
  intro t ht
  have hwc : ContinuousOn (fun s => Real.exp (-(a * s))) (Set.Icc (0 : ℝ) T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn
  have hw : ∀ x ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s => Real.exp (-(a * s))) (Real.exp (-(a * x)) * (-(a * 1))) x :=
    fun x _ => (((hasDerivAt_id x).const_mul a).neg).exp
  have hw' : ContinuousOn (fun s => Real.exp (-(a * s)) * (-(a * 1))) (Set.Icc (0 : ℝ) T) :=
    hwc.mul continuousOn_const
  have key := mul_eq_add_setIntegral_of_hasDerivAt hg hm hwc hw hw' ht
  have hint : ∀ s, Real.exp (-(a * s)) * (-(a * 1)) * m s + Real.exp (-(a * s)) * (a * m s + c)
      = c * Real.exp (-(a * s)) := fun s => by ring
  simp only [hint] at key
  -- `∫_0^t c e^{−a s} ds = (c/a)(1 − e^{−a t})`
  have hprim : ∫ s in Set.Icc (0 : ℝ) t, c * Real.exp (-(a * s))
      = -(c / a) * Real.exp (-(a * t)) - -(c / a) * Real.exp (-(a * 0)) := by
    refine setIntegral_deriv_eq_sub (w := fun s => -(c / a) * Real.exp (-(a * s)))
      (w' := fun s => c * Real.exp (-(a * s))) (T := t)
      ((continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg)).continuousOn) (fun x _ => ?_)
      ((continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id).neg)).continuousOn) le_rfl ht.1 le_rfl
    refine ((((hasDerivAt_id x).const_mul a).neg).exp.const_mul (-(c / a))).congr_deriv ?_
    simp only [Pi.neg_apply, id, mul_one]
    field_simp
  rw [hprim, show -(a * 0) = 0 by ring, Real.exp_zero, one_mul] at key
  have he : Real.exp (a * t) * Real.exp (-(a * t)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc m t = Real.exp (a * t) * (Real.exp (-(a * t)) * m t) := by
        rw [← mul_assoc, he, one_mul]
    _ = Real.exp (a * t) * (m₀ + (-(c / a) * Real.exp (-(a * t)) - -(c / a) * 1)) := by
        rw [key]
    _ = (m₀ + c / a) * Real.exp (a * t) - c / a * (Real.exp (a * t) * Real.exp (-(a * t))) := by
        ring
    _ = _ := by
        rw [he]
        ring

/-- `∫_E (½ (η_c + η_x a))² dν = ¼ (1 + a²)` when `∫ η_c² = ∫ η_x² = 1` and `∫ η_c η_x = 0`. -/
theorem integral_half_mul_self {ν : Measure E} (hc : MemLp ηc 2 ν) (hx : MemLp ηx 2 ν)
    (hηc : ∫ e, ηc e ^ 2 ∂ν = 1) (hηx : ∫ e, ηx e ^ 2 ∂ν = 1)
    (hηcx : ∫ e, ηc e * ηx e ∂ν = 0) (a : ℝ) :
    ∫ e, 1 / 2 * (ηc e + ηx e * a) * (1 / 2 * (ηc e + ηx e * a)) ∂ν = 1 / 4 * (1 + a ^ 2) := by
  have h1 : Integrable (fun e => ηc e ^ 2) ν := hc.integrable_sq
  have h2 : Integrable (fun e => ηc e * ηx e) ν :=
    Poisson.Compensated.integrable_mul_of_memLp_two hc hx
  have h3 : Integrable (fun e => ηx e ^ 2) ν := hx.integrable_sq
  have e : (fun e => 1 / 2 * (ηc e + ηx e * a) * (1 / 2 * (ηc e + ηx e * a)))
      = fun e => 1 / 4 * ηc e ^ 2 + a / 2 * (ηc e * ηx e) + a ^ 2 / 4 * ηx e ^ 2 := by
    funext e
    ring
  have i1 : Integrable (fun e => 1 / 4 * ηc e ^ 2) ν := h1.const_mul _
  have i2 : Integrable (fun e => a / 2 * (ηc e * ηx e)) ν := h2.const_mul _
  have i3 : Integrable (fun e => a ^ 2 / 4 * ηx e ^ 2) ν := h3.const_mul _
  have i12 : Integrable (fun e => 1 / 4 * ηc e ^ 2 + a / 2 * (ηc e * ηx e)) ν := i1.add i2
  rw [e, integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, hηc, hηx, hηcx]
  ring

/-- **The mean of the linear equation vanishes.** Over a filtration with a cross witness and for
`T > 0`, a solution of the linear equation has `𝔼 X_t = 0` at every `t ∈ [0, T]`. -/
theorem DealerLinear.expectation_eq_zero (h : DealerLinear D ℱ hℱW hℱN T ηc ηx X)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ ω, X t ω ∂P = 0 := by
  have h1 := linearFSDEJ_one D ℱ hℱW hℱN T
  set m : ℝ → ℝ := fun s => ∫ ω, X s ω ∂P with hmdef
  have hrate : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ ω, (X s ω * (fun _ _ => (0 : ℝ)) ω s
          + (fun _ _ => (1 : ℝ)) s ω * (Set.Icc (0 : ℝ) T).indicator (fun s => -X s ω) s) ∂P
        + ∑ j : Fin 1, ∫ ω, (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) s
            * (fun _ _ => (0 : Fin 1 → ℝ)) s ω j ∂P
        + ∫ ω, ∫ e, (Set.Ioc (0 : ℝ) T).indicator (fun s => 1 / 2 * (ηc e + ηx e
            * leftLimProc (fun _ : Fin 1 => X) 0 s ω)) s * (fun _ _ _ => (0 : ℝ)) s ω e ∂ν ∂P)
        = -1 * m s + 0 := by
    intro s hs
    simp only [Set.indicator_of_mem hs, mul_zero, zero_add, one_mul, Pi.zero_apply,
      integral_zero, Finset.sum_const_zero, add_zero, integral_neg, hmdef]
    ring
  have hg : MeasureTheory.IntegrableOn (fun s => -1 * m s + 0) (Set.Icc (0 : ℝ) T) :=
    (LinearFSDEJ.integrableOn_rate h h1 𝒲 hT).congr_fun hrate measurableSet_Icc
  have hm : ∀ s ∈ Set.Icc (0 : ℝ) T, m s = 0 + ∫ r in Set.Icc (0 : ℝ) s, (-1 * m r + 0) := by
    intro s hs
    have key := LinearFSDEJ.integral_mul_eq_at h h1 𝒲 hT hs
    simp only [mul_one, integral_zero, zero_add] at key
    rw [zero_add]
    refine key.trans (setIntegral_congr_fun measurableSet_Icc fun r hr => ?_)
    have := hrate r (Set.Icc_subset_Icc le_rfl hs.2 hr)
    simpa only [mul_zero, zero_add, one_mul] using this
  intro t ht
  have := eq_of_linear_integral (by norm_num : (-1 : ℝ) ≠ 0) hg hm t ht
  simpa using this

/-- The rate of the second moment of the linear equation: at almost every `s ∈ [0, T]` it is
`−(7/4) 𝔼 X_s² + ½`. -/
theorem DealerLinear.ae_rate_eq (h : DealerLinear D ℱ hℱW hℱN T ηc ηx X) (hT : 0 < T)
    (hc : MemLp ηc 2 ν) (hx : MemLp ηx 2 ν) (hηc : ∫ e, ηc e ^ 2 ∂ν = 1)
    (hηx : ∫ e, ηx e ^ 2 ∂ν = 1) (hηcx : ∫ e, ηc e * ηx e ∂ν = 0) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (∫ ω, (X s ω * (Set.Icc (0 : ℝ) T).indicator (fun s => -X s ω) s
          + X s ω * (Set.Icc (0 : ℝ) T).indicator (fun s => -X s ω) s) ∂P
        + ∑ _j : Fin 1, ∫ _ω, (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) s
            * (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) s ∂P
        + ∫ ω, ∫ e, (Set.Ioc (0 : ℝ) T).indicator (fun s => 1 / 2 * (ηc e + ηx e
            * leftLimProc (fun _ : Fin 1 => X) 0 s ω)) s
            * (Set.Ioc (0 : ℝ) T).indicator (fun s => 1 / 2 * (ηc e + ηx e
            * leftLimProc (fun _ : Fin 1 => X) 0 s ω)) s ∂ν ∂P)
        = -(7 / 4) * ∫ ω, X s ω * X s ω ∂P + 1 / 2 := by
  have hI : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Ioo (0 : ℝ) T := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := T)).mem_iff] with s hs hsI
    exact hs.mpr hsI
  filter_upwards [hI, h.ae_ae_leftLimProc_eq hT.le] with s hs hl
  have hIcc : s ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self hs
  have hIoc : s ∈ Set.Ioc (0 : ℝ) T := Set.Ioo_subset_Ioc_self hs
  have hXs : MemLp (X s) 2 P := h.memLp_apply hIcc
  simp only [Set.indicator_of_mem hIcc, Set.indicator_of_mem hIoc, Fin.sum_univ_one,
    integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hj : ∫ ω, ∫ e, 1 / 2 * (ηc e + ηx e * leftLimProc (fun _ : Fin 1 => X) 0 s ω)
        * (1 / 2 * (ηc e + ηx e * leftLimProc (fun _ : Fin 1 => X) 0 s ω)) ∂ν ∂P
      = 1 / 4 + 1 / 4 * ∫ ω, X s ω * X s ω ∂P := by
    rw [integral_congr_ae (hl.mono fun ω hω => by
      rw [integral_half_mul_self hc hx hηc hηx hηcx, hω])]
    have hsq' : ∫ ω, X s ω ^ 2 ∂P = ∫ ω, X s ω * X s ω ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => sq _)
    rw [integral_const_mul, integral_add (integrable_const _) hXs.integrable_sq, integral_const,
      probReal_univ, smul_eq_mul, one_mul, hsq', mul_add, mul_one]
  rw [hj]
  have e2 : (fun ω => X s ω * -X s ω + X s ω * -X s ω) = fun ω => -2 * (X s ω * X s ω) := by
    funext ω
    ring
  rw [e2, integral_const_mul]
  ring

/-- **The second moment of the linear equation.** Over a filtration with a cross witness, for
`T > 0`, `η_c, η_x ∈ L²(ν)` with `∫ η_c² = ∫ η_x² = 1` and `∫ η_c η_x = 0`, a solution of the
linear equation has `𝔼 X_t² = (2/7)(1 − e^{−7t/4})` at every `t ∈ [0, T]`. -/
theorem DealerLinear.integral_sq_eq (h : DealerLinear D ℱ hℱW hℱN T ηc ηx X)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (hc : MemLp ηc 2 ν) (hx : MemLp ηx 2 ν)
    (hηc : ∫ e, ηc e ^ 2 ∂ν = 1) (hηx : ∫ e, ηx e ^ 2 ∂ν = 1)
    (hηcx : ∫ e, ηc e * ηx e ∂ν = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ ω, X t ω ^ 2 ∂P = 2 / 7 * (1 - Real.exp (-(7 / 4) * t)) := by
  set v : ℝ → ℝ := fun s => ∫ ω, X s ω * X s ω ∂P with hvdef
  have hrate := h.ae_rate_eq hT hc hx hηc hηx hηcx
  have hg : MeasureTheory.IntegrableOn (fun s => -(7 / 4) * v s + 1 / 2) (Set.Icc (0 : ℝ) T) :=
    (LinearFSDEJ.integrableOn_rate h h 𝒲 hT).congr_fun_ae hrate
  have hm : ∀ s ∈ Set.Icc (0 : ℝ) T,
      v s = 0 + ∫ r in Set.Icc (0 : ℝ) s, (-(7 / 4) * v r + 1 / 2) := by
    intro s hs
    have key := LinearFSDEJ.integral_mul_eq_at h h 𝒲 hT hs
    simp only [mul_zero, integral_zero, zero_add] at key
    rw [zero_add]
    refine key.trans (setIntegral_congr_ae measurableSet_Icc ?_)
    have hsub : Set.Icc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl hs.2
    have := (ae_restrict_iff' measurableSet_Icc).mp hrate
    filter_upwards [this] with r hr hrs
    exact hr (hsub hrs)
  intro t ht
  have := eq_of_linear_integral (by norm_num : (-(7 / 4) : ℝ) ≠ 0) hg hm t ht
  have e : ∫ ω, X t ω ^ 2 ∂P = v t := integral_congr_ae (Eventually.of_forall fun ω => sq _)
  rw [e, this]
  ring

/-- **The derivative of the second moment of the linear equation**: in the setting of
`DealerLinear.integral_sq_eq`, `v(t) = 𝔼 X_t²` has `v' = −(7/4) v + ½` at every `t ∈ (0, T)`. -/
theorem DealerLinear.hasDerivAt_integral_sq (h : DealerLinear D ℱ hℱW hℱN T ηc ηx X)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (hc : MemLp ηc 2 ν) (hx : MemLp ηx 2 ν)
    (hηc : ∫ e, ηc e ^ 2 ∂ν = 1) (hηx : ∫ e, ηx e ^ 2 ∂ν = 1)
    (hηcx : ∫ e, ηc e * ηx e ∂ν = 0) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun t => ∫ ω, X t ω ^ 2 ∂P)
      (-(7 / 4) * (∫ ω, X t ω ^ 2 ∂P) + 1 / 2) t := by
  have hv := h.integral_sq_eq 𝒲 hT hc hx hηc hηx hηcx
  have hf : HasDerivAt (fun t => 2 / 7 * (1 - Real.exp (-(7 / 4) * t)))
      (2 / 7 * (-(Real.exp (-(7 / 4) * t) * (-(7 / 4) * 1)))) t :=
    ((((hasDerivAt_id t).const_mul (-(7 / 4))).exp).const_sub 1).const_mul (2 / 7)
  have hev : (fun t => ∫ ω, X t ω ^ 2 ∂P) =ᶠ[𝓝 t]
      fun t => 2 / 7 * (1 - Real.exp (-(7 / 4) * t)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact hv r (Set.Ioo_subset_Icc_self hr)
  refine (hf.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hv t (Set.Ioo_subset_Icc_self ht)]
  ring

/-- **The moments of the left limit at a fixed time.** Over a filtration whose null sets lie in
its time-`0` field, whose right-continuation is constant before `0` and which admits a cross
witness, for `T > 0`, `η_c, η_x` as in `DealerLinear.integral_sq_eq` and a solution of the linear
equation with left limits on `(0, T]` along every path: at every `t ∈ (0, T]`, `X_{t−}` is square
integrable with `𝔼 X_{t−} = 0` and `𝔼 X_{t−}² = (2/7)(1 − e^{−7t/4})`. -/
theorem DealerLinear.leftLim_moments (h : DealerLinear D ℱ hℱW hℱN T ηc ηx X)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hc : MemLp ηc 2 ν) (hx : MemLp ηx 2 ν) (hηc : ∫ e, ηc e ^ 2 ∂ν = 1)
    (hηx : ∫ e, ηx e ^ 2 ∂ν = 1) (hηcx : ∫ e, ηc e * ηx e ∂ν = 0)
    (hXl : ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 l))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) T) :
    MemLp (leftLimProc (fun _ : Fin 1 => X) 0 t) 2 P
      ∧ ∫ ω, leftLimProc (fun _ : Fin 1 => X) 0 t ω ∂P = 0
      ∧ ∫ ω, leftLimProc (fun _ : Fin 1 => X) 0 t ω ^ 2 ∂P
        = 2 / 7 * (1 - Real.exp (-(7 / 4) * t)) := by
  set L : Ω → ℝ := leftLimProc (fun _ : Fin 1 => X) 0 t with hLdef
  -- times increasing to `t`
  set sq : ℕ → ℝ := fun n => t - t / ((n : ℝ) + 2) with hsq
  have hsq_mem : ∀ n, sq n ∈ Set.Icc (0 : ℝ) T := fun n => by
    have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h1 : t / ((n : ℝ) + 2) ≤ t := div_le_self ht.1.le (by linarith [n.cast_nonneg (α := ℝ)])
    have h2 : 0 < t / ((n : ℝ) + 2) := div_pos ht.1 hn
    exact ⟨by simp only [hsq]; linarith, by simp only [hsq]; linarith [ht.2]⟩
  have hsq_lt : ∀ n, sq n < t := fun n => by
    have : 0 < t / ((n : ℝ) + 2) := div_pos ht.1 (by positivity)
    simp only [hsq]
    linarith
  have hsq_lim : Tendsto sq atTop (𝓝[<] t) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hsq_lt⟩
    have h0 : Tendsto (fun n : ℕ => t / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    simpa using tendsto_const_nhds.sub h0
  have hconv : ∀ ω, Tendsto (fun n => X (sq n) ω) atTop (𝓝 (L ω)) := fun ω => by
    obtain ⟨l, hl⟩ := hXl ω t ht
    rw [hLdef, leftLimProc, leftLim_eq_of_tendsto hl]
    exact hl.comp hsq_lim
  have hXm : ∀ r, Measurable (X r) := fun r => (h.X_adapted r).mono (ℱ.le r) le_rfl
  have hLm : Measurable L := measurable_of_tendsto_metrizable (fun n => hXm (sq n))
    (tendsto_pi_nhds.mpr hconv)
  -- the running supremum dominates
  set S : Ω → ℝ≥0∞ := fun ω => ⨆ r ∈ Set.Icc (0 : ℝ) T, (‖X r ω‖₊ : ℝ≥0∞) ^ 2 with hS
  have hSm : Measurable S := measurable_biSup_sq_of_rightContinuous hT.le hXm h.X_rightCont
  have hSlt : ∫⁻ ω, S ω ∂P < ⊤ :=
    (h.linearBSDEJ hT.le).lintegral_biSup_sq_lt_top 𝒲 hℱ0 hnull hT
  have hSfin : ∀ᵐ ω ∂P, S ω < ⊤ := ae_lt_top hSm hSlt.ne
  set B : Ω → ℝ := fun ω => (S ω).toReal with hB
  have hBi : Integrable B P := integrable_toReal_of_lintegral_ne_top hSm.aemeasurable hSlt.ne
  have hbound : ∀ᵐ ω ∂P, ∀ r ∈ Set.Icc (0 : ℝ) T, X r ω ^ 2 ≤ B ω := by
    filter_upwards [hSfin] with ω hω r hr
    have hle : (‖X r ω‖₊ : ℝ≥0∞) ^ 2 ≤ S ω :=
      le_iSup₂ (f := fun r (_ : r ∈ Set.Icc (0 : ℝ) T) => (‖X r ω‖₊ : ℝ≥0∞) ^ 2) r hr
    have := ENNReal.toReal_mono hω.ne hle
    simpa [Real.norm_eq_abs, sq_abs] using this
  have hLb : ∀ᵐ ω ∂P, L ω ^ 2 ≤ B ω := by
    filter_upwards [hbound] with ω hω
    exact le_of_tendsto' ((continuous_pow 2).continuousAt.tendsto.comp (hconv ω))
      fun n => hω (sq n) (hsq_mem n)
  have hLsq : Integrable (fun ω => L ω ^ 2) P :=
    hBi.mono' ((hLm.pow_const 2).aestronglyMeasurable)
      (hLb.mono fun ω hω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hω)
  have hL2 : MemLp L 2 P := (memLp_two_iff_integrable_sq hLm.aestronglyMeasurable).mpr hLsq
  refine ⟨hL2, ?_, ?_⟩
  · -- the mean, by dominated convergence under `1 + B`
    have hlim := tendsto_integral_of_dominated_convergence (fun ω => 1 + B ω)
      (F := fun n ω => X (sq n) ω) (f := L) (fun n => (hXm (sq n)).aestronglyMeasurable)
      ((integrable_const 1).add hBi)
      (fun n => by
        filter_upwards [hbound] with ω hω
        have := hω (sq n) (hsq_mem n)
        rw [Real.norm_eq_abs]
        nlinarith [abs_nonneg (X (sq n) ω), sq_abs (X (sq n) ω)])
      (Eventually.of_forall hconv)
    have h0 : (fun n => ∫ ω, X (sq n) ω ∂P) = fun _ => 0 :=
      funext fun n => h.expectation_eq_zero 𝒲 hT (sq n) (hsq_mem n)
    rw [h0] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  · -- the second moment, by dominated convergence under `B`
    have hlim := tendsto_integral_of_dominated_convergence B
      (F := fun n ω => X (sq n) ω ^ 2) (f := fun ω => L ω ^ 2)
      (fun n => ((hXm (sq n)).pow_const 2).aestronglyMeasurable) hBi
      (fun n => by
        filter_upwards [hbound] with ω hω
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hω (sq n) (hsq_mem n))
      (Eventually.of_forall fun ω =>
        (continuous_pow 2).continuousAt.tendsto.comp (hconv ω))
    have hv := h.integral_sq_eq 𝒲 hT hc hx hηc hηx hηcx
    have h1 : (fun n => ∫ ω, X (sq n) ω ^ 2 ∂P)
        = fun n => 2 / 7 * (1 - Real.exp (-(7 / 4) * sq n)) :=
      funext fun n => hv (sq n) (hsq_mem n)
    rw [h1] at hlim
    have hc' : Tendsto (fun n => 2 / 7 * (1 - Real.exp (-(7 / 4) * sq n))) atTop
        (𝓝 (2 / 7 * (1 - Real.exp (-(7 / 4) * t)))) :=
      ((continuous_const.mul (continuous_const.sub (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)))).tendsto t).comp
        (tendsto_nhdsWithin_iff.mp hsq_lim).1
    exact tendsto_nhds_unique hlim hc'

end Moments

end Dissertation.WellPosedness.Existence
