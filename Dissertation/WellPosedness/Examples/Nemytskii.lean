/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.MarkKernel

/-!
# The Nemytskii jump kernel

In the jump coefficient of the independent-copy interactions the mark is the integrator's and is
not `ν`-integrated, so Example 5.3 of the well-posedness paper embeds a pointwise jump kernel
`h̄ : ℝ × H₀ × H₀ × E → HW`, on the pointwise space `H₀ = HX × HY × HZY × HV`, through the
Nemytskii map on the tuple space `H = HX × HY × HZY × L²(ν; HV)`,

`[H_t(θ, θ')](e) = h̄(t, x, y, z, u(e), x', y', z', u'(e), e)` for `ν`-almost every `e`.

It is well defined on classes: representatives of `u`, `u'` that agree `ν`-almost everywhere give
maps that agree `ν`-almost everywhere. For a finite `ν` with `m = ν(E)`, a kernel `h̄` jointly
strongly measurable in `(p, p', e)`, Lipschitz for the Hilbert norm of `H₀` with a constant `L`
uniform in the time and the mark, and with `h̄(t, 0, 0, ·) ∈ L²(ν; HW)`, the map `H_t(θ, θ')`
lies in `L²(ν; HW)` and

`‖H_t(θ₁, θ'₁) − H_t(θ₂, θ'₂)‖_{L²(ν)} ≤ L max(1, m^{1/2}) (|θ₁ − θ₂|_H + |θ'₁ − θ'₂|_H)`:

the natural quantitative hypothesis the paper imposes on `H_t`.

## Main definitions

* `nemytskiiFun` — the Nemytskii map, as a function of the mark.
* `nemytskii` — its class in `L²(ν; HW)`, and `0` when the map is not square integrable.

## Main statements

* `nemytskiiFun_congr` — the Nemytskii map does not depend on the representatives of the
  `L²(ν)` channels.
* `memLp_nemytskiiFun` — the Nemytskii map is square integrable.
* `norm_toLp_norm_toL2_pointAt_le` — the `L²(ν)` norm of the point norm of a tuple.
* `kernelLipschitzH_nemytskii` — the Lipschitz bound into `L²(ν; HW)`.
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E}
  {HX HY HZY HV : Type*} [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [NormedAddCommGroup HZY]
  [InnerProductSpace ℝ HZY] [NormedAddCommGroup HV] [InnerProductSpace ℝ HV]
  {HW : Type*} [NormedAddCommGroup HW] [InnerProductSpace ℝ HW]

/-- The Nemytskii map `e ↦ h̄(t, x, y, z, u(e), x', y', z', u'(e), e)` of a pointwise jump kernel
`h̄`, at the tuples `θ = (x, y, z, u)`, `θ' = (x', y', z', u')`. -/
noncomputable def nemytskiiFun (h : ℝ → Tuple HX HY HZY HV → Tuple HX HY HZY HV → E → HW)
    (t : ℝ) (θ θ' : Tuple HX HY HZY (Lp HV 2 ν)) : E → HW :=
  fun e => h t (pointAt θ e) (pointAt θ' e) e

/-- **The Nemytskii map is well defined on classes**: evaluating the kernel at any
representatives `v`, `v'` of the `L²(ν)` channels `u`, `u'` gives a map equal to the Nemytskii
map `ν`-almost everywhere. -/
theorem nemytskiiFun_congr (h : ℝ → Tuple HX HY HZY HV → Tuple HX HY HZY HV → E → HW) (t : ℝ)
    (θ θ' : Tuple HX HY HZY (Lp HV 2 ν)) {v v' : E → HV} (hv : v =ᵐ[ν] θ.2.2.2)
    (hv' : v' =ᵐ[ν] θ'.2.2.2) :
    (fun e => h t (θ.1, θ.2.1, θ.2.2.1, v e) (θ'.1, θ'.2.1, θ'.2.2.1, v' e) e)
      =ᵐ[ν] nemytskiiFun h t θ θ' := by
  filter_upwards [hv, hv'] with e h₁ h₂
  simp only [nemytskiiFun, pointAt, h₁, h₂]

open Classical in
/-- The class in `L²(ν; HW)` of the Nemytskii map, and `0` when the map is not square
integrable. -/
noncomputable def nemytskii (h : ℝ → Tuple HX HY HZY HV → Tuple HX HY HZY HV → E → HW) (t : ℝ)
    (θ θ' : Tuple HX HY HZY (Lp HV 2 ν)) : Lp HW 2 ν :=
  if hm : MemLp (nemytskiiFun h t θ θ') 2 ν then hm.toLp _ else 0

/-- For a square-integrable Nemytskii map, `nemytskii` is its class. -/
theorem nemytskii_of_memLp {h : ℝ → Tuple HX HY HZY HV → Tuple HX HY HZY HV → E → HW} {t : ℝ}
    {θ θ' : Tuple HX HY HZY (Lp HV 2 ν)} (hm : MemLp (nemytskiiFun h t θ θ') 2 ν) :
    nemytskii h t θ θ' = hm.toLp _ := by
  unfold nemytskii
  rw [dif_pos hm]

variable [MeasurableSpace HX] [MeasurableSpace HY] [MeasurableSpace HZY] [MeasurableSpace HV]
  [BorelSpace HX] [BorelSpace HY] [BorelSpace HZY] [BorelSpace HV]
  [SecondCountableTopology HX] [SecondCountableTopology HY] [SecondCountableTopology HZY]
  [SecondCountableTopology HV] [IsFiniteMeasure ν]

/-- **The `L²(ν)` norm of the point norm**: for `m = ν(E) < ∞`,
`(∫_E |p_e|₂² ν(de))^{1/2} ≤ max(1, m^{1/2}) |θ|_H`, with `p_e = (x, y, z, u(e))`. -/
theorem norm_toLp_norm_toL2_pointAt_le (θ : Tuple HX HY HZY (Lp HV 2 ν)) :
    ‖(memLp_norm_toL2_pointAt θ).toLp _‖
      ≤ max 1 (Real.sqrt (ν.real Set.univ)) * ‖toL2 θ‖ := by
  set m : ℝ := ν.real Set.univ with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  set G := (memLp_norm_toL2_pointAt θ).toLp _ with hG
  have hsq : ‖G‖ ^ 2 = m * (‖θ.1‖ ^ 2 + ‖θ.2.1‖ ^ 2 + ‖θ.2.2.1‖ ^ 2) + ‖θ.2.2.2‖ ^ 2 := by
    rw [norm_sq_eq_integral_norm_sq, ← (integrable_norm_toL2_pointAt_sq θ).2]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_norm_toL2_pointAt θ).coeFn_toLp] with e he
    rw [he, Real.norm_eq_abs, abs_norm]
  set A : ℝ := ‖θ.1‖ ^ 2 + ‖θ.2.1‖ ^ 2 + ‖θ.2.2.1‖ ^ 2 with hA
  set D : ℝ := ‖θ.2.2.2‖ ^ 2 with hD
  have hA0 : 0 ≤ A := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hθ : ‖toL2 θ‖ ^ 2 = A + D := by rw [norm_toL2_sq, channelSq]
  set M : ℝ := max 1 (Real.sqrt m) with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM2 : Real.sqrt m ≤ M := le_max_right _ _
  have hMm : m ≤ M ^ 2 := by
    have := Real.sq_sqrt hm0
    nlinarith [Real.sqrt_nonneg m]
  have hM1' : 1 ≤ M ^ 2 := by nlinarith
  have hle : ‖G‖ ^ 2 ≤ (M * ‖toL2 θ‖) ^ 2 := by
    rw [hsq, mul_pow, hθ]
    nlinarith [mul_le_mul_of_nonneg_right hMm hA0, mul_le_mul_of_nonneg_right hM1' hD0]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hle

variable {h : ℝ → Tuple HX HY HZY HV → Tuple HX HY HZY HV → E → HW} {L : ℝ}

/-- **The Nemytskii map is square integrable**, for a finite `ν`, a kernel jointly strongly
measurable in `(p, p', e)` and Lipschitz for the Hilbert norm uniformly in the mark, with
`h̄(t, 0, 0, ·) ∈ L²(ν; HW)`. -/
theorem memLp_nemytskiiFun {t : ℝ}
    (hm : StronglyMeasurable fun q : (Tuple HX HY HZY HV × Tuple HX HY HZY HV) × E =>
      h t q.1.1 q.1.2 q.2)
    (hlip : ∀ p₁ p₂ p'₁ p'₂ e, ‖h t p₁ p'₁ e - h t p₂ p'₂ e‖
      ≤ L * (‖toL2 p₁ - toL2 p₂‖ + ‖toL2 p'₁ - toL2 p'₂‖))
    (h0 : MemLp (h t 0 0) 2 ν) (θ θ' : Tuple HX HY HZY (Lp HV 2 ν)) :
    MemLp (nemytskiiFun h t θ θ') 2 ν := by
  have hmeas : AEStronglyMeasurable (nemytskiiFun h t θ θ') ν :=
    (hm.comp_measurable (((measurable_pointAt θ).prodMk (measurable_pointAt θ')).prodMk
      measurable_id)).aestronglyMeasurable
  have hb : MemLp (fun e => ‖h t 0 0 e‖
      + L * (‖toL2 (pointAt θ e)‖ + ‖toL2 (pointAt θ' e)‖)) 2 ν :=
    h0.norm.add (((memLp_norm_toL2_pointAt θ).add (memLp_norm_toL2_pointAt θ')).const_mul L)
  refine hb.of_le hmeas (ae_of_all _ fun e => ?_)
  have hl := hlip (pointAt θ e) 0 (pointAt θ' e) 0 e
  rw [toL2_zero, sub_zero, sub_zero] at hl
  have hL : 0 ≤ L * (‖toL2 (pointAt θ e)‖ + ‖toL2 (pointAt θ' e)‖) :=
    (norm_nonneg _).trans hl
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖nemytskiiFun h t θ θ' e‖
      = ‖h t 0 0 e + (h t (pointAt θ e) (pointAt θ' e) e - h t 0 0 e)‖ := by
        rw [add_sub_cancel]; rfl
    _ ≤ ‖h t 0 0 e‖ + ‖h t (pointAt θ e) (pointAt θ' e) e - h t 0 0 e‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- **The Nemytskii map is Lipschitz into `L²(ν; HW)`**: for a finite `ν` with `m = ν(E)`, a
kernel jointly strongly measurable in `(p, p', e)`, Lipschitz for the Hilbert norm with a
constant `L ≥ 0` uniform in the time and the mark, and with `h̄(t, 0, 0, ·) ∈ L²(ν; HW)` at every
time,
`‖H_t(θ₁, θ'₁) − H_t(θ₂, θ'₂)‖_{L²(ν)} ≤ L max(1, m^{1/2}) (|θ₁ − θ₂|_H + |θ'₁ − θ'₂|_H)`. -/
theorem kernelLipschitzH_nemytskii (hL : 0 ≤ L)
    (hm : ∀ t, StronglyMeasurable fun q : (Tuple HX HY HZY HV × Tuple HX HY HZY HV) × E =>
      h t q.1.1 q.1.2 q.2)
    (hlip : ∀ t p₁ p₂ p'₁ p'₂ e, ‖h t p₁ p'₁ e - h t p₂ p'₂ e‖
      ≤ L * (‖toL2 p₁ - toL2 p₂‖ + ‖toL2 p'₁ - toL2 p'₂‖))
    (h0 : ∀ t, MemLp (h t 0 0) 2 ν) :
    KernelLipschitzH (L * max 1 (Real.sqrt (ν.real Set.univ))) (nemytskii (ν := ν) h) := by
  intro t θ₁ θ₂ θ'₁ θ'₂
  set M : ℝ := max 1 (Real.sqrt (ν.real Set.univ)) with hM
  have m1 := memLp_nemytskiiFun (hm t) (hlip t) (h0 t) θ₁ θ'₁
  have m2 := memLp_nemytskiiFun (hm t) (hlip t) (h0 t) θ₂ θ'₂
  set G := (memLp_norm_toL2_pointAt (θ₁ - θ₂)).toLp _ with hG
  set G' := (memLp_norm_toL2_pointAt (θ'₁ - θ'₂)).toLp _ with hG'
  have hae : ∀ᵐ e ∂ν, ‖(nemytskii h t θ₁ θ'₁ - nemytskii h t θ₂ θ'₂ : Lp HW 2 ν) e‖
      ≤ ‖(L • (G + G') : Lp ℝ 2 ν) e‖ := by
    rw [nemytskii_of_memLp m1, nemytskii_of_memLp m2]
    filter_upwards [Lp.coeFn_sub (m1.toLp _) (m2.toLp _), m1.coeFn_toLp, m2.coeFn_toLp,
      Lp.coeFn_smul L (G + G'), Lp.coeFn_add G G',
      (memLp_norm_toL2_pointAt (θ₁ - θ₂)).coeFn_toLp,
      (memLp_norm_toL2_pointAt (θ'₁ - θ'₂)).coeFn_toLp, pointAt_sub_ae θ₁ θ₂,
      pointAt_sub_ae θ'₁ θ'₂] with e hs h1 h2 hsm had hg hg' hp hp'
    rw [hs, Pi.sub_apply, h1, h2, hsm, Pi.smul_apply, had, Pi.add_apply, hg, hg', hp, hp',
      smul_eq_mul, Real.norm_of_nonneg (by positivity), toL2_sub, toL2_sub]
    exact hlip t _ _ _ _ e
  calc ‖nemytskii h t θ₁ θ'₁ - nemytskii h t θ₂ θ'₂‖ ≤ ‖(L • (G + G') : Lp ℝ 2 ν)‖ :=
        Lp.norm_le_norm_of_ae_le hae
    _ ≤ L * (‖G‖ + ‖G'‖) := by
        rw [norm_smul, Real.norm_of_nonneg hL]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hL
    _ ≤ L * (M * ‖toL2 θ₁ - toL2 θ₂‖ + M * ‖toL2 θ'₁ - toL2 θ'₂‖) := by
        gcongr
        · rw [← toL2_sub]; exact norm_toLp_norm_toL2_pointAt_le _
        · rw [← toL2_sub]; exact norm_toLp_norm_toL2_pointAt_le _
    _ = L * M * (‖toL2 θ₁ - toL2 θ₂‖ + ‖toL2 θ'₁ - toL2 θ'₂‖) := by ring

variable [MeasurableSpace.CountablyGenerated E] [CompleteSpace HW] [SecondCountableTopology HW]
  [MeasurableSpace HW] [BorelSpace HW]

end Dissertation.WellPosedness.System
