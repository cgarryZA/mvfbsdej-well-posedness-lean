/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.ExpFunctional

/-!
# The finite-activity mark-kernel embedding

Example 5.3 of the well-posedness paper embeds the two-point kernels of the independent-copy
interactions with a finite Lévy measure `ν` into its expectation-functional class. For a
pointwise kernel `ψ̄ : ℝ × H₀ × H₀ → F` on the pointwise space `H₀ = HX × HY × HZY × HV` of the
values `(x, y, z, u(e))`, the mark-integrated kernel on the tuple space
`H = HX × HY × HZY × L²(ν; HV)` is

`φ̄(t, θ, θ') = ∫_E ψ̄(t, x, y, z, u(e), x', y', z', u'(e)) ν(de)`.

The pointwise values `u(e)`, `u'(e)` enter only under the `ν`-integral, so `φ̄` does not depend on
the representatives of the classes `u`, `u'`. The Lipschitz constant of `ψ̄` is taken for the norm
`|p₁ − p₂|₂ + |p'₁ − p'₂|₂` on `H₀ × H₀`, with `|·|₂` the Hilbert norm
`(|x|² + |y|² + |z|²_F + |v|²)^{1/2}` of `H₀`; a kernel Lipschitz for the Euclidean norm of
`H₀ × H₀`, or for the maximum of the two Hilbert norms, is Lipschitz in this sense with the same
constant. With `m = ν(E) < ∞`, Cauchy–Schwarz in `L²(ν)` gives
`∫_E |p_e − q_e|₂ ν(de) ≤ max(m, m^{1/2}) |θ − θ'|_H` for the points `p_e, q_e` of two tuples
`θ, θ'` at the mark `e`, so

`‖φ̄(t, θ₁, θ'₁) − φ̄(t, θ₂, θ'₂)‖ ≤ Lip(ψ̄) max(m, m^{1/2}) (|θ₁ − θ₂|_H + |θ'₁ − θ'₂|_H)`,

the constant of Example 5.3 for the Hilbert norm `|·|_H` of `H`.

## Main definitions

* `pointAt` — the point `(x, y, z, u(e))` of a tuple at a mark.
* `markKernel` — the mark-integrated kernel `φ̄`.

## Main statements

* `sq_integral_le_measureReal_mul_integral_sq` — Cauchy–Schwarz on a finite measure.
* `integral_norm_toL2_pointAt_le` — `∫_E |p_e|₂ ν(de) ≤ max(m, m^{1/2}) |θ|_H`.
* `integrable_markIntegrand` — the integrand of `φ̄` is `ν`-integrable.
* `markKernel_congr` — `φ̄` does not depend on the representatives of the `L²(ν)` channels.
* `kernelLipschitzH_markKernel` — the Lipschitz bound with constant `Lip(ψ̄) max(m, m^{1/2})`.
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.System

/-! ### Cauchy–Schwarz on a finite measure -/

section CauchySchwarz

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [IsFiniteMeasure ν]

/-- **Cauchy–Schwarz on a finite measure**: `(∫ g)² ≤ ν(E) ∫ g²`. -/
theorem sq_integral_le_measureReal_mul_integral_sq {g : E → ℝ} (hg : Integrable g ν)
    (hg2 : Integrable (fun e => g e ^ 2) ν) :
    (∫ e, g e ∂ν) ^ 2 ≤ ν.real Set.univ * ∫ e, g e ^ 2 ∂ν := by
  set m : ℝ := ν.real Set.univ with hm
  set c : ℝ := ∫ e, g e ∂ν with hc
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hexp : ∫ e, (m * g e - c) ^ 2 ∂ν = m * (m * ∫ e, g e ^ 2 ∂ν - c ^ 2) := by
    have hi1 : Integrable (fun e => m ^ 2 * g e ^ 2) ν := hg2.const_mul _
    have hi2 : Integrable (fun e => 2 * m * c * g e) ν := hg.const_mul _
    have hkey : (fun e => (m * g e - c) ^ 2)
        = fun e => (m ^ 2 * g e ^ 2 - 2 * m * c * g e) + c ^ 2 := by
      funext e; ring
    have hi12 : Integrable (fun e => m ^ 2 * g e ^ 2 - 2 * m * c * g e) ν := hi1.sub hi2
    rw [hkey, integral_add hi12 (integrable_const _), integral_sub hi1 hi2,
      integral_const_mul, integral_const_mul, integral_const, smul_eq_mul, ← hm, ← hc]
    ring
  have h0 : 0 ≤ m * (m * ∫ e, g e ^ 2 ∂ν - c ^ 2) :=
    hexp ▸ integral_nonneg fun e => sq_nonneg _
  rcases hm0.lt_or_eq with hpos | hzero
  · have := (mul_nonneg_iff_of_pos_left hpos).mp h0
    linarith
  · have hν : ν = 0 := by
      rw [← Measure.measure_univ_eq_zero]
      have : ν.real Set.univ = 0 := hzero.symm
      rwa [measureReal_def, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)]
        at this
    have hc0 : c = 0 := by rw [hc, hν, integral_zero_measure]
    rw [hc0, ← hzero]
    simp

/-- **Cauchy–Schwarz on a finite measure**, square-root form: `∫ g ≤ ν(E)^{1/2} (∫ g²)^{1/2}`. -/
theorem integral_le_sqrt_measureReal_mul {g : E → ℝ} (hg : Integrable g ν)
    (hg2 : Integrable (fun e => g e ^ 2) ν) :
    ∫ e, g e ∂ν ≤ Real.sqrt (ν.real Set.univ * ∫ e, g e ^ 2 ∂ν) :=
  (le_abs_self _).trans ((Real.sqrt_sq_eq_abs _).symm.le.trans
    (Real.sqrt_le_sqrt (sq_integral_le_measureReal_mul_integral_sq hg hg2)))

end CauchySchwarz

/-! ### The points of a tuple at the marks -/

section Point

variable {E : Type*} [MeasurableSpace E] {ν : Measure E}
  {HX HY HZY HV : Type*} [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [NormedAddCommGroup HZY]
  [InnerProductSpace ℝ HZY] [NormedAddCommGroup HV] [InnerProductSpace ℝ HV]

/-- The point `(x, y, z, u(e))` of the pointwise space `HX × HY × HZY × HV` read off a tuple
`θ = (x, y, z, u)` with `u ∈ L²(ν; HV)` at the mark `e`, through the representative of `u`. -/
noncomputable def pointAt (θ : Tuple HX HY HZY (Lp HV 2 ν)) (e : E) : Tuple HX HY HZY HV :=
  (θ.1, θ.2.1, θ.2.2.1, θ.2.2.2 e)

/-- The squared `L²(ν)` norm is the integral of the squared pointwise norm. -/
theorem norm_sq_eq_integral_norm_sq (w : Lp HV 2 ν) : ‖w‖ ^ 2 = ∫ e, ‖w e‖ ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

/-- The points of a difference of tuples are the differences of the points, `ν`-almost
everywhere. -/
theorem pointAt_sub_ae (θ₁ θ₂ : Tuple HX HY HZY (Lp HV 2 ν)) :
    ∀ᵐ e ∂ν, pointAt (θ₁ - θ₂) e = pointAt θ₁ e - pointAt θ₂ e := by
  filter_upwards [Lp.coeFn_sub θ₁.2.2.2 θ₂.2.2.2] with e he
  simp only [pointAt, Prod.fst_sub, Prod.snd_sub]
  rw [he]
  rfl

/-- The squared Hilbert norm of the point of a tuple at a mark. -/
theorem norm_toL2_pointAt_sq (θ : Tuple HX HY HZY (Lp HV 2 ν)) (e : E) :
    ‖toL2 (pointAt θ e)‖ ^ 2 = ‖θ.1‖ ^ 2 + ‖θ.2.1‖ ^ 2 + ‖θ.2.2.1‖ ^ 2 + ‖θ.2.2.2 e‖ ^ 2 := by
  rw [norm_toL2_sq]
  rfl

variable [MeasurableSpace HV] [BorelSpace HV]

/-- The point of a tuple at the marks is almost everywhere strongly measurable in the mark. -/
theorem aestronglyMeasurable_pointAt (θ : Tuple HX HY HZY (Lp HV 2 ν)) :
    AEStronglyMeasurable (pointAt θ) ν :=
  aestronglyMeasurable_const.prodMk (aestronglyMeasurable_const.prodMk
    (aestronglyMeasurable_const.prodMk (Lp.aestronglyMeasurable θ.2.2.2)))

/-- The squared Hilbert norm of the point of a tuple is integrable over the marks, with integral
`ν(E) (|x|² + |y|² + |z|²_F) + ‖u‖²_{L²(ν)}`. -/
theorem integrable_norm_toL2_pointAt_sq [IsFiniteMeasure ν] (θ : Tuple HX HY HZY (Lp HV 2 ν)) :
    Integrable (fun e => ‖toL2 (pointAt θ e)‖ ^ 2) ν ∧
      ∫ e, ‖toL2 (pointAt θ e)‖ ^ 2 ∂ν
        = ν.real Set.univ * (‖θ.1‖ ^ 2 + ‖θ.2.1‖ ^ 2 + ‖θ.2.2.1‖ ^ 2) + ‖θ.2.2.2‖ ^ 2 := by
  have hu : Integrable (fun e => ‖θ.2.2.2 e‖ ^ 2) ν :=
    (Lp.memLp θ.2.2.2).integrable_norm_pow two_ne_zero
  have hc : Integrable (fun _ : E => ‖θ.1‖ ^ 2 + ‖θ.2.1‖ ^ 2 + ‖θ.2.2.1‖ ^ 2) ν :=
    integrable_const _
  have hfun : (fun e => ‖toL2 (pointAt θ e)‖ ^ 2)
      = fun e => (‖θ.1‖ ^ 2 + ‖θ.2.1‖ ^ 2 + ‖θ.2.2.1‖ ^ 2) + ‖θ.2.2.2 e‖ ^ 2 := by
    funext e; rw [norm_toL2_pointAt_sq]
  rw [hfun]
  refine ⟨hc.add hu, ?_⟩
  rw [integral_add hc hu, integral_const, smul_eq_mul, ← norm_sq_eq_integral_norm_sq]

/-- The Hilbert norm of the point of a tuple is square integrable over the marks. -/
theorem memLp_norm_toL2_pointAt [IsFiniteMeasure ν] (θ : Tuple HX HY HZY (Lp HV 2 ν)) :
    MemLp (fun e => ‖toL2 (pointAt θ e)‖) 2 ν :=
  (memLp_two_iff_integrable_sq
    ((continuous_norm.comp continuous_toL2).comp_aestronglyMeasurable
      (aestronglyMeasurable_pointAt θ))).mpr
    (integrable_norm_toL2_pointAt_sq θ).1

/-- **The mark integral of the point norm**: for `m = ν(E) < ∞`,
`∫_E |p_e|₂ ν(de) ≤ max(m, m^{1/2}) |θ|_H`, with `p_e = (x, y, z, u(e))`. -/
theorem integral_norm_toL2_pointAt_le [IsFiniteMeasure ν] (θ : Tuple HX HY HZY (Lp HV 2 ν)) :
    ∫ e, ‖toL2 (pointAt θ e)‖ ∂ν
      ≤ max (ν.real Set.univ) (Real.sqrt (ν.real Set.univ)) * ‖toL2 θ‖ := by
  set m : ℝ := ν.real Set.univ with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  obtain ⟨hi2, hI⟩ := integrable_norm_toL2_pointAt_sq θ
  have hi := (memLp_norm_toL2_pointAt θ).integrable one_le_two
  refine (integral_le_sqrt_measureReal_mul hi hi2).trans ?_
  rw [hI, ← hm]
  set A : ℝ := ‖θ.1‖ ^ 2 + ‖θ.2.1‖ ^ 2 + ‖θ.2.2.1‖ ^ 2 with hA
  set D : ℝ := ‖θ.2.2.2‖ ^ 2 with hD
  have hA0 : 0 ≤ A := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hθ : ‖toL2 θ‖ ^ 2 = A + D := by rw [norm_toL2_sq, channelSq]
  set M : ℝ := max m (Real.sqrt m) with hMdef
  have hM0 : 0 ≤ M := le_max_of_le_left hm0
  have hM1 : m ≤ M := le_max_left _ _
  have hM2 : Real.sqrt m ≤ M := le_max_right _ _
  have hMsq1 : m * m ≤ M ^ 2 := by nlinarith
  have hMsq2 : m ≤ M ^ 2 := by
    have := Real.sq_sqrt hm0
    nlinarith [Real.sqrt_nonneg m]
  have hle : m * (m * A + D) ≤ (M * ‖toL2 θ‖) ^ 2 := by
    rw [mul_pow, hθ]
    nlinarith [mul_le_mul_of_nonneg_right hMsq1 hA0, mul_le_mul_of_nonneg_right hMsq2 hD0]
  calc Real.sqrt (m * (m * A + D)) ≤ Real.sqrt ((M * ‖toL2 θ‖) ^ 2) := Real.sqrt_le_sqrt hle
    _ = M * ‖toL2 θ‖ := Real.sqrt_sq (by positivity)

/-- **The mark integral of the point distance**: for `m = ν(E) < ∞`,
`∫_E |p_e − q_e|₂ ν(de) ≤ max(m, m^{1/2}) |θ₁ − θ₂|_H`. -/
theorem integral_norm_toL2_pointAt_sub_le [IsFiniteMeasure ν]
    (θ₁ θ₂ : Tuple HX HY HZY (Lp HV 2 ν)) :
    ∫ e, ‖toL2 (pointAt θ₁ e) - toL2 (pointAt θ₂ e)‖ ∂ν
      ≤ max (ν.real Set.univ) (Real.sqrt (ν.real Set.univ)) * ‖toL2 θ₁ - toL2 θ₂‖ := by
  have h : ∫ e, ‖toL2 (pointAt θ₁ e) - toL2 (pointAt θ₂ e)‖ ∂ν
      = ∫ e, ‖toL2 (pointAt (θ₁ - θ₂) e)‖ ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [pointAt_sub_ae θ₁ θ₂] with e he
    rw [he, toL2_sub]
  rw [h, ← toL2_sub]
  exact integral_norm_toL2_pointAt_le _

end Point

/-! ### The mark-integrated kernel -/

section Kernel

variable {E : Type*} [MeasurableSpace E] {ν : Measure E}
  {HX HY HZY HV : Type*} [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [NormedAddCommGroup HZY]
  [InnerProductSpace ℝ HZY] [NormedAddCommGroup HV] [InnerProductSpace ℝ HV]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The mark-integrated kernel of a pointwise kernel `ψ̄ : ℝ × H₀ × H₀ → F`,
`φ̄(t, θ, θ') = ∫_E ψ̄(t, x, y, z, u(e), x', y', z', u'(e)) ν(de)`, on the tuple space
`H = HX × HY × HZY × L²(ν; HV)`. -/
noncomputable def markKernel (ν : Measure E)
    (ψ : ℝ → Tuple HX HY HZY HV → Tuple HX HY HZY HV → F) (t : ℝ)
    (θ θ' : Tuple HX HY HZY (Lp HV 2 ν)) : F :=
  ∫ e, ψ t (pointAt θ e) (pointAt θ' e) ∂ν

/-- **The mark-integrated kernel is well defined on classes**: evaluating the pointwise kernel at
any representatives `v`, `v'` of the `L²(ν)` channels `u`, `u'` gives the same integral. -/
theorem markKernel_congr (ψ : ℝ → Tuple HX HY HZY HV → Tuple HX HY HZY HV → F) (t : ℝ)
    (θ θ' : Tuple HX HY HZY (Lp HV 2 ν)) {v v' : E → HV} (hv : v =ᵐ[ν] θ.2.2.2)
    (hv' : v' =ᵐ[ν] θ'.2.2.2) :
    ∫ e, ψ t (θ.1, θ.2.1, θ.2.2.1, v e) (θ'.1, θ'.2.1, θ'.2.2.1, v' e) ∂ν
      = markKernel ν ψ t θ θ' := by
  refine integral_congr_ae ?_
  filter_upwards [hv, hv'] with e h h'
  simp only [pointAt, h, h']

/-- The Hilbert norm of the origin of the tuple space vanishes. -/
theorem toL2_zero : toL2 (0 : Tuple HX HY HZY HV) = 0 := by
  simpa using toL2_sub (0 : Tuple HX HY HZY HV) 0

variable [MeasurableSpace HX] [MeasurableSpace HY] [MeasurableSpace HZY] [MeasurableSpace HV]
  [BorelSpace HX] [BorelSpace HY] [BorelSpace HZY] [BorelSpace HV]
  [SecondCountableTopology HX] [SecondCountableTopology HY] [SecondCountableTopology HZY]
  [SecondCountableTopology HV]
  {ψ : ℝ → Tuple HX HY HZY HV → Tuple HX HY HZY HV → F} {L : ℝ}

/-- A pointwise kernel Lipschitz for the Hilbert norm is bounded by its value at the origin and
the Hilbert norms of its arguments. -/
theorem KernelLipschitzH.norm_le (hψ : KernelLipschitzH L ψ) (t : ℝ)
    (p p' : Tuple HX HY HZY HV) :
    ‖ψ t p p'‖ ≤ ‖ψ t 0 0‖ + L * (‖toL2 p‖ + ‖toL2 p'‖) := by
  have h := hψ t p 0 p' 0
  rw [toL2_zero, sub_zero, sub_zero] at h
  calc ‖ψ t p p'‖ = ‖ψ t 0 0 + (ψ t p p' - ψ t 0 0)‖ := by rw [add_sub_cancel]
    _ ≤ ‖ψ t 0 0‖ + ‖ψ t p p' - ψ t 0 0‖ := norm_add_le _ _
    _ ≤ ‖ψ t 0 0‖ + L * (‖toL2 p‖ + ‖toL2 p'‖) := by linarith

/-- The integrand of the mark-integrated kernel is `ν`-integrable, for a finite `ν` and a
pointwise kernel Lipschitz for the Hilbert norm. -/
theorem integrable_markIntegrand [IsFiniteMeasure ν] (hL : 0 ≤ L) (hψ : KernelLipschitzH L ψ)
    (t : ℝ) (θ θ' : Tuple HX HY HZY (Lp HV 2 ν)) :
    Integrable (fun e => ψ t (pointAt θ e) (pointAt θ' e)) ν := by
  have hm : AEStronglyMeasurable (fun e => ψ t (pointAt θ e) (pointAt θ' e)) ν :=
    (hψ.continuous hL t).comp_aestronglyMeasurable
      ((aestronglyMeasurable_pointAt θ).prodMk (aestronglyMeasurable_pointAt θ'))
  have hb : Integrable (fun e => ‖ψ t 0 0‖
      + L * (‖toL2 (pointAt θ e)‖ + ‖toL2 (pointAt θ' e)‖)) ν :=
    (integrable_const _).add ((((memLp_norm_toL2_pointAt θ).integrable one_le_two).add
      ((memLp_norm_toL2_pointAt θ').integrable one_le_two)).const_mul L)
  exact hb.mono' hm (ae_of_all _ fun e => hψ.norm_le t _ _)

/-- **The mark-integrated kernel is Lipschitz**, for a finite `ν` with `m = ν(E)` and a pointwise
kernel Lipschitz for the Hilbert norm with constant `Lip(ψ̄) = L`:
`‖φ̄(t, θ₁, θ'₁) − φ̄(t, θ₂, θ'₂)‖ ≤ L max(m, m^{1/2}) (|θ₁ − θ₂|_H + |θ'₁ − θ'₂|_H)`. -/
theorem kernelLipschitzH_markKernel [IsFiniteMeasure ν] (hL : 0 ≤ L)
    (hψ : KernelLipschitzH L ψ) :
    KernelLipschitzH (L * max (ν.real Set.univ) (Real.sqrt (ν.real Set.univ)))
      (markKernel ν ψ) := by
  intro t θ₁ θ₂ θ'₁ θ'₂
  set M : ℝ := max (ν.real Set.univ) (Real.sqrt (ν.real Set.univ)) with hM
  have i1 := integrable_markIntegrand hL hψ t θ₁ θ'₁
  have i2 := integrable_markIntegrand hL hψ t θ₂ θ'₂
  have hg : ∀ θ θ'' : Tuple HX HY HZY (Lp HV 2 ν),
      Integrable (fun e => ‖toL2 (pointAt θ e) - toL2 (pointAt θ'' e)‖) ν := fun θ θ'' =>
    ((memLp_norm_toL2_pointAt (θ - θ'')).integrable one_le_two).congr
      (by filter_upwards [pointAt_sub_ae θ θ''] with e he; rw [he, toL2_sub])
  have hg1 := hg θ₁ θ₂
  have hg2 := hg θ'₁ θ'₂
  rw [markKernel, markKernel, ← integral_sub i1 i2]
  calc ‖∫ e, (ψ t (pointAt θ₁ e) (pointAt θ'₁ e) - ψ t (pointAt θ₂ e) (pointAt θ'₂ e)) ∂ν‖
      ≤ ∫ e, ‖ψ t (pointAt θ₁ e) (pointAt θ'₁ e) - ψ t (pointAt θ₂ e) (pointAt θ'₂ e)‖ ∂ν :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ e, L * (‖toL2 (pointAt θ₁ e) - toL2 (pointAt θ₂ e)‖
          + ‖toL2 (pointAt θ'₁ e) - toL2 (pointAt θ'₂ e)‖) ∂ν :=
        integral_mono (i1.sub i2).norm ((hg1.add hg2).const_mul L) fun e => hψ t _ _ _ _
    _ = L * (∫ e, ‖toL2 (pointAt θ₁ e) - toL2 (pointAt θ₂ e)‖ ∂ν
          + ∫ e, ‖toL2 (pointAt θ'₁ e) - toL2 (pointAt θ'₂ e)‖ ∂ν) := by
        rw [integral_const_mul, integral_add hg1 hg2]
    _ ≤ L * (M * ‖toL2 θ₁ - toL2 θ₂‖ + M * ‖toL2 θ'₁ - toL2 θ'₂‖) := by
        gcongr
        · exact integral_norm_toL2_pointAt_sub_le θ₁ θ₂
        · exact integral_norm_toL2_pointAt_sub_le θ'₁ θ'₂
    _ = L * M * (‖toL2 θ₁ - toL2 θ₂‖ + ‖toL2 θ'₁ - toL2 θ'₂‖) := by ring

/-- The point of a tuple at the marks is measurable in the mark. -/
theorem measurable_pointAt (θ : Tuple HX HY HZY (Lp HV 2 ν)) : Measurable (pointAt θ) :=
  measurable_const.prodMk (measurable_const.prodMk
    (measurable_const.prodMk (Lp.stronglyMeasurable θ.2.2.2).measurable))

variable [IsFiniteMeasure ν] [MeasurableSpace.CountablyGenerated E]

end Kernel

end Dissertation.WellPosedness.System
