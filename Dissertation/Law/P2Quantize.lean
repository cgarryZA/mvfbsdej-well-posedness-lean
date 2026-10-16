/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Dissertation.Law.LawP2
import Dissertation.Law.P2Metric

/-!
# Quantisation of the laws of finite second moment

On a separable normed space `E` the simple function `quant n = SimpleFunc.approxOn id … univ 0 … n`
sends a point to a nearest point among `0` and the first `n` points of a fixed dense sequence of
`E`. It takes finitely many values, `‖quant n x‖ ≤ 2 ‖x‖` and `‖quant n x − x‖ ≤ ‖x‖`, and
`quant n x → x` for every `x`. The quantised law `μ.quantize n` of a law of finite second moment
is the pushforward of `μ` along `quant n`: the finitely supported law
`∑_{y ∈ range (quant n)} μ(quant n ⁻¹' {y}) δ_y`. The synchronous coupling of `x` with
`quant n x` bounds `W₂(μ.quantize n, μ)²` by `∫ ‖quant n x − x‖² dμ`, which tends to `0` by
dominated convergence with the dominating function `‖x‖²`. So every law of finite second moment
is the 2-Wasserstein limit of finitely supported laws, each supported in a finite set independent
of the law, with weights the masses of fixed measurable sets.

## Main definitions

* `Dissertation.Law.P2.mapOfLe`: the pushforward of a law of finite second moment along a
  measurable map with `‖φ x‖ ≤ c ‖x‖`.
* `Dissertation.Law.quant`: the `n`-th quantiser of `E`.
* `Dissertation.Law.P2.quantize`: the `n`-th quantised law.

## Main statements

* `Dissertation.Law.norm_quant_le`, `Dissertation.Law.norm_quant_sub_le`,
  `Dissertation.Law.tendsto_quant`: growth, error bound and convergence of the quantiser.
* `Dissertation.Law.P2.quantize_law`: the quantised law is finitely supported on the range of the
  quantiser.
* `Dissertation.Law.w2sq_quantize_le`: `W₂(μ.quantize n, μ)² ≤ ∫⁻ ‖quant n x − x‖² dμ`.
* `Dissertation.Law.tendsto_w2P_quantize`, `Dissertation.Law.tendsto_quantize`: the quantised
  laws converge to the law in the 2-Wasserstein distance.
-/

namespace Dissertation.Law

open MeasureTheory Filter Topology
open scoped ENNReal

/-! ### Pushforward along a map of linear growth -/

section MapOfLe

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]

/-- The pushforward of a law of finite second moment along a measurable map `φ` with
`‖φ x‖ ≤ c ‖x‖`. -/
noncomputable def P2.mapOfLe (μ : P2 E) {φ : E → F} (hφ : Measurable φ) {c : ℝ}
    (hc : ∀ x, ‖φ x‖ ≤ c * ‖x‖) : P2 F where
  law := μ.law.map φ
  isProbabilityMeasure := Measure.isProbabilityMeasure_map hφ.aemeasurable
  secondMoment_ne_top := by
    have hmono : secondMoment (μ.law.map φ) ≤ ENNReal.ofReal (c ^ 2) * secondMoment μ.law := by
      rw [secondMoment, lintegral_map (by fun_prop) hφ, secondMoment,
        ← lintegral_const_mul _ (by fun_prop)]
      refine lintegral_mono fun x => ?_
      rw [← ENNReal.ofReal_mul (sq_nonneg c)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h0 := norm_nonneg (φ x)
      have h1 := hc x
      nlinarith
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top μ.secondMoment_ne_top)
      hmono

/-- The underlying measure of `μ.mapOfLe hφ hc` is the image measure of `μ` under `φ`. -/
theorem P2.mapOfLe_law (μ : P2 E) {φ : E → F} (hφ : Measurable φ) {c : ℝ}
    (hc : ∀ x, ‖φ x‖ ≤ c * ‖x‖) : (μ.mapOfLe hφ hc).law = μ.law.map φ :=
  rfl

end MapOfLe

/-! ### The quantiser -/

section Quantiser

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The `n`-th quantiser of a separable normed space: the simple function sending a point to a
nearest point among `0` and the first `n` points of a fixed dense sequence. -/
noncomputable def quant (n : ℕ) : SimpleFunc E E :=
  SimpleFunc.approxOn id measurable_id Set.univ 0 (Set.mem_univ 0) n

/-- The quantiser at most doubles the norm. -/
theorem norm_quant_le (n : ℕ) (x : E) : ‖quant n x‖ ≤ 2 * ‖x‖ := by
  have h := SimpleFunc.norm_approxOn_zero_le measurable_id (Set.mem_univ (0 : E)) x n
  rw [two_mul]
  exact h

/-- The quantisation error at a point is at most the norm of the point. -/
theorem norm_quant_sub_le (n : ℕ) (x : E) : ‖quant n x - x‖ ≤ ‖x‖ := by
  have h := NNReal.coe_le_coe.mpr
    (SimpleFunc.nnnorm_approxOn_le measurable_id (Set.mem_univ (0 : E)) x n)
  simp only [coe_nnnorm, id, sub_zero] at h
  exact h

/-- The quantisations of a point converge to the point. -/
theorem tendsto_quant (x : E) : Tendsto (fun n => quant n x) atTop (𝓝 x) :=
  SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ (0 : E))
    (by simp only [id, closure_univ, Set.mem_univ])

/-- The `n`-th quantised law: the pushforward of a law of finite second moment along the `n`-th
quantiser. -/
noncomputable def P2.quantize (n : ℕ) (μ : P2 E) : P2 E :=
  μ.mapOfLe (quant n).measurable (norm_quant_le n)

/-- **The quantised law is finitely supported**: it is
`∑_{y ∈ range (quant n)} μ(quant n ⁻¹' {y}) δ_y`. -/
theorem P2.quantize_law (n : ℕ) (μ : P2 E) :
    (μ.quantize n).law
      = ∑ y ∈ (quant n).range, μ.law (quant n ⁻¹' {y}) • Measure.dirac y := by
  classical
  ext A hA
  rw [P2.quantize, P2.mapOfLe_law, Measure.map_apply (quant n).measurable hA,
    Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul, Set.indicator_apply,
    Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, SimpleFunc.sum_measure_preimage_singleton]
  congr 1
  ext x
  simp [SimpleFunc.mem_range_self]

/-- **The quantisation bound**: `W₂(μ.quantize n, μ)² ≤ ∫⁻ ‖quant n x − x‖² dμ`. -/
theorem w2sq_quantize_le (n : ℕ) (μ : P2 E) :
    w2sq (μ.quantize n).law μ.law ≤ ∫⁻ x, ENNReal.ofReal (‖quant n x - x‖ ^ 2) ∂μ.law := by
  have h := w2sq_map_le μ.law (quant n).measurable measurable_id
  rwa [Measure.map_id] at h

/-- The quadratic quantisation error of a law of finite second moment tends to `0`. -/
theorem tendsto_lintegral_quant (μ : P2 E) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (‖quant n x - x‖ ^ 2) ∂μ.law) atTop (𝓝 0) := by
  have h0 : (0 : ℝ≥0∞) = ∫⁻ _x : E, 0 ∂μ.law := by simp
  rw [h0]
  refine tendsto_lintegral_of_dominated_convergence (fun x => ENNReal.ofReal (‖x‖ ^ 2))
    (fun n => by fun_prop) (fun n => ae_of_all _ fun x => ?_) μ.secondMoment_ne_top
    (ae_of_all _ fun x => ?_)
  · have h := norm_quant_sub_le n x
    have h0 := norm_nonneg (quant n x - x)
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  · have h : Tendsto (fun n => ‖quant n x - x‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_quant x)
    have h2 : Tendsto (fun n => ‖quant n x - x‖ ^ 2) atTop (𝓝 0) := by
      simpa using h.pow 2
    have h3 := (ENNReal.continuous_ofReal.tendsto 0).comp h2
    rw [ENNReal.ofReal_zero] at h3
    exact h3

/-- **The quantised laws converge in the 2-Wasserstein distance**: `W₂(μ.quantize n, μ) → 0`. -/
theorem tendsto_w2P_quantize (μ : P2 E) :
    Tendsto (fun n => w2P (μ.quantize n) μ) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => w2sq (μ.quantize n).law μ.law) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tendsto_lintegral_quant μ)
      (fun n => zero_le) (fun n => w2sq_quantize_le n μ)
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsq
  rw [ENNReal.toReal_zero] at hreal
  have h := (Real.continuous_sqrt.tendsto 0).comp hreal
  rw [Real.sqrt_zero] at h
  exact h

/-- **The quantised laws converge in the 2-Wasserstein space.** -/
theorem tendsto_quantize [CompleteSpace E] (μ : P2 E) :
    Tendsto (fun n => (μ.quantize n).toP2W) atTop (𝓝 μ.toP2W) :=
  P2W.tendsto_toP2W_iff.mpr (tendsto_w2P_quantize μ)

end Quantiser

end Dissertation.Law
