/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Process.Filtration
import Mathlib.Algebra.Order.Chebyshev

/-!
# Bounds on squares of sums and integrals

Elementary inequalities for squares in `[0, ∞]`, used to estimate second moments.

## Main statements

* `sq_setLIntegral_le` — the Cauchy–Schwarz inequality `(∫_S g)² ≤ μ(S) ∫_S g²`.
* `enorm_setIntegral_sq_le` — `‖∫_S f‖² ≤ μ(S) ∫_S ‖f‖²`.
* `lintegral_enorm_sq_lt_top` — an `L²` function has finite `∫ ‖f‖²`.
* `add_sq_le_two_mul_add`, `enorm_add_sq_le` — `(a + b)² ≤ 2 a² + 2 b²`.
* `sq_finsetSum_le_card_mul` — `(∑_{i ∈ s} f_i)² ≤ #s ∑_{i ∈ s} f_i²`.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace Dissertation.WellPosedness

section CauchySchwarz

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- **The Cauchy–Schwarz inequality on a set**: `(∫_S g)² ≤ μ(S) ∫_S g²`. -/
theorem sq_setLIntegral_le {g : α → ℝ≥0∞} (S : Set α) (hg : AEMeasurable g (μ.restrict S)) :
    (∫⁻ x in S, g x ∂μ) ^ 2 ≤ μ S * ∫⁻ x in S, g x ^ 2 ∂μ := by
  have hsqr : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [← ENNReal.rpow_natCast x 2]
    norm_num
  have hhalf : ∀ x : ℝ≥0∞, (x ^ ((1 : ℝ) / 2)) ^ 2 = x := fun x => by
    rw [← ENNReal.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict S) Real.HolderConjugate.two_two hg
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, lintegral_const, Measure.restrict_apply_univ, hsqr, one_pow,
    one_mul] at h
  calc (∫⁻ x in S, g x ∂μ) ^ 2
      ≤ ((∫⁻ x in S, g x ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * μ S ^ ((1 : ℝ) / 2)) ^ 2 :=
        pow_le_pow_left' h 2
    _ = μ S * ∫⁻ x in S, g x ^ 2 ∂μ := by rw [mul_pow, hhalf, hhalf, mul_comm]

/-- **The squared norm of an integral over a set** is at most the measure of the set times the
integral of the squared norm. -/
theorem enorm_setIntegral_sq_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : α → F} (S : Set α) (hf : AEStronglyMeasurable f (μ.restrict S)) :
    ‖∫ x in S, f x ∂μ‖ₑ ^ 2 ≤ μ S * ∫⁻ x in S, ‖f x‖ₑ ^ 2 ∂μ :=
  (pow_le_pow_left' (enorm_integral_le_lintegral_enorm _) 2).trans
    (sq_setLIntegral_le S hf.enorm)

/-- The lower integral of the squared norm of an `L²` function is finite. -/
theorem lintegral_enorm_sq_lt_top {F : Type*} [NormedAddCommGroup F] {f : α → F}
    (hf : MemLp f 2 μ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ⊤ := by
  have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (f := f) (μ := μ) two_ne_zero
    ENNReal.ofNat_ne_top).mp hf.2
  simpa using h

/-- `(a + b)² ≤ 2 a² + 2 b²` in `[0, ∞]`. -/
theorem add_sq_le_two_mul_add (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  norm_num at h
  simpa [mul_add] using h

/-- `‖x + y‖² ≤ 2 ‖x‖² + 2 ‖y‖²`. -/
theorem enorm_add_sq_le {F : Type*} [NormedAddCommGroup F] (x y : F) :
    ‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 :=
  (pow_le_pow_left' (enorm_add_le x y) 2).trans (add_sq_le_two_mul_add _ _)

/-- **The Cauchy–Schwarz inequality for a finite sum** in `[0, ∞]`:
`(∑_{i ∈ s} f_i)² ≤ #s ∑_{i ∈ s} f_i²`. -/
theorem sq_finsetSum_le_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  by_cases h : ∀ i ∈ s, f i ≠ ⊤
  · have hf : ∀ i ∈ s, ((f i).toNNReal : ℝ≥0∞) = f i := fun i hi =>
      ENNReal.coe_toNNReal (h i hi)
    have e1 : ∑ i ∈ s, f i = ((∑ i ∈ s, (f i).toNNReal : NNReal) : ℝ≥0∞) := by
      push_cast
      exact (Finset.sum_congr rfl hf).symm
    have e2 : ∑ i ∈ s, f i ^ 2 = ((∑ i ∈ s, (f i).toNNReal ^ 2 : NNReal) : ℝ≥0∞) := by
      push_cast
      exact Finset.sum_congr rfl fun i hi => by rw [hf i hi]
    rw [e1, e2]
    have := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => (f i).toNNReal)
    exact_mod_cast this
  · push Not at h
    obtain ⟨i, hi, hfi⟩ := h
    have hc : (s.card : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
      exact Finset.ne_empty_of_mem hi
    have htop : ∑ i ∈ s, f i ^ 2 = ⊤ := by
      rw [ENNReal.sum_eq_top]
      exact ⟨i, hi, by simp [hfi]⟩
    rw [htop, ENNReal.mul_top hc]
    exact le_top

end CauchySchwarz

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {H : Type*} [NormedAddCommGroup H]
  [NormedSpace ℝ H] [CompleteSpace H]

variable {ℱ : Filtration ℝ mΩ} {P : Measure Ω} {V : Ω → ℝ → H} {a b : ℝ}

end Dissertation.WellPosedness
