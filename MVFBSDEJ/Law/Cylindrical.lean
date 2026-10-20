/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Law.Projection
import MVFBSDEJ.Law.ExpectationFunctional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Cylindrical functionals of a law

A cylindrical functional of a law is an outer function of the vector of the Bochner means of
finitely many scalar features. Assembling `J` features into a single map into the Euclidean space
of dimension `J` turns termwise Lipschitz bounds for the features into one Lipschitz bound for
that map, with constant the Euclidean norm of the vector of the feature constants. The bound on
the gap between the integrals of a Lipschitz map against two laws then controls the gap between
the two vectors of means by that constant times the 2-Wasserstein distance of the laws, and
composing with the outer function multiplies the constant by the Lipschitz constant of that
function.

## Main definitions

* `MVFBSDEJ.Law.featureMap`: the vector of the values of finitely many scalar features at a
  point.
* `MVFBSDEJ.Law.cylindricalFunctional`: an outer function of the vector of the Bochner means
  of finitely many scalar features against a law of finite second moment.

## Main statements

* `MVFBSDEJ.Law.norm_featureMap_sub_le`: the feature map is Lipschitz with constant the
  Euclidean norm of the vector of the feature constants.
* `MVFBSDEJ.Law.integral_featureMap`: the Bochner mean of the feature map is the vector of
  the Bochner means of the features.
* `MVFBSDEJ.Law.norm_cylindricalFunctional_sub_le`: the gap of a cylindrical functional
  between two laws of finite second moment is at most the constant of the outer function times
  the Euclidean norm of the vector of feature constants times the 2-Wasserstein distance.
-/

namespace MVFBSDEJ.Law

open MeasureTheory
open scoped ENNReal

/-! ### The feature map -/

section Cylindrical

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The vector of the values of `J` scalar features at a point. -/
noncomputable def featureMap {J : ℕ} (φ : Fin J → E → ℝ) (x : E) : EuclideanSpace ℝ (Fin J) :=
  WithLp.toLp 2 fun j => φ j x

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The `j`-th coordinate of the feature map is the value of the `j`-th feature. -/
theorem featureMap_apply {J : ℕ} (φ : Fin J → E → ℝ) (x : E) (j : Fin J) :
    featureMap φ x j = φ j x := rfl

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The feature map of features with termwise Lipschitz bounds is Lipschitz with constant the
Euclidean norm of the vector of those bounds. -/
theorem norm_featureMap_sub_le {J : ℕ} {φ : Fin J → E → ℝ} {K : Fin J → ℝ}
    (hlip : ∀ j x y, |φ j x - φ j y| ≤ K j * ‖x - y‖) (x y : E) :
    ‖featureMap φ x - featureMap φ y‖ ≤ Real.sqrt (∑ j, K j ^ 2) * ‖x - y‖ := by
  rw [EuclideanSpace.norm_eq]
  have h : ∑ j, ‖(featureMap φ x - featureMap φ y) j‖ ^ 2 ≤ (∑ j, K j ^ 2) * ‖x - y‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 : ‖(featureMap φ x - featureMap φ y) j‖ = |φ j x - φ j y| := by
      simp [PiLp.sub_apply, featureMap_apply, Real.norm_eq_abs]
    rw [h1]
    have h2 := hlip j x y
    have h3 : (0 : ℝ) ≤ |φ j x - φ j y| := abs_nonneg _
    nlinarith [norm_nonneg (x - y)]
  calc Real.sqrt (∑ j, ‖(featureMap φ x - featureMap φ y) j‖ ^ 2)
      ≤ Real.sqrt ((∑ j, K j ^ 2) * ‖x - y‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (∑ j, K j ^ 2) * ‖x - y‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
/-- The feature map of strongly measurable features is strongly measurable. -/
theorem stronglyMeasurable_featureMap {J : ℕ} {φ : Fin J → E → ℝ}
    (hm : ∀ j, StronglyMeasurable (φ j)) : StronglyMeasurable (featureMap φ) := by
  have h : Measurable fun x => featureMap φ x := by
    unfold featureMap
    fun_prop
  exact h.stronglyMeasurable

omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
/-- The Bochner mean of the feature map is the vector of the Bochner means of the features. -/
theorem integral_featureMap {J : ℕ} {φ : Fin J → E → ℝ} {μ : Measure E}
    (hint : ∀ j, Integrable (φ j) μ) :
    ∫ x, featureMap φ x ∂μ = WithLp.toLp 2 fun j => ∫ x, φ j x ∂μ := by
  refine PiLp.ext fun j => ?_
  rw [eval_integral_piLp (fun i => hint i) j]
  rfl

/-- A nonlinear cylindrical functional of a law: an outer function of the vector of the Bochner
means of `J` scalar features. -/
noncomputable def cylindricalFunctional {J : ℕ} (q : EuclideanSpace ℝ (Fin J) → ℝ)
    (φ : Fin J → E → ℝ) (μ : P2 E) : ℝ :=
  q (WithLp.toLp 2 fun j => ∫ x, φ j x ∂μ.law)

/-- The gap of a cylindrical functional between two laws of finite second moment is at most the
Lipschitz constant of the outer function times the Euclidean norm of the vector of feature
constants times the 2-Wasserstein distance of the laws. -/
theorem norm_cylindricalFunctional_sub_le {J : ℕ} {q : EuclideanSpace ℝ (Fin J) → ℝ}
    {φ : Fin J → E → ℝ} {Lq : ℝ} {K : Fin J → ℝ} (hLq : 0 ≤ Lq)
    (hq : ∀ v w : EuclideanSpace ℝ (Fin J), |q v - q w| ≤ Lq * ‖v - w‖)
    (hm : ∀ j, StronglyMeasurable (φ j))
    (hlip : ∀ j x y, |φ j x - φ j y| ≤ K j * ‖x - y‖) (μ ν : P2 E) :
    |cylindricalFunctional q φ μ - cylindricalFunctional q φ ν|
      ≤ Lq * Real.sqrt (∑ j, K j ^ 2) * w2P μ ν := by
  have hKK : (0 : ℝ) ≤ Real.sqrt (∑ j, K j ^ 2) := Real.sqrt_nonneg _
  have hΦm : StronglyMeasurable (featureMap φ) := stronglyMeasurable_featureMap hm
  have hΦlip := norm_featureMap_sub_le hlip
  have hiφ : ∀ (j : Fin J) (ρ : P2 E), Integrable (φ j) ρ.law := by
    intro j ρ
    refine integrable_of_norm_sub_le (hm j) (K := K j) (fun x y => ?_) ρ.secondMoment_ne_top
    simpa [Real.norm_eq_abs] using hlip j x y
  have hiΦ : ∀ ρ : P2 E, Integrable (featureMap φ) ρ.law := fun ρ =>
    integrable_of_norm_sub_le hΦm hΦlip ρ.secondMoment_ne_top
  have hint :=
    norm_integral_sub_le_w2_of_nonneg hΦm hKK hΦlip (hiΦ μ) (hiΦ ν) (w2sq_ne_top μ ν)
  rw [integral_featureMap (fun j => hiφ j μ), integral_featureMap (fun j => hiφ j ν)] at hint
  have hqq := hq (WithLp.toLp 2 fun j => ∫ x, φ j x ∂μ.law)
    (WithLp.toLp 2 fun j => ∫ x, φ j x ∂ν.law)
  calc |cylindricalFunctional q φ μ - cylindricalFunctional q φ ν|
      ≤ Lq * ‖(WithLp.toLp 2 fun j => ∫ x, φ j x ∂μ.law)
          - (WithLp.toLp 2 fun j => ∫ x, φ j x ∂ν.law)‖ := hqq
    _ ≤ Lq * (Real.sqrt (∑ j, K j ^ 2) * w2P μ ν) := mul_le_mul_of_nonneg_left hint hLq
    _ = Lq * Real.sqrt (∑ j, K j ^ 2) * w2P μ ν := by ring

end Cylindrical

end MVFBSDEJ.Law
