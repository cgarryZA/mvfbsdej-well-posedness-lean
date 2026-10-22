/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import MVFBSDEJ.Law.Wasserstein

/-!
# Lipschitz functionals of a law

For a map `φ` satisfying `‖φ x - φ y‖ ≤ K * ‖x - y‖` the gap between the integrals of `φ`
against two laws is controlled by the transport cost of any coupling of those laws: the gap is
at most `K` times the root mean squared displacement of the coupling, by the Lipschitz bound
followed by the inequality between the `L¹` and `L²` norms on a probability space. Taking the
infimum over couplings turns this into a bound by `K` times the 2-Wasserstein distance.

## Main statements

* `MVFBSDEJ.Law.integral_le_sqrt_integral_sq`: on a probability measure a nonnegative
  integrable function has integral at most the square root of the integral of its square.
* `MVFBSDEJ.Law.norm_integral_sub_le_of_isCoupling`: the gap across a coupling is at most
  `K` times the root quadratic transport cost of that coupling.
* `MVFBSDEJ.Law.norm_integral_sub_le_w2`: the gap is at most `K * w2 μ ν`, for a positive
  Lipschitz constant `K` and two laws whose squared 2-Wasserstein distance is finite.
* `MVFBSDEJ.Law.norm_integral_sub_le_w2_of_nonneg`: the same bound for a nonnegative
  Lipschitz constant.
-/

namespace MVFBSDEJ.Law

open MeasureTheory
open scoped ENNReal

/-- On a probability measure a nonnegative integrable function has integral at most the square
root of the integral of its square. -/
theorem integral_le_sqrt_integral_sq {α : Type*} [MeasurableSpace α] {π : Measure α}
    [IsProbabilityMeasure π] {g : α → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hg : Integrable g π)
    (hg2 : Integrable (fun x => g x ^ 2) π) :
    (∫ x, g x ∂π) ≤ Real.sqrt (∫ x, g x ^ 2 ∂π) := by
  set c : ℝ := ∫ x, g x ∂π with hc
  have hc0 : 0 ≤ c := integral_nonneg hg0
  have hsub : Integrable (fun x => g x ^ 2 - 2 * c * g x) π := hg2.sub (hg.const_mul (2 * c))
  have hexp : (∫ x, (g x - c) ^ 2 ∂π) = (∫ x, g x ^ 2 ∂π) - c ^ 2 := by
    have hkey : (fun x => (g x - c) ^ 2) = fun x => (g x ^ 2 - 2 * c * g x) + c ^ 2 := by
      funext x; ring
    rw [hkey, integral_add hsub (integrable_const _),
      integral_sub hg2 (hg.const_mul (2 * c)), integral_const_mul, integral_const]
    have huniv : π.real Set.univ = 1 := by simp
    simp only [smul_eq_mul, huniv]
    ring
  have h0 : 0 ≤ ∫ x, (g x - c) ^ 2 ∂π := integral_nonneg fun x => sq_nonneg _
  have hsq : c ^ 2 ≤ ∫ x, g x ^ 2 ∂π := by rw [hexp] at h0; linarith
  calc c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hc0).symm
    _ ≤ _ := Real.sqrt_le_sqrt hsq

section Coupling

variable {E : Type*} [MeasurableSpace E]

/-- A coupling of a probability measure with another law is a probability measure. -/
theorem isProbabilityMeasure_of_isCoupling {μ ν : Measure E} [IsProbabilityMeasure μ]
    {γ : Measure (E × E)} (hγ : IsCoupling μ ν γ) : IsProbabilityMeasure γ :=
  ⟨by rw [← Measure.fst_univ, hγ.1, measure_univ]⟩

end Coupling

section Cost

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

/-- The quadratic transport cost of a measure with square-integrable displacement is the
nonnegative real Bochner integral of the squared displacement. -/
theorem transportCostSq_toReal {γ : Measure (E × E)}
    (hd : Integrable (fun p : E × E => ‖p.1 - p.2‖ ^ 2) γ) :
    transportCostSq γ = ENNReal.ofReal (∫ p, ‖p.1 - p.2‖ ^ 2 ∂γ) := by
  rw [transportCostSq,
    ← ofReal_integral_eq_lintegral_ofReal hd (Filter.Eventually.of_forall fun p => by positivity)]

variable [BorelSpace E] [SecondCountableTopology E]

/-- A measure on the product of finite quadratic transport cost has square-integrable
displacement. -/
theorem integrable_normSq_of_transportCostSq_ne_top {γ : Measure (E × E)}
    (h : transportCostSq γ ≠ ⊤) : Integrable (fun p : E × E => ‖p.1 - p.2‖ ^ 2) γ := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => by positivity)]
  exact lt_of_le_of_ne le_top h

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The gap between the integrals of a `K`-Lipschitz map against the two marginals of a coupling
is at most `K` times the square root of the quadratic transport cost of that coupling. -/
theorem norm_integral_sub_le_of_isCoupling {μ ν : Measure E} {γ : Measure (E × E)}
    [IsProbabilityMeasure γ] (hγ : IsCoupling μ ν γ) {φ : E → F} (hφ : StronglyMeasurable φ)
    {K : ℝ} (hK : 0 ≤ K) (hlip : ∀ x y, ‖φ x - φ y‖ ≤ K * ‖x - y‖)
    (hiμ : Integrable φ μ) (hiν : Integrable φ ν)
    (hd : Integrable (fun p : E × E => ‖p.1 - p.2‖ ^ 2) γ) :
    ‖(∫ x, φ x ∂μ) - ∫ x, φ x ∂ν‖ ≤ K * Real.sqrt (∫ p, ‖p.1 - p.2‖ ^ 2 ∂γ) := by
  obtain ⟨h1, h2⟩ := hγ
  subst h1; subst h2
  have hfst : (∫ x, φ x ∂γ.fst) = ∫ p, φ p.1 ∂γ := by
    rw [Measure.fst, integral_map measurable_fst.aemeasurable hφ.aestronglyMeasurable]
  have hsnd : (∫ x, φ x ∂γ.snd) = ∫ p, φ p.2 ∂γ := by
    rw [Measure.snd, integral_map measurable_snd.aemeasurable hφ.aestronglyMeasurable]
  have hi1 : Integrable (fun p : E × E => φ p.1) γ := by
    rw [Measure.fst] at hiμ
    exact (integrable_map_measure hφ.aestronglyMeasurable measurable_fst.aemeasurable).mp hiμ
  have hi2 : Integrable (fun p : E × E => φ p.2) γ := by
    rw [Measure.snd] at hiν
    exact (integrable_map_measure hφ.aestronglyMeasurable measurable_snd.aemeasurable).mp hiν
  have hnormint : Integrable (fun p : E × E => ‖p.1 - p.2‖) γ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hd) (by fun_prop) ?_
    filter_upwards with p
    have h := norm_nonneg (p.1 - p.2)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg h]
    nlinarith [sq_nonneg (‖p.1 - p.2‖ - 1)]
  rw [hfst, hsnd, ← integral_sub hi1 hi2]
  calc ‖∫ p, (φ p.1 - φ p.2) ∂γ‖
      ≤ ∫ p, ‖φ p.1 - φ p.2‖ ∂γ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, K * ‖p.1 - p.2‖ ∂γ :=
        integral_mono (hi1.sub hi2).norm (hnormint.const_mul K) fun p => hlip _ _
    _ = K * ∫ p, ‖p.1 - p.2‖ ∂γ := integral_const_mul _ _
    _ ≤ K * Real.sqrt (∫ p, ‖p.1 - p.2‖ ^ 2 ∂γ) :=
        mul_le_mul_of_nonneg_left
          (integral_le_sqrt_integral_sq (fun p => norm_nonneg _) hnormint hd) hK

/-- The gap between the integrals of a `K`-Lipschitz map against two laws is at most `K` times
their 2-Wasserstein distance, for a positive constant `K` and laws at finite squared
2-Wasserstein distance. -/
theorem norm_integral_sub_le_w2 {μ ν : Measure E} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {φ : E → F} (hφ : StronglyMeasurable φ) {K : ℝ} (hK : 0 < K)
    (hlip : ∀ x y, ‖φ x - φ y‖ ≤ K * ‖x - y‖) (hiμ : Integrable φ μ) (hiν : Integrable φ ν)
    (hfin : w2sq μ ν ≠ ⊤) :
    ‖(∫ x, φ x ∂μ) - ∫ x, φ x ∂ν‖ ≤ K * w2 μ ν := by
  set D : ℝ := ‖(∫ x, φ x ∂μ) - ∫ x, φ x ∂ν‖ with hD
  have hD0 : 0 ≤ D := norm_nonneg _
  have key : ENNReal.ofReal (D ^ 2 / K ^ 2) ≤ w2sq μ ν := by
    refine le_iInf₂ fun γ hγ => ?_
    rcases eq_or_ne (transportCostSq γ) ⊤ with htop | htop
    · rw [htop]; exact le_top
    haveI : IsProbabilityMeasure γ := isProbabilityMeasure_of_isCoupling hγ
    have hd := integrable_normSq_of_transportCostSq_ne_top htop
    have hcost : 0 ≤ ∫ p, ‖p.1 - p.2‖ ^ 2 ∂γ := integral_nonneg fun p => by positivity
    have hbd := norm_integral_sub_le_of_isCoupling hγ hφ hK.le hlip hiμ hiν hd
    have hsq : D ^ 2 / K ^ 2 ≤ ∫ p, ‖p.1 - p.2‖ ^ 2 ∂γ := by
      rw [div_le_iff₀ (by positivity)]
      have hs : Real.sqrt (∫ p, ‖p.1 - p.2‖ ^ 2 ∂γ) ^ 2 = ∫ p, ‖p.1 - p.2‖ ^ 2 ∂γ :=
        Real.sq_sqrt hcost
      nlinarith [hbd, hD0, hK.le, Real.sqrt_nonneg (∫ p, ‖p.1 - p.2‖ ^ 2 ∂γ)]
    rw [transportCostSq_toReal hd]
    exact ENNReal.ofReal_le_ofReal hsq
  have hle : D ^ 2 / K ^ 2 ≤ (w2sq μ ν).toReal := by
    have := ENNReal.toReal_mono hfin key
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hw2 : w2 μ ν ^ 2 = (w2sq μ ν).toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have hwn : 0 ≤ w2 μ ν := Real.sqrt_nonneg _
  rw [div_le_iff₀ (by positivity)] at hle
  have h2 : D ^ 2 ≤ (K * w2 μ ν) ^ 2 := by rw [mul_pow, hw2]; nlinarith [hle]
  calc D = Real.sqrt (D ^ 2) := (Real.sqrt_sq hD0).symm
    _ ≤ Real.sqrt ((K * w2 μ ν) ^ 2) := Real.sqrt_le_sqrt h2
    _ = K * w2 μ ν := Real.sqrt_sq (by positivity)

/-- The gap between the integrals of a `K`-Lipschitz map against two laws is at most `K` times
their 2-Wasserstein distance, for a nonnegative constant `K` and laws at finite squared
2-Wasserstein distance. -/
theorem norm_integral_sub_le_w2_of_nonneg {μ ν : Measure E} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {φ : E → F} (hφ : StronglyMeasurable φ) {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ x y, ‖φ x - φ y‖ ≤ K * ‖x - y‖) (hiμ : Integrable φ μ) (hiν : Integrable φ ν)
    (hfin : w2sq μ ν ≠ ⊤) :
    ‖(∫ x, φ x ∂μ) - ∫ x, φ x ∂ν‖ ≤ K * w2 μ ν := by
  have hw : 0 ≤ w2 μ ν := w2_nonneg _ _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ : ℝ := ε / (w2 μ ν + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hlip' : ∀ x y, ‖φ x - φ y‖ ≤ (K + δ) * ‖x - y‖ := by
    intro x y
    have h := hlip x y
    nlinarith [norm_nonneg (x - y)]
  have h := norm_integral_sub_le_w2 hφ (by linarith : (0 : ℝ) < K + δ) hlip' hiμ hiν hfin
  have hle : δ * w2 μ ν ≤ ε := by
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  nlinarith

end Cost

end MVFBSDEJ.Law
