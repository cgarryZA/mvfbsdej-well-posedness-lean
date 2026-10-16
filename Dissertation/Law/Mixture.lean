/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.Cylindrical
import Dissertation.Law.Triangle

/-!
# Law functionals along mixtures

The mixture `(1 − t) μ + t μ'`, `t ∈ [0, 1]`, of two laws of finite second moment is again one.
An expectation functional `μ ↦ ∫ φ dμ` is affine along mixtures, so a law functional that is not
affine along some mixture is no expectation functional, for any integrand `φ`.

A profile read along mixtures at the distances `√t s` cannot be affine unless it is constant: if
`q` is Lipschitz and `q(a) − q(0) = (a/s)² (q(s) − q(0))` for `0 ≤ a ≤ s`, the Lipschitz bound
`|q(s) − q(0)| ≤ Lip(q) s` sends the right-hand side to `0` as `s → ∞`. Along the mixtures
`(1 − t) δ_a + t δ_b` the distance to `δ_a` is `√t |b − a|`.

The vector `(∫ φ_j dμ)_j` of the means of finitely many features is affine along mixtures, so a
cylindrical functional `Q((∫ φ_j dμ)_j)` at the mixture of two Dirac masses is `Q` at the mixture
of their feature vectors.

## Main definitions

* `Dissertation.Law.P2.mix`: the mixture `(1 − t) μ + t μ'` of two laws of finite second moment.
* `Dissertation.Law.AffineAlongMixtures`: a real law functional affine along mixtures.

## Main statements

* `Dissertation.Law.affineAlongMixtures_integral`: an expectation functional is affine along
  mixtures.
* `Dissertation.Law.exists_ne_integral_of_not_affineAlongMixtures`: a law functional not affine
  along mixtures is no expectation functional.
* `Dissertation.Law.w2_dirac_dirac`: the distance of two Dirac masses is that of their points.
* `Dissertation.Law.w2_mix_dirac`, `Dissertation.Law.w2P_mix_dirac`: the distance of the mixture
  `(1 − t) δ_a + t δ_b` to `δ_a` is `√t |b − a|`.
* `Dissertation.Law.not_affineAlongMixtures_of_profile`: a Lipschitz profile `q`, not constant
  on `[0, ∞)`, read along mixtures at the distances `√t s` is not affine along mixtures.
* `Dissertation.Law.cylindricalFunctional_dirac`,
  `Dissertation.Law.cylindricalFunctional_mix_dirac`: a cylindrical functional at a Dirac mass
  and at a mixture of two Dirac masses.
-/

namespace Dissertation.Law

open MeasureTheory
open scoped ENNReal

/-! ### Mixtures -/

section Mix

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

/-- The mixture `(1 − t) μ + t μ'`, `t ∈ [0, 1]`, of two laws of finite second moment. -/
noncomputable def P2.mix (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (μ μ' : P2 E) : P2 E where
  law := ENNReal.ofReal (1 - t) • μ.law + ENNReal.ofReal t • μ'.law
  isProbabilityMeasure := ⟨by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.ofReal_add (by linarith [ht.2]) ht.1, sub_add_cancel, ENNReal.ofReal_one]⟩
  secondMoment_ne_top := by
    rw [secondMoment, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      smul_eq_mul, smul_eq_mul]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top μ.secondMoment_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top μ'.secondMoment_ne_top⟩

/-- The law of the mixture is `(1 − t) μ + t μ'`. -/
theorem P2.mix_law (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (μ μ' : P2 E) :
    (P2.mix t ht μ μ').law = ENNReal.ofReal (1 - t) • μ.law + ENNReal.ofReal t • μ'.law :=
  rfl

/-- A real law functional is affine along mixtures:
`F((1 − t) μ + t μ') = (1 − t) F(μ) + t F(μ')` for all laws `μ, μ'` and `t ∈ [0, 1]`. -/
def AffineAlongMixtures (F : P2 E → ℝ) : Prop :=
  ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (μ μ' : P2 E),
    F (P2.mix t ht μ μ') = (1 - t) * F μ + t * F μ'

/-- The integral against a mixture is the mixture of the integrals. -/
theorem integral_mix {φ : E → ℝ} (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) {μ μ' : P2 E}
    (hμ : Integrable φ μ.law) (hμ' : Integrable φ μ'.law) :
    ∫ x, φ x ∂(P2.mix t ht μ μ').law = (1 - t) * ∫ x, φ x ∂μ.law + t * ∫ x, φ x ∂μ'.law := by
  rw [P2.mix_law, integral_add_measure (hμ.smul_measure ENNReal.ofReal_ne_top)
    (hμ'.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by linarith [ht.2]), ENNReal.toReal_ofReal ht.1, smul_eq_mul,
    smul_eq_mul]

/-- **An expectation functional is affine along mixtures**: `μ ↦ ∫ φ dμ`, for `φ` integrable
against every law of finite second moment. -/
theorem affineAlongMixtures_integral {φ : E → ℝ} (hφ : ∀ μ : P2 E, Integrable φ μ.law) :
    AffineAlongMixtures fun μ : P2 E => ∫ x, φ x ∂μ.law :=
  fun t ht μ μ' => integral_mix t ht (hφ μ) (hφ μ')

/-- **A law functional not affine along mixtures is no expectation functional**: for every `φ`
integrable against every law of finite second moment, `F(μ) ≠ ∫ φ dμ` for some law `μ`. -/
theorem exists_ne_integral_of_not_affineAlongMixtures {F : P2 E → ℝ}
    (hF : ¬ AffineAlongMixtures F) {φ : E → ℝ} (hφ : ∀ μ : P2 E, Integrable φ μ.law) :
    ∃ μ : P2 E, F μ ≠ ∫ x, φ x ∂μ.law := by
  by_contra h
  have hF' : F = fun μ : P2 E => ∫ x, φ x ∂μ.law := funext fun μ => by
    by_contra hμ
    exact h ⟨μ, hμ⟩
  exact hF (hF' ▸ affineAlongMixtures_integral hφ)

end Mix

/-! ### The distance of two Dirac masses -/

section Dirac

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The 2-Wasserstein distance of two Dirac masses is the distance of their points. -/
theorem w2_dirac_dirac (a b : E) : w2 (Measure.dirac a) (Measure.dirac b) = ‖a - b‖ := by
  have hm : Measurable fun x : E => ENNReal.ofReal (‖x - b‖ ^ 2) := by fun_prop
  rw [w2, w2sq_dirac, lintegral_dirac' _ hm, ENNReal.toReal_ofReal (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

/-- **The distance of `(1 − t) δ_a + t δ_b` to `δ_a` is `√t |b − a|`.** -/
theorem w2_mix_dirac (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (a b : E) :
    w2 (ENNReal.ofReal (1 - t) • Measure.dirac a + ENNReal.ofReal t • Measure.dirac b)
      (Measure.dirac a) = Real.sqrt t * ‖b - a‖ := by
  haveI : IsProbabilityMeasure
      (ENNReal.ofReal (1 - t) • Measure.dirac a + ENNReal.ofReal t • Measure.dirac b) :=
    (P2.mix t ht (P2.dirac a) (P2.dirac b)).isProbabilityMeasure
  have hm : Measurable fun x : E => ENNReal.ofReal (‖x - a‖ ^ 2) := by fun_prop
  have h : w2sq (ENNReal.ofReal (1 - t) • Measure.dirac a + ENNReal.ofReal t • Measure.dirac b)
      (Measure.dirac a) = ENNReal.ofReal (t * ‖b - a‖ ^ 2) := by
    rw [w2sq_dirac, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac' _ hm, lintegral_dirac' _ hm, sub_self, norm_zero, smul_eq_mul,
      smul_eq_mul, ← ENNReal.ofReal_mul ht.1]
    simp
  rw [w2, h, ENNReal.toReal_ofReal (mul_nonneg ht.1 (sq_nonneg _)), Real.sqrt_mul ht.1,
    Real.sqrt_sq (norm_nonneg _)]

/-- **The distance of the mixture `(1 − t) δ_a + t δ_b` to `δ_a` is `√t |b − a|`**, for laws of
finite second moment. -/
theorem w2P_mix_dirac (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (a b : E) :
    w2P (P2.mix t ht (P2.dirac a) (P2.dirac b)) (P2.dirac a) = Real.sqrt t * ‖b - a‖ :=
  w2_mix_dirac t ht a b

end Dirac

/-! ### Radial functionals -/

section Radial

/-- **A Lipschitz profile read along the distances `√t s` of mixtures is constant.** If
`q(a) = (1 − (a/s)²) q(0) + (a/s)² q(s)` whenever `0 ≤ a ≤ s`, `s > 0`, and `q` is Lipschitz,
then `q(a) = q(0)` for every `a ≥ 0`. -/
theorem eq_of_mix_profile {q : ℝ → ℝ} {Lq : ℝ} (hq : ∀ r r', |q r - q r'| ≤ Lq * |r - r'|)
    (h : ∀ s a, 0 < s → 0 ≤ a → a ≤ s → q a = (1 - a ^ 2 / s ^ 2) * q 0 + a ^ 2 / s ^ 2 * q s)
    {a : ℝ} (ha : 0 ≤ a) : q a = q 0 := by
  by_contra hne
  have hδ : 0 < |q a - q 0| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set δ := |q a - q 0| with hδdef
  set s := a + a ^ 2 * |Lq| / δ + 1 with hsdef
  have hX : 0 ≤ a ^ 2 * |Lq| / δ := by positivity
  have hs : 0 < s := by linarith
  have has : a ≤ s := by linarith
  have e : q a - q 0 = a ^ 2 / s ^ 2 * (q s - q 0) := by
    rw [h s a hs ha has]
    ring
  have hqs : |q s - q 0| ≤ |Lq| * s := by
    have h1 := hq s 0
    rw [sub_zero, abs_of_pos hs] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hs.le)
  have h1 : δ ≤ a ^ 2 / s ^ 2 * (|Lq| * s) := by
    rw [hδdef, e, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hqs (by positivity)
  have h2 : a ^ 2 / s ^ 2 * (|Lq| * s) = a ^ 2 * |Lq| / s := by
    field_simp
  rw [h2, le_div_iff₀ hs] at h1
  have h3 : a ^ 2 * |Lq| < δ * s := by
    have h4 : a ^ 2 * |Lq| / δ < s := by linarith
    rwa [div_lt_iff₀ hδ, mul_comm s δ] at h4
  linarith

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

/-- **A Lipschitz profile, not constant on `[0, ∞)`, read along mixtures, is not affine.** Let
`F` be a real law functional, and `q` Lipschitz with `q(a) ≠ q(b)` for some `a, b ≥ 0`. If for
every `s > 0` there are laws `μ, μ'` with `F(μ) = q(0)`, `F(μ') = q(s)` and
`F((1 − t) μ + t μ') = q(√t s)` for `t ∈ [0, 1]`, then `F` is not affine along mixtures. -/
theorem not_affineAlongMixtures_of_profile {F : P2 E → ℝ} {q : ℝ → ℝ} {Lq : ℝ}
    (hq : ∀ r r', |q r - q r'| ≤ Lq * |r - r'|) (hne : ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ q a ≠ q b)
    (hprof : ∀ s, 0 < s → ∃ μ μ' : P2 E, F μ = q 0 ∧ F μ' = q s ∧
      ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1), F (P2.mix t ht μ μ') = q (Real.sqrt t * s)) :
    ¬ AffineAlongMixtures F := by
  intro hF
  have h : ∀ s a, 0 < s → 0 ≤ a → a ≤ s →
      q a = (1 - a ^ 2 / s ^ 2) * q 0 + a ^ 2 / s ^ 2 * q s := by
    intro s a hs ha has
    obtain ⟨μ, μ', h0, h1, hmix⟩ := hprof s hs
    have ht : a ^ 2 / s ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one (by positivity)).mpr (by nlinarith)⟩
    have hsq : Real.sqrt (a ^ 2 / s ^ 2) * s = a := by
      rw [← div_pow, Real.sqrt_sq (div_nonneg ha hs.le)]
      field_simp
    have key := hF _ ht μ μ'
    rwa [hmix, hsq, h0, h1] at key
  obtain ⟨a, b, ha, hb, hab⟩ := hne
  exact hab ((eq_of_mix_profile hq h ha).trans (eq_of_mix_profile hq h hb).symm)

variable [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E] [Nontrivial E]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- For `s ≥ 0` a nontrivial real normed space has a point at distance `s` from `c`. -/
theorem exists_norm_sub_eq (c : E) {s : ℝ} (hs : 0 ≤ s) : ∃ y : E, ‖y - c‖ = s := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  refine ⟨c + (s / ‖v‖) • v, ?_⟩
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (div_nonneg hs (norm_nonneg _)),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hv)]

end Radial

/-! ### Cylindrical functionals -/

section Cylindrical

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [MeasurableSingletonClass E]

/-- The integral of a real function against the mixture `(1 − t) δ_u + t δ_{u'}` is
`(1 − t) f(u) + t f(u')`. -/
theorem integral_mix_dirac (f : E → ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (u u' : E) :
    ∫ x, f x ∂(P2.mix t ht (P2.dirac u) (P2.dirac u')).law = (1 - t) * f u + t * f u' := by
  rw [integral_mix t ht (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top)]
  simp only [P2.dirac, integral_dirac]

/-- **The mean feature vector of a mixture of two Dirac masses** is the mixture of the feature
vectors. -/
theorem featureMeans_mix_dirac {J : ℕ} (φ : Fin J → E → ℝ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (u u' : E) :
    (WithLp.toLp 2 fun j => ∫ x, φ j x ∂(P2.mix t ht (P2.dirac u) (P2.dirac u')).law :
        EuclideanSpace ℝ (Fin J))
      = (1 - t) • featureMap φ u + t • featureMap φ u' := by
  refine PiLp.ext fun j => ?_
  simp [featureMap_apply, integral_mix_dirac]

/-- A cylindrical functional at a Dirac mass is the outer function at the feature vector. -/
theorem cylindricalFunctional_dirac {J : ℕ} (Q : EuclideanSpace ℝ (Fin J) → ℝ)
    (φ : Fin J → E → ℝ) (w : E) :
    cylindricalFunctional Q φ (P2.dirac w) = Q (featureMap φ w) := by
  simp only [cylindricalFunctional, P2.dirac, integral_dirac]
  rfl

/-- A cylindrical functional at the mixture `(1 − t) δ_u + t δ_{u'}` is the outer function at the
mixture of the feature vectors. -/
theorem cylindricalFunctional_mix_dirac {J : ℕ} (Q : EuclideanSpace ℝ (Fin J) → ℝ)
    (φ : Fin J → E → ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (u u' : E) :
    cylindricalFunctional Q φ (P2.mix t ht (P2.dirac u) (P2.dirac u'))
      = Q ((1 - t) • featureMap φ u + t • featureMap φ u') := by
  rw [cylindricalFunctional, featureMeans_mix_dirac]

end Cylindrical

end Dissertation.Law
