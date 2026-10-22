/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Law.Cylindrical
import MVFBSDEJ.Law.Triangle

/-!
# Law functionals along mixtures

The mixture `(1 − t) μ + t μ'`, `t ∈ [0, 1]`, of two laws of finite second moment is again one.
An expectation functional `μ ↦ ∫ φ dμ` is affine along mixtures, so a law functional that is not
affine along some mixture is no expectation functional, for any integrand `φ`.

The 2-Wasserstein distance of two Dirac masses is the distance of their points.

## Main definitions

* `MVFBSDEJ.Law.P2.mix`: the mixture `(1 − t) μ + t μ'` of two laws of finite second moment.
* `MVFBSDEJ.Law.AffineAlongMixtures`: a real law functional affine along mixtures.

## Main statements

* `MVFBSDEJ.Law.affineAlongMixtures_integral`: an expectation functional is affine along
  mixtures.
* `MVFBSDEJ.Law.exists_ne_integral_of_not_affineAlongMixtures`: a law functional not affine
  along mixtures is no expectation functional.
* `MVFBSDEJ.Law.w2_dirac_dirac`: the distance of two Dirac masses is that of their points.
-/

namespace MVFBSDEJ.Law

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

end Dirac

end MVFBSDEJ.Law
