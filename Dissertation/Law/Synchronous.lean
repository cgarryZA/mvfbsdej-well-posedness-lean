/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Dissertation.Law.Wasserstein

/-!
# The synchronous coupling bound

Two random variables `Θ, Θ'` defined on a common probability space realise a coupling of their
laws through their joint law, so the squared 2-Wasserstein distance of the laws is at most the
expected squared distance of the pair.

## Main statements

* `Dissertation.Law.isCoupling_map_prodMk`: the joint law of a pair of random variables couples
  their laws.
* `Dissertation.Law.w2sq_map_le`: the squared 2-Wasserstein distance of the two laws is at most
  the lower integral of the squared distance of the pair.
* `Dissertation.Law.w2_sq_map_le`: the same bound in real form, for a square-integrable
  difference.
-/

namespace Dissertation.Law

open MeasureTheory
open scoped ENNReal

section JointLaw

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] (μ : Measure Ω)

/-- The joint law of a pair of random variables couples their laws. -/
theorem isCoupling_map_prodMk {Θ Θ' : Ω → E} (hΘ : Measurable Θ) (hΘ' : Measurable Θ') :
    IsCoupling (μ.map Θ) (μ.map Θ') (μ.map fun ω => (Θ ω, Θ' ω)) :=
  ⟨Measure.fst_map_prodMk hΘ', Measure.snd_map_prodMk hΘ⟩

end JointLaw

section Bound

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] (μ : Measure Ω)

/-- The squared 2-Wasserstein distance of the laws of two random variables is at most the lower
integral of the squared distance of the pair. -/
theorem w2sq_map_le {Θ Θ' : Ω → E} (hΘ : Measurable Θ) (hΘ' : Measurable Θ') :
    w2sq (μ.map Θ) (μ.map Θ') ≤ ∫⁻ ω, ENNReal.ofReal (‖Θ ω - Θ' ω‖ ^ 2) ∂μ := by
  refine (w2sq_le_transportCostSq (isCoupling_map_prodMk μ hΘ hΘ')).trans ?_
  rw [transportCostSq, lintegral_map measurable_normSq_sub (hΘ.prodMk hΘ')]

/-- The square of the 2-Wasserstein distance of the laws of two random variables with
square-integrable difference is at most the expected squared distance of the pair. -/
theorem w2_sq_map_le {Θ Θ' : Ω → E} (hΘ : Measurable Θ) (hΘ' : Measurable Θ')
    (hint : Integrable (fun ω => ‖Θ ω - Θ' ω‖ ^ 2) μ) :
    w2 (μ.map Θ) (μ.map Θ') ^ 2 ≤ ∫ ω, ‖Θ ω - Θ' ω‖ ^ 2 ∂μ := by
  have hnn : 0 ≤ ∫ ω, ‖Θ ω - Θ' ω‖ ^ 2 ∂μ := integral_nonneg fun ω => by positivity
  have h := w2sq_map_le μ hΘ hΘ'
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => by positivity)] at h
  have h' : (w2sq (μ.map Θ) (μ.map Θ')).toReal ≤ ∫ ω, ‖Θ ω - Θ' ω‖ ^ 2 ∂μ := by
    calc (w2sq (μ.map Θ) (μ.map Θ')).toReal
        ≤ (ENNReal.ofReal (∫ ω, ‖Θ ω - Θ' ω‖ ^ 2 ∂μ)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = _ := ENNReal.toReal_ofReal hnn
  rw [w2, Real.sq_sqrt ENNReal.toReal_nonneg]
  exact h'

end Bound

end Dissertation.Law
