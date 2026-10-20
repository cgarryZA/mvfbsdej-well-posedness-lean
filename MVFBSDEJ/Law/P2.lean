/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import MVFBSDEJ.Law.Wasserstein

/-!
# The laws of finite second moment

A law of finite second moment on a normed space `E` is a probability measure whose second moment
about the origin is finite. Bundling those two conditions with the measure gives the type `P2 E`,
on which the squared 2-Wasserstein distance is finite, so the real-valued `w2` is the square root
of that squared distance rather than the value `0` that an infinite squared distance produces.

As for `w2`, reflexivity and symmetry are available for `w2P` here, and on a separable Banach
space so is the triangle inequality, in `MVFBSDEJ/Law/Triangle.lean`; separation, the
vanishing of the distance forcing the two laws to agree, is not established.

## Main definitions

* `MVFBSDEJ.Law.P2`: a probability measure of finite second moment on a normed space.
* `MVFBSDEJ.Law.w2P`: the 2-Wasserstein distance between two laws of finite second moment.
* `MVFBSDEJ.Law.P2.dirac`: the Dirac mass at a point, as a law of finite second moment.
* `MVFBSDEJ.Law.P2.map`: the pushforward of a law of finite second moment along a measurable
  map that does not increase the norm.

## Main statements

* `MVFBSDEJ.Law.w2sq_ne_top`: two laws of finite second moment are at finite squared
  distance.
* `MVFBSDEJ.Law.w2P_self`, `MVFBSDEJ.Law.w2P_comm`: the distance of a law of finite
  second moment from itself vanishes, and the distance is symmetric.
* `MVFBSDEJ.Law.integrable_norm_of_secondMoment_ne_top`: the norm is integrable against a law
  of finite second moment.
* `MVFBSDEJ.Law.integrable_of_norm_sub_le`: a map with a Lipschitz bound is integrable
  against a law of finite second moment.
-/

namespace MVFBSDEJ.Law

open MeasureTheory
open scoped ENNReal

/-- A law of finite second moment on a normed space. -/
structure P2 (E : Type*) [NormedAddCommGroup E] [MeasurableSpace E] where
  /-- The underlying law. -/
  law : Measure E
  /-- The law is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure law
  /-- The second moment of the law about the origin is finite. -/
  secondMoment_ne_top : secondMoment law ≠ ⊤

attribute [instance] P2.isProbabilityMeasure

/-! ### The distance on the laws of finite second moment -/

section Basic

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

/-- The Dirac mass at a point, as a law of finite second moment. -/
noncomputable def P2.dirac [MeasurableSingletonClass E] (a : E) : P2 E where
  law := Measure.dirac a
  isProbabilityMeasure := inferInstance
  secondMoment_ne_top := by simp [secondMoment]

/-- The 2-Wasserstein distance between two laws of finite second moment. -/
noncomputable def w2P (μ ν : P2 E) : ℝ := w2 μ.law ν.law

/-- The 2-Wasserstein distance on the laws of finite second moment is nonnegative. -/
theorem w2P_nonneg (μ ν : P2 E) : 0 ≤ w2P μ ν := w2_nonneg _ _

end Basic

/-! ### Finiteness, symmetry and pushforward -/

section Moments

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- Two laws of finite second moment are at finite squared 2-Wasserstein distance. -/
theorem w2sq_ne_top (μ ν : P2 E) : w2sq μ.law ν.law ≠ ⊤ :=
  w2sq_ne_top_of_secondMoment_ne_top μ.secondMoment_ne_top ν.secondMoment_ne_top

/-- The 2-Wasserstein distance of a law of finite second moment from itself vanishes. -/
theorem w2P_self (μ : P2 E) : w2P μ μ = 0 := w2_self _

/-- The 2-Wasserstein distance on the laws of finite second moment is symmetric. -/
theorem w2P_comm (μ ν : P2 E) : w2P μ ν = w2P ν μ := w2_comm _ _

/-- The pushforward of a law of finite second moment along a measurable map that does not
increase the norm. -/
noncomputable def P2.map {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    (μ : P2 E) {P : E → F} (hP : Measurable P) (hlip : ∀ x, ‖P x‖ ≤ ‖x‖) : P2 F where
  law := μ.law.map P
  isProbabilityMeasure := Measure.isProbabilityMeasure_map hP.aemeasurable
  secondMoment_ne_top := by
    have hmono : secondMoment (μ.law.map P) ≤ secondMoment μ.law := by
      rw [secondMoment, lintegral_map (by fun_prop) hP]
      refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
      nlinarith [hlip x, norm_nonneg x, norm_nonneg (P x)]
    exact ne_top_of_le_ne_top μ.secondMoment_ne_top hmono

end Moments

/-! ### Integrability against a law of finite second moment -/

section Integrability

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- On a law of finite second moment the norm is integrable. -/
theorem integrable_norm_of_secondMoment_ne_top {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : secondMoment μ ≠ ⊤) : Integrable (fun x : E => ‖x‖) μ := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => norm_nonneg x)]
  have hb : ∀ x : E, ENNReal.ofReal ‖x‖ ≤ 1 + ENNReal.ofReal (‖x‖ ^ 2) := by
    intro x
    have h : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
    calc ENNReal.ofReal ‖x‖ ≤ ENNReal.ofReal (1 + ‖x‖ ^ 2) := ENNReal.ofReal_le_ofReal h
      _ = 1 + ENNReal.ofReal (‖x‖ ^ 2) := by
          rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one]
  calc ∫⁻ x, ENNReal.ofReal ‖x‖ ∂μ
      ≤ ∫⁻ x : E, (1 + ENNReal.ofReal (‖x‖ ^ 2)) ∂μ := lintegral_mono hb
    _ = 1 + secondMoment μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul,
          secondMoment]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, lt_of_le_of_ne le_top hμ⟩

variable {F : Type*} [NormedAddCommGroup F]

/-- A map with a Lipschitz bound is integrable against a law of finite second moment. -/
theorem integrable_of_norm_sub_le {φ : E → F} (hφ : StronglyMeasurable φ) {K : ℝ}
    (hlip : ∀ x y, ‖φ x - φ y‖ ≤ K * ‖x - y‖) {μ : Measure E} [IsProbabilityMeasure μ]
    (hμ : secondMoment μ ≠ ⊤) : Integrable φ μ := by
  refine Integrable.mono'
    ((integrable_const ‖φ 0‖).add ((integrable_norm_of_secondMoment_ne_top hμ).const_mul K))
    hφ.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have h1 : ‖φ x‖ ≤ ‖φ 0‖ + ‖φ x - φ 0‖ := by
    calc ‖φ x‖ = ‖φ 0 + (φ x - φ 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖φ 0‖ + ‖φ x - φ 0‖ := norm_add_le _ _
  have h2 := hlip x 0
  simp only [sub_zero] at h2
  simpa using h1.trans (by linarith)

end Integrability

end MVFBSDEJ.Law
