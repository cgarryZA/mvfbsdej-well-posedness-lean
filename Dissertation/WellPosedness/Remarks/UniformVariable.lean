/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Remarks.IntegralTransform
import Dissertation.WellPosedness.Enlarged.Filtration

/-!
# A uniform variable at every positive time

Remark 2.9 of the paper uses that, for `t > 0`, the σ-field `ℱ_t` of the standing basis supports
a variable with the uniform law on `[0, 1]`, a function of the first Brownian coordinate `W¹_t`.
With `Φ` the standard normal distribution function, `W¹_t / √t` has law
`N(0, 1)`, which has no atoms, so `Φ(W¹_t / √t)` is uniform by the probability integral transform
(`Dissertation.Law.map_cdfUnit_comp_eq_volume`); it is `ℱ_t`-measurable whenever `W¹` is adapted
to `ℱ`. Nothing is claimed at `t = 0`, where `W¹_0 = 0` almost surely.

`SupportsUniform ℱ P` records the conclusion: every `ℱ_t`, `t > 0`, carries a uniform variable. It
holds for every filtration to which a Brownian motion is adapted, in particular for the initially
enlarged filtration `enlJoint 𝒢₀ D h𝒢₀` of a Lévy driver with `d ≥ 1` Brownian coordinates, a
filtration of the paper's standing basis; the hypothesis `d ≥ 1` is part of the paper's standing
assumptions.

## Main definitions

* `SupportsUniform` — for every `t > 0`, `ℱ_t` carries a variable with the uniform law on
  `[0, 1]`.

## Main statements

* `map_brownian_div_sqrt` — `W_t / √t` has law `N(0, 1)` for `t > 0`.
* `map_cdfUnit_brownian_eq_volume` — `Φ(W_t / √t)` is uniform on `[0, 1]` for `t > 0`.
* `measurable_cdfUnit_brownian`, `supportsUniform_of_brownian` — it is `ℱ_t`-measurable when `W`
  is adapted to `ℱ`, which then supports a uniform variable at every positive time.
* `supportsUniform_enlJoint` — the initially enlarged filtration supports a uniform variable at
  every positive time.
-/

open MeasureTheory ProbabilityTheory unitInterval
open scoped NNReal

namespace Dissertation.WellPosedness.System

universe u v w

open Dissertation.Law LevyStochCalc

section Brownian

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- For every `t > 0`, the time-`t` field of `ℱ` carries a random variable with the uniform law
on `[0, 1]`. -/
def SupportsUniform (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) : Prop :=
  ∀ t : ℝ, 0 < t → ∃ V : Ω → I, Measurable[ℱ t] V ∧ P.map V = volume

/-- **The law of `W_t / √t` is standard normal** for a Brownian motion `W` and `t > 0`. -/
theorem map_brownian_div_sqrt (W : Brownian.BrownianMotion P) {t : ℝ} (ht : 0 < t) :
    P.map (fun ω => W.W t ω / √t) = gaussianReal 0 1 := by
  have hlaw : P.map (W.W t) = gaussianReal 0 ⟨t, ht.le⟩ := by
    have h := W.increment_gaussian le_rfl ht
    have hae : (fun ω => W.W t ω - W.W 0 ω) =ᵐ[P] W.W t := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω, sub_zero]
    rw [Measure.map_congr hae] at h
    rw [h]
    congr 1
    ext
    simp
  have hdiv : (fun ω => W.W t ω / √t) = (fun x => x / √t) ∘ W.W t := rfl
  rw [hdiv, ← Measure.map_map (by fun_prop : Measurable fun x : ℝ => x / √t)
    (W.measurable_eval t), hlaw, gaussianReal_map_div_const, zero_div]
  congr 1
  ext
  simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one, Real.sq_sqrt ht.le]
  exact div_self ht.ne'

/-- **`Φ(W_t / √t)` is uniform on `[0, 1]`** for a Brownian motion `W` and `t > 0`, with `Φ` the
standard normal distribution function. -/
theorem map_cdfUnit_brownian_eq_volume (W : Brownian.BrownianMotion P) {t : ℝ} (ht : 0 < t) :
    P.map (fun ω => cdfUnit (gaussianReal 0 1) (W.W t ω / √t)) = volume := by
  have hmeas : Measurable fun ω => W.W t ω / √t := (W.measurable_eval t).div_const _
  have h := map_cdfUnit_comp_eq_volume hmeas.aemeasurable (fun x => by
    rw [map_brownian_div_sqrt W ht]
    exact gaussianReal_absolutelyContinuous 0 one_ne_zero (Real.volume_singleton (a := x)))
  rwa [map_brownian_div_sqrt W ht] at h

/-- **`Φ(W_t / √t)` is `ℱ_t`-measurable** when the Brownian motion `W` is adapted to `ℱ`. -/
theorem measurable_cdfUnit_brownian (W : Brownian.BrownianMotion P)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hW : ∀ s, Measurable[ℱ s] (W.W s)) (t : ℝ) :
    Measurable[ℱ t] fun ω => cdfUnit (gaussianReal 0 1) (W.W t ω / √t) :=
  (measurable_cdfUnit _).comp ((hW t).div_const _)

/-- **A filtration carrying a Brownian motion supports a uniform variable at every positive
time**: for `t > 0`, `Φ(W_t / √t)` is `ℱ_t`-measurable and uniform on `[0, 1]`. -/
theorem supportsUniform_of_brownian (W : Brownian.BrownianMotion P)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hW : ∀ s, Measurable[ℱ s] (W.W s)) :
    SupportsUniform ℱ P :=
  fun t ht => ⟨_, measurable_cdfUnit_brownian W hW t, map_cdfUnit_brownian_eq_volume W ht⟩

end Brownian

section Driver

variable {Ω : Type u} {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- **The initially enlarged filtration supports a uniform variable at every positive time**: for
a Lévy driver with `d ≥ 1` Brownian coordinates, a sub-σ-algebra `𝒢₀` and `t > 0`,
`Φ(W¹_t / √t)` is `enlJoint 𝒢₀ D h𝒢₀ t`-measurable and uniform on `[0, 1]`. -/
theorem supportsUniform_enlJoint {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (D : Driver.LevyDriver.{u, v, w} P d ν)
    (h𝒢₀ : 𝒢₀ ≤ mΩ) (hd : 0 < d) :
    SupportsUniform (Enlarged.enlJoint 𝒢₀ D h𝒢₀) P :=
  supportsUniform_of_brownian (D.W.W ⟨0, hd⟩) fun s =>
    ((D.isBrownianFiltration ⟨0, hd⟩).measurable s).mono
      (Enlarged.filtration_le_enlJoint D h𝒢₀ s) le_rfl

end Driver

end Dissertation.WellPosedness.System
