/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.PaperSolutionForced

/-!
# Stochastic integrals of equal integrands

The Brownian integral and the compensated Poisson integral take the proofs of the measurability
and square integrability of the integrand as arguments. Two equal integrands have equal
stochastic integrals, whatever these proofs. At `λ = 1` and `q = 0`, for instance, the forced
integrands `1 · ψ + 0` of the `λ`-forced system (4.1) are the coefficient processes `ψ` of (1.1),
but the proofs about them are proofs about different terms.

## Main statements

* `multidimStochasticIntegral_eq_of_integrand_eq`, `compensatedIntegral_eq_of_integrand_eq` —
  equal integrands have equal stochastic integrals.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}

/-! ### Stochastic integrals of equal integrands -/

/-- **Equal integrands have equal Brownian integrals**: the multidimensional Itô integral of `Z`
does not depend on the proofs of the measurability and square integrability of `Z`. -/
theorem multidimStochasticIntegral_eq_of_integrand_eq {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (W : Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : ∀ j : Fin d, Brownian.IsBrownianFiltration (W.W j) ℱ) {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)}
    (h : Z₁ = Z₂)
    (hm₁ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z₁ s ω j))
    (hp₁ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₁ s ω j)
    (hq₁ : ∀ (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z₁ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z₂ s ω j))
    (hp₂ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₂ s ω j)
    (hq₂ : ∀ (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z₁ hm₁ hp₁ hq₁
      = Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z₂ hm₂ hp₂ hq₂ := by
  subst h
  rfl

/-- **Equal integrands have equal compensated Poisson integrals**: the integral of `φ` against
the compensated Poisson random measure does not depend on the proofs of the measurability and
square integrability of `φ`. -/
theorem compensatedIntegral_eq_of_integrand_eq {P : Measure Ω} [IsProbabilityMeasure P]
    [SigmaFinite ν] (N : Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : Poisson.IsPoissonFiltration N ℱ)
    {φ₁ φ₂ : Ω → ℝ → E → ℝ} (h : φ₁ = φ₂)
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hp₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (hq₁ : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hp₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (hq₂ : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    Poisson.Compensated.stochasticIntegral N ℱ hℱ φ₁ hm₁ hp₁ hq₁
      = Poisson.Compensated.stochasticIntegral N ℱ hℱ φ₂ hm₂ hp₂ hq₂ := by
  subst h
  rfl

end MVFBSDEJ.WellPosedness.System
