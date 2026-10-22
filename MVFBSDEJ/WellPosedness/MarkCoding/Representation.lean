/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.MarkCoding.Coding
import MVFBSDEJ.WellPosedness.MarkCoding.Integral
import LevyStochCalc.Driver.PredictableRepresentation

/-!
# Transport of the separation property along a map of the marks

Let `D = (W, N)` be a Lévy driver with mark space `(E, ℰ)` and σ-finite intensity `ν`, and let
`φ : E → F` be a measurable map of the marks, such as the coding map `E → (ℕ → Bool)` of a
countably generated mark space. An admissible marked integrand `K` for the driver
`(W, (id × φ)_* N)` with pushed-forward marks, read through `φ`, is an admissible marked
integrand for `D` with the same energy, and its compensated integral against `N` is almost surely
that of `K` against `(id × φ)_* N`. Hence a weight orthogonal to the time-`0` weights and to the
integral ranges of `D` over a filtration is orthogonal to those of the driver with pushed-forward
marks, so a separation property of that driver passes to `D`.

## Main definitions

* `pullMarkedHorizonIntegrand` — a marked horizon integrand on the image marks read through the
  mark map, for an equal filtration.

## Main statements

* `integral_pullMarkedHorizonIntegrand` — its compensated integral against `N` is that of the
  integrand against the image of `N`.
* `ae_eq_zero_of_perp_of_mapMarks` — the separation property of the driver with pushed-forward
  marks gives the one of the driver.
-/

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.MarkCoding

open LevyStochCalc LevyStochCalc.Poisson LevyStochCalc.Driver LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v v' w

section Transport

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}

variable {E : Type v} [MeasurableSpace E] {F : Type v'} [MeasurableSpace F] {ν : Measure E}
  {φ : E → F}

/-- A marked horizon integrand on the image marks, read through the mark map, as a marked
horizon integrand for an equal filtration. -/
def pullMarkedHorizonIntegrand (hφ : Measurable φ) {ℱ₁ ℱ₂ : Filtration ℝ ‹MeasurableSpace Ω›}
    (h : ℱ₁ = ℱ₂) (K : MarkedHorizonIntegrand P (ν.map φ) ℱ₁ T) :
    MarkedHorizonIntegrand P ν ℱ₂ T where
  toFun := pullMarks φ K.toFun
  measurable_uncurry := measurable_pullMarks hφ K.measurable_uncurry
  progressive := by
    subst h
    exact markedProgressivelyMeasurable_pullMarks hφ K.progressive
  vanishing ω s e hs := K.vanishing ω s (φ e) hs
  energy_ne_top := by
    rw [markedEnergy_pullMarks hφ K.measurable_uncurry]
    exact K.energy_ne_top

/-- The compensated integral against `N` of a marked horizon integrand read through the mark map
is almost surely the compensated integral of the integrand against the image of `N`. -/
theorem integral_pullMarkedHorizonIntegrand [SigmaFinite ν] (hφ : Measurable φ)
    [SigmaFinite (ν.map φ)] {ℱ₁ ℱ₂ : Filtration ℝ ‹MeasurableSpace Ω›} (h : ℱ₁ = ℱ₂)
    (N : PoissonRandomMeasure.{u, v, w} P ν) (hN₂ : IsPoissonFiltration N ℱ₂)
    (hN₁ : IsPoissonFiltration (PoissonRandomMeasure.mapMarks N hφ) ℱ₁)
    (K : MarkedHorizonIntegrand P (ν.map φ) ℱ₁ T) :
    (pullMarkedHorizonIntegrand hφ h K).integral N hN₂
      =ᵐ[P] K.integral (PoissonRandomMeasure.mapMarks N hφ) hN₁ := by
  subst h
  exact stochasticIntegral_pullMarks N hφ ℱ₁ hN₂ K.measurable_uncurry K.progressive
    K.sq_int_global T

end Transport

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

variable {F : Type v'} [MeasurableSpace F] {φ : E → F}

/-- **Separation transfers along a map of the marks.** Let `ℱ` carry the driver `D` and the
equal filtration `ℱ'` carry the driver with its marks pushed forward along `φ`. If the only
square-integrable weight measurable for `ℱ'_T` and orthogonal to every bounded
`ℱ'_0`-measurable weight and to both integral ranges of the pushed-forward driver over `ℱ'` is
the zero weight, then the same holds for `D` over `ℱ`. -/
theorem ae_eq_zero_of_perp_of_mapMarks {D : LevyDriver.{u, v, w} P d ν} (hφ : Measurable φ)
    [SigmaFinite (ν.map φ)] {ℱ ℱ' : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ : ℱ' = ℱ) {T : ℝ}
    {hcoord : ∀ k : Fin d, IsBrownianFiltration (D.W.W k) ℱ} {hℱN : IsPoissonFiltration D.N ℱ}
    {hcoord' : ∀ k : Fin d, IsBrownianFiltration ((LevyDriver.mapMarks D hφ).W.W k) ℱ'}
    {hℱN' : IsPoissonFiltration (LevyDriver.mapMarks D hφ).N ℱ'}
    (hsep : ∀ r : Ω → ℝ, MemLp r 2 P → AEStronglyMeasurable[ℱ' T] r P →
      (∀ g : Ω → ℝ, StronglyMeasurable[ℱ' 0] g → (∃ C, ∀ ω, |g ω| ≤ C) →
        ∫ ω, r ω * g ω ∂P = 0) →
      (∀ (i : Fin d) (G : HorizonIntegrand P ℱ' T),
        ∫ ω, r ω * G.integral ((LevyDriver.mapMarks D hφ).W.W i) (hcoord' i) ω ∂P = 0) →
      (∀ K : MarkedHorizonIntegrand P (ν.map φ) ℱ' T,
        ∫ ω, r ω * K.integral (LevyDriver.mapMarks D hφ).N hℱN' ω ∂P = 0) →
      r =ᵐ[P] 0)
    {r : Ω → ℝ} (hr2 : MemLp r 2 P) (hrm : AEStronglyMeasurable[ℱ T] r P)
    (hr0 : ∀ g : Ω → ℝ, StronglyMeasurable[ℱ 0] g → (∃ C, ∀ ω, |g ω| ≤ C) →
      ∫ ω, r ω * g ω ∂P = 0)
    (hrB : ∀ (i : Fin d) (G : HorizonIntegrand P ℱ T),
      ∫ ω, r ω * G.integral (D.W.W i) (hcoord i) ω ∂P = 0)
    (hrN : ∀ K : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, r ω * K.integral D.N hℱN ω ∂P = 0) :
    r =ᵐ[P] 0 := by
  subst hℱ
  refine hsep r hr2 hrm hr0 hrB fun K => ?_
  rw [← hrN (pullMarkedHorizonIntegrand hφ rfl K)]
  refine integral_congr_ae ?_
  filter_upwards [integral_pullMarkedHorizonIntegrand hφ rfl D.N hℱN hℱN' K] with ω hK
  rw [hK]
  rfl

end MVFBSDEJ.WellPosedness.MarkCoding
