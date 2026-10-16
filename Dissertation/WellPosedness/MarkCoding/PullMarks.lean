/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.MarkCoding.MapMarks
import LevyStochCalc.Poisson.SmallJump
import LevyStochCalc.Probability.MarkedPredictable
import LevyStochCalc.Poisson.CompensatedIntegrandComplete

/-!
# Reading a marked integrand through a map of the marks

For a map `φ : E → F` of the marks and a marked integrand `ψ : Ω → ℝ → F → ℝ` on the image
marks, the pulled-back integrand is `(ω, s, e) ↦ ψ(ω, s, φ e)`, the composite of `ψ` with the
sample–time–mark map `id × id × φ`. It inherits joint measurability, marked progressive
measurability and marked predictability from `ψ`, and its marked energy under `ν` is the marked
energy of `ψ` under `ν.map φ`: the sample–time–mark energy measure of `ν` is carried by
`id × id × φ` to that of `ν.map φ`. Cutting to the preimage of a mark set commutes with pulling
back.

## Main definitions

* `pullMarks` — a marked integrand on the image marks read through the mark map.
* `fullMap` — the sample–time–mark map `id × id × φ`.

## Main statements

* `markedProgressivelyMeasurable_pullMarks`, `markedPredictable_pullMarks` — pulling back
  preserves marked progressive measurability and marked predictability.
* `markedEnergy_pullMarks` — pulling back preserves the marked energy.
* `markedEnergyMeasure_map` — the energy measure of `ν` is carried to the one of `ν.map φ`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness.MarkCoding

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

universe u v v'

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {F : Type v'} [MeasurableSpace F] {P : Measure Ω} {ν : Measure E} {φ : E → F}

/-- A marked integrand on the image marks, read through the mark map `φ`. -/
def pullMarks (φ : E → F) (ψ : Ω → ℝ → F → ℝ) : Ω → ℝ → E → ℝ :=
  fun ω s e => ψ ω s (φ e)

/-- The sample–time–mark map `(ω, s, e) ↦ (ω, s, φ e)` induced by a map of the marks. -/
abbrev fullMap (φ : E → F) : Ω × ℝ × E → Ω × ℝ × F :=
  Prod.map id (markMap φ)

/-- The sample–time–mark map of a measurable map is measurable. -/
theorem measurable_fullMap (hφ : Measurable φ) : Measurable (fullMap (Ω := Ω) φ) :=
  measurable_id.prodMap (measurable_markMap hφ)

/-- A jointly measurable integrand pulls back to a jointly measurable integrand. -/
theorem measurable_pullMarks (hφ : Measurable φ) {ψ : Ω → ℝ → F → ℝ}
    (hψ : Measurable fun p : Ω × ℝ × F => ψ p.1 p.2.1 p.2.2) :
    Measurable fun p : Ω × ℝ × E => pullMarks φ ψ p.1 p.2.1 p.2.2 :=
  hψ.comp (measurable_fullMap hφ)

/-- A marked progressively measurable integrand pulls back to a marked progressively measurable
integrand. -/
theorem markedProgressivelyMeasurable_pullMarks {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hφ : Measurable φ) {ψ : Ω → ℝ → F → ℝ} (hψ : MarkedProgressivelyMeasurable ℱ ψ) :
    MarkedProgressivelyMeasurable ℱ (pullMarks φ ψ) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  exact (hψ t).comp_measurable (measurable_fullMap hφ)

/-- The mark energy of a pulled-back integrand at a sample point and a time is the mark energy
of the integrand under the image intensity. -/
theorem lintegral_pullMarks (hφ : Measurable φ) {ψ : Ω → ℝ → F → ℝ}
    (hψ : Measurable fun p : Ω × ℝ × F => ψ p.1 p.2.1 p.2.2) (ω : Ω) (s : ℝ) :
    ∫⁻ e, (‖pullMarks φ ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      = ∫⁻ e, (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂(ν.map φ) := by
  have hm : Measurable fun e : F => (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
    ((hψ.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id) :
      Measurable fun e : F => ((ω, s, e) : Ω × ℝ × F))).nnnorm.coe_nnreal_ennreal).pow_const 2
  rw [lintegral_map hm hφ]
  rfl

/-- The marked energy of a pulled-back integrand is the marked energy of the integrand under the
image intensity. -/
theorem markedEnergy_pullMarks (hφ : Measurable φ) {ψ : Ω → ℝ → F → ℝ}
    (hψ : Measurable fun p : Ω × ℝ × F => ψ p.1 p.2.1 p.2.2) (T : ℝ) :
    markedEnergy P ν T (pullMarks φ ψ) = markedEnergy P (ν.map φ) T ψ := by
  simp only [markedEnergy, lintegral_pullMarks hφ hψ]

/-- An integrand square integrable on every horizon under the image intensity pulls back to one
square integrable on every horizon under `ν`. -/
theorem sq_int_pullMarks (hφ : Measurable φ) {ψ : Ω → ℝ → F → ℝ}
    (hψ : Measurable fun p : Ω × ℝ × F => ψ p.1 p.2.1 p.2.2)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂(ν.map φ) ∂volume ∂P < ⊤) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖pullMarks φ ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := fun T hT => by
  have h := markedEnergy_pullMarks (P := P) (ν := ν) hφ hψ T
  simp only [markedEnergy] at h
  rw [h]
  exact hq T hT

/-- A marked predictable integrand on the image marks pulls back to a marked predictable
integrand. -/
theorem markedPredictable_pullMarks {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hφ : Measurable φ) {ψ : Ω → ℝ → F → ℝ} (hψ : MarkedPredictable ℱ (ν.map φ) ψ) :
    MarkedPredictable ℱ ν (pullMarks φ ψ) := by
  have hmap : Measurable[markedPredictableSigma ℱ ν, markedPredictableSigma ℱ (ν.map φ)]
      (fullMap φ) := by
    refine @measurable_generateFrom _ _ (markedPredictableSigma ℱ ν) _ _ ?_
    rintro _ ⟨r, q, S, B, hr, hS, hB, hBν, rfl⟩
    refine MeasurableSpace.measurableSet_generateFrom
      ⟨r, q, S, φ ⁻¹' B, hr, hS, hφ hB, ?_, rfl⟩
    rwa [Measure.map_apply hφ hB] at hBν
  exact hψ.comp hmap

omit [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F] in
/-- Cutting a pulled-back integrand to the preimage of a mark set is pulling back the cut
integrand. -/
theorem markCut_pullMarks (A : Set F) (ψ : Ω → ℝ → F → ℝ) :
    markCut (φ ⁻¹' A) (pullMarks φ ψ) = pullMarks φ (markCut A ψ) := by
  funext ω s e
  by_cases he : φ e ∈ A
  · simp [markCut, pullMarks, he]
  · simp [markCut, pullMarks, he]

/-- The sample–time–mark energy measure of `ν` is carried by the sample–time–mark map to that
of `ν.map φ`. -/
theorem markedEnergyMeasure_map [IsProbabilityMeasure P] [SigmaFinite ν] (hφ : Measurable φ)
    [SigmaFinite (ν.map φ)] (T : ℝ) :
    (markedEnergyMeasure P ν T).map (fullMap φ) = markedEnergyMeasure P (ν.map φ) T := by
  rw [markedEnergyMeasure, markedEnergyMeasure, fullMap, markMap,
    ← Measure.map_prod_map _ _ measurable_id (measurable_id.prodMap hφ), Measure.map_id,
    ← Measure.map_prod_map _ _ measurable_id hφ, Measure.map_id]

/-- A set integral against the image of a measure under the time–mark map is the set integral
of the composite over the preimage. -/
theorem setIntegral_map_markMap (hφ : Measurable φ) {μ : Measure (ℝ × E)} {f : ℝ × F → ℝ}
    (hf : Measurable f) {B : Set (ℝ × F)} (hB : MeasurableSet B) :
    ∫ q in B, f q ∂(μ.map (markMap φ)) = ∫ q in markMap φ ⁻¹' B, f (markMap φ q) ∂μ :=
  setIntegral_map hB hf.aestronglyMeasurable (measurable_markMap hφ).aemeasurable

end Dissertation.WellPosedness.MarkCoding
