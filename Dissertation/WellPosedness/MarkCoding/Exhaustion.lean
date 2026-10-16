/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.SmallJump
import LevyStochCalc.Poisson.CompensatedLinear
import LevyStochCalc.Poisson.CompensatorL1

/-!
# Compensated integrals over an exhausting family of marks

Let `N` be a Poisson random measure for a filtration `ℱ` and let `χ` be an admissible marked
integrand. For an increasing sequence of measurable mark sets `Sₖ` covering `E`, the integrand
`χ` cut to `Sₖ` differs from `χ` by its cut to the complement of `Sₖ`, whose energy tends to `0`
since the complements decrease to the empty set. By the Itô isometry the compensated integrals
of the cut integrands converge to the compensated integral of `χ` in `L²(P)`, hence in `L¹(P)`.

## Main statements

* `tendsto_lintegral_enorm_of_sq` — mean-square convergence to `0` gives mean convergence to `0`
  on a probability space.
* `tendsto_lintegral_sub_markCut` — the compensated integrals over an exhausting family of marks
  converge in mean.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace Dissertation.WellPosedness.MarkCoding

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- An integrand minus its cut to a mark set is its cut to the complement. -/
theorem sub_markCut (S : Set E) (χ : Ω → ℝ → E → ℝ) (ω : Ω) (s : ℝ) (e : E) :
    χ ω s e - markCut S χ ω s e = markCut Sᶜ χ ω s e := by
  by_cases he : e ∈ S
  · simp [markCut, he]
  · simp [markCut, he]

/-- On a probability space, random variables converging to `0` in mean square converge to `0`
in mean. -/
theorem tendsto_lintegral_enorm_of_sq {f : ℕ → Ω → ℝ} (hf : ∀ k, AEStronglyMeasurable (f k) P)
    (h : Tendsto (fun k => ∫⁻ ω, (‖f k ω‖₊ : ℝ≥0∞) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ ω, ‖f k ω‖ₑ ∂P) atTop (𝓝 0) := by
  have hc := (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hc.comp h)
    (fun _ => bot_le) fun k => ?_
  refine (lintegral_enorm_le_eLpNorm_two (hf k)).trans (le_of_eq ?_)
  rw [eLpNorm_two_eq_rpow]
  rfl

variable (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsPoissonFiltration N ℱ) (χ : Ω → ℝ → E → ℝ)
  (hm : Measurable fun p : Ω × ℝ × E => χ p.1 p.2.1 p.2.2)
  (hp : MarkedProgressivelyMeasurable ℱ χ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖χ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

/-- For an increasing sequence of measurable mark sets covering the mark space, the compensated
integrals at a time `T > 0` of the integrand cut to these sets converge in mean to the
compensated integral of the integrand. -/
theorem tendsto_lintegral_sub_markCut (S : ℕ → Set E) (hS : ∀ k, MeasurableSet (S k))
    (hmono : Monotone S) (hcover : ⋃ k, S k = Set.univ) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun k => ∫⁻ ω, ‖stochasticIntegral N ℱ hℱ χ hm hp hq T ω
      - stochasticIntegral N ℱ hℱ (markCut (S k) χ) (measurable_markCut hm (hS k))
          (hp.indicator_mark (hS k)) (fun T' hT' => sq_markCut hq (S k) T' hT') T ω‖ₑ ∂P)
      atTop (𝓝 0) := by
  refine tendsto_lintegral_enorm_of_sq (fun k =>
    ((stochasticIntegral_memLp N ℱ hℱ χ hm hp hq T).sub
      (stochasticIntegral_memLp N ℱ hℱ _ _ _ _ T)).aestronglyMeasurable) ?_
  have hanti : Antitone fun k => (S k)ᶜ := fun a b hab =>
    Set.compl_subset_compl.mpr (hmono hab)
  have hnull : ν (⋂ k, (S k)ᶜ) = 0 := by
    rw [← Set.compl_iUnion, hcover, Set.compl_univ, measure_empty]
  have hlim := tendsto_lintegral_sq_stochasticIntegral_markCut N ℱ hℱ χ hm hp hq
    (fun k => (S k)ᶜ) (fun k => (hS k).compl) hanti hnull hT
  refine hlim.congr fun k => ?_
  rw [isometry_stochasticIntegral N ℱ hℱ _ _ _ _ T hT,
    itoIsometry_diff_compensated N ℱ hℱ χ (markCut (S k) χ) hm _ hp _ hq _ T hT]
  simp only [sub_markCut]

variable {N ℱ hℱ} in
/-- The compensated integral of an integrand depends only on the integrand. -/
theorem stochasticIntegral_congr_fun {χ₁ χ₂ : Ω → ℝ → E → ℝ} (h : χ₁ = χ₂)
    (hm₁ : Measurable fun p : Ω × ℝ × E => χ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => χ₂ p.1 p.2.1 p.2.2)
    (hp₁ : MarkedProgressivelyMeasurable ℱ χ₁) (hp₂ : MarkedProgressivelyMeasurable ℱ χ₂)
    (hq₁ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖χ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hq₂ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖χ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) (T : ℝ) :
    stochasticIntegral N ℱ hℱ χ₁ hm₁ hp₁ hq₁ T = stochasticIntegral N ℱ hℱ χ₂ hm₂ hp₂ hq₂ T := by
  subst h
  rfl

end Dissertation.WellPosedness.MarkCoding
