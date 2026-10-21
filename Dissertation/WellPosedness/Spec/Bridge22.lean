/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Spec.Assumptions
import Dissertation.WellPosedness.Existence.OriginBound

/-!
# Assumption 2.2 and its coordinate form

Assumption 2.2 asks `ξ₀ ∈ L²(Ω, ℱ₀; ℝⁿ)` and the origin values of the coefficients in `L²(0, T)`.
The existence theorems take the initial datum by its coordinates `ξ₀^i`, each square integrable and
`ℱ₀`-measurable, and the origin values in `L²` of the closed interval `[0, T]`,
`Dissertation.WellPosedness.Existence.CoeffOrigin`. The two forms are equivalent: a vector is square
integrable, or strongly measurable, exactly when its coordinates are square integrable, or
measurable, and `(0, T)` and `[0, T]` differ by a null set.

## Main statements

* `memLp_iff_forall_coord`, `stronglyMeasurable_iff_forall_coord` — a vector of `ℝⁿ` is square
  integrable, or strongly measurable, if and only if its coordinates are square integrable, or
  measurable.
* `originValues_iff_coeffOrigin` — the origin values of Assumption 2.2 in `L²(0, T)` are
  `Dissertation.WellPosedness.Existence.CoeffOrigin`.
-/

open MeasureTheory Filter Dissertation.Law

namespace Dissertation.WellPosedness.Spec

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- A vector of `ℝⁿ` is square integrable if and only if its coordinates are. -/
theorem memLp_iff_forall_coord {P : Measure Ω} {ξ : Ω → EuclideanSpace ℝ (Fin n)} :
    MemLp ξ 2 P ↔ ∀ i, MemLp (fun ω => ξ ω i) 2 P := by
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).comp_memLp' h
  · simpa using memLp_toLp_of_forall (u := fun ω i => ξ ω i) h

omit [MeasurableSpace Ω] in
/-- A vector of `ℝⁿ` is strongly measurable if and only if its coordinates are measurable. -/
theorem stronglyMeasurable_iff_forall_coord {m₀ : MeasurableSpace Ω}
    {ξ : Ω → EuclideanSpace ℝ (Fin n)} :
    StronglyMeasurable[m₀] ξ ↔ ∀ i, Measurable[m₀] (fun ω => ξ ω i) := by
  refine ⟨fun h i => ?_, fun h => ?_⟩
  · exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.measurable.comp
      h.measurable
  · simpa using (measurable_toLp_of_forall (mΩ := m₀) (x := fun i ω => ξ ω i) h).stronglyMeasurable

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {m d : ℕ}

/-- **The origin values of Assumption 2.2 are `CoeffOrigin`**: square integrability over the open
interval `(0, T)` is square integrability over `[0, T]`. -/
theorem originValues_iff_coeffOrigin {T : ℝ} {C : Coeffs ν n m d} :
    OriginValues T C ↔ CoeffOrigin T C := by
  have e : volume.restrict (Set.Ioo (0 : ℝ) T) = volume.restrict (Set.Icc 0 T) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  constructor
  · rintro ⟨hb, hσ, hh, hf⟩
    rw [e] at hb hσ hh hf
    exact ⟨hb, hσ, hh, hf⟩
  · rintro ⟨hb, hσ, hh, hf⟩
    rw [← e] at hb hσ hh hf
    exact ⟨hb, hσ, hh, hf⟩

end Dissertation.WellPosedness.Spec
