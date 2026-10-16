/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.Joint

/-!
# Pushing the marks of a Lévy driver forward

Let `N` be a Poisson random measure on `ℝ × E` with intensity `Leb|[0, ∞) ⊗ ν`, and let
`φ : E → F` be a measurable map for which `ν.map φ` is σ-finite. The image of `N` under the
time–mark map `id × φ` is a Poisson random measure on `ℝ × F` with intensity
`Leb|[0, ∞) ⊗ ν.map φ`: its count on a measurable region `B` is the count of `N` on the preimage
of `B`, and the intensity of `B` is the intensity of that preimage, so every defining property
of `N` passes to the image. A filtration for which `N` is a Poisson random measure is one for the
image, and every count of the image is a count of `N`. For a Lévy driver `D = (W, N)` the pair of
`W` and the image of `N` is therefore again a Lévy driver.

## Main definitions

* `markMap` — the time–mark map `id × φ`.
* `PoissonRandomMeasure.mapMarks` — the image of a Poisson random measure under `id × φ`.
* `LevyDriver.mapMarks` — the Lévy driver with its marks pushed forward along `φ`.

## Main statements

* `referenceIntensity_map` — the intensity of the image marks is the image of the intensity.
* `PoissonRandomMeasure.mapMarks_apply` — the counts of the image are counts of preimages.
* `isPoissonFiltration_mapMarks` — a filtration for `N` is one for its image.
* `sigmaPoisson_mapMarks_le` — the counts of the image generate a sub-σ-algebra of those of `N`.
-/

open MeasureTheory ProbabilityTheory

namespace Dissertation.WellPosedness.MarkCoding

open LevyStochCalc LevyStochCalc.Poisson LevyStochCalc.Driver

universe u v v' w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {F : Type v'} [MeasurableSpace F] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E}
  [SigmaFinite ν] {φ : E → F}

/-- The time–mark map `(s, e) ↦ (s, φ e)` induced by a map of the marks. -/
abbrev markMap (φ : E → F) : ℝ × E → ℝ × F :=
  Prod.map id φ

omit [MeasurableSpace E] [MeasurableSpace F] in
/-- The preimage of a product region under the time–mark map. -/
theorem markMap_preimage_prod (φ : E → F) (S : Set ℝ) (A : Set F) :
    markMap φ ⁻¹' (S ×ˢ A) = S ×ˢ (φ ⁻¹' A) :=
  rfl

/-- The time–mark map of a measurable map is measurable. -/
theorem measurable_markMap (hφ : Measurable φ) : Measurable (markMap φ) :=
  measurable_id.prodMap hφ

/-- The intensity with the image marks is the image of the intensity under the time–mark map. -/
theorem referenceIntensity_map (hφ : Measurable φ) [SigmaFinite (ν.map φ)] :
    referenceIntensity (ν.map φ) = (referenceIntensity ν).map (markMap φ) := by
  rw [referenceIntensity, referenceIntensity, markMap,
    ← Measure.map_prod_map _ _ measurable_id hφ, Measure.map_id]

/-- The intensity with the image marks of a region is the intensity of its preimage. -/
theorem referenceIntensity_map_apply (hφ : Measurable φ) [SigmaFinite (ν.map φ)]
    {B : Set (ℝ × F)} (hB : MeasurableSet B) :
    referenceIntensity (ν.map φ) B = referenceIntensity ν (markMap φ ⁻¹' B) := by
  rw [referenceIntensity_map hφ, Measure.map_apply (measurable_markMap hφ) hB]

/-- The image of a Poisson random measure with intensity `Leb|[0, ∞) ⊗ ν` under the time–mark
map of a measurable `φ`: a Poisson random measure with intensity `Leb|[0, ∞) ⊗ ν.map φ`. -/
noncomputable def PoissonRandomMeasure.mapMarks (N : PoissonRandomMeasure.{u, v, w} P ν)
    (hφ : Measurable φ) [SigmaFinite (ν.map φ)] :
    PoissonRandomMeasure.{u, v', w} P (ν.map φ) where
  N ω := (N.N ω).map (markMap φ)
  measurable_eval {B} hB := by
    simp only [Measure.map_apply (measurable_markMap hφ) hB]
    exact N.measurable_eval (measurable_markMap hφ hB)
  integer_valued {B} hB hfin := by
    simp only [Measure.map_apply (measurable_markMap hφ) hB]
    rw [referenceIntensity_map_apply hφ hB] at hfin
    exact N.integer_valued (measurable_markMap hφ hB) hfin
  infinite_at_infinite_intensity {B} hB hinf := by
    simp only [Measure.map_apply (measurable_markMap hφ) hB]
    rw [referenceIntensity_map_apply hφ hB] at hinf
    exact N.infinite_at_infinite_intensity (measurable_markMap hφ hB) hinf
  poisson_law {B} hB hfin := by
    have hfun : (fun ω => ((N.N ω).map (markMap φ)) B) = fun ω => N.N ω (markMap φ ⁻¹' B) := by
      funext ω
      exact Measure.map_apply (measurable_markMap hφ) hB
    rw [referenceIntensity_map_apply hφ hB] at hfin ⊢
    rw [hfun]
    exact N.poisson_law (measurable_markMap hφ hB) hfin
  independent_disjoint {ι} _ B hBm hBd := by
    have hfun : (fun (i : ι) (ω : Ω) => ((N.N ω).map (markMap φ)) (B i))
        = fun (i : ι) (ω : Ω) => N.N ω (markMap φ ⁻¹' B i) := by
      funext i ω
      exact Measure.map_apply (measurable_markMap hφ) (hBm i)
    rw [hfun]
    exact N.independent_disjoint (fun i => markMap φ ⁻¹' B i)
      (fun i => measurable_markMap hφ (hBm i)) fun i j hij => (hBd hij).preimage _
  joint_past_future_independent {s t} hs hst {A'} hA' hA'ν := by
    have hA'ν' : ν (φ ⁻¹' A') ≠ ⊤ := by rwa [Measure.map_apply hφ hA'] at hA'ν
    have hfut : (fun ω => ((N.N ω).map (markMap φ)) (Set.Ioc s t ×ˢ A'))
        = fun ω => N.N ω (Set.Ioc s t ×ˢ (φ ⁻¹' A')) := by
      funext ω
      rw [Measure.map_apply (measurable_markMap hφ) (measurableSet_Ioc.prod hA'),
        markMap_preimage_prod]
    rw [hfut]
    refine indep_of_indep_of_le_left
      (N.joint_past_future_independent hs hst (hφ hA') hA'ν') (iSup₂_le fun B hB => ?_)
    have hfun : (fun ω => ((N.N ω).map (markMap φ)) B) = fun ω => N.N ω (markMap φ ⁻¹' B) := by
      funext ω
      exact Measure.map_apply (measurable_markMap hφ) hB.2
    rw [hfun]
    exact le_iSup₂ (f := fun B (_ : B ∈ {C : Set (ℝ × E) |
      C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C}) =>
      MeasurableSpace.comap (fun ω => N.N ω B) inferInstance)
      (markMap φ ⁻¹' B) ⟨fun q hq => ⟨(hB.1 hq).1, trivial⟩, measurable_markMap hφ hB.2⟩

/-- The count of the image on a measurable region is the count of `N` on its preimage. -/
theorem PoissonRandomMeasure.mapMarks_apply (N : PoissonRandomMeasure.{u, v, w} P ν)
    (hφ : Measurable φ) [SigmaFinite (ν.map φ)] {B : Set (ℝ × F)} (hB : MeasurableSet B)
    (ω : Ω) : (PoissonRandomMeasure.mapMarks N hφ).N ω B = N.N ω (markMap φ ⁻¹' B) :=
  Measure.map_apply (measurable_markMap hφ) hB

/-- A filtration for which `N` is a Poisson random measure is one for its image under the
time–mark map. -/
theorem isPoissonFiltration_mapMarks {N : PoissonRandomMeasure.{u, v, w} P ν}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (h : IsPoissonFiltration N ℱ)
    (hφ : Measurable φ) [SigmaFinite (ν.map φ)] :
    IsPoissonFiltration (PoissonRandomMeasure.mapMarks N hφ) ℱ where
  measurable t B hB hBm := by
    simp only [PoissonRandomMeasure.mapMarks_apply N hφ hBm]
    exact h.measurable (fun q hq => ⟨(hB hq).1, trivial⟩) (measurable_markMap hφ hBm)
  indep_future s hs := by
    refine indep_of_indep_of_le_right (h.indep_future hs) (iSup₂_le fun B hB => ?_)
    simp only [PoissonRandomMeasure.mapMarks_apply N hφ hB.2]
    exact le_iSup₂ (f := fun D (_ : D ∈ {D : Set (ℝ × E) |
      D ⊆ Set.Ioi s ×ˢ Set.univ ∧ MeasurableSet D}) =>
      MeasurableSpace.comap (fun ω => N.N ω D) inferInstance)
      (markMap φ ⁻¹' B) ⟨fun q hq => ⟨(hB.1 hq).1, trivial⟩, measurable_markMap hφ hB.2⟩

/-- The σ-algebra generated by the counts of the image lies in the one generated by the counts
of `N`. -/
theorem sigmaPoisson_mapMarks_le (N : PoissonRandomMeasure.{u, v, w} P ν)
    (hφ : Measurable φ) [SigmaFinite (ν.map φ)] :
    sigmaPoisson (PoissonRandomMeasure.mapMarks N hφ) ≤ sigmaPoisson N := by
  refine iSup₂_le fun B hB => ?_
  simp only [PoissonRandomMeasure.mapMarks_apply N hφ hB]
  exact comap_count_le_sigmaPoisson N (measurable_markMap hφ hB)

variable {d : ℕ}

/-- The Lévy driver `(W, (id × φ)_* N)` obtained from `D = (W, N)` by pushing its marks
forward along a measurable `φ`. -/
noncomputable def LevyDriver.mapMarks (D : LevyDriver.{u, v, w} P d ν) (hφ : Measurable φ)
    [SigmaFinite (ν.map φ)] : LevyDriver.{u, v', w} P d (ν.map φ) where
  W := D.W
  N := PoissonRandomMeasure.mapMarks D.N hφ
  indep := indep_of_indep_of_le_right D.indep (sigmaPoisson_mapMarks_le D.N hφ)

end Dissertation.WellPosedness.MarkCoding
