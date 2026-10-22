/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.MarkCoding.MapMarks
import LevyStochCalc.BSDEJ.Solves

/-!
# The filtration of a Lévy driver with pushed-forward marks

Let `φ : E → F` be a measurable map that is initial, `comap φ 𝓕 = ℰ` for the σ-algebras `ℰ`
of `E` and `𝓕` of `F`. Then the time–mark map `id × φ` is initial, and every measurable region
of `ℝ × E` is the preimage of a measurable region of `ℝ × F`. The counts of the image of a
Poisson random measure `N` under `id × φ` are therefore exactly the counts of `N`, and both
random measures have the same natural filtration, with no null sets involved. For a Lévy driver
`D` the driver with its marks pushed forward along `φ` has the same joint natural filtration as
`D`.

## Main statements

* `comap_markMap` — the time–mark map of an initial map is initial.
* `naturalFiltration_mapMarks` — the image of `N` has the natural filtration of `N`.
* `LevyDriver.filtration_mapMarks` — the joint natural filtration is unchanged.
-/

open MeasureTheory

namespace MVFBSDEJ.WellPosedness.MarkCoding

open LevyStochCalc LevyStochCalc.Poisson LevyStochCalc.Driver

universe u v v' w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [mE : MeasurableSpace E]
  {F : Type v'} [mF : MeasurableSpace F] {P : Measure Ω} [IsProbabilityMeasure P]
  {ν : Measure E} [SigmaFinite ν] {φ : E → F}

/-- The time–mark map of an initial map of the marks is initial. -/
theorem comap_markMap (hc : MeasurableSpace.comap φ mF = mE) :
    MeasurableSpace.comap (markMap φ) (inferInstance : MeasurableSpace (ℝ × F))
      = (inferInstance : MeasurableSpace (ℝ × E)) := by
  change MeasurableSpace.comap (markMap φ)
      (MeasurableSpace.comap Prod.fst _ ⊔ MeasurableSpace.comap Prod.snd mF)
    = MeasurableSpace.comap Prod.fst _ ⊔ MeasurableSpace.comap Prod.snd mE
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
  conv_rhs => rw [← hc, MeasurableSpace.comap_comp]
  rfl

/-- For an initial map of the marks, every measurable region of `ℝ × E` is the preimage under
the time–mark map of a measurable region of `ℝ × F`. -/
theorem exists_preimage_markMap (hc : MeasurableSpace.comap φ mF = mE) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) : ∃ B' : Set (ℝ × F), MeasurableSet B' ∧ markMap φ ⁻¹' B' = B := by
  have h : MeasurableSet[MeasurableSpace.comap (markMap φ) inferInstance] B := by
    rw [comap_markMap hc]
    exact hB
  exact h

/-- The image of a Poisson random measure under the time–mark map of an initial map of the marks
has the same natural filtration. -/
theorem naturalFiltration_mapMarks (N : PoissonRandomMeasure.{u, v, w} P ν)
    (hφ : Measurable φ) [SigmaFinite (ν.map φ)] (hc : MeasurableSpace.comap φ mF = mE) :
    naturalFiltration (PoissonRandomMeasure.mapMarks N hφ) = naturalFiltration N := by
  refine Filtration.ext (funext fun t => ?_)
  change (⨆ B ∈ {C : Set (ℝ × F) | C ⊆ Set.Iic t ×ˢ Set.univ ∧ MeasurableSet C},
      MeasurableSpace.comap (fun ω => (PoissonRandomMeasure.mapMarks N hφ).N ω B) inferInstance)
    = ⨆ B ∈ {C : Set (ℝ × E) | C ⊆ Set.Iic t ×ˢ Set.univ ∧ MeasurableSet C},
      MeasurableSpace.comap (fun ω => N.N ω B) inferInstance
  refine le_antisymm (iSup₂_le fun B hB => ?_) (iSup₂_le fun B hB => ?_)
  · simp only [PoissonRandomMeasure.mapMarks_apply N hφ hB.2]
    exact le_iSup₂ (f := fun B (_ : B ∈ {C : Set (ℝ × E) |
      C ⊆ Set.Iic t ×ˢ Set.univ ∧ MeasurableSet C}) =>
      MeasurableSpace.comap (fun ω => N.N ω B) inferInstance)
      (markMap φ ⁻¹' B) ⟨fun q hq => ⟨(hB.1 hq).1, trivial⟩, measurable_markMap hφ hB.2⟩
  · obtain ⟨B', hB'm, hB'⟩ := exists_preimage_markMap hc hB.2
    have hcut : markMap φ ⁻¹' (B' ∩ Set.Iic t ×ˢ Set.univ) = B := by
      rw [Set.preimage_inter, hB']
      exact Set.inter_eq_left.mpr (hB.1.trans fun q hq => ⟨hq.1, trivial⟩)
    have hm : MeasurableSet (B' ∩ Set.Iic t ×ˢ Set.univ) :=
      hB'm.inter (measurableSet_Iic.prod MeasurableSet.univ)
    have hfun : (fun ω => N.N ω B)
        = fun ω => (PoissonRandomMeasure.mapMarks N hφ).N ω (B' ∩ Set.Iic t ×ˢ Set.univ) := by
      funext ω
      rw [PoissonRandomMeasure.mapMarks_apply N hφ hm, hcut]
    rw [hfun]
    exact le_iSup₂ (f := fun B (_ : B ∈ {C : Set (ℝ × F) |
      C ⊆ Set.Iic t ×ˢ Set.univ ∧ MeasurableSet C}) =>
      MeasurableSpace.comap (fun ω => (PoissonRandomMeasure.mapMarks N hφ).N ω B) inferInstance)
      (B' ∩ Set.Iic t ×ˢ Set.univ) ⟨Set.inter_subset_right, hm⟩

variable {d : ℕ}

/-- Pushing the marks of a Lévy driver forward along an initial map leaves its joint natural
filtration unchanged. -/
theorem LevyDriver.filtration_mapMarks (D : LevyDriver.{u, v, w} P d ν) (hφ : Measurable φ)
    [SigmaFinite (ν.map φ)] (hc : MeasurableSpace.comap φ mF = mE) :
    (LevyDriver.mapMarks D hφ).filtration = D.filtration := by
  simp only [LevyStochCalc.Driver.LevyDriver.filtration, LevyDriver.mapMarks,
    naturalFiltration_mapMarks D.N hφ hc]

end MVFBSDEJ.WellPosedness.MarkCoding
