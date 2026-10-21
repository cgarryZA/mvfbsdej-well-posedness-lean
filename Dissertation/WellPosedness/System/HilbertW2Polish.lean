/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.P2Complete
import Dissertation.WellPosedness.System.HilbertW2Space

/-!
# The Hilbert-norm 2-Wasserstein space of the tuple space is Polish

The map `μ ↦ toL2 # μ` from the laws of finite second moment on the tuple space to those on the
tuple space with the Hilbert norm is a bijection, with inverse `ρ ↦ ofL2 # ρ`, and by definition
of `P2WH` an isometry onto the 2-Wasserstein space `P2W (TupleL2 …)`. That space is a separable
complete metric space (`Dissertation.Law.P2W.instCompleteSpace`, `Dissertation.Law.P2W.instT0Space`,
`Dissertation.Law.P2W.instSeparableSpace`), so `P2WH` is one as well, and is Polish.

## Main statements

* `lawToL2_injective`, `lawToL2_surjective` — `μ ↦ toL2 # μ` is a bijection.
* `P2WH.isometry_lawToL2` — it is an isometry of `P2WH` into the 2-Wasserstein space of the tuple
  space with the Hilbert norm.
* `P2WH.instT0Space`, `P2WH.instCompleteSpace`, `P2WH.instSecondCountableTopology`,
  `P2WH.instPolishSpace` — `P2WH` is a complete separable metric space, hence Polish.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.System

variable {HX HY HZY HUY : Type*} [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [NormedAddCommGroup HZY]
  [InnerProductSpace ℝ HZY] [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY]
  [MeasurableSpace HX] [MeasurableSpace HY] [MeasurableSpace HZY] [MeasurableSpace HUY]
  [BorelSpace HX] [BorelSpace HY] [BorelSpace HZY] [BorelSpace HUY]
  [SecondCountableTopology HX] [SecondCountableTopology HY] [SecondCountableTopology HZY]
  [SecondCountableTopology HUY]

omit [SecondCountableTopology HX] in
/-- `μ ↦ toL2 # μ` is injective. -/
theorem lawToL2_injective :
    Function.Injective (lawToL2 : P2 (Tuple HX HY HZY HUY) → P2 (TupleL2 HX HY HZY HUY)) := by
  intro μ μ' h
  have h' := congrArg (fun ρ : P2 (TupleL2 HX HY HZY HUY) => ρ.law.map ofL2) h
  simp only [lawToL2, P2.mapOfLe_law, Measure.map_map measurable_ofL2 measurable_toL2] at h'
  have hid : (ofL2 ∘ toL2 : Tuple HX HY HZY HUY → Tuple HX HY HZY HUY) = id :=
    funext ofL2_toL2
  rw [hid, Measure.map_id, Measure.map_id] at h'
  exact P2.ext_law h'

omit [SecondCountableTopology HX] in
/-- `μ ↦ toL2 # μ` is surjective, with right inverse `ρ ↦ ofL2 # ρ`. -/
theorem lawToL2_surjective :
    Function.Surjective (lawToL2 : P2 (Tuple HX HY HZY HUY) → P2 (TupleL2 HX HY HZY HUY)) := by
  intro ρ
  have hle : ∀ w : TupleL2 HX HY HZY HUY, ‖ofL2 w‖ ≤ 1 * ‖w‖ := fun w => by
    rw [one_mul]
    exact (norm_le_norm_toL2 (ofL2 w)).trans_eq (by rw [toL2_ofL2])
  refine ⟨ρ.mapOfLe measurable_ofL2 hle, P2.ext_law ?_⟩
  rw [lawToL2, P2.mapOfLe_law, P2.mapOfLe_law, Measure.map_map measurable_toL2 measurable_ofL2]
  have hid : (toL2 ∘ ofL2 : TupleL2 HX HY HZY HUY → TupleL2 HX HY HZY HUY) = id :=
    funext toL2_ofL2
  rw [hid, Measure.map_id]

variable [CompleteSpace HX] [CompleteSpace HY] [CompleteSpace HZY] [CompleteSpace HUY]

/-- `μ ↦ toL2 # μ` is an isometry of `P2WH` into the 2-Wasserstein space of the tuple space with
the Hilbert norm. -/
theorem P2WH.isometry_lawToL2 :
    Isometry fun μ : P2WH HX HY HZY HUY => (lawToL2 μ.toP2).toP2W :=
  Isometry.of_dist_eq fun _ _ => rfl

/-- **`P2WH` is T₀**: the Hilbert-norm 2-Wasserstein pseudometric is a metric. -/
instance P2WH.instT0Space : T0Space (P2WH HX HY HZY HUY) := by
  refine ⟨fun μ μ' h => lawToL2_injective ?_⟩
  have hd : dist μ μ' = 0 := Metric.inseparable_iff.mp h
  have hd' : dist (lawToL2 μ.toP2).toP2W (lawToL2 μ'.toP2).toP2W = 0 := hd
  exact (Metric.inseparable_iff.mpr hd').eq

/-- **`P2WH` is complete.** -/
instance P2WH.instCompleteSpace : CompleteSpace (P2WH HX HY HZY HUY) := by
  rw [completeSpace_iff_isComplete_range P2WH.isometry_lawToL2.isUniformInducing]
  have hr : Set.range (fun μ : P2WH HX HY HZY HUY => (lawToL2 μ.toP2).toP2W) = Set.univ :=
    Set.range_eq_univ.mpr fun ρ => by
      obtain ⟨μ, hμ⟩ := lawToL2_surjective ρ.toP2
      exact ⟨μ.toP2WH, hμ⟩
  rw [hr]
  exact completeSpace_iff_isComplete_univ.mp inferInstance

/-- **`P2WH` is second countable.** -/
instance P2WH.instSecondCountableTopology : SecondCountableTopology (P2WH HX HY HZY HUY) :=
  P2WH.isometry_lawToL2.isUniformInducing.isInducing.secondCountableTopology

/-- **`P2WH` is Polish.** -/
instance P2WH.instPolishSpace : PolishSpace (P2WH HX HY HZY HUY) where

end Dissertation.WellPosedness.System
