/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.P2Borel
import Dissertation.WellPosedness.System.HilbertW2

/-!
# The 2-Wasserstein space of the tuple space with the Hilbert norm

The paper equips `P₂(H)` with the 2-Wasserstein distance of the Hilbert norm of the tuple space
`H`, `w2H`. The type synonym `P2WH HX HY HZY HUY` of the laws of finite second moment on the
tuple space carries that distance: it is the pseudometric induced by the map `μ ↦ toL2 # μ` into
the 2-Wasserstein space of the tuple space realised with its Hilbert norm, `TupleL2`, and `P2WH`
carries the Borel σ-algebra of its topology.

Every Borel set of `P2WH` lies in the evaluation σ-algebra on the laws: the Borel σ-algebra of
the induced topology is the pullback of that of `P2W TupleL2`, and the map `μ ↦ toL2 # μ` is
measurable for the evaluation σ-algebras and, composed with the identity into `P2W TupleL2`, for
the Borel one (`Dissertation.Law.measurable_toP2W`).

## Main definitions

* `P2WH` — the laws of finite second moment on the tuple space, with the Hilbert-norm `W₂`.
* `P2.toP2WH`, `P2WH.toP2` — the identity maps between `P2 (Tuple …)` and `P2WH`.
* `lawToL2` — the image `toL2 # μ` of a law on the tuple space.
* `TupleP2WH` — `P2WH` for the tuple space `H` of the paper.

## Main statements

* `P2WH.dist_toP2WH` — the distance on `P2WH` is `w2H`.
* `measurable_lawToL2` — `μ ↦ toL2 # μ` is measurable for the evaluation σ-algebras.
* `measurable_toP2WH` — the identity from the evaluation σ-algebra to the Borel σ-algebra of
  `P2WH` is measurable.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.System

variable {HX HY HZY HUY : Type*} [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [NormedAddCommGroup HZY]
  [InnerProductSpace ℝ HZY] [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY]
  [MeasurableSpace HX] [MeasurableSpace HY] [MeasurableSpace HZY] [MeasurableSpace HUY]

variable (HX HY HZY HUY) in
/-- The laws of finite second moment on the tuple space, with the 2-Wasserstein distance of the
Hilbert norm `(‖x‖² + ‖y‖² + ‖z‖² + ‖u‖²)^{1/2}`. -/
def P2WH : Type _ := P2 (Tuple HX HY HZY HUY)

/-- A law of finite second moment on the tuple space, as a point of `P2WH`. -/
def _root_.Dissertation.Law.P2.toP2WH (μ : P2 (Tuple HX HY HZY HUY)) : P2WH HX HY HZY HUY := μ

/-- A point of `P2WH`, as a law of finite second moment on the tuple space. -/
def P2WH.toP2 (μ : P2WH HX HY HZY HUY) : P2 (Tuple HX HY HZY HUY) := μ

variable [BorelSpace HX] [BorelSpace HY] [BorelSpace HZY] [BorelSpace HUY]
  [SecondCountableTopology HX] [SecondCountableTopology HY] [SecondCountableTopology HZY]
  [SecondCountableTopology HUY]

/-- The image `toL2 # μ` of a law of finite second moment on the tuple space, a law of finite
second moment on the tuple space with the Hilbert norm. -/
noncomputable def lawToL2 (μ : P2 (Tuple HX HY HZY HUY)) : P2 (TupleL2 HX HY HZY HUY) :=
  μ.mapOfLe measurable_toL2 norm_toL2_le

omit [SecondCountableTopology HX] in
/-- **`μ ↦ toL2 # μ` is measurable** for the evaluation σ-algebras. -/
theorem measurable_lawToL2 :
    Measurable (lawToL2 : P2 (Tuple HX HY HZY HUY) → P2 (TupleL2 HX HY HZY HUY)) :=
  P2.measurable_of_law fun A hA => by
    simp only [lawToL2, P2.mapOfLe_law, Measure.map_apply measurable_toL2 hA]
    exact (Measure.measurable_coe (measurable_toL2 hA)).comp P2.measurable_law

variable [CompleteSpace HX] [CompleteSpace HY] [CompleteSpace HZY] [CompleteSpace HUY]

/-- The 2-Wasserstein pseudometric of the Hilbert norm on the laws of the tuple space, induced by
`μ ↦ toL2 # μ` from the 2-Wasserstein space of `TupleL2`. -/
noncomputable instance P2WH.instPseudoMetricSpace : PseudoMetricSpace (P2WH HX HY HZY HUY) :=
  PseudoMetricSpace.induced (fun μ => (lawToL2 μ.toP2).toP2W) inferInstance

/-- The Borel σ-algebra of the Hilbert-norm 2-Wasserstein topology. -/
noncomputable instance P2WH.instMeasurableSpace : MeasurableSpace (P2WH HX HY HZY HUY) :=
  borel (P2WH HX HY HZY HUY)

/-- The σ-algebra of `P2WH` is the Borel σ-algebra of its topology. -/
instance P2WH.instBorelSpace : BorelSpace (P2WH HX HY HZY HUY) :=
  ⟨rfl⟩

/-- The distance on `P2WH` is the 2-Wasserstein distance of the Hilbert norm. -/
theorem P2WH.dist_toP2WH (μ μ' : P2 (Tuple HX HY HZY HUY)) :
    dist μ.toP2WH μ'.toP2WH = w2H μ μ' :=
  rfl

/-- **The identity from the evaluation σ-algebra to the Borel σ-algebra of `P2WH` is
measurable**: every Borel set of `P₂(H)` for the Hilbert-norm 2-Wasserstein distance lies in
the evaluation σ-algebra. -/
theorem measurable_toP2WH :
    Measurable (P2.toP2WH : P2 (Tuple HX HY HZY HUY) → P2WH HX HY HZY HUY) := by
  have hf : Measurable fun μ : P2 (Tuple HX HY HZY HUY) => (lawToL2 μ).toP2W :=
    measurable_lawToL2.toP2W
  intro s hs
  have hs' : MeasurableSet[MeasurableSpace.comap (fun μ : P2WH HX HY HZY HUY =>
      (lawToL2 μ.toP2).toP2W) (borel (P2W (TupleL2 HX HY HZY HUY)))] s := by
    rw [← borel_comap]
    exact hs
  obtain ⟨t, ht, rfl⟩ := hs'
  exact hf ht

/-- An evaluation-measurable map into the laws of the tuple space is Borel measurable into
`P2WH`. -/
theorem _root_.Measurable.toP2WH {α : Type*} [MeasurableSpace α]
    {f : α → P2 (Tuple HX HY HZY HUY)} (hf : Measurable f) : Measurable fun a => (f a).toP2WH :=
  measurable_toP2WH.comp hf

variable {E : Type*} [MeasurableSpace E]

/-- The laws of finite second moment on the tuple space `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)` of
the paper, with the 2-Wasserstein distance of the Hilbert norm of `H`. -/
abbrev TupleP2WH (ν : Measure E) (n m d : ℕ) : Type _ :=
  P2WH (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m × Fin d))
    (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)

end Dissertation.WellPosedness.System
