/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.P2Measurable
import Dissertation.WellPosedness.Existence.WPZero

/-!
# Measurability of the tuple of a progressive tuple

For a progressive tuple `(X, Y, Z, U)` the tuple `Θ_s(ω) = (X_s(ω), Y_s(ω), Z_s(ω), U_s(ω, ·))`
of the tuple space `H`, with its jump channel the `L²(ν)` class `uLift`, is jointly measurable in
`(ω, s)` and progressively measurable as an `H`-valued process, and its law flow `s ↦ Law(Θ_s)`
is measurable for the evaluation σ-algebra on `P₂(H)`, at every time and for the exact law.

A map into `H` is measurable when its four channels are; the jump channel is the `L²(ν)` class of a
family jointly measurable in the parameter and the mark (`measurable_uLift`), with no integrability
needed. Joint measurability takes the parameter `(ω, s)` with the product of the ambient σ-algebra
and the Borel one; progressive measurability at time `t` takes the truncation `1_{s ≤ t} Θ_s(ω)`
with `ℱ_t ⊗ 𝔅`, the truncated jump channel being the class of the truncated family since
`uLift ν 0 = 0`. The law flow is then measurable by `Dissertation.Law.measurable_lawP2_flow`.

## Main statements

* `uLift_zero` — the class of the zero family is `0`.
* `measurable_tupleH_mk` — a map into `H` with measurable channels is measurable.
* `ProgTuple.measurable_tupleAt` — the tuple is jointly measurable.
* `ProgTuple.progressivelyMeasurable_tupleAt` — the tuple is progressively measurable.
* `ProgTuple.measurable_lawP2_tupleAt` — the law flow is measurable.
-/

open MeasureTheory Filter Dissertation.Law

namespace Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}

/-- The `L²(ν)` class of the zero family is `0`. -/
theorem uLift_zero {ι : Type*} [Fintype ι] :
    uLift ν (fun _ _ => (0 : ℝ) : E → ι → ℝ) = 0 := by
  have h : MemLp (fun e => (WithLp.toLp 2 ((fun _ _ => (0 : ℝ) : E → ι → ℝ) e) :
      EuclideanSpace ℝ ι)) 2 ν :=
    (MemLp.zero : MemLp (0 : E → EuclideanSpace ℝ ι) 2 ν)
  rw [uLift_of_memLp h]
  have : (fun e => (WithLp.toLp 2 ((fun _ _ => (0 : ℝ) : E → ι → ℝ) e) : EuclideanSpace ℝ ι))
      = 0 := by funext e; rfl
  simp only [this]
  exact MemLp.toLp_zero _

/-- **A map into the tuple space with measurable channels is measurable**: for coordinate
families `x, y, z` measurable in the parameter and a mark-indexed family `u` jointly measurable
in the parameter and the mark, `a ↦ (x_a, y_a, z_a, uLift ν u_a) ∈ H` is measurable. -/
theorem measurable_tupleH_mk [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    {α : Type*} {mα : MeasurableSpace α} {x : α → Fin n → ℝ} {y : α → Fin m → ℝ}
    {z : α → Fin m × Fin d → ℝ} {u : α → E → Fin m → ℝ} (hx : Measurable x) (hy : Measurable y)
    (hz : Measurable z) (hu : Measurable fun p : α × E => u p.1 p.2) :
    Measurable fun a => ((WithLp.toLp 2 (x a), WithLp.toLp 2 (y a), WithLp.toLp 2 (z a),
      uLift ν (u a)) : TupleH ν n m d) :=
  ((WithLp.measurable_toLp 2 _).comp hx).prodMk (((WithLp.measurable_toLp 2 _).comp hy).prodMk
    (((WithLp.measurable_toLp 2 _).comp hz).prodMk (measurable_uLift hu)))

end Dissertation.WellPosedness.System

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.System

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ} {P : Measure Ω}
  [IsProbabilityMeasure P] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}

namespace ProgTuple

omit [IsProbabilityMeasure P] in
/-- **The tuple of a progressive tuple is jointly measurable** in the sample point and the
time. -/
theorem measurable_tupleAt (hΘ : ProgTuple ℱ P ν T X Y Z U) :
    Measurable (Function.uncurry fun ω s => tupleAt ν X Y Z U s ω) :=
  measurable_tupleH_mk (x := fun p : Ω × ℝ => fun i => X i p.2 p.1)
    (y := fun p : Ω × ℝ => fun k => Y k p.2 p.1)
    (z := fun p : Ω × ℝ => fun q : Fin m × Fin d => Z q.1 p.2 p.1 q.2)
    (u := fun p e k => U k p.2 p.1 e) (measurable_pi_iff.mpr hΘ.measurable_X)
    (measurable_pi_iff.mpr hΘ.measurable_Y)
    (measurable_pi_iff.mpr fun q => hΘ.Z_meas q.1 q.2)
    (measurable_pi_iff.mpr fun k =>
      (hΘ.U_meas k).comp MeasurableEquiv.prodAssoc.measurable)

omit [IsProbabilityMeasure P] in
/-- **The tuple of a progressive tuple is progressively measurable** as a process with values in
the tuple space. -/
theorem progressivelyMeasurable_tupleAt (hΘ : ProgTuple ℱ P ν T X Y Z U) :
    LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => tupleAt ν X Y Z U s ω := by
  have hXq := fun i => LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous
      (ℱ := ℱ) (hΘ.X_adapted i) (hΘ.X_rightCont i)
  have hYq := fun k => LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous
      (ℱ := ℱ) (hΘ.Y_adapted k) (hΘ.Y_rightCont k)
  have hZq := hΘ.Z_prog
  have hUq := hΘ.U_prog
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have heq : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => tupleAt ν X Y Z U s p.1) p.2)
      = fun p : Ω × ℝ =>
        ((WithLp.toLp 2 fun i => (Set.Iic t).indicator (fun s => X i s p.1) p.2 :
            EuclideanSpace ℝ (Fin n)),
          (WithLp.toLp 2 fun k => (Set.Iic t).indicator (fun s => Y k s p.1) p.2 :
            EuclideanSpace ℝ (Fin m)),
          (WithLp.toLp 2 fun q : Fin m × Fin d =>
            (Set.Iic t).indicator (fun s => Z q.1 s p.1 q.2) p.2 :
            EuclideanSpace ℝ (Fin m × Fin d)),
          uLift ν fun e k => (Set.Iic t).indicator (fun s => U k s p.1 e) p.2) := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · simp only [Set.indicator_of_mem hp, tupleAt]
    · simp only [Set.indicator_of_notMem hp]
      rw [uLift_zero]
      rfl
  rw [heq]
  exact (measurable_tupleH_mk
    (x := fun p : Ω × ℝ => fun i => (Set.Iic t).indicator (fun s => X i s p.1) p.2)
    (y := fun p : Ω × ℝ => fun k => (Set.Iic t).indicator (fun s => Y k s p.1) p.2)
    (z := fun p : Ω × ℝ => fun q : Fin m × Fin d =>
      (Set.Iic t).indicator (fun s => Z q.1 s p.1 q.2) p.2)
    (u := fun p e k => (Set.Iic t).indicator (fun s => U k s p.1 e) p.2)
    (measurable_pi_iff.mpr fun i => (hXq i t).measurable)
    (measurable_pi_iff.mpr fun k => (hYq k t).measurable)
    (measurable_pi_iff.mpr fun q : Fin m × Fin d => (hZq q.1 q.2 t).measurable)
    (measurable_pi_iff.mpr fun k =>
      (hUq k t).measurable.comp MeasurableEquiv.prodAssoc.measurable)).stronglyMeasurable

/-- **The law flow of a progressive tuple is measurable**: `s ↦ Law(Θ_s)`, the exact law at every
time, is measurable for the evaluation σ-algebra on the laws of finite second moment. -/
theorem measurable_lawP2_tupleAt (hΘ : ProgTuple ℱ P ν T X Y Z U) :
    Measurable fun s => lawP2 P (tupleAt ν X Y Z U s) :=
  measurable_lawP2_flow (Θ := fun ω s => tupleAt ν X Y Z U s ω) hΘ.measurable_tupleAt

end ProgTuple

end Dissertation.WellPosedness.Existence
