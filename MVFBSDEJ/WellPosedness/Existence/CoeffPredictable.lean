/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Spec.Bridge23
import LevyStochCalc.Probability.Predictable

/-!
# Progressive and predictable coefficient processes

For jointly Borel coefficients, the drift, diffusion and driver evaluated along a progressive tuple
with its own laws are progressively measurable, the jump coefficient has a marked progressive
representative, and the `L²(ν)`-valued jump coefficient along a predictable tuple and a Borel law
flow, cut off to the horizon, is predictable.

## Main statements

* `MVFBSDEJ.WellPosedness.Spec.JointBorel.coeffRegular` — the progressive measurability
  of the coefficient processes.
* `MVFBSDEJ.WellPosedness.Spec.JointBorel.predictable_jump` — the predictability of the
  jump coefficient.
-/

open MeasureTheory ProbabilityTheory

namespace MVFBSDEJ.WellPosedness.Spec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ} {T : ℝ}
  {C : Coeffs ν n m d}

/-- For jointly Borel coefficients, along every progressive tuple with its own laws, the drift,
diffusion and driver evaluations are progressively measurable, and the jump coefficient has a
jointly measurable, marked progressively measurable representative. -/
theorem JointBorel.coeffRegular (hJ : JointBorel T C) (ℱ : Filtration ℝ mΩ) (P : Measure Ω)
    [IsProbabilityMeasure P] : CoeffRegular ℱ P T C :=
  ((jointBorel_iff.mp hJ).1.toCoeffBorel).coeffRegular ℱ P

/-- For jointly Borel coefficients, a predictable tuple `Θ` and a Borel law flow `ρ`, the
`L²(ν)`-valued jump coefficient `s ↦ h(s, Θ_s, ·, ρ_s)`, cut off to the horizon, is predictable. -/
theorem JointBorel.predictable_jump (hJ : JointBorel T C) {ℱ : Filtration ℝ mΩ}
    {Θ : Ω → ℝ → TupleH ν n m d} {ρ : ℝ → TupleP2WH ν n m d}
    (hΘ : LevyStochCalc.Probability.Predictable ℱ Θ) (hρ : Measurable ρ) :
    LevyStochCalc.Probability.Predictable ℱ (fun ω s =>
      (Set.Icc (0 : ℝ) T).indicator (fun t => C.h t (Θ ω t) (ρ t).toP2) s) := by
  classical
  have hh := (jointBorel_iff.mp hJ).1.h_meas
  rw [← BorelSpace.measurable_eq (α := Lp (EuclideanSpace ℝ (Fin n)) 2 ν),
    ← BorelSpace.measurable_eq (α := Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d)]
    at hh
  set S : Set (ℝ × TupleH ν n m d × TupleP2WH ν n m d) := {q | q.1 ∈ Set.Icc (0 : ℝ) T}
  have hS : MeasurableSet S := measurable_fst measurableSet_Icc
  have hφ : Measurable fun q : S => ((⟨q.1.1, q.2⟩ : Set.Icc (0 : ℝ) T), q.1.2.1, q.1.2.2) :=
    (Measurable.subtype_mk (measurable_fst.comp measurable_subtype_coe)).prodMk
      ((measurable_snd.fst.comp measurable_subtype_coe).prodMk
        (measurable_snd.snd.comp measurable_subtype_coe))
  have hG : Measurable fun q : S => C.h q.1.1 q.1.2.1 q.1.2.2.toP2 := hh.comp hφ
  have hcut : Measurable fun q : ℝ × TupleH ν n m d × TupleP2WH ν n m d =>
      (Set.Icc (0 : ℝ) T).indicator (fun t => C.h t q.2.1 q.2.2.toP2) q.1 := by
    have heq : (fun q : ℝ × TupleH ν n m d × TupleP2WH ν n m d =>
          (Set.Icc (0 : ℝ) T).indicator (fun t => C.h t q.2.1 q.2.2.toP2) q.1)
        = fun q => if hq : q ∈ S then (fun r : S => C.h r.1.1 r.1.2.1 r.1.2.2.toP2) ⟨q, hq⟩
          else (fun _ : (Sᶜ : Set _) => (0 : Lp (EuclideanSpace ℝ (Fin n)) 2 ν)) ⟨q, hq⟩ := by
      funext q
      by_cases hq : q ∈ S
      · rw [dif_pos hq, Set.indicator_of_mem (show q.1 ∈ Set.Icc (0 : ℝ) T from hq)]
      · rw [dif_neg hq, Set.indicator_of_notMem (show q.1 ∉ Set.Icc (0 : ℝ) T from hq)]
    rw [heq]
    exact hG.dite measurable_const hS
  letI : MeasurableSpace (ℝ × Ω) := LevyStochCalc.Probability.predictableSigma ℱ
  have h1 : Measurable fun p : ℝ × Ω => p.1 := by
    refine measurable_of_Ioi fun r => ?_
    have e : (fun p : ℝ × Ω => p.1) ⁻¹' Set.Ioi r = Set.Ioi r ×ˢ Set.univ := by
      ext p
      simp
    rw [e]
    exact LevyStochCalc.Probability.measurableSet_predictableSigma_Ioi_prod MeasurableSet.univ
  have h2 : Measurable fun p : ℝ × Ω => Θ p.2 p.1 := hΘ.measurable
  exact (hcut.comp (h1.prodMk (h2.prodMk (hρ.comp h1)))).stronglyMeasurable

end MVFBSDEJ.WellPosedness.Spec
