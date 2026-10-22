/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.Progressive

/-!
# Composition of a progressive process with a measurable function of time and state

Let `H : Ω → ℝ → A` be progressively measurable for a filtration `ℱ`, and let `F : ℝ × A → V` be
jointly measurable. Then `(ω, s) ↦ F(s, H_s(ω))` is progressively measurable. On the time window
`s ≤ t` the process agrees with `F(s, 1_{s ≤ t} H_s(ω))`, a measurable function of
`(s, 1_{s ≤ t} H_s(ω))`, which is `ℱ_t ⊗ 𝔅`-measurable in `(ω, s)` by the progressive
measurability of `H`; no condition on `F(s, 0)` is needed. The same argument with a function
`G : ℝ × A × E → V` jointly measurable in the time, the state and the mark gives a marked
progressively measurable process `(ω, s, e) ↦ G(s, H_s(ω), e)`.

## Main statements

* `progressivelyMeasurable_comp_measurable` — a jointly measurable function of the time and a
  progressive process is progressive.
* `markedProgressivelyMeasurable_comp_measurable` — a jointly measurable function of the time, a
  progressive process and the mark is marked progressive.
-/

open MeasureTheory

namespace MVFBSDEJ.WellPosedness.System

open LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
  {A : Type*} [TopologicalSpace A] [TopologicalSpace.PseudoMetrizableSpace A] [MeasurableSpace A]
  [BorelSpace A] [Zero A]
  {V : Type*} [TopologicalSpace V] [TopologicalSpace.PseudoMetrizableSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [OpensMeasurableSpace V] [Zero V]
  {H : Ω → ℝ → A}

/-- **Composition with a jointly measurable function of time and state.** If `H` is
progressively measurable and `F` is jointly measurable in the time and the state, then
`(ω, s) ↦ F(s, H_s(ω))` is progressively measurable. -/
theorem progressivelyMeasurable_comp_measurable (hH : ProgressivelyMeasurable ℱ H)
    {F : ℝ → A → V} (hF : Measurable (Function.uncurry F)) :
    ProgressivelyMeasurable ℱ fun ω s => F s (H ω s) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hin : Measurable fun p : Ω × ℝ => (p.2, (Set.Iic t).indicator (H p.1) p.2) :=
    measurable_snd.prodMk (hH t).measurable
  have heq : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => F s (H p.1 s)) p.2)
      = {p : Ω × ℝ | p.2 ∈ Set.Iic t}.indicator
        fun p => F p.2 ((Set.Iic t).indicator (H p.1) p.2) := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ {p : Ω × ℝ | p.2 ∈ Set.Iic t}
        from hp), Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show p ∉ {p : Ω × ℝ | p.2 ∈
        Set.Iic t} from hp)]
  rw [heq]
  exact ((hF.comp hin).indicator (measurable_snd measurableSet_Iic)).stronglyMeasurable

/-- **Composition with a jointly measurable function of time, state and mark.** If `H` is
progressively measurable and `G` is jointly measurable in the time, the state and the mark, then
`(ω, s, e) ↦ G(s, H_s(ω), e)` is marked progressively measurable. -/
theorem markedProgressivelyMeasurable_comp_measurable {E : Type*} [MeasurableSpace E]
    (hH : ProgressivelyMeasurable ℱ H) {G : ℝ → A → E → V}
    (hG : Measurable fun p : ℝ × A × E => G p.1 p.2.1 p.2.2) :
    MarkedProgressivelyMeasurable ℱ fun ω s e => G s (H ω s) e := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hHt : Measurable fun q : Ω × ℝ => (Set.Iic t).indicator (H q.1) q.2 := (hH t).measurable
  have hin : Measurable fun p : Ω × ℝ × E =>
      (p.2.1, (Set.Iic t).indicator (H p.1) p.2.1, p.2.2) :=
    measurable_snd.fst.prodMk
      ((hHt.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)
  have heq : (fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => G s (H p.1 s) p.2.2) p.2.1)
      = {p : Ω × ℝ × E | p.2.1 ∈ Set.Iic t}.indicator
        fun p => G p.2.1 ((Set.Iic t).indicator (H p.1) p.2.1) p.2.2 := by
    funext p
    by_cases hp : p.2.1 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem
        (show p ∈ {p : Ω × ℝ × E | p.2.1 ∈ Set.Iic t} from hp), Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem
        (show p ∉ {p : Ω × ℝ × E | p.2.1 ∈ Set.Iic t} from hp)]
  rw [heq]
  exact ((hG.comp hin).indicator (measurable_snd.fst measurableSet_Iic)).stronglyMeasurable

end MVFBSDEJ.WellPosedness.System
