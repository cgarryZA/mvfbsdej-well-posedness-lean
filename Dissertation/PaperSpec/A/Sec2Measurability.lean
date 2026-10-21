/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Setting

/-!
# The measurability of the coefficient evaluations, (2.5)

Statement numbers refer to the well-posedness paper at `1f67672`. The coefficients are jointly
Borel in their arguments (§2). Along a diagonal input, the drift, diffusion and driver evaluations
are progressively measurable processes, and the jump coefficient, evaluated at the predictable
tuple and its law, is predictable as an `L²(ν)`-valued process, read through a
`𝒫 ⊗ ℰ`-measurable representative by (2.4).

## Main definitions

* `Dissertation.PaperSpec.A.eq_coefmeas` — the first line of (2.5).
* `Dissertation.PaperSpec.A.eq_coefmeas_jump` — the second line of (2.5).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Spec

universe u v

/-- (2.5), the first line: for jointly Borel coefficients, along every progressive tuple with its
own laws, the drift, diffusion and driver evaluations are progressively measurable, and the jump
coefficient has a jointly measurable, marked progressively measurable representative. -/
def eq_coefmeas : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ)
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Type v} [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (T : ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Dissertation.WellPosedness.Existence.CoeffRegular ℱ P T C

/-- (2.5), the second line: for jointly Borel coefficients, a predictable tuple `Θ` and a Borel
law flow `ρ`, the `L²(ν)`-valued jump coefficient `s ↦ h(s, Θ_s, ·, ρ_s)`, cut off to the
horizon, is predictable. -/
def eq_coefmeas_jump : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ)
    {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d : ℕ) (T : ℝ) (C : Coeffs ν n m d)
    (Θ : Ω → ℝ → TupleH ν n m d) (ρ : ℝ → TupleP2WH ν n m d),
    JointBorel T C → LevyStochCalc.Probability.Predictable ℱ Θ → Measurable ρ →
    LevyStochCalc.Probability.Predictable ℱ (fun ω s =>
      (Set.Icc (0 : ℝ) T).indicator (fun t => C.h t (Θ ω t) (ρ t).toP2) s)

end Dissertation.PaperSpec.A
