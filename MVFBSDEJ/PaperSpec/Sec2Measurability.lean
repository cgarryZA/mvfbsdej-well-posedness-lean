/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Setting

/-!
# The measurability of the coefficient evaluations, (2.5)

Statement numbers refer to the well-posedness paper at `1f67672`. The coefficients are jointly
Borel in their arguments (§2). Along a diagonal input, the drift, diffusion and driver evaluations
are progressively measurable processes, and the jump coefficient, evaluated at the predictable
tuple and its law, is predictable as an `L²(ν)`-valued process and has a `𝒫 ⊗ ℰ`-measurable
representative `(ω, s, e) ↦ γ(ω, s, e)`, the reading of the display through (2.4).

## Main definitions

* `MVFBSDEJ.PaperSpec.eq_coefmeas` — the first line of (2.5).
* `MVFBSDEJ.PaperSpec.eq_coefmeas_jump` — the second line of (2.5).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace MVFBSDEJ.PaperSpec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Spec

universe u v

/-- (2.5), the first line: for jointly Borel coefficients, along every progressive tuple with its
own laws, the drift, diffusion and driver evaluations are progressively measurable, and the jump
coefficient has a jointly measurable, marked progressively measurable representative. -/
def eq_coefmeas : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ)
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Type v} [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (T : ℝ) (C : Coeffs ν n m d),
    JointBorel T C → MVFBSDEJ.WellPosedness.Existence.CoeffRegular ℱ P T C

/-- (2.5), the second line: for jointly Borel coefficients, a predictable tuple `Θ` and a Borel
law flow `ρ`, the `L²(ν)`-valued jump coefficient `s ↦ h(s, Θ_s, ·, ρ_s)`, cut off to the
horizon, is predictable, and there are marked predictable processes `γ_i(ω, s, e)` such that
`e ↦ (γ_i(ω, s, e))_i` represents `h(s, Θ_s(ω), ·, ρ_s)` in `L²(ν; ℝⁿ)` at every `ω` and every
`s ∈ (0, T]`. -/
def eq_coefmeas_jump : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ)
    {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d : ℕ) (T : ℝ) (C : Coeffs ν n m d)
    (Θ : Ω → ℝ → TupleH ν n m d) (ρ : ℝ → TupleP2WH ν n m d),
    JointBorel T C → LevyStochCalc.Probability.Predictable ℱ Θ → Measurable ρ →
    LevyStochCalc.Probability.Predictable ℱ (fun ω s =>
      (Set.Icc (0 : ℝ) T).indicator (fun t => C.h t (Θ ω t) (ρ t).toP2) s)
    ∧ ∃ γ : Fin n → Ω → ℝ → E → ℝ,
      (∀ i, LevyStochCalc.Probability.MarkedPredictable ℱ ν (γ i))
      ∧ ∀ ω, ∀ s ∈ Set.Ioc (0 : ℝ) T,
        (fun e => (WithLp.toLp 2 fun i => γ i ω s e : EuclideanSpace ℝ (Fin n)))
          =ᵐ[ν] C.h s (Θ ω s) (ρ s).toP2

end MVFBSDEJ.PaperSpec
