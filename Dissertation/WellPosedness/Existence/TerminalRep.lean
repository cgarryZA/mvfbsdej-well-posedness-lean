/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.Example

/-!
# The terminal representation property of a filtration

The existence proof of the well-posedness paper uses the predictable representation property of
the filtration only at `λ = 0`, where the backward equation of the `λ`-system (4.1) is a family of
decoupled martingale representations. In backward form it reads: every square-integrable
`ℱ_T`-measurable `ξ` is

`ξ = Y_t + ∫_t^T Z_s dW_s + ∫_t^T ∫_E U_s(e) Ñ(ds, de)`,   `t ∈ [0, T]`,

for a solution `(Y, Z, U)` of the linear backward equation with jumps (4.4) with drift `0`.
`HasTerminalRep` records this for a filtration `ℱ` carrying the driver. The initial value `Y_0`
is `ℱ_0`-measurable and need not be deterministic: over a filtration with a nontrivial time-`0`
field, such as the initially enlarged filtration of the paper, it is in general random.

## Main definitions

* `HasTerminalRep` — every square-integrable `ℱ_T`-measurable terminal value is attained by the
  linear backward equation with drift `0`.
-/

open MeasureTheory

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- **The terminal representation property** of the filtration `ℱ` carrying the driver `D` at
the horizon `T`: every square-integrable `ξ` that is almost everywhere strongly
`ℱ_T`-measurable is the terminal value of a solution `(Y, Z, U)` of the linear backward equation
with jumps with drift `0` over `ℱ`. -/
def HasTerminalRep (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ) (T : ℝ) : Prop :=
  ∀ ξ : Ω → ℝ, MemLp ξ 2 P → AEStronglyMeasurable[ℱ T] ξ P →
    ∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ),
      LinearBSDEJ D ℱ hℱW hℱN T ξ (fun _ _ => 0) Y Z U

end Dissertation.WellPosedness.Existence
