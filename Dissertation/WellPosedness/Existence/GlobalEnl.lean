/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.TerminalRepEnl
import Dissertation.WellPosedness.Existence.PaperSolution
import Dissertation.WellPosedness.Enlarged.CrossWitness

/-!
# Solutions of (1.1) over the initially enlarged filtration

Let `D` be a Lévy driver with joint natural filtration `ℱ`, and let `𝒢₀` be a σ-algebra
independent of `⨆ t, ℱ_t`. The filtration of the well-posedness paper is
`enlJoint 𝒢₀ D h𝒢₀`, the usual augmentation of `t ↦ ℱ_t ⊔ 𝒢₀`. `PaperSolutionEnl` is a solution
of (1.1) in the sense of the paper over this filtration.

## Main definitions

* `PaperSolutionEnl` — `(X, Y, Z, U)` solves (1.1) in the sense of the paper over
  `enlJoint 𝒢₀ D h𝒢₀`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System Dissertation.WellPosedness.Enlarged LevyStochCalc
  LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- `(X, Y, Z, U)` is a solution of (1.1) in the sense of the well-posedness paper over the usual
augmentation `enlJoint 𝒢₀ D h𝒢₀` of the joint filtration of the driver enlarged at time `0` by a
σ-algebra `𝒢₀` independent of it. -/
abbrev PaperSolutionEnl (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T : ℝ) (C : Coeffs ν n m d)
    (ξ₀ : Fin n → Ω → ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop :=
  PaperSolution D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T C ξ₀ X Y Z U γ

end Dissertation.WellPosedness.Existence
