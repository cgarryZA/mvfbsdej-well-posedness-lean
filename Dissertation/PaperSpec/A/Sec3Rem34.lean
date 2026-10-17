/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3
import Dissertation.WellPosedness.Examples.SingularDrift

/-!
# Remark 3.4 of the well-posedness paper: uniqueness without origin integrability

Statement numbers refer to arXiv 2608.23203v1, in the standing setting of §2. Remark 3.4:
uniqueness (Theorem 3.3, `thm_uniq`) requires only Assumptions 2.3–2.5, and existence requires
Assumption 2.2.

## Main definitions

* `Dissertation.PaperSpec.A.rem_uniq_singular` — a system violating Assumption 2.2 and satisfying
  (2.3) and Assumptions 2.3–2.5, with a solution in `ℍ`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.Law

universe u v w

/-- Remark 3.4, a solution without Assumption 2.2. In the standing setting with `𝒢₀ = ⊥`,
`n = m = 1` and any `d`, on every horizon `T > 0`: the system of Example 5.1(i) with `β₁ = 1`,
`β₂ = 0`, `σ_c = 0`, `h_c = 0` and the deterministic drift `t^{-1/2}` added to `b` satisfies (2.3),
Assumption 2.3 with `L = 1`, Assumption 2.4 with `G = 1` and Assumption 2.5 with `G = 1`, `α = 1`,
`β₁ = 1`, `β₂ = 0`, violates Assumption 2.2 for every initial datum, and from the initial datum
`0` has a tuple of `ℍ_weak` satisfying (1.1) with `𝔼 sup_{t ≤ T} |X_t|² < ∞` and
`𝔼 sup_{t ≤ T} |Y_t|² < ∞`: a solution in `ℍ` with the drift integral read pathwise. -/
def rem_uniq_singular : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] (ν : Measure E)
    [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] (d : ℕ) (P : Measure Ω)
    [IsProbabilityMeasure P] (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    JointBorel T (singularCoeffs (ν := ν) (d := d))
    ∧ Assumption23 (enlJoint ⊥ D bot_le) P T 1 (singularCoeffs (ν := ν) (d := d))
    ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
    ∧ Assumption25 (enlJoint ⊥ D bot_le) P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 0
        (singularCoeffs (ν := ν) (d := d))
    ∧ (∀ ξ₀ : Ω → EuclideanSpace ℝ (Fin 1),
        ¬ Assumption22 (enlJoint ⊥ D bot_le) P T (singularCoeffs (ν := ν) (d := d)) ξ₀)
    ∧ ∃ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin d → ℝ)
        (U : Fin 1 → ℝ → Ω → E → ℝ),
        WeakSolution D bot_le hind₀ T (singularCoeffs (ν := ν) (d := d)) (fun _ => 0) X Y Z U
        ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P < ⊤
        ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y k t ω)) ∂P < ⊤

end Dissertation.PaperSpec.A
