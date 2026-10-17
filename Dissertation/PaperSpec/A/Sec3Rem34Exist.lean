/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Setting
import Dissertation.WellPosedness.Spec.Assumptions
import Dissertation.WellPosedness.System.SingularDiffusion

/-!
# Remark 3.4 of the well-posedness paper: existence without Assumption 2.2 fails

Statement numbers refer to arXiv 2608.23203v1, in the standing setting of §2. Remark 3.4:
uniqueness (Theorem 3.3, `thm_uniq`) requires only Assumptions 2.3–2.5, and existence requires
Assumption 2.2. Read as a statement about Theorem 3.5: Assumption 2.2 cannot be dropped from it,
since (2.3) and Assumptions 2.3–2.5 alone do not give a solution.

## Main definitions

* `Dissertation.PaperSpec.A.rem_uniq_exist` — a system satisfying (2.3) and Assumptions 2.3–2.5,
  violating Assumption 2.2, and with no tuple of `ℍ_weak` satisfying (1.1) from any initial datum.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec

universe u v w

/-- Remark 3.4, Assumption 2.2 cannot be dropped from the existence theorem. In the standing
setting with `n = m = 1` and `d ≥ 1`, on every horizon `T > 0`: the system of Example 5.1(i) with
`β₁ = 1`, `β₂ = 0`, `σ_c = 0`, `h_c = 0` and the deterministic diffusion `t^{-1/2}` added to the
first column of `σ` satisfies (2.3), Assumption 2.3 with `L = 1`, Assumption 2.4 with `G = 1` and
Assumption 2.5 with `G = 1`, `α = 1`, `β₁ = 1`, `β₂ = 0`; and for every initial datum `ξ₀` it
violates Assumption 2.2, no tuple of `ℍ_weak` satisfies (1.1), and (1.1) has no solution in
`ℍ`. -/
def rem_uniq_exist : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < d → ∀ T : ℝ, 0 < T →
    JointBorel T (singularDiffusionCoeffs (ν := ν) (d := d))
    ∧ Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T 1 (singularDiffusionCoeffs (ν := ν) (d := d))
    ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
    ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 0
        (singularDiffusionCoeffs (ν := ν) (d := d))
    ∧ ∀ ξ₀ : Ω → EuclideanSpace ℝ (Fin 1),
      ¬ Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T (singularDiffusionCoeffs (ν := ν) (d := d)) ξ₀
      ∧ (¬ ∃ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin d → ℝ)
          (U : Fin 1 → ℝ → Ω → E → ℝ),
          WeakSolution D h𝒢₀ hind₀ T (singularDiffusionCoeffs (ν := ν) (d := d)) ξ₀ X Y Z U)
      ∧ ¬ ∃ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin d → ℝ)
          (U : Fin 1 → ℝ → Ω → E → ℝ),
          Solution D h𝒢₀ hind₀ T (singularDiffusionCoeffs (ν := ν) (d := d)) ξ₀ X Y Z U

end Dissertation.PaperSpec.A
