/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec5

/-!
# Example 5.1(i) of the well-posedness paper: sharpness of the constants

Statement numbers refer to the well-posedness paper at `f598204`. Example 5.1(i) states that the
displayed identity is sharp for the constants `β₁, β₂`: no larger constants satisfy the interior
inequality (2.7) for its coefficients with `G = 1`.

## Main definitions

* `Dissertation.PaperSpec.A.ex_concrete_i_sharp` — the sharpness of `β₁, β₂`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Matrix

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec

universe u v w

/-- Example 5.1(i), sharpness. In the standing setting with `n = m = d = 1`, for `T > 0`,
`β₁, β₂ > 0`, `σ_c ∈ ℝ` and `h_c ∈ L²(ν)`: if the interior inequality (2.7) holds for the
coefficients of Example 5.1(i) with `G = 1` and constants `β₁', β₂'` for almost every
`t ∈ [0, T]`, then `β₁' ≤ β₁` and `β₂' ≤ β₂`. -/
def ex_concrete_i_sharp : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ T : ℝ, 0 < T → ∀ β₁ β₂ : ℝ, 0 < β₁ → 0 < β₂ →
    ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
      (β₁' β₂' : ℝ),
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Mono27At (enlJoint 𝒢₀ D h𝒢₀) P t (1 : Matrix (Fin 1) (Fin 1) ℝ) β₁' β₂'
        (affineCoeffs β₁ β₂ σc hc)) →
    β₁' ≤ β₁ ∧ β₂' ≤ β₂

end Dissertation.PaperSpec.A
