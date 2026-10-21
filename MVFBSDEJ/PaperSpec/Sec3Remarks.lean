/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Setting

/-!
# The remarks of Section 3 of the well-posedness paper

Statement numbers refer to the well-posedness paper at `1f67672`, in the standing setting of §2.

## Main definitions

* `MVFBSDEJ.PaperSpec.rem_cwp_class` — Remark 3.2: a tuple of `ℍ²` satisfying (1.1) lies
  in `𝕊`.
-/

open MeasureTheory Filter ProbabilityTheory

namespace MVFBSDEJ.PaperSpec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Enlarged
  MVFBSDEJ.WellPosedness.Spec

universe u v w

/-- Remark 3.2 (solution class). In the standing setting, for `T > 0`, coefficients satisfying
(2.3), Assumption 2.2 with initial datum `ξ₀` and Assumption 2.3 with a constant `L`: a tuple
`Θ = (X, Y, Z, U)` of `ℍ²` satisfying (1.1) lies in `𝕊`, that is, it solves (1.1) in `𝕊`. -/
def rem_cwp_class : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    ∀ T : ℝ, 0 < T → ∀ (L : ℝ) (C : Coeffs ν n m d) (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
    ∀ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
      (U : Fin m → ℝ → Ω → E → ℝ),
    WeakSolution D h𝒢₀ hind₀ T C ξ₀ X Y Z U → Solution D h𝒢₀ hind₀ T C ξ₀ X Y Z U

end MVFBSDEJ.PaperSpec
