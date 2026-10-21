/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Acceptance.Sec4Continuation
import MVFBSDEJ.Acceptance.WitnessNonzero

/-!
# The diffusion process of Example 5.1(i) at `σ_c = 0`

Statement numbers refer to the well-posedness paper at `1f67672`. The system of Example 5.1(i)
with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = 1` and `σ_c = h_c = 0`, the system of the instance
`MVFBSDEJ.Acceptance.thm_cwp_hypotheses`, has the diffusion coefficient `σ = −z`, so its
diffusion process along a tuple is `−Z` on `[0, T]`.

## Main statements

* `MVFBSDEJ.Acceptance.diffusionProc_affine` — the diffusion process along a tuple.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.PaperSpec
  MVFBSDEJ.WellPosedness.Stability LevyStochCalc

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = β`, `σ_c = 0` and
`h_c = 0`. -/
local notation "sys " β:max =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) β β 0 0

/-- The diffusion process of Example 5.1(i) with `σ_c = 0` along a tuple is `−Z`, cut to
`[0, T]`. -/
theorem diffusionProc_affine {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : ℝ} {X Y : Fin 1 → ℝ → Ω → ℝ} {Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ}
    {U : Fin 1 → ℝ → Ω → ℝ → ℝ} (s : ℝ) (ω : Ω) :
    diffusionProc P T (sys 1) X Y Z U 0 s ω 0
      = (Set.Icc (0 : ℝ) T).indicator (fun s => -Z 0 s ω 0) s := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · simp [diffusionProc, Set.indicator_of_mem hs, affineCoeffs, tupleAt]
  · simp [diffusionProc, Set.indicator_of_notMem hs]

end MVFBSDEJ.Acceptance
