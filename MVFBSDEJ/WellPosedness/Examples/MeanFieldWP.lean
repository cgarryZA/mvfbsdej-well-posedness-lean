/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Examples.MeanFieldMonotone
import MVFBSDEJ.WellPosedness.Existence.AffineExample
import MVFBSDEJ.WellPosedness.Existence.GlobalEnl
import MVFBSDEJ.WellPosedness.System.PaperUniquenessInt
import LevyStochCalc.Driver.GaussianInitial

/-!
# Example 5.1(ii): the full-rank coupling matrix

The mean-field system of Example 5.1(ii) of the paper, on the tuple space
`H = ℝⁿ × ℝⁿ × ℝ^{n×d} × L²(ν; ℝⁿ)`,

`b = −2y − m_Y(μ)`, `σ = −2z − m_Z(μ)`, `h = −2u − m_U(μ)`, `f = 2x + m_X(μ)`,
`g(x, ρ) = 2x + 𝔟(ρ)`,

is coupled by the matrix `G = 1`, which has full rank `min n n`, the rank condition of
Theorem 3.5.

## Main statements

* `rank_one_eq_min` — the identity matrix has full rank.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Enlarged LevyStochCalc
  LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {n d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- The identity matrix has full rank. -/
theorem rank_one_eq_min : (1 : Matrix (Fin n) (Fin n) ℝ).rank = min n n := by
  rw [Matrix.rank_one, Fintype.card_fin, min_self]

end MVFBSDEJ.WellPosedness.Existence
