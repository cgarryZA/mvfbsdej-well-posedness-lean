/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.Stability
import Dissertation.WellPosedness.System.Uniqueness
import Dissertation.WellPosedness.BrownianPoisson.Example
import Dissertation.WellPosedness.BrownianPoisson.LegIsometry
import LevyStochCalc.BSDEJ.CadlagLegs

/-!
# The identity coupling matrix

The coupling operator `GX I` of the identity matrix `I ∈ ℝ^{n×n}` is the identity.

## Main statements

* `GX_one` — the coupling operator of the identity matrix is the identity.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open LevyStochCalc LevyStochCalc.BSDEJ.Solves Dissertation.WellPosedness.BrownianPoisson
  Dissertation.WellPosedness.Stability

universe u v w

/-! ### The identity coupling matrix -/

section Coefficients

variable {E : Type*} [MeasurableSpace E] (ν : Measure E) (n d : ℕ)

variable {ν n d}

/-- The coupling operator of the identity matrix is the identity. -/
theorem GX_one : GX (1 : Matrix (Fin n) (Fin n) ℝ) = ContinuousLinearMap.id ℝ _ := by
  ext x : 1
  rw [← WithLp.toLp_ofLp 2 x, GX_toLp, Matrix.one_mulVec]
  rfl

end Coefficients

end Dissertation.WellPosedness.System
