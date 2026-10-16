/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.Assumptions
import Dissertation.Law.LipschitzFunctional

/-!
# Nonnegativity of the sum of the channel norms

The sum `‖x‖ + ‖y‖ + ‖z‖ + ‖u‖` of the four channel norms of a tuple `(x, y, z, u)` of the tuple
space `HX × HY × HZY × HUY` is nonnegative.

## Main statements

* `Dissertation.Law.tupleNorm_nonneg`: the sum of the four channel norms is nonnegative.
-/

namespace Dissertation.Law

open MeasureTheory
open scoped ENNReal

/-! ### The sum of the four channel norms -/

section TupleNorm

open WellPosedness

variable {HX HY HZY HUY : Type*}
  [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY]
  [NormedAddCommGroup HZY] [InnerProductSpace ℝ HZY]
  [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY]

/-- The sum of the four channel norms is nonnegative. -/
theorem tupleNorm_nonneg (θ : Tuple HX HY HZY HUY) : 0 ≤ tupleNorm θ := by
  unfold tupleNorm; positivity

end TupleNorm

end Dissertation.Law
