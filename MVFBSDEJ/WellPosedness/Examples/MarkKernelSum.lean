/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Examples.MarkKernel

/-!
# The sum of the channel norms and the Hilbert norm

The sum of the channel norms `‖(x, y, z, u)‖_Σ = |x| + |y| + |z|_F + ‖u‖` of a tuple, the norm of
the tuple differences in Assumption 2.3, is at most twice its Hilbert norm
`|θ|_H = (|x|² + |y|² + |z|²_F + ‖u‖²)^{1/2}`.

## Main statements

* `tupleNorm_le_two_mul_norm_toL2` — `‖θ‖_Σ ≤ 2 |θ|_H`.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

section Norm

variable {HX HY HZY HUY : Type*} [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [NormedAddCommGroup HZY]
  [InnerProductSpace ℝ HZY] [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY]

/-- The sum of the four channel norms of a tuple is at most twice its Hilbert norm. -/
theorem tupleNorm_le_two_mul_norm_toL2 (θ : Tuple HX HY HZY HUY) :
    tupleNorm θ ≤ 2 * ‖toL2 θ‖ := by
  have h := tupleNorm_sq_le θ
  rw [← norm_toL2_sq] at h
  exact (pow_le_pow_iff_left₀ (tupleNorm_nonneg θ) (by positivity) two_ne_zero).mp
    (by rw [mul_pow]; linarith)

end Norm

end MVFBSDEJ.WellPosedness.System
