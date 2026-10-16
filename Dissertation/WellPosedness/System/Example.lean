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

The coupling operator `GX I` of the identity matrix `I ∈ ℝ^{n×n}` is the identity, so `G = I`
satisfies both branches of Assumption 2.4 with `c_G = 1`.

## Main statements

* `GX_one` — the coupling operator of the identity matrix is the identity.
* `gCoerciveForward_GX_one`, `gCoerciveBackward_GX_one` — Assumption 2.4 for `G = I`, with
  `c_G = 1`.
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

/-- Assumption 2.4, forward branch, for `G = I` with `c_G = 1`. -/
theorem gCoerciveForward_GX_one : GCoerciveForward (GX (1 : Matrix (Fin n) (Fin n) ℝ)) 1 :=
  fun x => by rw [GX_one, one_mul]; rfl

/-- Assumption 2.4, backward branch, for `G = I` with `c_G = 1`. -/
theorem gCoerciveBackward_GX_one : GCoerciveBackward (GX (1 : Matrix (Fin n) (Fin n) ℝ)) 1 :=
  fun y => by rw [adjoint_GX, Matrix.transpose_one, GX_one, one_mul]; rfl

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

end Coefficients

end Dissertation.WellPosedness.System
