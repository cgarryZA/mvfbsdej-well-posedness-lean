/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.FrozenCell
import Dissertation.WellPosedness.Analysis.LegIncrements
import Dissertation.WellPosedness.Examples.LinearGenerator
import Dissertation.WellPosedness.Enlarged.Bot
import Dissertation.WellPosedness.Examples.FullLawBeyond
import Dissertation.WellPosedness.Examples.MeanFieldWP
import Dissertation.WellPosedness.Robustness.JumpMargin
import Dissertation.WellPosedness.Spec.Bridge22
import Dissertation.WellPosedness.Spec.Bridge25
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import LevyStochCalc.Brownian.CrossOrthogonality
import LevyStochCalc.Poisson.CompensatedPullOut
import LevyStochCalc.Poisson.PathwiseIdentity
import LevyStochCalc.Poisson.CompensatedDensityMarkApprox
import LevyStochCalc.Probability.MarkedPredictable
import LevyStochCalc.Poisson.CompensatedDensityRectSimple
import LevyStochCalc.Brownian.ItoIntegrandComplete
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Average
import LevyStochCalc.Driver.Existence
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import LevyStochCalc.Driver.VectorIncrement
import LevyStochCalc.Poisson.CompensatedIsometry
import LevyStochCalc.Driver.CellProfileStep
import LevyStochCalc.Poisson.CompensatedProfileLinear
import LevyStochCalc.Brownian.AugmentedFiltration
import Mathlib.Tactic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.SetToL1
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import LevyStochCalc.Driver.GaussianInitial
import Dissertation.WellPosedness.Examples.ScalarRiccati
import Dissertation.WellPosedness.Stability.MulDeterministic
import Dissertation.WellPosedness.Examples.MeanField
import Dissertation.WellPosedness.Existence.GlobalEnl
import Dissertation.WellPosedness.Remarks.LinearMean
import Mathlib.Tactic.Finiteness
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Instances.Matrix

/-!
# The smallest singular value of the identity matrix

`sMin G` is the smallest singular value of a matrix `G`: the square root of the smallest
eigenvalue of `Gᴴ G` when `G` has at most as many columns as rows, and of `G Gᴴ` otherwise. For
the identity matrix of size `n ≥ 1` it is `1`.

## Main statements

* `sMin_one` — `s_min(I) = 1`.
-/

open MeasureTheory ProbabilityTheory Filter Matrix Dissertation.Law Dissertation.WellPosedness
  Dissertation.WellPosedness.System Dissertation.WellPosedness.Enlarged
  Dissertation.WellPosedness.Spec LevyStochCalc LevyStochCalc.Driver
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness

universe u v w

/-- **`s_min(I) = 1`** for the identity matrix of size `n ≥ 1`: every eigenvalue of `Iᵀ I = I`
lies in the spectrum `{1}`. -/
theorem sMin_one {n : ℕ} [NeZero n] : sMin (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  have h : ∀ i,
      (isHermitian_conjTranspose_mul_self (1 : Matrix (Fin n) (Fin n) ℝ)).eigenvalues i = 1 := by
    intro i
    have hs : spectrum ℝ ((1 : Matrix (Fin n) (Fin n) ℝ)ᴴ * 1) = {1} := by
      rw [conjTranspose_one, one_mul, spectrum.one_eq]
    have hi := (isHermitian_conjTranspose_mul_self
      (1 : Matrix (Fin n) (Fin n) ℝ)).eigenvalues_mem_spectrum_real i
    rw [hs] at hi
    exact hi
  rw [sMin, if_pos le_rfl]
  simp only [h, ciInf_const, Real.sqrt_one]

end Dissertation.WellPosedness
