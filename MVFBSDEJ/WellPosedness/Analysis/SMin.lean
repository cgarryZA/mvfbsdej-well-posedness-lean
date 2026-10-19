/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.SetToL1
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic
import Mathlib.Tactic.Finiteness
import Mathlib.Topology.Instances.Matrix
import LevyStochCalc.BSDEJ.DriftLeg
import LevyStochCalc.Brownian.AugmentedFiltration
import LevyStochCalc.Brownian.CrossOrthogonality
import LevyStochCalc.Brownian.ItoCellIsometry
import LevyStochCalc.Brownian.ItoIntegrandComplete
import LevyStochCalc.Brownian.MultidimIto
import LevyStochCalc.Driver.CellProfileStep
import LevyStochCalc.Driver.Existence
import LevyStochCalc.Driver.GaussianInitial
import LevyStochCalc.Driver.VectorIncrement
import LevyStochCalc.Ito.CompensatedCellIsometry
import LevyStochCalc.Poisson.CompensatedDensityMarkApprox
import LevyStochCalc.Poisson.CompensatedDensityRectSimple
import LevyStochCalc.Poisson.CompensatedIsometry
import LevyStochCalc.Poisson.CompensatedLinear
import LevyStochCalc.Poisson.CompensatedProfileLinear
import LevyStochCalc.Poisson.CompensatedPullOut
import LevyStochCalc.Poisson.PathwiseIdentity
import LevyStochCalc.Probability.MarkedPredictable
import MVFBSDEJ.WellPosedness.BrownianPoisson.FrozenCell
import MVFBSDEJ.WellPosedness.Enlarged.Bot
import MVFBSDEJ.WellPosedness.Examples.FullLawBeyond
import MVFBSDEJ.WellPosedness.Examples.LinearGenerator
import MVFBSDEJ.WellPosedness.Examples.MeanField
import MVFBSDEJ.WellPosedness.Examples.MeanFieldWP
import MVFBSDEJ.WellPosedness.Existence.GlobalEnl
import MVFBSDEJ.WellPosedness.Remarks.LinearMean
import MVFBSDEJ.WellPosedness.Robustness.JumpMargin
import MVFBSDEJ.WellPosedness.Spec.Bridge22
import MVFBSDEJ.WellPosedness.Spec.Bridge25
import MVFBSDEJ.WellPosedness.Stability.Sub
import MVFBSDEJ.WellPosedness.System.FullRank

/-!
# The smallest singular value of the identity matrix

`sMin G` is the smallest singular value of a matrix `G`: the square root of the smallest
eigenvalue of `Gᴴ G` when `G` has at most as many columns as rows, and of `G Gᴴ` otherwise. For
the identity matrix of size `n ≥ 1` it is `1`.

## Main statements

* `sMin_one` — `s_min(I) = 1`.
-/

open MeasureTheory ProbabilityTheory Filter Matrix MVFBSDEJ.Law MVFBSDEJ.WellPosedness
  MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Enlarged
  MVFBSDEJ.WellPosedness.Spec LevyStochCalc LevyStochCalc.Driver
open scoped ENNReal NNReal

namespace MVFBSDEJ.WellPosedness

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

end MVFBSDEJ.WellPosedness
