/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.CoeffBorelW2
import Dissertation.WellPosedness.Existence.GlobalRank
import Dissertation.WellPosedness.System.DiagonalLipschitzH

/-!
# Theorem 3.5 with Assumption 2.3 in the Hilbert norm

Assumption 2.3 of the well-posedness paper measures the law argument in the 2-Wasserstein distance
of the Hilbert norm of the tuple space, `Dissertation.WellPosedness.System.DiagonalLipschitzH`.
Theorem 3.5, `exists_solves_and_uniqueness`, is stated with
`Dissertation.WellPosedness.System.DiagonalLipschitz`, the same bound for the 2-Wasserstein distance
of the maximum of the four channel norms. `Dissertation.WellPosedness.System.DiagonalLipschitzH` at
`L` gives `Dissertation.WellPosedness.System.DiagonalLipschitz` at `2L`, and the terminal bound
(2.6) at `L` gives it at `2L`, so Theorem 3.5 holds under the paper's Assumption 2.3; the conclusion
carries no constant. This file states it, combined with `exists_solves_and_uniqueness_of_rank`, with
Assumption 2.4 as the full rank of the coupling matrix, over a general filtration carrying a Lévy
driver.

This form takes the joint Borel measurability (2.3) of the coefficients, `CoeffBorelW2`, with
`P₂(H)` carrying the Hilbert-norm `W₂`, in place of the measurability (2.5) of the coefficient
processes along every progressive tuple, `CoeffRegular`, which `CoeffBorelW2.toCoeffBorel` and
`CoeffBorel.coeffRegular` derive from it.

## Main statements

* `exists_solves_and_uniqueness_of_rank_of_diagonalLipschitzH` — Theorem 3.5 under Assumption
  2.3 with the Hilbert-norm `W₂` and a full-rank coupling matrix.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T L cG α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
  {C : Coeffs ν n m d} {ξ₀ : Fin n → Ω → ℝ}

section General

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}

/-- **Theorem 3.5 at the paper's Assumptions 2.3 and 2.4.** Over a right-continuous filtration
carrying the driver, whose null sets lie in its time-`0` field, whose right-continuation is
constant before `0`, which admits a cross witness and has the terminal representation property
at the horizon `T > 0`, let the coefficients be jointly Borel measurable on `[0, T] × H × P₂(H)`,
(2.3) with the Hilbert-norm `W₂` on `P₂(H)`, and satisfy Assumption 2.2, Assumption 2.3 along the
diagonal with constant `L` and the Hilbert-norm `W₂` on `P₂(H)` and `g` Borel measurable in the
state, and Assumption 2.5 along the diagonal with a
coupling matrix `G ∈ ℝ^{m×n}` of full rank and admissible constants `α, β₁, β₂`, and let `ξ₀` be
square integrable and `ℱ_0`-measurable. Then the system (1.1) with initial datum `ξ₀` has a
solution, and any two solutions coincide: `X¹, X²` and `Y¹, Y²` are indistinguishable on
`[0, T]`, and `𝔼 ∫_0^T |Z¹ − Z²|²_F = 0`, `𝔼 ∫_0^T ‖U¹ − U²‖²_{L²(ν)} = 0`, coordinatewise. -/
theorem exists_solves_and_uniqueness_of_rank_of_diagonalLipschitzH [ℱ.IsRightContinuous]
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hrep : HasTerminalRep D ℱ hℱW hℱN T) (hT : 0 < T) (hmeas : CoeffBorelW2 T C)
    (horig : CoeffOrigin T C) (hL : DiagonalLipschitzH ℱ P T L C)
    (hLT : TerminalLipschitz ℱ P T L C.g) (hg : ∀ ρ, Measurable fun x => C.g x ρ)
    (hG : G.rank = min m n) (hconst : Constants n m α β₁ β₂)
    (hM : DiagonalMonotone ℱ P T G β₁ β₂ C) (hMT : TerminalMonotone ℱ P T G α C.g)
    (hξ : ∀ i, MemLp (ξ₀ i) 2 P) (hξm : ∀ i, Measurable[ℱ 0] (ξ₀ i)) :
    (∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
      (U : Fin m → ℝ → Ω → E → ℝ) (γ : Fin n → ℝ → Ω → E → ℝ),
      Solves D ℱ hℱW hℱN T C ξ₀ X Y Z U γ)
    ∧ ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ)
      (γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ),
      Solves D ℱ hℱW hℱN T C ξ₀ X₁ Y₁ Z₁ U₁ γ₁ → Solves D ℱ hℱW hℱN T C ξ₀ X₂ Y₂ Z₂ U₂ γ₂ →
      (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
        ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
        ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
        ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0) :=
  exists_solves_and_uniqueness_of_rank 𝒲 hℱ0 hnull hrep hT (hmeas.toCoeffBorel.coeffRegular ℱ P)
    horig hL.diagonalLipschitz hLT.two_mul hg hG hconst hM hMT hξ hξm

end General

end Dissertation.WellPosedness.Existence
