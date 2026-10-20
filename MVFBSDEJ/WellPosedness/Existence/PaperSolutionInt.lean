/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Existence.PaperSolution
import MVFBSDEJ.WellPosedness.System.PaperUniquenessInt

/-!
# Theorem 3.5 with uniqueness among the paper's solutions in `ℍ²_weak`

Theorem 3.5 of the well-posedness paper: under Assumptions 2.2–2.5 the system (1.1) has a
solution in `ℍ²`, unique by Theorem 3.3, whose uniqueness statement ranges over the tuples of
`ℍ²_weak` satisfying (1.1). `exists_paperSolution_and_uniqueness` states the existence in the
sense of `PaperSolution`. A solution in `ℍ²` is a solution of `PaperWeakSolutionInt`
(`PaperSolution.toWeakInt`), and Theorem 3.3 holds for `PaperWeakSolutionInt` under Assumptions
2.3–2.5 (`PaperWeakSolutionInt.uniqueness`); Assumption 2.3 with the Hilbert-norm `W₂` gives
Assumption 2.3 with constant `2L` (`DiagonalLipschitzH.diagonalLipschitz`), and a full-rank
coupling matrix gives Assumption 2.4 (`gCoerciveForward_of_rank`, `gCoerciveBackward_of_rank`).
So the solution of Theorem 3.5 in the sense of the paper coincides with every solution of (1.1)
in `ℍ²_weak` in the sense of `PaperWeakSolutionInt` with the same initial datum.

## Main statements

* `exists_paperSolution_unique_paperWeakSolutionInt` — Theorem 3.5 in the sense of the paper,
  with uniqueness among the solutions of `PaperWeakSolutionInt`.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.System LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T L α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
  {C : Coeffs ν n m d} {ξ₀ : Fin n → Ω → ℝ}

section General

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}

/-- **Theorem 3.5 for solutions in the sense of the paper, with uniqueness among solutions in
`ℍ²_weak`.** Under the hypotheses of `exists_paperSolution_and_uniqueness` — a right-continuous
filtration carrying the driver, whose null sets lie in its time-`0` field, whose
right-continuation is constant before `0`, which admits a cross witness and has the terminal
representation property at the horizon `T > 0`; coefficients jointly Borel measurable on
`[0, T] × H × P₂(H)`, (2.3) with the Hilbert-norm `W₂` on `P₂(H)`, satisfying Assumption 2.2,
Assumption 2.3 along the diagonal with constant `L` and the Hilbert-norm `W₂` on `P₂(H)` and `g`
Borel measurable in the state, and Assumption 2.5 along the diagonal with a coupling matrix
`G ∈ ℝ^{m×n}` of full rank and admissible constants `α, β₁, β₂`; a square-integrable
`ℱ_0`-measurable `ξ₀` — the system (1.1) with initial datum `ξ₀` has a solution `(X, Y, Z, U)`
in the sense of the paper, and every solution `(X', Y', Z', U')` of (1.1) in `ℍ²_weak` in the
sense of `PaperWeakSolutionInt` with initial datum `ξ₀` coincides with it: `X, X'` and `Y, Y'`
are indistinguishable on `[0, T]`, and `𝔼 ∫_0^T |Z − Z'|²_F = 0`,
`𝔼 ∫_0^T ‖U − U'‖²_{L²(ν)} = 0`, coordinatewise. -/
theorem exists_paperSolution_unique_paperWeakSolutionInt [ℱ.IsRightContinuous]
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hrep : HasTerminalRep D ℱ hℱW hℱN T) (hT : 0 < T) (hmeas : CoeffBorelW2 T C)
    (horig : CoeffOrigin T C) (hL : DiagonalLipschitzH ℱ P T L C)
    (hLT : TerminalLipschitz ℱ P T L C.g) (hg : ∀ ρ, Measurable fun x => C.g x ρ)
    (hG : G.rank = min m n) (hconst : Constants n m α β₁ β₂)
    (hM : DiagonalMonotone ℱ P T G β₁ β₂ C) (hMT : TerminalMonotone ℱ P T G α C.g)
    (hξ : ∀ i, MemLp (ξ₀ i) 2 P) (hξm : ∀ i, Measurable[ℱ 0] (ξ₀ i)) :
    ∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
      (U : Fin m → ℝ → Ω → E → ℝ) (γ : Fin n → ℝ → Ω → E → ℝ),
      PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ
      ∧ ∀ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ)
        (Z' : Fin m → ℝ → Ω → Fin d → ℝ) (U' : Fin m → ℝ → Ω → E → ℝ)
        (γ' : Fin n → ℝ → Ω → E → ℝ),
        PaperWeakSolutionInt D ℱ hℱW hℱN T C ξ₀ X' Y' Z' U' γ' →
        (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X i t ω = X' i t ω)
          ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y k t ω = Y' k t ω)
          ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z k s ω j - Z' k s ω j) = 0)
          ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
              (fun ω s e => U k s ω e - U' k s ω e) = 0) := by
  obtain ⟨⟨X, Y, Z, U, γ, h⟩, -⟩ := exists_paperSolution_and_uniqueness 𝒲 hℱ0 hnull hrep hT
    hmeas horig hL hLT hg hG hconst hM hMT hξ hξm
  exact ⟨X, Y, Z, U, γ, h, fun _ _ _ _ _ h' =>
    PaperWeakSolutionInt.uniqueness (h.toWeakInt hT.le) h' 𝒲 hℱ0 hnull hT hL.diagonalLipschitz
      hLT.two_mul (inv_nonneg.mpr (sq_nonneg (sMin G))) (gCoerciveForward_of_rank hG)
      (gCoerciveBackward_of_rank hG) hconst hM hMT⟩

end General

end MVFBSDEJ.WellPosedness.Existence
