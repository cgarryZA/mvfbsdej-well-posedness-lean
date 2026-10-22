/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Existence.GlobalLipschitzH
import MVFBSDEJ.WellPosedness.System.PaperUniqueness

/-!
# Theorem 3.5 for solutions in the sense of the paper

Theorem 3.5 of the well-posedness paper asserts that the system (1.1) has a solution in `𝕊`,
unique in the sense of Theorem 3.3: `X`, `Y` indistinguishable on `[0, T]` and `Z`, `U` equal in
energy. `exists_solves_and_uniqueness_of_rank_of_diagonalLipschitzH` states it for the predicate
`Solves`; this file states it for the paper's solution notion `PaperSolution`, under the same
hypotheses.

* **Existence.** A solution of `Solves` becomes a solution in the sense of the paper after passing
  to predictable versions of `(Z, U)`
  (`MVFBSDEJ.WellPosedness.System.Solves.exists_paperSolution`), which needs the measurability
  (2.5) along every progressive tuple, a consequence of (2.3) (`CoeffBorelW2.toCoeffBorel`,
  `CoeffBorel.coeffRegular`).
* **Uniqueness.** A solution in the sense of the paper, extended off `[0, T]`, is a solution of
  `Solves` with the same `Z`, `U` and the same values on `[0, T]`
  (`MVFBSDEJ.WellPosedness.System.PaperSolution.exists_solves`), so the uniqueness of `Solves`
  applies (`MVFBSDEJ.WellPosedness.System.PaperSolution.uniqueness_of_solves_uniqueness`).

## Main statements

* `exists_paperSolution_and_uniqueness` — Theorem 3.5 in the sense of the paper, over a general
  filtration.
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

/-- **Theorem 3.5 for solutions in the sense of the paper.** Over a right-continuous filtration
carrying the driver, whose null sets lie in its time-`0` field, whose right-continuation is
constant before `0`, which admits a cross witness and has the terminal representation property
at the horizon `T > 0`, let the coefficients be jointly Borel measurable on
`[0, T] × H × P₂(H)`, (2.3) with the Hilbert-norm `W₂` on `P₂(H)`, and satisfy Assumption 2.2,
Assumption 2.3 along the diagonal with constant `L` and the Hilbert-norm `W₂` on `P₂(H)` and `g`
Borel measurable in the state, and Assumption 2.5 along the diagonal with a coupling matrix
`G ∈ ℝ^{m×n}` of full rank and admissible constants `α, β₁, β₂`, and let `ξ₀` be square
integrable and `ℱ_0`-measurable. Then the system (1.1) with initial datum `ξ₀` has a solution in
the sense of the paper, and any two such solutions coincide: `X¹, X²` and `Y¹, Y²` are
indistinguishable on `[0, T]`, and `𝔼 ∫_0^T |Z¹ − Z²|²_F = 0`,
`𝔼 ∫_0^T ‖U¹ − U²‖²_{L²(ν)} = 0`, coordinatewise. -/
theorem exists_paperSolution_and_uniqueness [ℱ.IsRightContinuous]
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
      PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ)
    ∧ ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ)
      (γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ),
      PaperSolution D ℱ hℱW hℱN T C ξ₀ X₁ Y₁ Z₁ U₁ γ₁ →
      PaperSolution D ℱ hℱW hℱN T C ξ₀ X₂ Y₂ Z₂ U₂ γ₂ →
      (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
        ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
        ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
        ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0) := by
  obtain ⟨⟨X, Y, Z, U, γ, hsol⟩, huniq⟩ :=
    exists_solves_and_uniqueness_of_rank_of_diagonalLipschitzH 𝒲 hℱ0 hnull hrep hT hmeas horig
      hL hLT hg hG hconst hM hMT hξ hξm
  refine ⟨?_, fun _ _ _ _ _ _ _ _ _ _ h₁ h₂ =>
    PaperSolution.uniqueness_of_solves_uniqueness hT.le huniq h₁ h₂⟩
  obtain ⟨Z', U', -, -, hp⟩ :=
    hsol.exists_paperSolution (hmeas.toCoeffBorel.coeffRegular ℱ P) 𝒲 hℱ0 hnull hT
  exact ⟨X, Y, Z', U', γ, hp⟩

end General

end MVFBSDEJ.WellPosedness.Existence
