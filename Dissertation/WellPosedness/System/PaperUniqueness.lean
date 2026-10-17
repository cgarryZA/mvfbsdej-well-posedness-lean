/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.Stability
import Dissertation.WellPosedness.System.Uniqueness
import Dissertation.WellPosedness.System.PaperSolutionSolves

/-!
# Theorem 3.3 for solutions in the sense of the paper

Theorem 3.3 of the paper asserts that under Assumptions 2.3–2.5 two solutions of (1.1) in `ℍ²`
with the same coefficients and the same initial datum coincide: `X`, `Y` indistinguishable on
`[0, T]` and `Z`, `U` equal in energy. `Solves.uniqueness` states it for the predicate `Solves`;
this file shows that such a statement passes to the paper's solution notion `PaperSolution`.

A solution in the sense of the paper, extended off `[0, T]`, is a solution of `Solves` with the
same `Z`, `U` and the same values of `X`, `Y` on `[0, T]` (`PaperSolution.exists_solves`), and the
conclusion of Theorem 3.3 sees `X`, `Y` only on `[0, T]`. So any uniqueness statement for `Solves`
of this form passes to the paper's notion, with no condition on the coefficients
(`PaperSolution.uniqueness_of_solves_uniqueness`).

## Main statements

* `PaperSolution.uniqueness_of_solves_uniqueness` — uniqueness for `Solves` gives uniqueness in
  the sense of the paper.
-/

open MeasureTheory Filter Matrix
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ} {C : Coeffs ν n m d} {ξ₀ : Fin n → Ω → ℝ}
  {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {L cG α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}

section General

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}

/-- **Uniqueness for `Solves` gives uniqueness in the sense of the paper.** For `T ≥ 0`, if any
two solutions of `Solves` with coefficients `C` and initial datum `ξ₀` have indistinguishable `X`
and `Y` on `[0, T]` and `Z`, `U` differing by zero energy, coordinatewise, then so do any two
solutions of (1.1) in the sense of the paper with the same coefficients and initial datum. -/
theorem PaperSolution.uniqueness_of_solves_uniqueness (hT : 0 ≤ T)
    (huniq : ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ)
      (γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ),
      Solves D ℱ hℱW hℱN T C ξ₀ X₁ Y₁ Z₁ U₁ γ₁ → Solves D ℱ hℱW hℱN T C ξ₀ X₂ Y₂ Z₂ U₂ γ₂ →
      (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
        ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
        ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
        ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0))
    (h₁ : PaperSolution D ℱ hℱW hℱN T C ξ₀ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : PaperSolution D ℱ hℱW hℱN T C ξ₀ X₂ Y₂ Z₂ U₂ γ₂) :
    (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
      ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
      ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
      ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0) := by
  obtain ⟨X₁', Y₁', hX₁, hY₁, hs₁⟩ := h₁.exists_solves hT
  obtain ⟨X₂', Y₂', hX₂, hY₂, hs₂⟩ := h₂.exists_solves hT
  obtain ⟨hX, hY, hZ, hU⟩ := huniq _ _ _ _ _ _ _ _ _ _ hs₁ hs₂
  refine ⟨fun i => ?_, fun k => ?_, hZ, hU⟩
  · filter_upwards [hX i] with ω hω t ht
    rw [← congrFun (hX₁ i t ht) ω, ← congrFun (hX₂ i t ht) ω]
    exact hω t ht
  · filter_upwards [hY k] with ω hω t ht
    rw [← congrFun (hY₁ k t ht) ω, ← congrFun (hY₂ k t ht) ω]
    exact hω t ht

end General

end Dissertation.WellPosedness.System
