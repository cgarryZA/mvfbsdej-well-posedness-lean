/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.PaperWeakSolutionIntSolves
import Dissertation.WellPosedness.System.UniquenessInt

/-!
# Theorem 3.3 in the paper's solution notion, in `ℍ²`

Theorem 3.3 of the well-posedness paper: under Assumptions 2.3–2.5, if `Θ¹, Θ² ∈ ℍ²` satisfy
(1.1) with the same initial condition, then `Θ¹ = Θ²`. Assumption 2.2 is not used (Remark 3.4):
along each solution the drift and the driver need only have almost surely integrable paths on
`[0, T]`, and the initial datum need not be square integrable. The terminal condition
`g(X_T, Law X_T)` presupposes that `X_T` is square integrable. This file states the theorem for
the solution notion `PaperWeakSolutionInt`, which records these conditions in the encoding of
`PaperSolution`, under the hypotheses of Theorem 3.3.

A solution of `PaperWeakSolutionInt`, extended off `[0, T]`, is a solution of `SolvesInt` with
the same `Z`, `U` and the same values of `X`, `Y` on `[0, T]`
(`PaperWeakSolutionInt.exists_solvesInt`), and the conclusion of Theorem 3.3 sees `X`, `Y` only
on `[0, T]`. So any uniqueness statement for `SolvesInt` of this form passes to
`PaperWeakSolutionInt`, with no condition on the coefficients
(`PaperWeakSolutionInt.uniqueness_of_solvesInt_uniqueness`), and `SolvesInt.uniqueness` gives
the theorem.

## Main statements

* `PaperWeakSolutionInt.uniqueness_of_solvesInt_uniqueness` — uniqueness for `SolvesInt` gives
  uniqueness for `PaperWeakSolutionInt`.
* `PaperWeakSolutionInt.uniqueness` — Theorem 3.3 in the paper's solution notion, in
  `ℍ²`.
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

/-- **Uniqueness for `SolvesInt` gives uniqueness for `PaperWeakSolutionInt`.** For `T ≥ 0`, if
any two solutions of `SolvesInt` with coefficients `C` and initial datum `ξ₀` have
indistinguishable `X` and `Y` on `[0, T]` and `Z`, `U` differing by zero energy, coordinatewise,
then so do any two solutions of `PaperWeakSolutionInt` with the same coefficients and initial
datum. -/
theorem PaperWeakSolutionInt.uniqueness_of_solvesInt_uniqueness (hT : 0 ≤ T)
    (huniq : ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ)
      (γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ),
      SolvesInt D ℱ hℱW hℱN T C ξ₀ X₁ Y₁ Z₁ U₁ γ₁ →
      SolvesInt D ℱ hℱW hℱN T C ξ₀ X₂ Y₂ Z₂ U₂ γ₂ →
      (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
        ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
        ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
        ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0))
    (h₁ : PaperWeakSolutionInt D ℱ hℱW hℱN T C ξ₀ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : PaperWeakSolutionInt D ℱ hℱW hℱN T C ξ₀ X₂ Y₂ Z₂ U₂ γ₂) :
    (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
      ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
      ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
      ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0) := by
  obtain ⟨X₁', Y₁', hX₁, hY₁, hs₁⟩ := h₁.exists_solvesInt hT
  obtain ⟨X₂', Y₂', hX₂, hY₂, hs₂⟩ := h₂.exists_solvesInt hT
  obtain ⟨hX, hY, hZ, hU⟩ := huniq _ _ _ _ _ _ _ _ _ _ hs₁ hs₂
  refine ⟨fun i => ?_, fun k => ?_, hZ, hU⟩
  · filter_upwards [hX i] with ω hω t ht
    rw [← congrFun (hX₁ i t ht) ω, ← congrFun (hX₂ i t ht) ω]
    exact hω t ht
  · filter_upwards [hY k] with ω hω t ht
    rw [← congrFun (hY₁ k t ht) ω, ← congrFun (hY₂ k t ht) ω]
    exact hω t ht

/-- **Theorem 3.3 in the paper's solution notion, in `ℍ²`.** Under Assumption 2.3 along the
diagonal, Assumption 2.4 with `c_G ≥ 0` and Assumption 2.5 along the diagonal with admissible
constants, two solutions of (1.1) in `ℍ²` in the sense of `PaperWeakSolutionInt` — drift and
driver integrable along almost every path, `X_T` square integrable — with the same coefficients
and the same initial datum coincide: `X¹, X²` and `Y¹, Y²` are indistinguishable on `[0, T]`, and
`𝔼 ∫_0^T |Z¹ − Z²|²_F = 0`, `𝔼 ∫_0^T ‖U¹ − U²‖²_{L²(ν)} = 0`, coordinatewise, over a filtration
whose null sets lie in its time-`0` field, whose right-continuation is constant before `0` and
which admits a cross witness. -/
theorem PaperWeakSolutionInt.uniqueness
    (h₁ : PaperWeakSolutionInt D ℱ hℱW hℱN T C ξ₀ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : PaperWeakSolutionInt D ℱ hℱW hℱN T C ξ₀ X₂ Y₂ Z₂ U₂ γ₂)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g) (hcG : 0 ≤ cG)
    (hGf : n ≤ m → GCoerciveForward (GX G) cG) (hGb : m ≤ n → GCoerciveBackward (GX G) cG)
    (hconst : Constants n m α β₁ β₂) (hM : DiagonalMonotone ℱ P T G β₁ β₂ C)
    (hMT : TerminalMonotone ℱ P T G α C.g) :
    (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
      ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
      ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
      ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0) :=
  PaperWeakSolutionInt.uniqueness_of_solvesInt_uniqueness hT.le
    (fun _ _ _ _ _ _ _ _ _ _ s₁ s₂ =>
      SolvesInt.uniqueness s₁ s₂ 𝒲 hℱ0 hnull hT hL hLT hcG hGf hGb hconst hM hMT) h₁ h₂

end General

end Dissertation.WellPosedness.System
