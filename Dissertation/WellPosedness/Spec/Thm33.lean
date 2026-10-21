/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Spec.Bridge25
import Dissertation.WellPosedness.System.PaperUniquenessInt
import Dissertation.WellPosedness.Existence.GlobalEnl

/-!
# Theorem 3.3 under the printed assumptions

Theorem 3.3 of the well-posedness paper: under Assumptions 2.3–2.5, two tuples of `ℍ²` satisfying
(1.1) with the same initial condition coincide. This file states it over the paper's filtration, the
usual augmentation `enlJoint 𝒢₀ D h𝒢₀` of the filtration of the driver `D` enlarged at time `0` by a
σ-algebra `𝒢₀` independent of it, for the solution notion
`Dissertation.WellPosedness.System.PaperWeakSolutionInt`, with the hypotheses of the paper: the
standing setting, the measurability (2.3), Assumption 2.3 with a constant `L`, Assumption 2.4 as the
full rank of `G`, and Assumption 2.5.

The proof applies `Dissertation.WellPosedness.System.PaperWeakSolutionInt.uniqueness` with the
Lipschitz constant `2L` of the maximum-norm form of Assumption 2.3 and `c_G = s_min(G)⁻²`. The
measurability (2.3) and the positivity of the dimensions are part of the standing setting and are
not used.

## Main definitions

* `PaperWeakSolutionIntEnl` — `Dissertation.WellPosedness.System.PaperWeakSolutionInt` over
  `enlJoint 𝒢₀ D h𝒢₀`.

## Main statements

* `PaperWeakSolutionIntEnl.uniqueness_of_assumptions` — Theorem 3.3 under the printed
  assumptions.
-/

open MeasureTheory Filter ProbabilityTheory Matrix
open scoped ENNReal

namespace Dissertation.WellPosedness.Spec

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged LevyStochCalc

universe u v w

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- `(X, Y, Z, U)` is a solution of (1.1) in `ℍ²`, in the sense of `PaperWeakSolutionInt`,
over the usual augmentation `enlJoint 𝒢₀ D h𝒢₀` of the joint filtration of the driver enlarged at
time `0` by a σ-algebra `𝒢₀` independent of it. -/
abbrev PaperWeakSolutionIntEnl (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (h𝒢₀ : 𝒢₀ ≤ mΩ) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T : ℝ) (C : Coeffs ν n m d)
    (ξ₀ : Fin n → Ω → ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop :=
  PaperWeakSolutionInt D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T C ξ₀ X Y Z U γ

variable {T L α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d}

/-- **Theorem 3.3 under the printed assumptions.** Over `enlJoint 𝒢₀ D h𝒢₀`, with `n, m, d ≥ 1`
and `T > 0`, let the coefficients satisfy the measurability (2.3), Assumption 2.3 with a constant
`L`, Assumption 2.4 (`G` of full rank) and Assumption 2.5 with `G` and constants `α, β₁, β₂`.
Then any two solutions of (1.1) in `ℍ²` in the sense of `PaperWeakSolutionInt` with the same
initial datum coincide: `X¹, X²` and `Y¹, Y²` are indistinguishable on `[0, T]`, and
`𝔼 ∫_0^T |Z¹ − Z²|²_F = 0`, `𝔼 ∫_0^T ‖U¹ − U²‖²_{L²(ν)} = 0`, coordinatewise. -/
theorem PaperWeakSolutionIntEnl.uniqueness_of_assumptions
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (_hn : 0 < n) (_hm : 0 < m) (_hd : 0 < d)
    (hT : 0 < T) (_hJ : JointBorel T C) (h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C)
    (hG : G.rank = min m n) (h25 : Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C) :
    ∀ (ξ₀ : Fin n → Ω → ℝ) (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ)
      (γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ),
      PaperWeakSolutionIntEnl D h𝒢₀ hind₀ T C ξ₀ X₁ Y₁ Z₁ U₁ γ₁ →
      PaperWeakSolutionIntEnl D h𝒢₀ hind₀ T C ξ₀ X₂ Y₂ Z₂ U₂ γ₂ →
      (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
        ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
        ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
        ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0) :=
  fun _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ =>
  PaperWeakSolutionInt.uniqueness
    (h₁ := h₁)
    (h₂ := h₂)
    (𝒲 := crossWitnessEnl D h𝒢₀ hind₀)
    (hℱ0 := hF0_enlJoint D h𝒢₀)
    (hnull := fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (hT := hT)
    (hL := h23.interior.diagonalLipschitz_two_mul)
    (hLT := (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul)
    (hcG := inv_nonneg.mpr (sq_nonneg (sMin G)))
    (hGf := gCoerciveForward_of_rank hG)
    (hGb := gCoerciveBackward_of_rank hG)
    (hconst := h25.constants)
    (hM := h25.diagonalMonotone)
    (hMT := h25.terminalMonotone)

end Dissertation.WellPosedness.Spec
