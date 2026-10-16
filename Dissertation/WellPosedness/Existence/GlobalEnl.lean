/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.TerminalRepEnl
import Dissertation.WellPosedness.Existence.PaperSolution
import Dissertation.WellPosedness.Enlarged.CrossWitness

/-!
# Theorem 3.5 over the initially enlarged filtration

Let `D` be a Lévy driver with joint natural filtration `ℱ`, and let `𝒢₀` be a σ-algebra
independent of `⨆ t, ℱ_t`. The filtration of the well-posedness paper is
`enlJoint 𝒢₀ D h𝒢₀`, the usual augmentation of `t ↦ ℱ_t ⊔ 𝒢₀`. It is right-continuous, its
null sets lie in its time-`0` field, its right-continuation is constant before `0`, it admits a
cross witness (`Enlarged.crossWitnessEnl`), and for `d > 0` it has the terminal representation
property at every horizon `T > 0` (`hasTerminalRep_enlJoint`). So Theorem 3.5, over a general
filtration with these properties, holds over `enlJoint 𝒢₀ D h𝒢₀`.

Its time-`0` field contains `𝒢₀` (`Enlarged.le_enlJoint_zero`), so the initial datum `ξ₀` may be
any square-integrable `𝒢₀`-measurable random vector, random in general.

## Main definitions

* `SolvesEnl` — `(X, Y, Z, U)` solves (1.1) over `enlJoint 𝒢₀ D h𝒢₀`.
* `PaperSolutionEnl` — `(X, Y, Z, U)` solves (1.1) in the sense of the paper over
  `enlJoint 𝒢₀ D h𝒢₀`.

## Main statements

* `exists_solvesEnl_and_uniqueness_of_rank_of_diagonalLipschitzH` — Theorem 3.5 at the paper's
  Assumptions 2.3 and 2.4 over `enlJoint 𝒢₀ D h𝒢₀`: existence, and uniqueness in the sense of
  Theorem 3.3.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System Dissertation.WellPosedness.Enlarged LevyStochCalc
  LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- `(X, Y, Z, U)` solves the system (1.1) over the usual augmentation `enlJoint 𝒢₀ D h𝒢₀` of the
joint filtration of the driver enlarged at time `0` by a σ-algebra `𝒢₀` independent of it. -/
abbrev SolvesEnl (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T : ℝ) (C : Coeffs ν n m d)
    (ξ₀ : Fin n → Ω → ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop :=
  Solves D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T C ξ₀ X Y Z U γ

/-- `(X, Y, Z, U)` is a solution of (1.1) in the sense of the well-posedness paper over the usual
augmentation `enlJoint 𝒢₀ D h𝒢₀` of the joint filtration of the driver enlarged at time `0` by a
σ-algebra `𝒢₀` independent of it. -/
abbrev PaperSolutionEnl (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T : ℝ) (C : Coeffs ν n m d)
    (ξ₀ : Fin n → Ω → ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop :=
  PaperSolution D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T C ξ₀ X Y Z U γ

variable {T L cG α β₁ β₂ : ℝ}
  {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d} {ξ₀ : Fin n → Ω → ℝ}

/-- **Theorem 3.5 at the paper's Assumptions 2.3 and 2.4, over the initially enlarged filtration.**
For a Lévy driver `D` with `d > 0` Brownian coordinates, a σ-algebra `𝒢₀` independent of its joint
natural filtration and a horizon `T > 0`, let the coefficients be jointly Borel measurable on
`[0, T] × H × P₂(H)`, (2.3) with the Hilbert-norm `W₂` on `P₂(H)`, and satisfy Assumption 2.2,
Assumption 2.3 along the diagonal with constant `L` and the Hilbert-norm `W₂` on `P₂(H)` and `g`
Borel measurable in the state, and Assumption 2.5 along the diagonal with a coupling matrix
`G ∈ ℝ^{m×n}` of full rank and admissible constants `α, β₁, β₂`, and let `ξ₀` be square integrable
and measurable for the time-`0` field of `enlJoint 𝒢₀ D h𝒢₀`. Then the system (1.1) with initial
datum `ξ₀` has a solution over `enlJoint 𝒢₀ D h𝒢₀`, and any two solutions over `enlJoint 𝒢₀ D h𝒢₀`
coincide: `X¹, X²` and `Y¹, Y²` are indistinguishable on `[0, T]`, and `𝔼 ∫_0^T |Z¹ − Z²|²_F = 0`,
`𝔼 ∫_0^T ‖U¹ − U²‖²_{L²(ν)} = 0`, coordinatewise. -/
theorem exists_solvesEnl_and_uniqueness_of_rank_of_diagonalLipschitzH
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (hd : 0 < d) (hT : 0 < T)
    (hmeas : CoeffBorelW2 T C) (horig : CoeffOrigin T C)
    (hL : DiagonalLipschitzH (enlJoint 𝒢₀ D h𝒢₀) P T L C)
    (hLT : TerminalLipschitz (enlJoint 𝒢₀ D h𝒢₀) P T L C.g)
    (hg : ∀ ρ, Measurable fun x => C.g x ρ) (hG : G.rank = min m n)
    (hconst : Constants n m α β₁ β₂) (hM : DiagonalMonotone (enlJoint 𝒢₀ D h𝒢₀) P T G β₁ β₂ C)
    (hMT : TerminalMonotone (enlJoint 𝒢₀ D h𝒢₀) P T G α C.g) (hξ : ∀ i, MemLp (ξ₀ i) 2 P)
    (hξm : ∀ i, Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] (ξ₀ i)) :
    (∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
      (U : Fin m → ℝ → Ω → E → ℝ) (γ : Fin n → ℝ → Ω → E → ℝ),
      SolvesEnl D h𝒢₀ hind₀ T C ξ₀ X Y Z U γ)
    ∧ ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ)
      (γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ),
      SolvesEnl D h𝒢₀ hind₀ T C ξ₀ X₁ Y₁ Z₁ U₁ γ₁ → SolvesEnl D h𝒢₀ hind₀ T C ξ₀ X₂ Y₂ Z₂ U₂ γ₂ →
      (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
        ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
        ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
        ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0) :=
  exists_solves_and_uniqueness_of_rank_of_diagonalLipschitzH (crossWitnessEnl D h𝒢₀ hind₀)
    (hF0_enlJoint D h𝒢₀) (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (hasTerminalRep_enlJoint D h𝒢₀ hind₀ hd hT) hT hmeas horig hL hLT hg hG hconst hM hMT hξ hξm

end Dissertation.WellPosedness.Existence
