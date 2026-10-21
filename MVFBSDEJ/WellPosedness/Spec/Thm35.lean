/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Spec.Bridge22
import MVFBSDEJ.WellPosedness.Spec.Thm33
import MVFBSDEJ.WellPosedness.Existence.PaperSolutionInt

/-!
# Theorem 3.5 under the printed assumptions

Theorem 3.5 of the well-posedness paper: for every horizon `T > 0`, under Assumptions 2.2–2.5 the
system (1.1) has a solution in `𝕊`, unique by Theorem 3.3, that is among the tuples of `ℍ²`
satisfying (1.1) with the same initial condition. This file states it over the paper's filtration
`enlJoint 𝒢₀ D h𝒢₀`, for the solution notions `MVFBSDEJ.WellPosedness.System.PaperSolution` and
`MVFBSDEJ.WellPosedness.System.PaperWeakSolutionInt`, with the hypotheses of the paper: the
standing setting, the measurability (2.3), Assumption 2.2 with the initial datum `ξ₀ : Ω → ℝⁿ`,
Assumption 2.3 with a constant `L`, Assumption 2.4 as the full rank of `G`, and Assumption 2.5.

The proof applies
`MVFBSDEJ.WellPosedness.Existence.exists_paperSolution_unique_paperWeakSolutionInt`, which takes
the initial datum by its coordinates `ξ₀^i` and the terminal function by its sections `x ↦ g(x, ρ)`.
The positivity of `n` and `m` is part of the standing setting and is not used.

## Main statements

* `exists_paperSolutionEnl_unique_of_assumptions` — Theorem 3.5 under the printed assumptions.
-/

open MeasureTheory Filter ProbabilityTheory Matrix
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.Spec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged LevyStochCalc

universe u v w

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {T L α β₁ β₂ : ℝ}
  {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d} {ξ₀ : Ω → EuclideanSpace ℝ (Fin n)}

/-- **Theorem 3.5 under the printed assumptions.** Over `enlJoint 𝒢₀ D h𝒢₀`, with `n, m, d ≥ 1`
and `T > 0`, let the coefficients satisfy the measurability (2.3), Assumption 2.2 with the initial
datum `ξ₀`, Assumption 2.3 with a constant `L`, Assumption 2.4 (`G` of full rank) and
Assumption 2.5 with `G` and constants `α, β₁, β₂`. Then (1.1) with initial datum `ξ₀` has a
solution `(X, Y, Z, U)` in the sense of `PaperSolution`, and every solution `(X', Y', Z', U')` in
`ℍ²` in the sense of `PaperWeakSolutionInt` with initial datum `ξ₀` coincides with it:
`X, X'` and `Y, Y'` are indistinguishable on `[0, T]`, and `𝔼 ∫_0^T |Z − Z'|²_F = 0`,
`𝔼 ∫_0^T ‖U − U'‖²_{L²(ν)} = 0`, coordinatewise. -/
theorem exists_paperSolutionEnl_unique_of_assumptions
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (_hn : 0 < n) (_hm : 0 < m) (hd : 0 < d)
    (hT : 0 < T) (hJ : JointBorel T C) (h22 : Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀)
    (h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C) (hG : G.rank = min m n)
    (h25 : Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C) :
    ∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
      (U : Fin m → ℝ → Ω → E → ℝ) (γ : Fin n → ℝ → Ω → E → ℝ),
      PaperSolutionEnl D h𝒢₀ hind₀ T C (fun i ω => ξ₀ ω i) X Y Z U γ
      ∧ ∀ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ)
        (Z' : Fin m → ℝ → Ω → Fin d → ℝ) (U' : Fin m → ℝ → Ω → E → ℝ)
        (γ' : Fin n → ℝ → Ω → E → ℝ),
        PaperWeakSolutionIntEnl D h𝒢₀ hind₀ T C (fun i ω => ξ₀ ω i) X' Y' Z' U' γ' →
        (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X i t ω = X' i t ω)
          ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y k t ω = Y' k t ω)
          ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z k s ω j - Z' k s ω j) = 0)
          ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
              (fun ω s e => U k s ω e - U' k s ω e) = 0) :=
  exists_paperSolution_unique_paperWeakSolutionInt
    (𝒲 := crossWitnessEnl D h𝒢₀ hind₀)
    (hℱ0 := hF0_enlJoint D h𝒢₀)
    (hnull := fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (hrep := hasTerminalRep_enlJoint D h𝒢₀ hind₀ hd hT)
    (hT := hT)
    (hmeas := (jointBorel_iff.mp hJ).1)
    (horig := originValues_iff_coeffOrigin.mp h22.origin)
    (hL := lipInterior_iff_diagonalLipschitzH.mp h23.interior)
    (hLT := lipTerminal_iff_terminalLipschitz.mp h23.terminal)
    (hg := hJ.measurable_g_section)
    (hG := hG)
    (hconst := h25.constants)
    (hM := h25.diagonalMonotone)
    (hMT := h25.terminalMonotone)
    (hξ := memLp_iff_forall_coord.mp h22.initial_memLp)
    (hξm := stronglyMeasurable_iff_forall_coord.mp h22.initial_meas)

end MVFBSDEJ.WellPosedness.Spec
