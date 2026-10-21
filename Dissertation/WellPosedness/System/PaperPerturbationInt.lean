/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.PaperStability
import Dissertation.WellPosedness.System.PaperWeakSolutionForcedIntSolves
import Dissertation.WellPosedness.System.UniquenessInt

/-!
# Lemma 4.3 in the paper's solution notion, in `ℍ²`

Lemma 4.3 of the well-posedness paper: under Assumptions 2.3–2.5, for `λ ∈ [λ̲, 1]`, `λ̲ > 0`,
two solutions `Θ¹, Θ²` of the `λ`-forced system (4.1) with the same coefficients, initial data
`ξ₀¹, ξ₀²` and forcings `q¹, q²`, whose `X`, `Y` are càdlàg adapted with finite
`𝔼 ∫_0^T |·|² dt`, whose `X_T` is square integrable and whose `Z`, `U` lie in `H²_W`, `H²_N`,
satisfy

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ_t|²_F + ‖δU_t‖²_{L²(ν)}) dt
  ≤ C_B (𝔼|δξ₀|² + 𝔼|δq^g_T|²
    + 𝔼 ∫_0^T (|δq^b_t|² + |δq^σ_t|²_F + ‖δq^h_t‖²_{L²(ν)} + |δq^f_t|²) dt)`.   (4.14)

Assumption 2.2 is not used: along each solution the forced drift and driver need only have
almost surely integrable paths on `[0, T]`, and neither the initial data nor the terminal values
need be square integrable. This file states the lemma for the solution notion
`PaperWeakSolutionForcedInt`, which records these conditions in the encoding of
`PaperSolutionForced`, under the hypotheses of Lemma 4.3 and with the same two sides.

A solution of `PaperWeakSolutionForcedInt`, extended off `[0, T]`, is a solution of
`SolvesForcedInt` with the same `Z`, `U` and the same values of `X`, `Y` on `[0, T]`
(`PaperWeakSolutionForcedInt.exists_solvesForcedInt`); the left-hand side of (4.14) sees `X` and
`Y` only on `[0, T]` (`supSize_eq_of_eqOn`), and the right-hand side does not see the solutions.
So `SolvesForcedInt.supSize_sub_le` gives the lemma.

Two hypotheses of the paper's statement are absent. The initial data need not be
`ℱ_0`-measurable: by the forward identity at `0`, `ξ₀ = X_0` almost surely. And `Θ¹ − Θ² ∈ 𝕊`
is not a hypothesis of `SolvesForcedInt.supSize_sub_le`.

## Main statements

* `PaperWeakSolutionForcedInt.supSize_sub_le` — Lemma 4.3 in the paper's solution notion, in
  `ℍ²`.
-/

open MeasureTheory Filter Matrix
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open LevyStochCalc.BSDEJ.Solves Dissertation.WellPosedness.BrownianPoisson
  Dissertation.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T lam : ℝ} {C : Coeffs ν n m d}
  {ξ₁ ξ₂ : Fin n → Ω → ℝ}
  {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ : Fin m → Ω → ℝ}
  {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {L cG α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}

/-- **Lemma 4.3 in the paper's solution notion, in `ℍ²`.** Let the coefficients satisfy
Assumption 2.3 along the diagonal with constant `L`, Assumption 2.4 with coupling matrix `G` and
constant `c_G ≥ 0` (the forward bound when `n ≤ m`, the backward one when `m ≤ n`) and
Assumption 2.5 along the diagonal with admissible constants `α, β₁, β₂`, and let `λ ∈ [λ̲, 1]`,
`λ̲ > 0`. Two solutions of the `λ`-forced system (4.1) in the sense of
`PaperWeakSolutionForcedInt` — forced drift and driver integrable along almost every path, `X_T`
square integrable — with these coefficients, initial data `ξ₀¹, ξ₀²` and forcings `q¹, q²`
satisfy

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)
  ≤ C_B (𝔼|δξ₀|² + 𝔼|δq^g_T|² + 𝔼 ∫_0^T (|δq^b|² + |δq^σ|²_F + ‖δq^h‖² + |δq^f|²))`,

`C_B = aprioriConst T (10 L²) (4 L²) ‖G‖ c_G α β₁ β₂ λ̲`, over a filtration whose null sets lie
in its time-`0` field, whose right-continuation is constant before `0` and which admits a cross
witness. -/
theorem PaperWeakSolutionForcedInt.supSize_sub_le {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
    {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
    (h₁ : PaperWeakSolutionForcedInt D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : PaperWeakSolutionForcedInt D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    {lamLow : ℝ} (hlow : 0 < lamLow) (hlam : lamLow ≤ lam) (hlam1 : lam ≤ 1)
    (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g) (hcG : 0 ≤ cG)
    (hGf : n ≤ m → GCoerciveForward (GX G) cG) (hGb : m ≤ n → GCoerciveBackward (GX G) cG)
    (hconst : Constants n m α β₁ β₂) (hM : DiagonalMonotone ℱ P T G β₁ β₂ C)
    (hMT : TerminalMonotone ℱ P T G α C.g) :
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      ≤ ENNReal.ofReal (aprioriConst T (10 * L ^ 2) (4 * L ^ 2) ‖GX G‖ cG α β₁ β₂ lamLow)
        * dataSize P ν T (fun i ω => ξ₁ i ω - ξ₂ i ω) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
          (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
          (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω) := by
  obtain ⟨X₁', Y₁', hX₁, hY₁, hs₁⟩ := h₁.exists_solvesForcedInt hT.le
  obtain ⟨X₂', Y₂', hX₂, hY₂, hs₂⟩ := h₂.exists_solvesForcedInt hT.le
  have h := hs₁.supSize_sub_le hs₂ 𝒲 hℱ0 hnull hT hlow hlam hlam1 hL hLT hcG hGf hGb hconst hM
    hMT
  rwa [supSize_eq_of_eqOn (X := fun i t ω => X₁ i t ω - X₂ i t ω)
    (Y := fun k t ω => Y₁ k t ω - Y₂ k t ω)
    (fun i t ht => funext fun ω => by
      simp only [congrFun (hX₁ i t ht) ω, congrFun (hX₂ i t ht) ω])
    (fun k t ht => funext fun ω => by
      simp only [congrFun (hY₁ k t ht) ω, congrFun (hY₂ k t ht) ω])] at h

end Dissertation.WellPosedness.System
