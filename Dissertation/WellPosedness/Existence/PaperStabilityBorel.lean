/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.CoeffBorel
import Dissertation.WellPosedness.System.Stability
import Dissertation.WellPosedness.System.Uniqueness
import Dissertation.WellPosedness.System.PaperStability

/-!
# Theorem 3.1 in the sense of the paper under the joint measurability of the coefficients

`PaperSolution.supSize_sub_le` states Theorem 3.1 of the well-posedness paper for solutions in the
sense of the paper, with the cross-evaluation `CrossEval` of system 1 along `Θ²` as a hypothesis.
When `C¹` is jointly measurable, (2.3) with the evaluation σ-algebra on `P₂(H)`, that hypothesis
holds with the canonical representative `coeffJump P T C¹ X² Y² Z² U²` of `h¹` along `Θ²`: the
extension of `Θ²` off `[0, T]` solves `Solves` and is a progressive tuple, along which
`CoeffBorel.crossEval` applies, and both the cross-evaluation and `coeffJump` see the tuple only
on `[0, T]` (`CrossEval.of_eqOn`, `coeffJump_eq_of_eqOn`). This file states the result for
`PaperSolution`.

## Main statements

* `coeffJump_eq_of_eqOn` — the canonical representative of the jump coefficient sees `X` and `Y`
  only on `[0, T]`.
* `PaperSolution.supSize_sub_le_of_coeffBorel` — Theorem 3.1 in the sense of the paper for a
  jointly measurable `C¹`.
-/

open MeasureTheory Filter Matrix Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open LevyStochCalc.BSDEJ.Solves Dissertation.WellPosedness.BrownianPoisson
  Dissertation.WellPosedness.Stability Dissertation.WellPosedness.Existence

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}

/-- **The canonical jump representative sees `X` and `Y` only on `[0, T]`**: if `X' = X` and
`Y' = Y` at every time of `[0, T]`, then `coeffJump` along `(X', Y', Z, U)` equals `coeffJump`
along `(X, Y, Z, U)`. -/
theorem _root_.Dissertation.WellPosedness.Existence.coeffJump_eq_of_eqOn {C : Coeffs ν n m d}
    {X X' : Fin n → ℝ → Ω → ℝ} {Y Y' : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
    {U : Fin m → ℝ → Ω → E → ℝ} (hX : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X i t)
    (hY : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y k t) :
    coeffJump P T C X' Y' Z U = coeffJump P T C X Y Z U := by
  funext i s ω e
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · simp only [coeffJump, Set.indicator_of_mem hs, tupleAt_eq_of_eqOn hX hY hs]
  · simp only [coeffJump, Set.indicator_of_notMem hs]

variable {C₁ C₂ : Coeffs ν n m d}
  {ξ₁ ξ₂ : Fin n → Ω → ℝ} {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {L cG α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}

/-- **Theorem 3.1 for solutions in the sense of the paper and a jointly measurable system 1.** Let
`C¹` be jointly measurable, (2.3) with the evaluation σ-algebra on `P₂(H)`, and satisfy Assumption
2.3 along the diagonal with constant `L`, Assumption 2.4 with coupling matrix `G` and constant
`c_G ≥ 0` and Assumption 2.5 along the diagonal with admissible constants `α, β₁, β₂`, let
`g¹, g²` be Borel measurable in the state, and let `Θᵏ` be a solution of (1.1) for `Cᵏ` in the
sense of the paper, with jump representative `γᵏ`. Then

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)
  ≤ C_stab (𝔼|δξ₀|² + 𝔼|δ̂g_T|² + 𝔼 ∫_0^T (|δb|² + |δσ|²_F + ‖δh‖² + |δf|²))`,

the coefficient differences `ψ¹ − ψ²` evaluated along `Θ²`, the jump coefficients through the
canonical representative `coeffJump` of `h¹` along `Θ²` and the representative `γ²`, and
`C_stab = aprioriConst T (10 L²) (4 L²) ‖G‖ c_G α β₁ β₂ 1`, over a filtration whose null sets lie
in its time-`0` field, whose right-continuation is constant before `0` and which admits a cross
witness. -/
theorem PaperSolution.supSize_sub_le_of_coeffBorel {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
    {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
    (h₁ : PaperSolution D ℱ hℱW hℱN T C₁ ξ₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : PaperSolution D ℱ hℱW hℱN T C₂ ξ₂ X₂ Y₂ Z₂ U₂ γ₂) (hmeas₁ : CoeffBorel T C₁)
    (hg₁ : ∀ ρ, Measurable fun x => C₁.g x ρ) (hg₂ : ∀ ρ, Measurable fun x => C₂.g x ρ)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hL : DiagonalLipschitz ℱ P T L C₁) (hLT : TerminalLipschitz ℱ P T L C₁.g) (hcG : 0 ≤ cG)
    (hGf : n ≤ m → GCoerciveForward (GX G) cG) (hGb : m ≤ n → GCoerciveBackward (GX G) cG)
    (hconst : Constants n m α β₁ β₂) (hM : DiagonalMonotone ℱ P T G β₁ β₂ C₁)
    (hMT : TerminalMonotone ℱ P T G α C₁.g) :
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      ≤ ENNReal.ofReal (aprioriConst T (10 * L ^ 2) (4 * L ^ 2) ‖GX G‖ cG α β₁ β₂ 1)
        * dataSize P ν T (fun i ω => ξ₁ i ω - ξ₂ i ω)
          (fun i ω s => driftProc P T C₁ X₂ Y₂ Z₂ U₂ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
          (fun i s ω j => diffusionProc P T C₁ X₂ Y₂ Z₂ U₂ i s ω j
            - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
          (fun i s ω e => jumpProc T (coeffJump P T C₁ X₂ Y₂ Z₂ U₂) i s ω e
            - jumpProc T γ₂ i s ω e)
          (fun k ω s => driverProc P T C₁ X₂ Y₂ Z₂ U₂ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
          (fun k ω => terminalVal P T C₁ X₂ k ω - terminalVal P T C₂ X₂ k ω) := by
  obtain ⟨X₂', Y₂', hX₂, hY₂, hs₂⟩ := h₂.exists_solves hT.le
  have hX := (hmeas₁.crossEval (SolvesForced.progTuple hs₂)).of_eqOn
    (fun i t ht => (hX₂ i t ht).symm) (fun k t ht => (hY₂ k t ht).symm)
  rw [coeffJump_eq_of_eqOn hX₂ hY₂] at hX
  exact h₁.supSize_sub_le h₂ hX hg₁ hg₂ 𝒲 hℱ0 hnull hT hL hLT hcG hGf hGb hconst hM hMT

end Dissertation.WellPosedness.System
