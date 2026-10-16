/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.BridgeLip
import Dissertation.WellPosedness.System.BridgeMono
import Dissertation.WellPosedness.System.SolvesInt

/-!
# The Lipschitz and monotonicity bounds along two solutions in `ℍ²_weak`

Let `Θ¹, Θ²` solve the `λ`-forced system (4.1) in `ℍ²_weak` (`SolvesForcedInt`) with the same
coefficients. By Fubini, the finite energies of `Θ¹, Θ²` on `[0, T]` make `Θ¹_s, Θ²_s` square
integrable at almost every time `s ∈ [0, T]`; being strongly `ℱ_s`-measurable, `(Θ¹_s, μ¹_s)` and
`(Θ²_s, μ²_s)` are diagonal inputs at almost every time. And `X¹_T, X²_T` are square integrable and
`ℱ_T`-measurable. So Assumptions 2.3 and 2.5 along the diagonal apply at the pair, as in the proof
of Theorem 3.3, and give the expected Lipschitz bounds (3.2) and (2.6) with (2.9), with
`K = 10 L²` and `K_T = 4 L²`, and Assumption 2.5 at the pair, in the coordinates of
`PairLipschitz` and `PairMonotone`. No condition on the filtration beyond carrying the driver is
needed, and no integrability of the coefficient processes along either solution.

## Main statements

* `SolvesForcedInt.lip_pair`, `SolvesForcedInt.lipT_pair` — (3.2) and (2.6) with (2.9) along two
  solutions.
* `SolvesForcedInt.pairLipschitz` — the expected Lipschitz bounds at the pair.
* `SolvesForcedInt.mono_pair`, `SolvesForcedInt.monoT_pair` — (2.7) and the terminal inequality
  along two solutions.
* `SolvesForcedInt.pairMonotone` — Assumption 2.5 at the pair.
-/

open MeasureTheory Filter Matrix Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam : ℝ} {C : Coeffs ν n m d}
  {ξ₁ ξ₂ : Fin n → Ω → ℝ}
  {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ : Fin m → Ω → ℝ}
  {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {L α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}

namespace SolvesForcedInt

variable (h₁ : SolvesForcedInt D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
  (h₂ : SolvesForcedInt D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
include h₁ h₂

/-- **(3.2) along two solutions in `ℍ²_weak`.** For two solutions of the `λ`-forced system in
`ℍ²_weak` with the same coefficients, satisfying Assumption 2.3 along the diagonal with constant
`L`, at almost every time `s ∈ [0, T]`,
`𝔼[|δb_s|² + |δσ_s|²_F + ‖δh_s‖²_{L²(ν)} + |δf_s|²] ≤ 10 L² 𝔼 |δΘ_s|²`, in coordinates. -/
theorem lip_pair (hL : DiagonalLipschitz ℱ P T L C) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∫⁻ ω, (esq (fun i => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
            - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
          + ∑ i, esq (fun j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
          + ∑ i, ∫⁻ e, (‖jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
          + esq (fun k => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
            - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)) ∂P
        ≤ ENNReal.ofReal (10 * L ^ 2) * ∫⁻ ω, (esq (fun i => X₁ i s ω - X₂ i s ω)
          + esq (fun k => Y₁ k s ω - Y₂ k s ω) + ∑ k, esq (fun j => Z₁ k s ω j - Z₂ k s ω j)
          + ∑ k, ∫⁻ e, (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P :=
  hL.lip_pair h₁.stronglyMeasurable_tupleAt h₂.stronglyMeasurable_tupleAt h₁.ae_memLp_tupleAt
    h₂.ae_memLp_tupleAt h₁.ae_ae_memLp_jump h₂.ae_ae_memLp_jump h₁.jump_rep h₂.jump_rep

/-- **(2.6) with (2.9) along two solutions in `ℍ²_weak`.** For two solutions of the `λ`-forced
system in `ℍ²_weak` with the same terminal function, satisfying (2.6) along the diagonal with
constant `L`,
`𝔼 |δg_T|² ≤ 4 L² 𝔼 |δX_T|²`, in coordinates. -/
theorem lipT_pair (hLT : TerminalLipschitz ℱ P T L C.g) :
    ∫⁻ ω, esq (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) ∂P
      ≤ ENNReal.ofReal (4 * L ^ 2) * ∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P :=
  hLT.lipT_pair (fun i => (h₁.fwd i).X_adapted T) (fun i => (h₂.fwd i).X_adapted T) h₁.XT_sq
    h₂.XT_sq

/-- **The expected Lipschitz bounds at a pair of solutions in `ℍ²_weak`.** Two solutions of the
`λ`-forced system in `ℍ²_weak` with the same coefficients, satisfying Assumption 2.3 along the
diagonal with constant `L`, satisfy `PairLipschitz` with `K = 10 L²` and `K_T = 4 L²`. -/
theorem pairLipschitz (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g) :
    PairLipschitz P ν T (10 * L ^ 2) (4 * L ^ 2) (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) where
  lip := h₁.lip_pair h₂ hL
  lipT := h₁.lipT_pair h₂ hLT

/-- **(2.7) along two solutions in `ℍ²_weak`.** For two solutions of the `λ`-forced system in
`ℍ²_weak` with the same coefficients, satisfying Assumption 2.5 along the diagonal, at almost every
time
`s ∈ [0, T]`,
`𝔼[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F − ⟨δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)]
  ≤ −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²] − β₂ 𝔼|G δX|²`, in coordinates. -/
theorem mono_pair (hM : DiagonalMonotone ℱ P T G β₁ β₂ C) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∫ ω, ((fun i => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
          + ∑ j, (fun i => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
          - (fun k => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
            ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)
          + ∫ e, (fun i => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
            ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν) ∂P
        ≤ -β₁ * ∫ ω, ((Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
              ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
            + ∑ j, (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
              ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
            + ∫ e, (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e)
              ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν) ∂P
          - β₂ * ∫ ω, (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)
              ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω) ∂P :=
  hM.mono_pair h₁.stronglyMeasurable_tupleAt h₂.stronglyMeasurable_tupleAt h₁.ae_memLp_tupleAt
    h₂.ae_memLp_tupleAt h₁.ae_ae_memLp_jump h₂.ae_ae_memLp_jump h₁.jump_rep h₂.jump_rep

/-- **The terminal inequality of Assumption 2.5 along two solutions in `ℍ²_weak`.** For two
solutions of the `λ`-forced system in `ℍ²_weak` with the same terminal function, satisfying the
terminal inequality along the diagonal, `α 𝔼|G δX_T|² ≤ 𝔼⟨δg_T, G δX_T⟩`, in coordinates. -/
theorem monoT_pair (hMT : TerminalMonotone ℱ P T G α C.g) :
    α * ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ∂P
      ≤ ∫ ω, (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
          ⬝ᵥ (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ∂P :=
  hMT.monoT_pair (fun i => (h₁.fwd i).X_adapted T) (fun i => (h₂.fwd i).X_adapted T) h₁.XT_sq
    h₂.XT_sq

/-- **Assumption 2.5 at a pair of solutions in `ℍ²_weak`.** Two solutions of the `λ`-forced system
in
`ℍ²_weak` with the same coefficients, satisfying Assumption 2.5 along the diagonal with coupling
matrix `G` and constants `α, β₁, β₂`, satisfy `PairMonotone` with the same `G, α, β₁, β₂`. -/
theorem pairMonotone (hM : DiagonalMonotone ℱ P T G β₁ β₂ C)
    (hMT : TerminalMonotone ℱ P T G α C.g) :
    PairMonotone P ν T G α β₁ β₂ (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) where
  mono := h₁.mono_pair h₂ hM
  monoT := h₁.monoT_pair h₂ hMT

end SolvesForcedInt

end Dissertation.WellPosedness.System
