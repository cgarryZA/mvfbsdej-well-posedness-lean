/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.SolvesIntEnergy

/-!
# The difference of two solutions of the `λ`-forced system in `ℍ²_weak`

Let `Θ¹, Θ²` solve the `λ`-forced system (4.1) in `ℍ²_weak` (`SolvesForcedInt`) with coefficients
`C¹, C²`, initial data `ξ₀¹, ξ₀²` and forcings `q¹, q²`, at the same `λ`, and let the expected
Lipschitz bounds (`PairLipschitz`) and Assumption 2.5 (`PairMonotone`) hold at the pair. The
equations of each solution are those of `LinearFSDEJInt` and `LinearBSDEJInt`, whose drifts need
not be square integrable. Their difference is nevertheless the difference system `PairDiff` of
Lemma 4.3, whose equations are the `L²` ones of `LinearFSDEJ` and `LinearBSDEJ`, as in the proof
of Theorem 3.3 of the well-posedness paper:

* the drift `λ δb + δq^b` and the driver `λ δf + δq^f` of the difference equations have finite
  energy on `[0, T]`, by (3.2) at the pair integrated in time
  (`SolvesForcedInt.energy_drift_sub_ne_top`);
* the terminal difference `λ δg_T + δq^g_T` is square integrable, by (2.6) with (2.9) at the pair
  (`SolvesForcedInt.memLp_terminal_sub`);
* the initial difference `δξ₀` is square integrable, by the forward difference equation at `T`,
  since `δX_T` is (`LinearFSDEJInt.memLp_initial_sub`).

For the same coefficients, Assumptions 2.3 and 2.5 along the diagonal give the conditions at the
pair (`SolvesForcedInt.pairLipschitz`, `SolvesForcedInt.pairMonotone`), with no condition on the
filtration beyond carrying the driver.

## Main statements

* `SolvesForcedInt.fwd_sub`, `SolvesForcedInt.bwd_sub` — the difference equations (4.15)–(4.16)
  in the `L²` form.
* `SolvesForcedInt.pairDiff` — the difference of two solutions is a `PairDiff`, given
  `PairLipschitz` and `PairMonotone` for it.
* `SolvesForcedInt.pairDiff_of_assumptions` — the same under Assumptions 2.3 and 2.5 along the
  diagonal, for the same coefficients.
-/

open MeasureTheory Filter Matrix MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam : ℝ}
  {C₁ C₂ : Coeffs ν n m d} {ξ₁ ξ₂ : Fin n → Ω → ℝ}
  {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ : Fin m → Ω → ℝ}
  {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {K KT α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}

namespace SolvesForcedInt

variable (h₁ : SolvesForcedInt D ℱ hℱW hℱN T lam C₁ ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
  (h₂ : SolvesForcedInt D ℱ hℱW hℱN T lam C₂ ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
include h₁ h₂

/-- **The forward difference equation (4.15) in `ℍ²_weak`**: for `T ≥ 0` and the expected Lipschitz
bounds at the pair, coordinate `i` of `δX` solves the linear forward equation of `LinearFSDEJ`
from `δξ₀` with drift `λ δb + δq^b`, diffusion `λ δσ + δq^σ` and jump integrand
`λ δγ + δq^h`. -/
theorem fwd_sub (hT : 0 ≤ T)
    (hL : PairLipschitz P ν T K KT (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω)) (i : Fin n) :
    LinearFSDEJ D ℱ hℱW hℱN T (fun ω => ξ₁ i ω - ξ₂ i ω)
      (fun ω s => lam * (driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s
          - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s) + (qb₁ i ω s - qb₂ i ω s))
      (fun t ω => X₁ i t ω - X₂ i t ω)
      (fun s ω j => lam * (diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
          - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j))
      (fun s ω e => lam * (jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
          + (qh₁ i s ω e - qh₂ i s ω e)) := by
  have hb := h₁.energy_drift_sub_ne_top h₂ hL i
  have hξ := (h₁.fwd i).memLp_initial_sub (h₂.fwd i) hT hb ((h₁.XT_sq i).sub (h₂.XT_sq i))
  convert (h₁.fwd i).sub (h₂.fwd i) hb hξ using 1 <;> ext <;> ring

/-- **The backward difference equation (4.16) in `ℍ²_weak`**: for `T ≥ 0` and the expected Lipschitz
bounds at the pair, coordinate `k` of `(δY, δZ, δU)` solves the linear backward equation of
`LinearBSDEJ` with terminal value `λ δg + δq^g` and drift `λ δf + δq^f`. -/
theorem bwd_sub (hT : 0 ≤ T)
    (hL : PairLipschitz P ν T K KT (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω)) (k : Fin m) :
    LinearBSDEJ D ℱ hℱW hℱN T
      (fun ω => lam * (terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω)
        + (qg₁ k ω - qg₂ k ω))
      (fun ω s => lam * (driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s
          - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s) + (qf₁ k ω s - qf₂ k ω s))
      (fun t ω => Y₁ k t ω - Y₂ k t ω) (fun s ω j => Z₁ k s ω j - Z₂ k s ω j)
      (fun s ω e => U₁ k s ω e - U₂ k s ω e) := by
  convert (h₁.bwd k).sub (h₂.bwd k) (h₁.energy_driver_sub_ne_top h₂ hL k)
    (h₁.memLp_terminal_sub h₂ hT hL k) using 1 <;> ext <;> ring

/-- **The difference of two solutions in `ℍ²_weak` is a `PairDiff`.** For two solutions of the
`λ`-forced system in `ℍ²_weak` at the same `λ`, with coefficients `C¹, C²`, initial data `ξ₀¹, ξ₀²`
and forcings `q¹, q²`, and `T ≥ 0`, the difference `(δX, δY, δZ, δU)` with the coefficient
differences along the pair `(δb, δσ, δγ, δf, δg)` and the forcing difference `δq` is a `PairDiff`
with initial difference `δξ₀`, given the expected Lipschitz bounds and Assumption 2.5 at the
pair. -/
theorem pairDiff (hT : 0 ≤ T)
    (hL : PairLipschitz P ν T K KT (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω))
    (hM : PairMonotone P ν T G α β₁ β₂ (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω)) :
    PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G (fun i ω => ξ₁ i ω - ξ₂ i ω)
      (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
      (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω)
      (fun i ω s => qb₁ i ω s - qb₂ i ω s) (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
      (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
      (fun k ω => qg₁ k ω - qg₂ k ω) :=
  pairDiff_of_legs (h₁.fwd_sub h₂ hT hL) (h₁.bwd_sub h₂ hT hL) (h₁.forcing.sub h₂.forcing) hL hM

end SolvesForcedInt

variable {C : Coeffs ν n m d} {L : ℝ}

/-- **The difference of two solutions in `ℍ²_weak` is a difference system.** For two solutions of
the
`λ`-forced system in `ℍ²_weak` with the same coefficients and `T ≥ 0`, satisfying Assumption 2.3
along the diagonal with constant `L` and Assumption 2.5 along the diagonal with coupling matrix `G`
and constants `α, β₁, β₂`, the difference is a `PairDiff` with Lipschitz constants `10 L²` and
`4 L²`. -/
theorem SolvesForcedInt.pairDiff_of_assumptions
    (h₁ : SolvesForcedInt D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForcedInt D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hT : 0 ≤ T) (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g)
    (hM : DiagonalMonotone ℱ P T G β₁ β₂ C) (hMT : TerminalMonotone ℱ P T G α C.g) :
    PairDiff D ℱ hℱW hℱN T lam (10 * L ^ 2) (4 * L ^ 2) α β₁ β₂ G (fun i ω => ξ₁ i ω - ξ₂ i ω)
      (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
      (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
      (fun i ω s => qb₁ i ω s - qb₂ i ω s) (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
      (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
      (fun k ω => qg₁ k ω - qg₂ k ω) :=
  h₁.pairDiff h₂ hT (h₁.pairLipschitz h₂ hL hLT) (h₁.pairMonotone h₂ hM hMT)

end MVFBSDEJ.WellPosedness.System
