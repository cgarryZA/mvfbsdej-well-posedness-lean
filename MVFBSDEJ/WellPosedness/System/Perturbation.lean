/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.Apriori
import MVFBSDEJ.WellPosedness.System.BridgeLip
import MVFBSDEJ.WellPosedness.System.BridgeMono

/-!
# Continuous perturbation stability along the homotopy

Lemma 4.3 of the well-posedness paper. Let the coefficients `C = (b, σ, h, f, g)` satisfy
Assumption 2.3 along the diagonal with constant `L`, Assumption 2.4 with coupling matrix `G` and
constant `c_G`, and Assumption 2.5 with constants `α, β₁, β₂`. Fix `λ̲ ∈ (0, 1]` and
`λ ∈ [λ̲, 1]`, and let `Θ¹, Θ²` solve the `λ`-forced system (4.1) with the same coefficients,
initial data `ξ₀¹, ξ₀²` and forcings `q¹, q²`. Writing `δ· = ·¹ − ·²`,

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ_t|²_F + ‖δU_t‖²_{L²(ν)}) dt
  ≤ C_B (𝔼|δξ₀|² + 𝔼|δq^g_T|²
    + 𝔼 ∫_0^T (|δq^b_t|² + |δq^σ_t|²_F + ‖δq^h_t‖²_{L²(ν)} + |δq^f_t|²) dt)`,   (4.14)

with `C_B = aprioriConst T (10 L²) (4 L²) ‖G‖ c_G α β₁ β₂ λ̲`, `‖G‖` the operator norm of
`x ↦ G x`. The constant depends only on `T, L, ‖G‖, c_G, α, β₁, β₂` and `λ̲`, is free of the
dimensions, of `ν(E)` and of the Burkholder–Davis–Gundy constant, and is at most its value at
`λ̲ = 1` divided by `λ̲²`.

The difference of the two solutions is a difference system `PairDiff`: Assumption 2.3 with the
coupling bounds (2.8)–(2.9) gives the expected Lipschitz bounds at the pair with `K = 10 L²` and
`K_T = 4 L²`, and Assumption 2.5 at the pair holds. Assumption 2.4 with the admissible
constants of Assumption 2.5 selects the rank case, and `PairDiff.apriori` gives (4.14).

The solutions are those of `SolvesForced`, which goes beyond the paper in two conditions: the
coefficient processes along each solution are square integrable in `dt ⊗ dP`, and they are
jointly and progressively measurable, (2.5). The difference `Θ¹ − Θ² ∈ 𝕊` is not assumed: over
the filtrations below each solution lies in `𝕊` by Lemma 4.1. The filtration is one on which
Lemma 4.1 applies: its null sets lie in its time-`0` field, its right-continuation is constant
before `0`, and it admits a cross witness.

## Main statements

* `rankCase_of_coercive` — Assumptions 2.4 and 2.5 select the rank case of the closure step.
* `SolvesForced.pairDiff_of_assumptions` — the difference of two solutions is a `PairDiff`.
* `SolvesForced.supSize_sub_le` — Lemma 4.3, the estimate (4.14).
-/

open MeasureTheory Filter Matrix MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability

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
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {L cG α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}

/-- **The rank case from Assumptions 2.4 and 2.5.** Under the admissible constants of
Assumption 2.5, with the forward coercivity of Assumption 2.4 when `n ≤ m` and the backward one
when `m ≤ n`, Case A or Case B of the closure step holds. -/
theorem rankCase_of_coercive (hconst : Constants n m α β₁ β₂)
    (hGf : n ≤ m → GCoerciveForward (GX G) cG) (hGb : m ≤ n → GCoerciveBackward (GX G) cG) :
    RankCase G cG α β₁ β₂ :=
  hconst.rankCase (fun h => (gCoerciveForward_GX_iff G cG).mp (hGf h))
    (fun h => (gCoerciveBackward_GX_iff G cG).mp (hGb h))

/-- **The difference of two solutions is a difference system.** For two solutions of the
`λ`-forced system with the same coefficients, satisfying Assumption 2.3 along the diagonal with
constant `L` and Assumption 2.5 along the diagonal with coupling matrix `G` and constants
`α, β₁, β₂`, the difference is a `PairDiff` with Lipschitz constants `10 L²` and `4 L²`, over a
filtration whose null sets lie in its time-`0` field, whose right-continuation is constant before
`0` and which admits a cross witness. -/
theorem SolvesForced.pairDiff_of_assumptions
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g)
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
  h₁.pairDiff h₂ hT.le (h₁.pairLipschitz h₂ 𝒲 hℱ0 hnull hT hL hLT)
    (h₁.pairMonotone h₂ 𝒲 hℱ0 hnull hT hM hMT)

/-- **Lemma 4.3, continuous perturbation stability along the homotopy.** Let the coefficients
satisfy Assumption 2.3 along the diagonal with constant `L`, Assumption 2.4 with coupling matrix
`G` and constant `c_G ≥ 0` (the forward bound when `n ≤ m`, the backward one when `m ≤ n`) and
Assumption 2.5 along the diagonal with admissible constants `α, β₁, β₂`, and let
`λ ∈ [λ̲, 1]`, `λ̲ > 0`. Two solutions of the `λ`-forced system (4.1) with these coefficients,
initial data `ξ₀¹, ξ₀²` and forcings `q¹, q²` — solutions whose coefficient processes are jointly
and progressively measurable and square integrable — satisfy

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)
  ≤ C_B (𝔼|δξ₀|² + 𝔼|δq^g_T|² + 𝔼 ∫_0^T (|δq^b|² + |δq^σ|²_F + ‖δq^h‖² + |δq^f|²))`,

`C_B = aprioriConst T (10 L²) (4 L²) ‖G‖ c_G α β₁ β₂ λ̲`, over a filtration whose null sets lie
in its time-`0` field, whose right-continuation is constant before `0` and which admits a cross
witness. -/
theorem SolvesForced.supSize_sub_le
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
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
          (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω) :=
  (h₁.pairDiff_of_assumptions h₂ 𝒲 hℱ0 hnull hT hL hLT hM hMT).apriori 𝒲 hℱ0 hnull hT hlow hlam
    hlam1 (by positivity) (by positivity) hcG hconst.α_nonneg hconst.β₁_nonneg hconst.β₂_nonneg
    (mulVec_dotProduct_le G) (rankCase_of_coercive hconst hGf hGb)

end MVFBSDEJ.WellPosedness.System
