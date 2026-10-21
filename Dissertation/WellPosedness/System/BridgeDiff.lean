/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.PairDiff
import Dissertation.WellPosedness.Stability.Sub
import Dissertation.WellPosedness.System.Solves

/-!
# The difference of two solutions of the `λ`-forced system

Let `Θ¹, Θ²` solve the `λ`-forced system (4.1) with coefficients `C¹, C²`, initial data
`ξ₀¹, ξ₀²` and forcings `q¹, q²`, at the same `λ`. Writing `δ· = ·¹ − ·²` and, for the
coefficient processes along the two solutions,

`δb_s = b¹(s, Θ¹_s, μ¹_s) − b²(s, Θ²_s, μ²_s)`,   `δg_T = g¹(X¹_T, Law X¹_T) − g²(X²_T, Law X²_T)`,

and likewise `δσ`, `δf` and the difference `δγ` of the jump representatives, the equations are
linear in the integrands, so the difference `(δX, δY, δZ, δU)` solves

`dδX_t = (λ δb_t + δq^b_t) dt + (λ δσ_t + δq^σ_t) dW_t + ∫_E (λ δγ_t(e) + δq^h_t(e)) Ñ(dt, de)`,
`δX_0 = δξ₀`,
`dδY_t = −(λ δf_t + δq^f_t) dt + δZ_t dW_t + ∫_E δU_t(e) Ñ(dt, de)`,  `δY_T = λ δg_T + δq^g_T`,

the difference equations (4.15)–(4.16), and the difference `δq` of two forcings is a forcing. These
are the equation and forcing fields of the difference system
`Dissertation.WellPosedness.Stability.PairDiff`. Its other two groups of fields are conditions on
the differences alone: the expected Lipschitz bounds (3.2) and (2.6) with (2.9) at the pair,
`PairLipschitz`, and Assumption 2.5 at the pair, `PairMonotone`. Given both, the difference of two
solutions is a `Dissertation.WellPosedness.Stability.PairDiff`.

The two coefficient systems may differ, as in the comparison of two systems of Theorem 3.1;
Lemma 4.3 is the case `C¹ = C²`.

## Main definitions

* `PairLipschitz` — the expected Lipschitz bounds at the pair, the `lip`, `lipT` fields of
  `Dissertation.WellPosedness.Stability.PairDiff`.
* `PairMonotone` — Assumption 2.5 at the pair, the `mono`, `monoT` fields of
  `Dissertation.WellPosedness.Stability.PairDiff`.

## Main statements

* `Forcing.sub` — the difference of two forcings is a forcing.
* `SolvesForced.fwd_sub`, `SolvesForced.bwd_sub` — the difference equations (4.15)–(4.16).
* `pairDiff_of_legs` — the difference equations, a forcing, `PairLipschitz` and `PairMonotone`
  give a `Dissertation.WellPosedness.Stability.PairDiff`.
* `SolvesForced.pairDiff` — the difference of two solutions is a
  `Dissertation.WellPosedness.Stability.PairDiff`, given `PairLipschitz` and `PairMonotone` for it.
-/

open MeasureTheory Filter Matrix Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open LevyStochCalc Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {n m d : ℕ}

/-! ### The difference of two forcings -/

/-- **The difference of two forcings is a forcing.** -/
theorem Forcing.sub [SigmaFinite ν] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} {T : ℝ}
    {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
    {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ : Fin m → Ω → ℝ}
    (h₁ : Forcing ℱ P ν T qb₁ qσ₁ qh₁ qf₁ qg₁) (h₂ : Forcing ℱ P ν T qb₂ qσ₂ qh₂ qf₂ qg₂) :
    Forcing ℱ P ν T (fun i ω s => qb₁ i ω s - qb₂ i ω s)
      (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
      (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω) where
  qb_meas i := (h₁.qb_meas i).sub (h₂.qb_meas i)
  qb_prog i := (h₁.qb_prog i).sub (h₂.qb_prog i)
  qb_vanish i ω s hs := by rw [h₁.qb_vanish i ω s hs, h₂.qb_vanish i ω s hs, sub_zero]
  qb_sq i := BSDEJ.Solves.energy_sub_ne_top (h₁.qb_meas i) (h₂.qb_meas i) (h₁.qb_sq i)
    (h₂.qb_sq i)
  qσ_meas i j := (h₁.qσ_meas i j).sub (h₂.qσ_meas i j)
  qσ_prog i j := (h₁.qσ_prog i j).sub (h₂.qσ_prog i j)
  qσ_vanish i ω s hs := by
    funext j
    simp [h₁.qσ_vanish i ω s hs, h₂.qσ_vanish i ω s hs]
  qσ_sq i j := BSDEJ.Solves.energy_sub_ne_top (h₁.qσ_meas i j) (h₂.qσ_meas i j) (h₁.qσ_sq i j)
    (h₂.qσ_sq i j)
  qh_meas i := (h₁.qh_meas i).sub (h₂.qh_meas i)
  qh_prog i := by
    simpa only [neg_one_mul, ← sub_eq_add_neg] using
      Poisson.Compensated.markedProgressivelyMeasurable_add (h₁.qh_prog i)
        (Poisson.Compensated.markedProgressivelyMeasurable_const_mul (h₂.qh_prog i) (-1))
  qh_vanish i ω s e hs := by rw [h₁.qh_vanish i ω s e hs, h₂.qh_vanish i ω s e hs, sub_zero]
  qh_sq i := by
    simpa only [neg_one_mul, ← sub_eq_add_neg] using
      Poisson.Compensated.markedEnergy_add_ne_top (h₁.qh_meas i) ((h₂.qh_meas i).const_mul (-1))
        (h₁.qh_sq i) (Poisson.Compensated.markedEnergy_const_mul_ne_top (h₂.qh_meas i)
          (h₂.qh_sq i) (-1))
  qf_meas k := (h₁.qf_meas k).sub (h₂.qf_meas k)
  qf_prog k := (h₁.qf_prog k).sub (h₂.qf_prog k)
  qf_vanish k ω s hs := by rw [h₁.qf_vanish k ω s hs, h₂.qf_vanish k ω s hs, sub_zero]
  qf_sq k := BSDEJ.Solves.energy_sub_ne_top (h₁.qf_meas k) (h₂.qf_meas k) (h₁.qf_sq k)
    (h₂.qf_sq k)
  qg_meas k := (h₁.qg_meas k).sub (h₂.qg_meas k)
  qg_sq k := (h₁.qg_sq k).sub (h₂.qg_sq k)

/-! ### The conditions at the pair -/

/-- **The expected Lipschitz bounds at the pair**: (3.2), Assumption 2.3 with the coupling bound
(2.8) in expectation at almost every time of `[0, T]`, and its terminal form, (2.6) with (2.9),
for a difference `(δX, δY, δZ, δU)` with coefficient differences `(δb, δσ, δh, δf, δg)`. These
are the `lip` and `lipT` fields of `PairDiff`. -/
structure PairLipschitz (P : Measure Ω) (ν : Measure E) (T K KT : ℝ)
    (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (b : Fin n → Ω → ℝ → ℝ) (σ : Fin n → ℝ → Ω → Fin d → ℝ) (h : Fin n → ℝ → Ω → E → ℝ)
    (f : Fin m → Ω → ℝ → ℝ) (g : Fin m → Ω → ℝ) : Prop where
  /-- (3.2) at almost every time. -/
  lip : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
    ∫⁻ ω, (esq (fun i => b i ω s) + ∑ i, esq (σ i s ω)
        + ∑ i, ∫⁻ e, (‖h i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν + esq (fun k => f k ω s)) ∂P
      ≤ ENNReal.ofReal K * ∫⁻ ω, (esq (fun i => X i s ω) + esq (fun k => Y k s ω)
        + ∑ k, esq (Z k s ω) + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P
  /-- (2.6) with (2.9). -/
  lipT : ∫⁻ ω, esq (fun k => g k ω) ∂P ≤ ENNReal.ofReal KT * ∫⁻ ω, esq (fun i => X i T ω) ∂P

/-- **Assumption 2.5 at the pair**, interior (2.7) at almost every time of `[0, T]` and terminal,
for a difference `(δX, δY, δZ, δU)` with coefficient differences `(δb, δσ, δh, δf, δg)` and
coupling matrix `G`. These are the `mono` and `monoT` fields of `PairDiff`. -/
structure PairMonotone (P : Measure Ω) (ν : Measure E) (T : ℝ) (G : Matrix (Fin m) (Fin n) ℝ)
    (α β₁ β₂ : ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (b : Fin n → Ω → ℝ → ℝ) (σ : Fin n → ℝ → Ω → Fin d → ℝ) (h : Fin n → ℝ → Ω → E → ℝ)
    (f : Fin m → Ω → ℝ → ℝ) (g : Fin m → Ω → ℝ) : Prop where
  /-- (2.7) at almost every time. -/
  mono : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
    ∫ ω, ((fun i => b i ω s) ⬝ᵥ (Gᵀ *ᵥ fun k => Y k s ω)
        + ∑ j, (fun i => σ i s ω j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k s ω j)
        - (fun k => f k ω s) ⬝ᵥ (G *ᵥ fun i => X i s ω)
        + ∫ e, (fun i => h i s ω e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k s ω e) ∂ν) ∂P
      ≤ -β₁ * ∫ ω, ((Gᵀ *ᵥ fun k => Y k s ω) ⬝ᵥ (Gᵀ *ᵥ fun k => Y k s ω)
          + ∑ j, (Gᵀ *ᵥ fun k => Z k s ω j) ⬝ᵥ (Gᵀ *ᵥ fun k => Z k s ω j)
          + ∫ e, (Gᵀ *ᵥ fun k => U k s ω e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k s ω e) ∂ν) ∂P
        - β₂ * ∫ ω, (G *ᵥ fun i => X i s ω) ⬝ᵥ (G *ᵥ fun i => X i s ω) ∂P
  /-- Assumption 2.5, terminal. -/
  monoT : α * ∫ ω, (G *ᵥ fun i => X i T ω) ⬝ᵥ (G *ᵥ fun i => X i T ω) ∂P
    ≤ ∫ ω, (fun k => g k ω) ⬝ᵥ (G *ᵥ fun i => X i T ω) ∂P

/-! ### The difference system -/

variable {P : Measure Ω} [IsProbabilityMeasure P] [SigmaFinite ν]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam : ℝ}

/-- **The difference system from its equations and the conditions at the pair**: if each
coordinate of `δX` solves the linear forward equation from `δξ₀` with drift `λ δb + q^b`,
diffusion `λ δσ + q^σ` and jump integrand `λ δh + q^h`, each coordinate of `(δY, δZ, δU)` solves
the linear backward equation with terminal value `λ δg + q^g` and drift `λ δf + q^f`, `q` is a
forcing, and `PairLipschitz` and `PairMonotone` hold, then `PairDiff` holds. -/
theorem pairDiff_of_legs {K KT α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
    {ξ₀ : Fin n → Ω → ℝ} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
    {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
    {b : Fin n → Ω → ℝ → ℝ} {σ : Fin n → ℝ → Ω → Fin d → ℝ} {h : Fin n → ℝ → Ω → E → ℝ}
    {f : Fin m → Ω → ℝ → ℝ} {g : Fin m → Ω → ℝ}
    {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
    {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
    (hfwd : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (ξ₀ i) (fun ω s => lam * b i ω s + qb i ω s) (X i)
      (fun s ω j => lam * σ i s ω j + qσ i s ω j) (fun s ω e => lam * h i s ω e + qh i s ω e))
    (hbwd : ∀ k, LinearBSDEJ D ℱ hℱW hℱN T (fun ω => lam * g k ω + qg k ω)
      (fun ω s => lam * f k ω s + qf k ω s) (Y k) (Z k) (U k))
    (hq : Forcing ℱ P ν T qb qσ qh qf qg) (hL : PairLipschitz P ν T K KT X Y Z U b σ h f g)
    (hM : PairMonotone P ν T G α β₁ β₂ X Y Z U b σ h f g) :
    PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg where
  fwd := hfwd
  bwd := hbwd
  qb_meas := hq.qb_meas
  qσ_meas := hq.qσ_meas
  qh_meas := hq.qh_meas
  qf_meas := hq.qf_meas
  qg_meas k := (hq.qg_sq k).aestronglyMeasurable
  lip := hL.lip
  lipT := hL.lipT
  mono := hM.mono
  monoT := hM.monoT

variable [MeasurableSpace.CountablyGenerated E]
  {C₁ C₂ : Coeffs ν n m d} {ξ₁ ξ₂ : Fin n → Ω → ℝ}
  {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ : Fin m → Ω → ℝ}
  {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ}

/-- **The forward difference equation (4.15)**: coordinate `i` of `δX` solves the linear forward
equation from `δξ₀` with drift `λ δb + δq^b`, diffusion `λ δσ + δq^σ` and jump integrand
`λ δγ + δq^h`. -/
theorem SolvesForced.fwd_sub
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam C₁ ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam C₂ ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hT : 0 ≤ T) (i : Fin n) :
    LinearFSDEJ D ℱ hℱW hℱN T (fun ω => ξ₁ i ω - ξ₂ i ω)
      (fun ω s => lam * (driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s
          - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s) + (qb₁ i ω s - qb₂ i ω s))
      (fun t ω => X₁ i t ω - X₂ i t ω)
      (fun s ω j => lam * (diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
          - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j))
      (fun s ω e => lam * (jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
          + (qh₁ i s ω e - qh₂ i s ω e)) := by
  convert (h₁.fwd i).sub (h₂.fwd i) hT using 1 <;> ext <;> ring

/-- **The backward difference equation (4.16)**: coordinate `k` of `(δY, δZ, δU)` solves the
linear backward equation with terminal value `λ δg + δq^g` and drift `λ δf + δq^f`. -/
theorem SolvesForced.bwd_sub
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam C₁ ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam C₂ ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (k : Fin m) :
    LinearBSDEJ D ℱ hℱW hℱN T
      (fun ω => lam * (terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₂ k ω)
        + (qg₁ k ω - qg₂ k ω))
      (fun ω s => lam * (driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s
          - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s) + (qf₁ k ω s - qf₂ k ω s))
      (fun t ω => Y₁ k t ω - Y₂ k t ω) (fun s ω j => Z₁ k s ω j - Z₂ k s ω j)
      (fun s ω e => U₁ k s ω e - U₂ k s ω e) := by
  convert (h₁.bwd k).sub (h₂.bwd k) using 1 <;> ext <;> ring

/-- **The difference of two solutions is a `PairDiff`.** For two solutions of the `λ`-forced
system at the same `λ`, with coefficients `C¹, C²`, initial data `ξ₀¹, ξ₀²` and forcings
`q¹, q²`, the difference `(δX, δY, δZ, δU)` with the coefficient differences along the pair
`(δb, δσ, δγ, δf, δg)` and the forcing difference `δq` is a `PairDiff` with initial difference
`δξ₀`, given the expected Lipschitz bounds and Assumption 2.5 at the pair. -/
theorem SolvesForced.pairDiff
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam C₁ ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam C₂ ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hT : 0 ≤ T) {K KT α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
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
  pairDiff_of_legs (h₁.fwd_sub h₂ hT) (h₁.bwd_sub h₂) (h₁.forcing.sub h₂.forcing) hL hM

end Dissertation.WellPosedness.System
