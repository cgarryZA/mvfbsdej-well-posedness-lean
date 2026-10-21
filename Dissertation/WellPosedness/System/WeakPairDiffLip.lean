/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.WeakPairEnergy

/-!
# Two solutions in `ℍ²` under the Lipschitz condition alone

The difference system `PairDiff` records, besides the difference equations and the Lipschitz
bounds at the pair, Assumption 2.5 at the pair with a coupling matrix `G`. With `G = 0` and
`α = β₁ = β₂ = 0` both monotonicity conditions hold for every system, so two solutions of the
`λ`-forced system (4.1) in `ℍ²` whose coefficients satisfy Assumption 2.3 along the diagonal
have a difference system with `G = 0`, whatever the monotonicity of the coefficients: the
difference equations and the Lipschitz bounds use Assumption 2.3 alone, as in the proof of
Theorem 3.3 of the well-posedness paper.

A property holding almost everywhere for the marked energy measure on `Ω × [0, T] × E` holds, at
almost every time of `[0, T]`, almost surely for almost every mark, with no measurability.

## Main statements

* `GX_zero`, `GZ_zero`, `GU_zero` — the coupling operators of the zero matrix vanish.
* `diagonalMonotone_zero`, `terminalMonotone_zero` — Assumption 2.5 with `G = 0` and zero
  constants holds for every system.
* `PaperWeakSolutionForcedInt.exists_pairDiff_lip` — the difference of the extended solutions is
  a `PairDiff` with `G = 0`, under Assumption 2.3 along the diagonal alone.
* `ae_time_ae_of_ae_markedEnergyMeasure` — the time-first form of an almost-everywhere property
  of the marked energy measure.
-/

open MeasureTheory Filter Topology Dissertation.Law Matrix
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open LevyStochCalc Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability

universe u v w

/-! ### The zero coupling matrix -/

section Zero

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}

/-- The coupling operator `x ↦ G x` of the zero matrix is zero. -/
theorem GX_zero : GX (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
  unfold GX
  simp

/-- The coupling operator `z ↦ G z` on `n × d` matrices of the zero matrix is zero. -/
theorem GZ_zero : GZ (d := d) (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
  unfold GZ
  simp

/-- The coupling operator `u ↦ G u` on `L²(ν; ℝⁿ)` of the zero matrix is zero. -/
theorem GU_zero : GU (0 : Matrix (Fin m) (Fin n) ℝ) ν = 0 := by
  ext u : 1
  refine Lp.ext ?_
  filter_upwards [coeFn_GU (0 : Matrix (Fin m) (Fin n) ℝ) ν u,
    Lp.coeFn_zero (EuclideanSpace ℝ (Fin m)) 2 ν] with e he h0
  rw [he, GX_zero, _root_.zero_apply, _root_.zero_apply, h0]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}

/-- **Assumption 2.5, interior, with `G = 0` and `β₁ = β₂ = 0`**, holds for every system: both
sides of (2.7) vanish. -/
theorem diagonalMonotone_zero (C : Coeffs ν n m d) :
    DiagonalMonotone ℱ P T (0 : Matrix (Fin m) (Fin n) ℝ) 0 0 C :=
  Eventually.of_forall fun t Θ Θ' _ _ _ _ => le_of_eq (by
    simp [interiorPairing, dissipation, GX_zero, GZ_zero, GU_zero])

/-- **Assumption 2.5, terminal, with `G = 0` and `α = 0`**, holds for every terminal function:
both sides vanish. -/
theorem terminalMonotone_zero
    (g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)) :
    TerminalMonotone ℱ P T (0 : Matrix (Fin m) (Fin n) ℝ) 0 g := by
  intro ξ ξ' _ _ _ _
  simp [GX_zero]

end Zero

/-! ### The time-first form of the marked energy measure -/

section Marked

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {P : Measure Ω}
  {ν : Measure E} [SFinite P] [SFinite ν] {T : ℝ}

/-- A property holding almost everywhere for the marked energy measure on `Ω × [0, T] × E` holds,
at almost every time of `[0, T]`, almost surely for almost every mark. -/
theorem ae_time_ae_of_ae_markedEnergyMeasure {p : Ω × ℝ × E → Prop}
    (h : ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T), p q) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, ∀ᵐ e ∂ν, p (ω, s, e) := by
  set μ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  have h₁ : MeasurePreserving (MeasurableEquiv.prodAssoc (α := ℝ) (β := Ω) (γ := E)).symm
      (μ.prod (P.prod ν)) ((μ.prod P).prod ν) := (measurePreserving_prodAssoc μ P ν).symm
  have h₂ : MeasurePreserving (Prod.map (Prod.swap : ℝ × Ω → Ω × ℝ) (id : E → E))
      ((μ.prod P).prod ν) ((P.prod μ).prod ν) :=
    (Measure.measurePreserving_swap).prod (MeasurePreserving.id ν)
  have h₃ : MeasurePreserving (MeasurableEquiv.prodAssoc (α := Ω) (β := ℝ) (γ := E))
      ((P.prod μ).prod ν) (P.prod (μ.prod ν)) := measurePreserving_prodAssoc P μ ν
  have hmp := h₃.comp (h₂.comp h₁)
  rw [Poisson.Compensated.markedEnergyMeasure] at h
  have h' := hmp.quasiMeasurePreserving.ae h
  filter_upwards [Measure.ae_ae_of_ae_prod h'] with s hs
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  exact hω

end Marked

/-! ### The difference of two solutions under Assumption 2.3 -/

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam : ℝ} {C : Coeffs ν n m d}
  {ξ₁ ξ₂ : Fin n → Ω → ℝ}
  {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ}
  {qg₁ qg₂ : Fin m → Ω → ℝ}
  {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {L : ℝ}

/-- **The difference of two solutions in `ℍ²` under Assumption 2.3 alone.** For two
solutions of the `λ`-forced system in `ℍ²` with the same coefficients and `T ≥ 0`, satisfying
Assumption 2.3 along the diagonal with constant `L`, there are `X'^k, Y'^k` equal to `X^k, Y^k`
at every time of `[0, T]` such that the difference is a `PairDiff` with Lipschitz constants
`10 L²` and `4 L²`, coupling matrix `0` and constants `α = β₁ = β₂ = 0`. -/
theorem PaperWeakSolutionForcedInt.exists_pairDiff_lip
    (h₁ : PaperWeakSolutionForcedInt D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : PaperWeakSolutionForcedInt D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hT : 0 ≤ T) (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g) :
    ∃ (X₁' X₂' : Fin n → ℝ → Ω → ℝ) (Y₁' Y₂' : Fin m → ℝ → Ω → ℝ),
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁' i t = X₁ i t ∧ X₂' i t = X₂ i t)
      ∧ (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁' k t = Y₁ k t ∧ Y₂' k t = Y₂ k t)
      ∧ PairDiff D ℱ hℱW hℱN T lam (10 * L ^ 2) (4 * L ^ 2) 0 0 0
        (0 : Matrix (Fin m) (Fin n) ℝ)
        (fun i ω => ξ₁ i ω - ξ₂ i ω)
        (fun i t ω => X₁' i t ω - X₂' i t ω) (fun k t ω => Y₁' k t ω - Y₂' k t ω)
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
  h₁.exists_pairDiff h₂ hT hL hLT (diagonalMonotone_zero C) (terminalMonotone_zero C.g)

end Dissertation.WellPosedness.System
