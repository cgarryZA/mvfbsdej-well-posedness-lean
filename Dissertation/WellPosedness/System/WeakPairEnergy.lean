/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.WeakPairDiff

/-!
# The jump energy of two solutions in `ℍ²` at the predictable tuples

The marked energy `𝔼 ∫_0^T ∫_E |φ_s(e)|² ν(de) ds` is an iterated lower integral, so it depends only
on the class of `φ` almost everywhere for `P ⊗ ds ⊗ ν` on `Ω × [0, T] × E`, measurable or not. For
two solutions of (1.1) of the well-posedness paper in `ℍ²`, the jump coefficient
`h(s, Θ^{k,−}_s, ·, μ^{k,−}_s)` at the predictable tuples, through the canonical representative
`Dissertation.WellPosedness.Existence.coeffJump`, agrees almost everywhere with the solutions'
representative `γ^k`, so the difference of the jump coefficients has the marked energy of `γ¹ − γ²`.

## Main statements

* `markedEnergy_congr_ae` — the marked energy of an integrand is that of any integrand agreeing
  with it almost everywhere for the marked energy measure.
* `PaperWeakSolutionInt.markedEnergy_coeffJump_sub_leftLim_eq` — the marked energy of the
  difference of the jump coefficients at the predictable tuples is that of `γ¹ − γ²`.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open LevyStochCalc

universe u v w

/-- **The marked energy depends only on the class of the integrand.** Two integrands agreeing
almost everywhere for the marked energy measure on `Ω × [0, T] × E` have the same marked energy on
`[0, T]`; no measurability is needed. -/
theorem markedEnergy_congr_ae {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} {ν : Measure E} [SFinite ν] {T : ℝ} {φ₁ φ₂ : Ω → ℝ → E → ℝ}
    (h : ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
      φ₁ q.1 q.2.1 q.2.2 = φ₂ q.1 q.2.1 q.2.2) :
    Poisson.Compensated.markedEnergy P ν T φ₁ = Poisson.Compensated.markedEnergy P ν T φ₂ := by
  rw [Poisson.Compensated.markedEnergyMeasure] at h
  unfold Poisson.Compensated.markedEnergy
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod h] with ω hω
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod hω] with s hs
  refine lintegral_congr_ae ?_
  filter_upwards [hs] with e he
  rw [he]

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {C : Coeffs ν n m d}
  {ξ₁ ξ₂ : Fin n → Ω → ℝ} {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ}

/-- **The jump energy at the predictable tuples.** For two solutions of (1.1) in `ℍ²` with
the same coefficients, with the joint measurability (2.3), `T ≥ 0`, and every path of `X^k` and
`Y^k` with left limits at every time of `(0, T]`, coordinatewise
`𝔼 ∫_0^T ∫_E |coeffJump(h, Θ¹⁻) − coeffJump(h, Θ²⁻)|² dν dt = 𝔼 ∫_0^T ∫_E |γ¹ − γ²|² dν dt`. -/
theorem PaperWeakSolutionInt.markedEnergy_coeffJump_sub_leftLim_eq
    (h₁ : PaperWeakSolutionInt D ℱ hℱW hℱN T C ξ₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : PaperWeakSolutionInt D ℱ hℱW hℱN T C ξ₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hT : 0 ≤ T) (hC : Existence.CoeffBorel T C)
    (hXl₁ : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X₁ i s ω) (𝓝[<] t) (𝓝 l))
    (hYl₁ : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y₁ k s ω) (𝓝[<] t) (𝓝 l))
    (hXl₂ : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X₂ i s ω) (𝓝[<] t) (𝓝 l))
    (hYl₂ : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y₂ k s ω) (𝓝[<] t) (𝓝 l))
    (i : Fin n) :
    Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
        jumpProc T (Existence.coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i s ω e
          - jumpProc T (Existence.coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e)
      = Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e) := by
  have hj := (paperWeakSolutionForcedInt_one_zero_iff.mpr h₁).ae_forcedJump_sub_leftLim_eq
    (paperWeakSolutionForcedInt_one_zero_iff.mpr h₂) hT hC hXl₁ hYl₁ hXl₂ hYl₂
  refine markedEnergy_congr_ae ?_
  filter_upwards [hj] with q hq
  simpa only [one_mul, Pi.zero_apply, sub_self, add_zero] using hq i

end Dissertation.WellPosedness.System
