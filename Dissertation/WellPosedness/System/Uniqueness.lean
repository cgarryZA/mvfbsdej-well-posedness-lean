/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.Perturbation

/-!
# Uniqueness for the system (1.1)

Theorem 3.3 of the well-posedness paper: under Assumptions 2.3–2.5 the system (1.1) has at most
one solution. Two solutions `Θ¹, Θ²` of (1.1) with the same coefficients and the same initial
datum are two solutions of the `λ`-forced system (4.1) at `λ = 1` with zero forcings and zero
initial difference, so the right-hand side of (4.14) vanishes and Lemma 4.3 at `λ̲ = 1` gives

`𝔼 sup_{t ≤ T} |X¹_t − X²_t|² + 𝔼 sup_{t ≤ T} |Y¹_t − Y²_t|²
  + 𝔼 ∫_0^T (|Z¹_t − Z²_t|²_F + ‖U¹_t − U²_t‖²_{L²(ν)}) dt = 0`.

Hence `X¹, X²` and `Y¹, Y²` are indistinguishable on `[0, T]`, and `Z¹ − Z²` and `U¹ − U²` have
zero energy on `[0, T]`.

Assumption 2.2 is not used, as in Remark 3.4. The solutions are those of `Solves`, which goes
beyond the paper in two conditions: the coefficient processes along each solution are jointly
and progressively measurable and square integrable in `dt ⊗ dP` (without Assumption 2.2 this
asks `b` and `f` along each solution to be square integrable in time rather than integrable).
The filtration is one on which Lemma 4.1 applies: its null sets lie in its time-`0` field, its
right-continuation is constant before `0`, and it admits a cross witness.

## Main statements

* `Solves.uniqueness` — Theorem 3.3.
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
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ} {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {L cG α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}

omit [IsProbabilityMeasure P] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- Zero forcings and a common initial datum have zero data size. -/
theorem dataSize_sub_self_zero (T : ℝ) (ξ₀ : Fin n → Ω → ℝ) :
    dataSize P ν T (fun i ω => ξ₀ i ω - ξ₀ i ω)
      (fun i ω s => (0 : Fin n → Ω → ℝ → ℝ) i ω s - (0 : Fin n → Ω → ℝ → ℝ) i ω s)
      (fun i s ω j =>
        (0 : Fin n → ℝ → Ω → Fin d → ℝ) i s ω j - (0 : Fin n → ℝ → Ω → Fin d → ℝ) i s ω j)
      (fun i s ω e => (0 : Fin n → ℝ → Ω → E → ℝ) i s ω e - (0 : Fin n → ℝ → Ω → E → ℝ) i s ω e)
      (fun k ω s => (0 : Fin m → Ω → ℝ → ℝ) k ω s - (0 : Fin m → Ω → ℝ → ℝ) k ω s)
      (fun k ω => (0 : Fin m → Ω → ℝ) k ω - (0 : Fin m → Ω → ℝ) k ω) = 0 := by
  simp [dataSize, esq, LevyStochCalc.Brownian.Ito.energy,
    LevyStochCalc.Poisson.Compensated.markedEnergy]

/-- **Theorem 3.3, uniqueness.** Under Assumption 2.3 along the diagonal, Assumption 2.4 with
`c_G ≥ 0` and Assumption 2.5 along the diagonal with admissible constants, two solutions of (1.1)
with the same coefficients and the same initial datum — solutions whose coefficient processes are
jointly and progressively measurable and square integrable — coincide: `X¹, X²` and `Y¹, Y²` are
indistinguishable on `[0, T]`, and `𝔼 ∫_0^T |Z¹ − Z²|²_F = 0`,
`𝔼 ∫_0^T ‖U¹ − U²‖²_{L²(ν)} = 0`, coordinatewise, over a filtration whose null sets lie in its
time-`0` field, whose right-continuation is constant before `0` and which admits a cross
witness. -/
theorem Solves.uniqueness (h₁ : Solves D ℱ hℱW hℱN T C ξ₀ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : Solves D ℱ hℱW hℱN T C ξ₀ X₂ Y₂ Z₂ U₂ γ₂)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g) (hcG : 0 ≤ cG)
    (hGf : n ≤ m → GCoerciveForward (GX G) cG) (hGb : m ≤ n → GCoerciveBackward (GX G) cG)
    (hconst : Constants n m α β₁ β₂) (hM : DiagonalMonotone ℱ P T G β₁ β₂ C)
    (hMT : TerminalMonotone ℱ P T G α C.g) :
    (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
      ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
      ∧ (∀ k j, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
      ∧ (∀ k, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0) := by
  obtain ⟨hX, hY, hZ, hU⟩ :=
    (SolvesForced.pairDiff_of_assumptions h₁ h₂ 𝒲 hℱ0 hnull hT hL hLT hM hMT).eq_zero 𝒲 hℱ0
      hnull hT one_pos le_rfl (by positivity) (by positivity) hcG hconst.α_nonneg
      hconst.β₁_nonneg hconst.β₂_nonneg (rankCase_of_coercive hconst hGf hGb)
      (dataSize_sub_self_zero T ξ₀)
  refine ⟨fun i => ?_, fun k => ?_, hZ, hU⟩
  · filter_upwards [hX i] with ω hω t ht
    exact sub_eq_zero.mp (hω t ht)
  · filter_upwards [hY k] with ω hω t ht
    exact sub_eq_zero.mp (hω t ht)

end Dissertation.WellPosedness.System
