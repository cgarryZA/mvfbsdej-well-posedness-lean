/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.BridgeDiffInt
import Dissertation.WellPosedness.System.Stability
import Dissertation.WellPosedness.System.Uniqueness

/-!
# Uniqueness for the system (1.1) in the class `ℍ²`

Theorem 3.3 of the well-posedness paper: under Assumptions 2.3–2.5, if `Θ¹, Θ² ∈ 𝕊` satisfy
(1.1) with the same initial condition, then `Θ¹ = Θ²`, and `Θ¹ − Θ² ∈ 𝕊`. Assumption 2.2 is not
used (Remark 3.4): along each solution the drift and the driver need only have almost surely
integrable paths, the initial datum need not be square integrable, and neither need the terminal
value. Along the pair, the coefficient differences are square integrable in `dt ⊗ dP` by the
diagonal Lipschitz bound, so the difference is a difference system `PairDiff`
(`SolvesForcedInt.pairDiff_of_assumptions`); with zero forcings and the same initial datum its
data size vanishes, and Lemma 4.3 at `λ̲ = 1` gives

`𝔼 sup_{t ≤ T} |X¹_t − X²_t|² + 𝔼 sup_{t ≤ T} |Y¹_t − Y²_t|²
  + 𝔼 ∫_0^T (|Z¹_t − Z²_t|²_F + ‖U¹_t − U²_t‖²_{L²(ν)}) dt = 0`.

The solutions are those of `SolvesInt`: tuples in `ℍ²` with `X_T` square integrable, whose
coefficient processes are jointly and progressively measurable, (2.5), and whose diffusion and
jump coefficients along the solution have finite energy, as the `L²` stochastic integrals of
(1.1) require. The filtration is one on which Lemma 4.1 applies to the difference: its null sets
lie in its time-`0` field, its right-continuation is constant before `0`, and it admits a cross
witness. The augmented joint filtration `augJoint D` of the driver has these properties.

Lemma 4.3 holds in the same class, for two solutions of the `λ`-forced system in `ℍ²`
(`SolvesForcedInt.supSize_sub_le`).

## Main definitions

* `SolvesIntAug` — `SolvesInt` over `augJoint D`.

## Main statements

* `SolvesForcedInt.supSize_sub_le` — Lemma 4.3 in `ℍ²`.
* `SolvesInt.uniqueness` — Theorem 3.3 in `ℍ²`.
-/

open MeasureTheory Filter Matrix Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open LevyStochCalc.BSDEJ.Solves Dissertation.WellPosedness.BrownianPoisson
  Dissertation.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- `(X, Y, Z, U)` solves the system (1.1) in `ℍ²` over the augmented joint filtration
`augJoint D` of the driver. -/
abbrev SolvesIntAug (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (T : ℝ)
    (C : Coeffs ν n m d) (ξ₀ : Fin n → Ω → ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop :=
  SolvesInt D (augJoint D) D.isBrownianFiltration_aug D.isPoissonFiltration_aug T C ξ₀ X Y Z U γ

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam : ℝ} {C : Coeffs ν n m d}
  {ξ₀ ξ₁ ξ₂ : Fin n → Ω → ℝ}
  {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ : Fin m → Ω → ℝ}
  {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {L cG α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}

/-- **Lemma 4.3 in `ℍ²`.** Let the coefficients satisfy Assumption 2.3 along the diagonal with
constant `L`, Assumption 2.4 with coupling matrix `G` and constant `c_G ≥ 0` (the forward bound
when `n ≤ m`, the backward one when `m ≤ n`) and Assumption 2.5 along the diagonal with admissible
constants `α, β₁, β₂`, and let `λ ∈ [λ̲, 1]`, `λ̲ > 0`. Two solutions of the `λ`-forced system
(4.1) in `ℍ²` with these coefficients, initial data `ξ₀¹, ξ₀²` and forcings `q¹, q²` satisfy

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)
  ≤ C_B (𝔼|δξ₀|² + 𝔼|δq^g_T|² + 𝔼 ∫_0^T (|δq^b|² + |δq^σ|²_F + ‖δq^h‖² + |δq^f|²))`,

`C_B = aprioriConst T (10 L²) (4 L²) ‖G‖ c_G α β₁ β₂ λ̲`, over a filtration whose null sets lie
in its time-`0` field, whose right-continuation is constant before `0` and which admits a cross
witness. -/
theorem SolvesForcedInt.supSize_sub_le
    (h₁ : SolvesForcedInt D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForcedInt D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
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
  (h₁.pairDiff_of_assumptions h₂ hT.le hL hLT hM hMT).apriori 𝒲 hℱ0 hnull hT hlow hlam hlam1
    (by positivity) (by positivity) hcG hconst.α_nonneg hconst.β₁_nonneg hconst.β₂_nonneg
    (mulVec_dotProduct_le G) (rankCase_of_coercive hconst hGf hGb)

/-- **Theorem 3.3, uniqueness in `ℍ²`.** Under Assumption 2.3 along the diagonal,
Assumption 2.4 with `c_G ≥ 0` and Assumption 2.5 along the diagonal with admissible constants,
two solutions of (1.1) in `ℍ²` (`X`, `Y` of finite energy on `[0, T]`, `X_T` square
integrable, drift and driver integrable along almost every path), with the same coefficients and
the same initial datum, coincide: `X¹, X²` and
`Y¹, Y²` are indistinguishable on `[0, T]`, and `𝔼 ∫_0^T |Z¹ − Z²|²_F = 0`,
`𝔼 ∫_0^T ‖U¹ − U²‖²_{L²(ν)} = 0`, coordinatewise, over a filtration whose null sets lie in its
time-`0` field, whose right-continuation is constant before `0` and which admits a cross
witness. -/
theorem SolvesInt.uniqueness (h₁ : SolvesInt D ℱ hℱW hℱN T C ξ₀ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesInt D ℱ hℱW hℱN T C ξ₀ X₂ Y₂ Z₂ U₂ γ₂)
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
    (SolvesForcedInt.pairDiff_of_assumptions h₁ h₂ hT.le hL hLT hM hMT).eq_zero 𝒲 hℱ0 hnull hT
      one_pos le_rfl (by positivity) (by positivity) hcG hconst.α_nonneg hconst.β₁_nonneg
      hconst.β₂_nonneg (rankCase_of_coercive hconst hGf hGb) (dataSize_sub_self_zero T ξ₀)
  refine ⟨fun i => ?_, fun k => ?_, hZ, hU⟩
  · filter_upwards [hX i] with ω hω t ht
    exact sub_eq_zero.mp (hω t ht)
  · filter_upwards [hY k] with ω hω t ht
    exact sub_eq_zero.mp (hω t ht)

end Dissertation.WellPosedness.System
