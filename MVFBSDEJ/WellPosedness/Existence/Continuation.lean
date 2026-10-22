/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Existence.CoeffForcing
import MVFBSDEJ.WellPosedness.Existence.SelfRegular
import MVFBSDEJ.WellPosedness.Existence.StableZero
import MVFBSDEJ.WellPosedness.Existence.Step

/-!
# Lemmas 4.2 and 4.4

The continuation step `ForcedSolvable.add` passes the solvability of the `λ₀`-forced system
(4.1) to the `(λ₀ + ζ)`-system for every real `ζ` with `ζ² K_L C_s ≤ 1/4`, given the stability
of the `λ₀`-system with constant `C_s` and that the coefficient processes `Ψ(Θ)` along its
solutions are forcings. Both hypotheses are discharged in the two regimes of the paper.

* At `λ₀ = 0` the system does not see its coefficients. It is stable with the constant
  `C₀(T) = 6 (T + 4) (1 + e^{2T}) (1 + 4 e^{2T})`, which depends on the horizon only, and
  `Ψ(Θ)` is a forcing by the measurability (2.5) of the coefficients, the hypothesis
  `CoeffRegular`, and Assumptions 2.2–2.3, with a new representative of the jump coefficient.
  With the solvability of the `λ = 0` system this is Lemma 4.2: the `ζ`-system is solvable for
  every `ζ` with `ζ² K_L C₀(T) ≤ 1/4`.
* At `λ₀ ∈ [λ̲, 1]`, `λ̲ > 0`, the system is stable with the constant `C_B(λ̲)` of (4.14), and
  `Ψ(Θ)` is a forcing by the solution predicate itself, since `λ₀ ≠ 0`, once `g` is Borel
  measurable in the state. This is Lemma 4.4: the increment `ζ` with `ζ² K_L C_B(λ̲) ≤ 1/4`
  does not depend on `λ₀`.

## Main statements

* `forcedSolvable_zero`, `forcedStable_zero`, `forcedStable_of_le`,
  `coeffForcingAlong_of_ne_zero`, `coeffForcingAlong_zero` — the hypotheses of the step at
  `λ₀ = 0` and at `λ₀ ∈ [λ̲, 1]`.
* `forcedSolvable_of_sq_le` — Lemma 4.2: solvability at every `ζ` with `ζ² K_L C₀(T) ≤ 1/4`.
* `ForcedSolvable.add_of_le` — Lemma 4.4: solvability passes from `λ₀ ∈ [λ̲, 1]` to `λ₀ + ζ`
  for every `ζ` with `ζ² K_L C_B(λ̲) ≤ 1/4`.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.System LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam ζ L : ℝ}
  {C : Coeffs ν n m d} {ξ₀ : Fin n → Ω → ℝ}

/-! ### The hypotheses of the step -/

/-- **The `λ = 0` system has a solution for every forcing**, over a right-continuous filtration
carrying the driver, whose right-continuation is constant before `0`, whose time-`0` field
contains the null sets and which has the terminal representation property at the horizon
`T ≥ 0`, for coefficients with (2.5) along every progressive tuple and a square-integrable
`ℱ_0`-measurable initial datum. -/
theorem forcedSolvable_zero [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hrep : HasTerminalRep D ℱ hℱW hℱN T) (hT : 0 ≤ T) (hreg : CoeffRegular ℱ P T C)
    (hξ : ∀ i, MemLp (ξ₀ i) 2 P) (hξm : ∀ i, Measurable[ℱ 0] (ξ₀ i)) :
    ForcedSolvable D ℱ hℱW hℱN T 0 C ξ₀ :=
  fun _ _ _ _ _ hF => exists_solvesForced_zero hℱ0 hnull hrep hT hreg hξ hξm hF

/-- **The `λ = 0` system is stable with constant `C₀(T)`**, over a filtration whose null sets
lie in its time-`0` field, whose right-continuation is constant before `0` and which admits a
cross witness. -/
theorem forcedStable_zero (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ForcedStable D ℱ hℱW hℱN T 0 C ξ₀ (zeroConst T) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂
  have h := h₁.supSize_sub_le_zero h₂ 𝒲 hℱ0 hnull hT
  rwa [dataSize_initial_sub_self] at h

/-- **The `λ`-system is stable with the constant of (4.14)** for `λ ∈ [λ̲, 1]`, `λ̲ > 0`, under
Assumption 2.3 along the diagonal with constant `L`, Assumption 2.4 with coupling matrix `G` and
constant `c_G ≥ 0` and Assumption 2.5 along the diagonal with admissible constants
`α, β₁, β₂`, over a filtration whose null sets lie in its time-`0` field, whose
right-continuation is constant before `0` and which admits a cross witness. -/
theorem forcedStable_of_le {cG α β₁ β₂ lamLow : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hlow : 0 < lamLow) (hlam : lamLow ≤ lam) (hlam1 : lam ≤ 1)
    (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g) (hcG : 0 ≤ cG)
    (hGf : n ≤ m → GCoerciveForward (GX G) cG) (hGb : m ≤ n → GCoerciveBackward (GX G) cG)
    (hconst : Constants n m α β₁ β₂) (hM : DiagonalMonotone ℱ P T G β₁ β₂ C)
    (hMT : TerminalMonotone ℱ P T G α C.g) :
    ForcedStable D ℱ hℱW hℱN T lam C ξ₀
      (aprioriConst T (10 * L ^ 2) (4 * L ^ 2) ‖GX G‖ cG α β₁ β₂ lamLow) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂
  have h := h₁.supSize_sub_le h₂ 𝒲 hℱ0 hnull hT hlow hlam hlam1 hL hLT hcG hGf hGb hconst hM hMT
  rwa [dataSize_initial_sub_self] at h

/-- **For `λ ≠ 0` the coefficient processes along the solutions are forcings**, with the jump
representative of the solution, once `g` is Borel measurable in the state. -/
theorem coeffForcingAlong_of_ne_zero (hlam : lam ≠ 0) (hg : ∀ ρ, Measurable fun x => C.g x ρ) :
    CoeffForcingAlong D ℱ hℱW hℱN T lam C ξ₀ :=
  fun _ _ _ _ _ _ _ _ _ γ h => ⟨γ, h, h.forcing_coeff hlam hg⟩

/-- **At `λ = 0` the coefficient processes along the solutions are forcings**, with a new
representative of the jump coefficient, for coefficients with (2.5) along every progressive
tuple, Assumption 2.2, and Assumption 2.3 along the diagonal with `g` Borel measurable in the
state, over a filtration whose null sets lie in its time-`0` field, whose right-continuation is
constant before `0` and which admits a cross witness. -/
theorem coeffForcingAlong_zero (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hreg : CoeffRegular ℱ P T C) (horig : CoeffOrigin T C) (hL : DiagonalLipschitz ℱ P T L C)
    (hLT : TerminalLipschitz ℱ P T L C.g) (hg : ∀ ρ, Measurable fun x => C.g x ρ) :
    CoeffForcingAlong D ℱ hℱW hℱN T 0 C ξ₀ := by
  intro qb qσ qh qf qg X Y Z U γ h
  obtain ⟨γ', hγ', hF⟩ := h.exists_forcing_coeff 𝒲 hℱ0 hnull hT hreg horig hL hLT hg
  have h' : SolvesForced D ℱ hℱW hℱN T 0 C ξ₀ qb qσ qh qf qg X Y Z U γ' :=
    { forcing := h.forcing
      jump_rep := hγ'.jump_rep
      fwd := fun i => by simpa only [zero_mul, zero_add] using h.fwd i
      bwd := h.bwd }
  exact ⟨γ', h', hF⟩

/-! ### Lemmas 4.2 and 4.4 -/

/-- **Lemma 4.2, the base step.** Over a right-continuous filtration carrying the driver, whose
null sets lie in its time-`0` field, whose right-continuation is constant before `0`, which
admits a cross witness and has the terminal representation property at the horizon `T > 0`, let
the coefficients have (2.5) along every progressive tuple and satisfy Assumption 2.2 and
Assumption 2.3 along the diagonal with constant `L`, with `g` Borel measurable in the state, and
let `ξ₀` be square integrable and `ℱ_0`-measurable. Then for every real `ζ` with
`ζ² K_L C₀(T) ≤ 1/4` the `ζ`-system with initial datum `ξ₀` has a solution for every forcing. -/
theorem forcedSolvable_of_sq_le [ℱ.IsRightContinuous] (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hrep : HasTerminalRep D ℱ hℱW hℱN T) (hT : 0 < T) (hreg : CoeffRegular ℱ P T C)
    (horig : CoeffOrigin T C) (hL : DiagonalLipschitz ℱ P T L C)
    (hLT : TerminalLipschitz ℱ P T L C.g) (hg : ∀ ρ, Measurable fun x => C.g x ρ)
    (hξ : ∀ i, MemLp (ξ₀ i) 2 P) (hξm : ∀ i, Measurable[ℱ 0] (ξ₀ i))
    (hsmall : ζ ^ 2 * lipConst T L * zeroConst T ≤ 4⁻¹) :
    ForcedSolvable D ℱ hℱW hℱN T ζ C ξ₀ := by
  simpa only [zero_add] using (forcedSolvable_zero hℱ0 hnull hrep hT.le hreg hξ hξm).add
    (coeffForcingAlong_zero 𝒲 hℱ0 hnull hT hreg horig hL hLT hg)
    (forcedStable_zero 𝒲 hℱ0 hnull hT) 𝒲 hℱ0 hnull hT hL hLT hsmall

/-- **Lemma 4.4, the continuation step at a fixed increment.** Let the coefficients satisfy
Assumption 2.3 along the diagonal with constant `L` and `g` Borel measurable in the state,
Assumption 2.4 with coupling matrix `G` and constant `c_G ≥ 0` and Assumption 2.5 along the
diagonal with admissible constants `α, β₁, β₂`, over a filtration whose null sets lie in its
time-`0` field, whose right-continuation is constant before `0` and which admits a cross
witness, and let `0 < λ̲ ≤ λ₀ ≤ 1`. If the `λ₀`-system with initial datum `ξ₀` has a solution for
every forcing, then so has the `(λ₀ + ζ)`-system, for every real `ζ` with
`ζ² K_L C_B(λ̲) ≤ 1/4`, `C_B(λ̲)` the constant of (4.14). -/
theorem ForcedSolvable.add_of_le {cG α β₁ β₂ lamLow : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
    (hWP : ForcedSolvable D ℱ hℱW hℱN T lam C ξ₀) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hlow : 0 < lamLow) (hlam : lamLow ≤ lam) (hlam1 : lam ≤ 1)
    (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g)
    (hg : ∀ ρ, Measurable fun x => C.g x ρ) (hcG : 0 ≤ cG)
    (hGf : n ≤ m → GCoerciveForward (GX G) cG) (hGb : m ≤ n → GCoerciveBackward (GX G) cG)
    (hconst : Constants n m α β₁ β₂) (hM : DiagonalMonotone ℱ P T G β₁ β₂ C)
    (hMT : TerminalMonotone ℱ P T G α C.g)
    (hsmall : ζ ^ 2 * lipConst T L
      * aprioriConst T (10 * L ^ 2) (4 * L ^ 2) ‖GX G‖ cG α β₁ β₂ lamLow ≤ 4⁻¹) :
    ForcedSolvable D ℱ hℱW hℱN T (lam + ζ) C ξ₀ :=
  hWP.add (coeffForcingAlong_of_ne_zero (hlow.trans_le hlam).ne' hg)
    (forcedStable_of_le 𝒲 hℱ0 hnull hT hlow hlam hlam1 hL hLT hcG hGf hGb hconst hM hMT) 𝒲 hℱ0
    hnull hT hL hLT hsmall

end MVFBSDEJ.WellPosedness.Existence
