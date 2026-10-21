/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.PaperForcedWP
import Dissertation.WellPosedness.System.PredictableForcing

/-!
# `WP(λ)` over the predictable forcings

The paper calls the forced system (4.1) well posed at `λ`, `WP(λ)`, if it has a unique solution for
every forcing `q` whose jump component `q^h` is predictable. `PaperForcedWP` quantifies over the
larger class `Dissertation.WellPosedness.System.Forcing`, in which `q^h` is marked progressively
measurable. This file states `WP(λ)` over the paper's class
`Dissertation.WellPosedness.System.PredForcing`, for the paper's solution notion
`Dissertation.WellPosedness.System.PaperSolutionForced` (`PaperForcedSolvablePred`,
`PaperForcedUniquePred`, `PaperForcedWPPred`), and shows that each is equivalent to its form over
`Dissertation.WellPosedness.System.Forcing`, with no condition on the coefficients, the filtration
or the horizon.

* Every forcing in the paper's class is a forcing, so the form over
  `Dissertation.WellPosedness.System.Forcing` gives the form over
  `Dissertation.WellPosedness.System.PredForcing`.
* Every forcing `q` has a predictable version `q'`, differing from `q` only in its jump component
  and by zero marked energy (`Dissertation.WellPosedness.System.Forcing.exists_predForcing`), and
  the solutions for `q` and for `q'` are the same
  (`Dissertation.WellPosedness.System.PaperSolutionForced.congr_qh`). A solution for `q'` is thus
  one for `q`, and two solutions for `q` are two solutions for `q'`: the form over
  `Dissertation.WellPosedness.System.PredForcing` gives the form over
  `Dissertation.WellPosedness.System.Forcing`.

In particular Lemma 4.4 holds with its hypothesis `WP(λ₀)` taken over the paper's class
(`PaperForcedWPPred.add_of_le`), under the hypotheses of `PaperForcedWP.add_of_le`.

## Main definitions

* `PaperForcedSolvablePred`, `PaperForcedUniquePred`, `PaperForcedWPPred` — `WP(λ)` over the
  predictable forcings, in the sense of the paper.

## Main statements

* `paperForcedSolvable_iff_paperForcedSolvablePred`,
  `paperForcedUnique_iff_paperForcedUniquePred`, `paperForcedWP_iff_paperForcedWPPred` — the
  forms over the two classes of forcings agree.
* `PaperForcedWPPred.add_of_le` — Lemma 4.4 over the predictable forcings.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### `WP(λ)` over the predictable forcings -/

section Predicates

variable (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ)

/-- **The existence half of `WP(λ)` over the predictable forcings, in the sense of the paper**:
for the initial datum `ξ₀`, the `λ`-forced system (4.1) with coefficients `C` has a solution in
the sense of the paper for every forcing whose jump component is marked predictable. -/
def PaperForcedSolvablePred (T lam : ℝ) (C : Coeffs ν n m d) (ξ₀ : Fin n → Ω → ℝ) : Prop :=
  ∀ (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
    (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ), PredForcing ℱ P ν T qb qσ qh qf qg →
    ∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
      (U : Fin m → ℝ → Ω → E → ℝ) (γ : Fin n → ℝ → Ω → E → ℝ),
      PaperSolutionForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ

/-- **The uniqueness half of `WP(λ)` over the predictable forcings, in the sense of the paper**:
any two solutions of the `λ`-forced system (4.1) in the sense of the paper with coefficients
`C`, initial datum `ξ₀` and the same forcing, whose jump component is marked predictable,
coincide: `X¹, X²` and `Y¹, Y²` are indistinguishable on `[0, T]`, and
`𝔼 ∫_0^T |Z¹ − Z²|²_F = 0`, `𝔼 ∫_0^T ‖U¹ − U²‖²_{L²(ν)} = 0`, coordinatewise. -/
def PaperForcedUniquePred (T lam : ℝ) (C : Coeffs ν n m d) (ξ₀ : Fin n → Ω → ℝ) : Prop :=
  ∀ (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
    (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ) (X₁ X₂ : Fin n → ℝ → Ω → ℝ)
    (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ)
    (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ) (γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ),
    PredForcing ℱ P ν T qb qσ qh qf qg →
    PaperSolutionForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X₁ Y₁ Z₁ U₁ γ₁ →
    PaperSolutionForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X₂ Y₂ Z₂ U₂ γ₂ →
    (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
      ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
      ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
      ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0)

/-- **`WP(λ)` over the predictable forcings, in the sense of the paper**: for the initial datum
`ξ₀`, the `λ`-forced system (4.1) with coefficients `C` has a solution in the sense of the paper
for every forcing whose jump component is marked predictable, and any two such solutions with
the same such forcing coincide. -/
def PaperForcedWPPred (T lam : ℝ) (C : Coeffs ν n m d) (ξ₀ : Fin n → Ω → ℝ) : Prop :=
  PaperForcedSolvablePred D ℱ hℱW hℱN T lam C ξ₀ ∧ PaperForcedUniquePred D ℱ hℱW hℱN T lam C ξ₀

end Predicates

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam ζ L : ℝ}
  {C : Coeffs ν n m d} {ξ₀ : Fin n → Ω → ℝ}

/-! ### The two classes of forcings give the same `WP(λ)` -/

omit [MeasurableSpace.CountablyGenerated E] [IsProbabilityMeasure P] in
/-- The jump components of a forcing and of a predictable version of it, agreeing
`dP ⊗ ds ⊗ ν`-almost everywhere on `Ω × [0, T] × E`, differ by zero marked energy, in either
order. -/
private theorem markedEnergy_sub_eq_zero_of_version {qb : Fin n → Ω → ℝ → ℝ}
    {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh qh' : Fin n → ℝ → Ω → E → ℝ}
    {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ} (hF : Forcing ℱ P ν T qb qσ qh qf qg)
    (hF' : Forcing ℱ P ν T qb qσ qh' qf qg)
    (hae : ∀ i, ∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
      qh i p.2.1 p.1 p.2.2 = qh' i p.2.1 p.1 p.2.2) :
    (∀ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e - qh' i s ω e) = 0)
      ∧ ∀ i, Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => qh' i s ω e - qh i s ω e) = 0 :=
  ⟨fun i => markedEnergy_sub_eq_zero_of_ae_eq (φ₁ := fun ω s e => qh i s ω e)
      (φ₂ := fun ω s e => qh' i s ω e) (hF.qh_meas i) (hF'.qh_meas i) (hae i),
    fun i => markedEnergy_sub_eq_zero_of_ae_eq (φ₁ := fun ω s e => qh' i s ω e)
      (φ₂ := fun ω s e => qh i s ω e) (hF'.qh_meas i) (hF.qh_meas i)
      ((hae i).mono fun _ hp => hp.symm)⟩

/-- **Solvability over all forcings is solvability over the predictable ones, in the sense of
the paper.** The `λ`-forced system (4.1) has a solution in the sense of the paper for every
forcing if and only if it has one for every forcing whose jump component is marked
predictable. -/
theorem paperForcedSolvable_iff_paperForcedSolvablePred :
    PaperForcedSolvable D ℱ hℱW hℱN T lam C ξ₀
      ↔ PaperForcedSolvablePred D ℱ hℱW hℱN T lam C ξ₀ := by
  refine ⟨fun h qb qσ qh qf qg hF => h qb qσ qh qf qg hF.toForcing,
    fun h qb qσ qh qf qg hF => ?_⟩
  obtain ⟨qh', hF', hae⟩ := hF.exists_predForcing D.N
  obtain ⟨X, Y, Z, U, γ, hs⟩ := h qb qσ qh' qf qg hF'
  exact ⟨X, Y, Z, U, γ,
    hs.congr_qh hF (markedEnergy_sub_eq_zero_of_version hF hF'.toForcing hae).2⟩

/-- **Uniqueness over all forcings is uniqueness over the predictable ones, in the sense of the
paper.** Any two solutions of the `λ`-forced system (4.1) in the sense of the paper with the
same forcing coincide if and only if any two such solutions with the same forcing, whose jump
component is marked predictable, coincide. -/
theorem paperForcedUnique_iff_paperForcedUniquePred :
    PaperForcedUnique D ℱ hℱW hℱN T lam C ξ₀
      ↔ PaperForcedUniquePred D ℱ hℱW hℱN T lam C ξ₀ := by
  refine ⟨fun h qb qσ qh qf qg X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ γ₁ γ₂ _ h₁ h₂ =>
    h qb qσ qh qf qg X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ γ₁ γ₂ h₁ h₂,
    fun h qb qσ qh qf qg X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ γ₁ γ₂ h₁ h₂ => ?_⟩
  obtain ⟨qh', hF', hae⟩ := h₁.forcing.exists_predForcing D.N
  have h0 := (markedEnergy_sub_eq_zero_of_version h₁.forcing hF'.toForcing hae).1
  exact h qb qσ qh' qf qg X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ γ₁ γ₂ hF' (h₁.congr_qh hF'.toForcing h0)
    (h₂.congr_qh hF'.toForcing h0)

/-- **`WP(λ)` over all forcings is `WP(λ)` over the predictable ones, in the sense of the
paper.** -/
theorem paperForcedWP_iff_paperForcedWPPred :
    PaperForcedWP D ℱ hℱW hℱN T lam C ξ₀ ↔ PaperForcedWPPred D ℱ hℱW hℱN T lam C ξ₀ :=
  and_congr paperForcedSolvable_iff_paperForcedSolvablePred
    paperForcedUnique_iff_paperForcedUniquePred

/-! ### Lemma 4.4 over the predictable forcings -/

variable {cG α β₁ β₂ lamLow : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}

/-- **Lemma 4.4 over the predictable forcings, in the sense of the paper.** Let the
coefficients have (2.5) along every progressive tuple and satisfy Assumption 2.3 along the
diagonal with constant `L` and `g` Borel measurable in the state, Assumption 2.4 with coupling
matrix `G` and constant `c_G ≥ 0` and Assumption 2.5 along the diagonal with admissible constants
`α, β₁, β₂`, over a filtration whose null sets lie in its time-`0` field, whose
right-continuation is constant before `0` and which admits a cross witness, and let
`0 < λ̲ ≤ λ₀ ≤ 1` and `T > 0`. If the `λ₀`-system with initial datum `ξ₀` is well posed in the
sense of the paper over the forcings with a marked predictable jump component, then so is the
`(λ₀ + ζ)`-system, for every real `ζ` with `ζ² K_L C_B(λ̲) ≤ 1/4`, `C_B(λ̲)` the constant of
(4.14). -/
theorem PaperForcedWPPred.add_of_le (hWP : PaperForcedWPPred D ℱ hℱW hℱN T lam C ξ₀)
    (hreg : CoeffRegular ℱ P T C) (𝒲 : D.CrossWitness ℱ)
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
    PaperForcedWPPred D ℱ hℱW hℱN T (lam + ζ) C ξ₀ :=
  paperForcedWP_iff_paperForcedWPPred.mp
    ((paperForcedWP_iff_paperForcedWPPred.mpr hWP).add_of_le hreg 𝒲 hℱ0 hnull hT hlow hlam
      hlam1 hL hLT hg hcG hGf hGb hconst hM hMT hsmall)

end Dissertation.WellPosedness.Existence
