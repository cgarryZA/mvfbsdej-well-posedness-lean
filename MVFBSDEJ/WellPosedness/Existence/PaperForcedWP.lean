/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Existence.Unique
import MVFBSDEJ.WellPosedness.System.PaperSolutionForcedOne
import MVFBSDEJ.WellPosedness.System.PaperSolutionForcedSolves

/-!
# `WP(λ)` in the sense of the paper: Lemmas 4.2 and 4.4

The paper calls the forced system (4.1) well posed at `λ`, `WP(λ)`, if it has a unique solution in
`𝕊` for every forcing `q`. `ForcedSolvable`, `ForcedUnique` and `ForcedWP` state `WP(λ)` for the
predicate `MVFBSDEJ.WellPosedness.System.SolvesForced`; `PaperForcedSolvable`,
`PaperForcedUnique` and `PaperForcedWP` state it for the paper's solution notion
`MVFBSDEJ.WellPosedness.System.PaperSolutionForced`, with the same quantifiers: every forcing in
the sense of `MVFBSDEJ.WellPosedness.System.Forcing` has a solution, and any two solutions with
the same forcing coincide in the sense of Theorem 3.3. The jump component of a
`MVFBSDEJ.WellPosedness.System.Forcing` is marked progressively measurable, where the paper
takes it predictable, so the quantifiers range over a class of forcings containing the paper's
(normalised to vanish off `[0, T]`).

The two forms pass into each other through the bridges of
`MVFBSDEJ.WellPosedness.System.PaperSolutionForcedSolves`.

* **Uniqueness.** A solution in the sense of the paper, extended off `[0, T]`, is a solution of
  `MVFBSDEJ.WellPosedness.System.SolvesForced` with the same `Z`, `U` and the same values on
  `[0, T]`, and the conclusion of Theorem 3.3 sees `X`, `Y` only on `[0, T]`: `ForcedUnique` gives
  `PaperForcedUnique` with no condition on the coefficients (`ForcedUnique.paperForcedUnique`).
* **Existence.** A solution of `MVFBSDEJ.WellPosedness.System.SolvesForced` is one in the sense
  of the paper after passing to predictable versions of `(Z, U)`, which needs the measurability
  (2.5) along every progressive tuple, `CoeffRegular`, and the `S²` bounds of Lemma 4.1:
  `ForcedSolvable` gives `PaperForcedSolvable` for `CoeffRegular` coefficients over a filtration on
  which Lemma 4.1 applies (`ForcedSolvable.paperForcedSolvable`). Conversely `PaperForcedSolvable`
  gives `ForcedSolvable` with no condition on the coefficients
  (`PaperForcedSolvable.forcedSolvable`).

Lemma 4.2 is stated for `MVFBSDEJ.WellPosedness.System.SolvesForced` under the joint Borel
measurability (2.3), `CoeffBorelW2`, which gives `CoeffRegular` (`CoeffBorelW2.toCoeffBorel`,
`CoeffBorel.coeffRegular`); in the sense of the paper it holds under the same hypotheses
(`paperForcedWP_of_le_smallCoupling`). Lemma 4.4 is stated for
`MVFBSDEJ.WellPosedness.System.SolvesForced` without a measurability hypothesis, since for
`λ₀ ≠ 0` and `g` Borel measurable in the state the coefficient processes along a solution of
`MVFBSDEJ.WellPosedness.System.SolvesForced` are forcings by the solution predicate itself; in
the sense of the paper it takes `CoeffRegular` for the passage to predictable versions at `λ₀ + ζ`
(`PaperForcedWP.add_of_le`). Uniqueness at `λ₀ + ζ` follows from the stability (4.14) at `λ₀`
(`ForcedStable.forcedUnique_add`), so of `WP(λ₀)` only the existence half enters.

## Main definitions

* `PaperForcedSolvable` — the existence half of `WP(λ)` in the sense of the paper.
* `PaperForcedUnique` — the uniqueness half of `WP(λ)` in the sense of the paper.
* `PaperForcedWP` — `WP(λ)` in the sense of the paper.

## Main statements

* `PaperForcedSolvable.forcedSolvable`, `ForcedSolvable.paperForcedSolvable`,
  `ForcedUnique.paperForcedUnique`, `ForcedWP.paperForcedWP` — passage between the two forms.
* `paperForcedWP_of_le_smallCoupling` — Lemma 4.2.
* `PaperForcedWP.add_of_le` — Lemma 4.4.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.System LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### `WP(λ)` in the sense of the paper -/

section Predicates

variable (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ)

/-- **The existence half of `WP(λ)` in the sense of the paper**: for the initial datum `ξ₀`, the
`λ`-forced system (4.1) with coefficients `C` has a solution in the sense of the paper for every
forcing. -/
def PaperForcedSolvable (T lam : ℝ) (C : Coeffs ν n m d) (ξ₀ : Fin n → Ω → ℝ) : Prop :=
  ∀ (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
    (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ), Forcing ℱ P ν T qb qσ qh qf qg →
    ∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
      (U : Fin m → ℝ → Ω → E → ℝ) (γ : Fin n → ℝ → Ω → E → ℝ),
      PaperSolutionForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ

/-- **The uniqueness half of `WP(λ)` in the sense of the paper**: any two solutions of the
`λ`-forced system (4.1) in the sense of the paper with coefficients `C`, initial datum `ξ₀` and
the same forcing coincide: `X¹, X²` and `Y¹, Y²` are indistinguishable on `[0, T]`, and
`𝔼 ∫_0^T |Z¹ − Z²|²_F = 0`, `𝔼 ∫_0^T ‖U¹ − U²‖²_{L²(ν)} = 0`, coordinatewise. -/
def PaperForcedUnique (T lam : ℝ) (C : Coeffs ν n m d) (ξ₀ : Fin n → Ω → ℝ) : Prop :=
  ∀ (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
    (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ) (X₁ X₂ : Fin n → ℝ → Ω → ℝ)
    (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ)
    (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ) (γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ),
    PaperSolutionForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X₁ Y₁ Z₁ U₁ γ₁ →
    PaperSolutionForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X₂ Y₂ Z₂ U₂ γ₂ →
    (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
      ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
      ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
      ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0)

/-- **`WP(λ)` in the sense of the paper**: for the initial datum `ξ₀`, the `λ`-forced system
(4.1) with coefficients `C` has a solution in the sense of the paper for every forcing, and any
two such solutions with the same forcing coincide. -/
def PaperForcedWP (T lam : ℝ) (C : Coeffs ν n m d) (ξ₀ : Fin n → Ω → ℝ) : Prop :=
  PaperForcedSolvable D ℱ hℱW hℱN T lam C ξ₀ ∧ PaperForcedUnique D ℱ hℱW hℱN T lam C ξ₀

end Predicates

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam ζ L : ℝ}
  {C : Coeffs ν n m d} {ξ₀ : Fin n → Ω → ℝ}

/-! ### Passage between the two forms -/

/-- **Solvability in the sense of the paper gives solvability of `SolvesForced`**, for `T ≥ 0`. -/
theorem PaperForcedSolvable.forcedSolvable (h : PaperForcedSolvable D ℱ hℱW hℱN T lam C ξ₀)
    (hT : 0 ≤ T) : ForcedSolvable D ℱ hℱW hℱN T lam C ξ₀ := by
  intro qb qσ qh qf qg hF
  obtain ⟨X, Y, Z, U, γ, hs⟩ := h qb qσ qh qf qg hF
  obtain ⟨X', Y', -, -, hs'⟩ := hs.exists_solvesForced hT
  exact ⟨X', Y', Z, U, γ, hs'⟩

/-- **Solvability of `SolvesForced` gives solvability in the sense of the paper**, for
coefficients with (2.5) along every progressive tuple and `T > 0`, over a filtration whose null
sets lie in its time-`0` field, whose right-continuation is constant before `0` and which admits
a cross witness. -/
theorem ForcedSolvable.paperForcedSolvable (h : ForcedSolvable D ℱ hℱW hℱN T lam C ξ₀)
    (hC : CoeffRegular ℱ P T C) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    PaperForcedSolvable D ℱ hℱW hℱN T lam C ξ₀ := by
  intro qb qσ qh qf qg hF
  obtain ⟨X, Y, Z, U, γ, hs⟩ := h qb qσ qh qf qg hF
  obtain ⟨Z', U', -, -, hp⟩ := hs.exists_paperSolutionForced hC 𝒲 hℱ0 hnull hT
  exact ⟨X, Y, Z', U', γ, hp⟩

/-- **Uniqueness for `SolvesForced` gives uniqueness in the sense of the paper**, for `T ≥ 0`. -/
theorem ForcedUnique.paperForcedUnique (h : ForcedUnique D ℱ hℱW hℱN T lam C ξ₀) (hT : 0 ≤ T) :
    PaperForcedUnique D ℱ hℱW hℱN T lam C ξ₀ := by
  intro qb qσ qh qf qg X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ γ₁ γ₂ h₁ h₂
  obtain ⟨X₁', Y₁', hX₁, hY₁, hs₁⟩ := h₁.exists_solvesForced hT
  obtain ⟨X₂', Y₂', hX₂, hY₂, hs₂⟩ := h₂.exists_solvesForced hT
  obtain ⟨hX, hY, hZ, hU⟩ := h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs₁ hs₂
  refine ⟨fun i => ?_, fun k => ?_, hZ, hU⟩
  · filter_upwards [hX i] with ω hω t ht
    rw [← congrFun (hX₁ i t ht) ω, ← congrFun (hX₂ i t ht) ω]
    exact hω t ht
  · filter_upwards [hY k] with ω hω t ht
    rw [← congrFun (hY₁ k t ht) ω, ← congrFun (hY₂ k t ht) ω]
    exact hω t ht

/-- **`WP(λ)` for `SolvesForced` gives `WP(λ)` in the sense of the paper**, for coefficients with
(2.5) along every progressive tuple and `T > 0`, over a filtration whose null sets lie in its
time-`0` field, whose right-continuation is constant before `0` and which admits a cross
witness. -/
theorem ForcedWP.paperForcedWP (h : ForcedWP D ℱ hℱW hℱN T lam C ξ₀)
    (hC : CoeffRegular ℱ P T C) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    PaperForcedWP D ℱ hℱW hℱN T lam C ξ₀ :=
  ⟨h.1.paperForcedSolvable hC 𝒲 hℱ0 hnull hT, h.2.paperForcedUnique hT.le⟩

/-! ### Lemmas 4.2 and 4.4 -/

variable {cG α β₁ β₂ lamLow : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}

/-- **Lemma 4.2 in the sense of the paper.** Under the hypotheses of `forcedWP_of_sq_le`,
`WP(λ)` in the sense of the paper holds for every `λ ∈ [0, λ*]`, with
`λ* = 1 / (2 (1 + K_L C₀(T))) ∈ (0, 1]` depending only on `T` and `L`. -/
theorem paperForcedWP_of_le_smallCoupling [ℱ.IsRightContinuous] (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hrep : HasTerminalRep D ℱ hℱW hℱN T) (hT : 0 < T) (hmeas : CoeffBorelW2 T C)
    (horig : CoeffOrigin T C) (hL : DiagonalLipschitz ℱ P T L C)
    (hLT : TerminalLipschitz ℱ P T L C.g) (hg : ∀ ρ, Measurable fun x => C.g x ρ)
    (hξ : ∀ i, MemLp (ξ₀ i) 2 P) (hξm : ∀ i, Measurable[ℱ 0] (ξ₀ i)) (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ smallCoupling T L) :
    PaperForcedWP D ℱ hℱW hℱN T lam C ξ₀ :=
  (forcedWP_of_le_smallCoupling 𝒲 hℱ0 hnull hrep hT hmeas horig hL hLT hg hξ hξm hlam0
    hlam).paperForcedWP (hmeas.toCoeffBorel.coeffRegular ℱ P) 𝒲 hℱ0 hnull hT

/-- **Lemma 4.4 in the sense of the paper, `WP(λ₀)` passes to `WP(λ₀ + ζ)`.** Let the
coefficients have (2.5) along every progressive tuple and satisfy Assumption 2.3 along the
diagonal with constant `L` and `g` Borel measurable in the state, Assumption 2.4 with coupling
matrix `G` and constant `c_G ≥ 0` and Assumption 2.5 along the diagonal with admissible constants
`α, β₁, β₂`, over a filtration whose null sets lie in its time-`0` field, whose
right-continuation is constant before `0` and which admits a cross witness, and let
`0 < λ̲ ≤ λ₀ ≤ 1` and `T > 0`. If the `λ₀`-system with initial datum `ξ₀` is well posed in the
sense of the paper, then so is the `(λ₀ + ζ)`-system, for every real `ζ` with
`ζ² K_L C_B(λ̲) ≤ 1/4`, `C_B(λ̲)` the constant of (4.14). -/
theorem PaperForcedWP.add_of_le (hWP : PaperForcedWP D ℱ hℱW hℱN T lam C ξ₀)
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
    PaperForcedWP D ℱ hℱW hℱN T (lam + ζ) C ξ₀ :=
  ⟨((hWP.1.forcedSolvable hT.le).add_of_le 𝒲 hℱ0 hnull hT hlow hlam hlam1 hL hLT hg hcG hGf hGb
      hconst hM hMT hsmall).paperForcedSolvable hreg 𝒲 hℱ0 hnull hT,
    ((forcedStable_of_le 𝒲 hℱ0 hnull hT hlow hlam hlam1 hL hLT hcG hGf hGb hconst hM
      hMT).forcedUnique_add 𝒲 hℱ0 hnull hT hL hLT hg hsmall).paperForcedUnique hT.le⟩

end MVFBSDEJ.WellPosedness.Existence
