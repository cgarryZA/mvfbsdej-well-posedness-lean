/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.Dealer.ExposureMonotone
import Dissertation.WellPosedness.Existence.PaperSolution
import Dissertation.WellPosedness.Robustness.Corollary
import Dissertation.WellPosedness.Existence.AffineExample
import Dissertation.WellPosedness.Existence.GlobalEnl
import Dissertation.WellPosedness.System.PaperUniquenessInt
import LevyStochCalc.Driver.GaussianInitial

/-!
# Example 5.5: well-posedness of the exposure-sensitive dealer market

For `β₁, β₂ > 0`, `σ_c ∈ ℝ^{n×d}`, `h_c ∈ L²(ν; ℝⁿ)`, every exposure profile `h_x ∈ L²(ν)` and
every interaction strength `ε ≥ 0`, the exposure-sensitive dealer system of Example 5.5 of the
paper,

`b = −β₁ y`, `σ = σ_c − β₁ z`, `h = h_c + h_x x − β₁ u − ε A_{μ^U}(u)`,
`f = β₂ x + ⟨h_x, u⟩_{L²(ν)}`, `g(x, ρ) = x`,

with `A_λ(u) = ∫ ∇V(u − v) λ(dv)` the crowding operator and `μ^U` the `U`-marginal of the
measure argument, satisfies (2.3) with the Hilbert-norm `W₂` on `P₂(H)`, Assumption 2.2,
Assumption 2.3 with `L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`, and Assumption 2.5 with `G = I`,
`α = 1` and the constants `β₁, β₂` of Example 5.1(i). No smallness condition on `ε` or `h_x` and
no margin enter, so Theorem 3.5 applies directly: when the Lévy driver has `d > 0` Brownian
coordinates, the system is well-posed over the initially enlarged filtration with a random
initial datum.

## Main statements

* `dealerExp_assumptions` — Assumptions 2.2, 2.3 and 2.5, and (2.3), for every `ε ≥ 0` and every
  `h_x`.
* `exists_solvesEnl_dealerExp_and_uniqueness` — well-posedness over `enlJoint 𝒢₀ D h𝒢₀`, with a
  random initial datum.
-/

open MeasureTheory Filter ProbabilityTheory Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System Dissertation.WellPosedness.Enlarged LevyStochCalc
  LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {n d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {β₁ β₂ ε : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}
  {hx : Lp ℝ 2 ν}

/-- **Example 5.5, the assumptions, at every interaction strength and exposure profile.** Let
`β₁, β₂ > 0`, `ε ≥ 0` and `h_x ∈ L²(ν)`. Over any filtration, the exposure-sensitive dealer
system `dealerExpCoeffs β₁ β₂ σ_c h_c h_x ε` satisfies (2.3) with the Hilbert-norm `W₂`;
Assumption 2.2; Assumption 2.3 along the diagonal with the Hilbert-norm `W₂` and at the terminal
time, with the constant `L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`; and Assumption 2.5 with
`G = I`, `α = 1` and the admissible constants `β₁, β₂`. -/
theorem dealerExp_assumptions {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (T : ℝ) (hβ₁ : 0 < β₁)
    (hβ₂ : 0 < β₂) (hε : 0 ≤ ε) :
    CoeffBorelW2 T (dealerExpCoeffs β₁ β₂ σc hc hx ε)
      ∧ CoeffOrigin T (dealerExpCoeffs β₁ β₂ σc hc hx ε)
      ∧ DiagonalLipschitzH ℱ P T (max (max (β₁ + ε + ‖hx‖) (β₂ + ‖hx‖)) 1)
          (dealerExpCoeffs β₁ β₂ σc hc hx ε)
      ∧ TerminalLipschitz ℱ P T (max (max (β₁ + ε + ‖hx‖) (β₂ + ‖hx‖)) 1)
          (dealerExpCoeffs β₁ β₂ σc hc hx ε).g
      ∧ Constants n n 1 β₁ β₂
      ∧ DiagonalMonotone ℱ P T 1 β₁ β₂ (dealerExpCoeffs β₁ β₂ σc hc hx ε)
      ∧ TerminalMonotone ℱ P T 1 1 (dealerExpCoeffs β₁ β₂ σc hc hx ε).g :=
  ⟨coeffBorelW2_dealerExp T, coeffOrigin_dealerExp T,
    diagonalLipschitzH_dealerExp hβ₁.le hβ₂.le hε, terminalLipschitz_dealerExp,
    constants_dealer hβ₁ hβ₂, diagonalMonotone_dealerExp hε, terminalMonotone_dealerExp⟩

/-! ### The initially enlarged filtration -/

section Enlarged

variable {ξ₀ : Fin n → Ω → ℝ}

/-- **Example 5.5 with a random initial datum, at every interaction strength and exposure
profile.** Let `D` be a Lévy driver with `d > 0` Brownian coordinates, `𝒢₀` a σ-algebra
independent of its joint natural filtration, `T > 0`, `β₁, β₂ > 0`, `ε ≥ 0`,
`σ_c ∈ ℝ^{n×d}`, `h_c ∈ L²(ν; ℝⁿ)`, `h_x ∈ L²(ν)`, and `ξ₀` square integrable and measurable for
the time-`0` field of `enlJoint 𝒢₀ D h𝒢₀`. Then the exposure-sensitive dealer system
`dealerExpCoeffs β₁ β₂ σ_c h_c h_x ε` has a solution over `enlJoint 𝒢₀ D h𝒢₀` whose forward
component starts at `ξ₀` almost surely, and any two solutions over it coincide: `X¹, X²` and
`Y¹, Y²` are indistinguishable on `[0, T]`, and `𝔼 ∫_0^T |Z¹ − Z²|²_F = 0`,
`𝔼 ∫_0^T ‖U¹ − U²‖²_{L²(ν)} = 0`, coordinatewise. -/
theorem exists_solvesEnl_dealerExp_and_uniqueness
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (hd : 0 < d) {T : ℝ} (hT : 0 < T)
    (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (hε : 0 ≤ ε) (hξ : ∀ i, MemLp (ξ₀ i) 2 P)
    (hξm : ∀ i, Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] (ξ₀ i)) :
    (∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin n → ℝ → Ω → ℝ) (Z : Fin n → ℝ → Ω → Fin d → ℝ)
      (U : Fin n → ℝ → Ω → E → ℝ) (γ : Fin n → ℝ → Ω → E → ℝ),
      SolvesEnl D h𝒢₀ hind₀ T (dealerExpCoeffs β₁ β₂ σc hc hx ε) ξ₀ X Y Z U γ
        ∧ ∀ i, X i 0 =ᵐ[P] ξ₀ i)
    ∧ ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin n → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin n → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin n → ℝ → Ω → E → ℝ)
      (γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ),
      SolvesEnl D h𝒢₀ hind₀ T (dealerExpCoeffs β₁ β₂ σc hc hx ε) ξ₀ X₁ Y₁ Z₁ U₁ γ₁ →
      SolvesEnl D h𝒢₀ hind₀ T (dealerExpCoeffs β₁ β₂ σc hc hx ε) ξ₀ X₂ Y₂ Z₂ U₂ γ₂ →
      (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
        ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
        ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
        ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0) := by
  obtain ⟨hmeas, horig, hL, hLT, hconst, hM, hMT⟩ :=
    dealerExp_assumptions (ℱ := enlJoint 𝒢₀ D h𝒢₀) (P := P) (σc := σc) (hc := hc) (hx := hx) T
      hβ₁ hβ₂ hε
  obtain ⟨⟨X, Y, Z, U, γ, h⟩, huniq⟩ :=
    exists_solvesEnl_and_uniqueness_of_rank_of_diagonalLipschitzH D h𝒢₀ hind₀ hd hT hmeas horig
      hL hLT (fun _ => measurable_id) (by rw [Matrix.rank_one, Fintype.card_fin, min_self])
      hconst hM hMT hξ hξm
  exact ⟨⟨X, Y, Z, U, γ, h, fun i => (h.fwd i).initial_ae_eq hT.le⟩, huniq⟩

end Enlarged

end Dissertation.WellPosedness.Existence
