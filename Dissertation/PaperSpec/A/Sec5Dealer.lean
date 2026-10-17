/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec5

/-!
# Example 5.5 of the well-posedness paper: the dealer market

Statement and equation numbers refer to arXiv 2608.23203v1, in the standing setting of §2 with
`n = m = d = 1` and `G = 1`. Example 5.5 tilts the jump response of Example 5.1(i) by the
crowding correction `A_{μ^U}(u) = ∫ ∇V(u − v) μ^U(dv)` of the `U`-marginal of the law.

## Main definitions

* `Dissertation.PaperSpec.A.ex55Coeffs` — the coefficients of Example 5.5.
* `Dissertation.PaperSpec.A.ex_dealer_coeffs` — at `ε = 0` they are those of Example 5.1(i).
* `Dissertation.PaperSpec.A.ex_dealer` — the origin value, (2.3) and Assumptions 2.2–2.4.
* `Dissertation.PaperSpec.A.ex_dealer_mono` — monotonicity at every `ε ≥ 0`.
* `Dissertation.PaperSpec.A.ex_dealer_wp` — well-posedness at every `ε ≥ 0`.
* `Dissertation.PaperSpec.A.ex_dealer_mean`, `ex_dealer_mean_corr` — the crowding correction is no
  function of the mean, over every σ-finite `ν` and when `L²(ν)` is not reduced to `0`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.Law

universe u v w

/-- The coefficients of Example 5.5 (with `n = m = d = 1`): for `β₁, β₂ ∈ ℝ`, `σ_c ∈ ℝ`,
`h_c ∈ L²(ν)` and `ε ∈ ℝ`, at `θ = (x, y, z, u)` and a law `μ` with `U`-marginal `μ^U`:
`b = −β₁ y`, `σ = σ_c − β₁ z`, `h = h_c − β₁ u − ε A_{μ^U}(u)`, `f = β₂ x` and `g(x, ρ) = x`. -/
noncomputable def ex55Coeffs {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (β₁ β₂ : ℝ) (σc : EuclideanSpace ℝ (Fin 1 × Fin 1))
    (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) (ε : ℝ) : Coeffs ν 1 1 1 where
  b _ θ _ := -(β₁ • θ.2.1)
  σ _ θ _ := σc - β₁ • θ.2.2.1
  h _ θ μ := hc - β₁ • θ.2.2.2 - ε • ex55Crowd μ.margU.law θ.2.2.2
  f _ θ _ := β₂ • θ.1
  g x _ := x

/-- Example 5.5, the coefficients at `ε = 0`. For `ν` σ-finite on a countably generated space,
the coefficients of Example 5.5 with `ε = 0` are those of Example 5.1(i). -/
def ex_dealer_coeffs : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (β₁ β₂ : ℝ) (σc : EuclideanSpace ℝ (Fin 1 × Fin 1))
    (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
    ex55Coeffs ν β₁ β₂ σc hc 0 = affineCoeffs β₁ β₂ σc hc

/-- Example 5.5, the assumptions. In the standing setting with `n = m = d = 1`, for `T > 0`,
`β₁, β₂ > 0`, `σ_c ∈ ℝ`, `h_c ∈ L²(ν)`, `ε ≥ 0` and `ξ₀ ∈ L²(Ω, ℱ₀)`, the coefficients of
Example 5.5 have origin value `h(t, 0, δ₀) = h_c` and satisfy (2.3), Assumption 2.2,
Assumption 2.3 with `L = max{β₁ + ε, β₂, 1}`, and Assumption 2.4 for `G = 1` with `c_G = 1`. -/
def ex_dealer : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ →
    ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
      (ε : ℝ), 0 ≤ ε →
    ∀ ξ₀ : Ω → EuclideanSpace ℝ (Fin 1),
    StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₀ → MemLp ξ₀ 2 P →
    (∀ t, (ex55Coeffs ν β₁ β₂ σc hc ε).h t 0 (P2.dirac 0) = hc)
      ∧ JointBorel T (ex55Coeffs ν β₁ β₂ σc hc ε)
      ∧ Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T (ex55Coeffs ν β₁ β₂ σc hc ε) ξ₀
      ∧ Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T (max (max (β₁ + ε) β₂) 1)
          (ex55Coeffs ν β₁ β₂ σc hc ε)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ (sMin (1 : Matrix (Fin 1) (Fin 1) ℝ) ^ 2)⁻¹ = 1

/-- Example 5.5, monotonicity at every `ε ≥ 0`. In the setting of `ex_dealer`, for every `t` and
all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`: `𝔼⟨A_{μ^U}(U) − A_{μ'^U}(U'), U − U'⟩_{L²(ν)} ≥ 0`;
`𝔼 ∫_E ⟨δh(e), δU(e)⟩ ν(de) ≤ −β₁ 𝔼‖δU‖²_{L²(ν)}`; and Assumption 2.5 holds with `G = 1`,
`α = 1` and the constants `β₁, β₂`. -/
def ex_dealer_mono : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ →
    ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
      (ε : ℝ), 0 ≤ ε →
    (∀ t, ∀ p ∈ diagonalInputs ν 1 1 1 (enlJoint 𝒢₀ D h𝒢₀) P t,
      ∀ p' ∈ diagonalInputs ν 1 1 1 (enlJoint 𝒢₀ D h𝒢₀) P t,
      0 ≤ ∫ ω, inner ℝ (ex55Crowd p.2.margU.law (p.1 ω).2.2.2
          - ex55Crowd p'.2.margU.law (p'.1 ω).2.2.2) ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2) ∂P)
    ∧ (∀ t, ∀ p ∈ diagonalInputs ν 1 1 1 (enlJoint 𝒢₀ D h𝒢₀) P t,
      ∀ p' ∈ diagonalInputs ν 1 1 1 (enlJoint 𝒢₀ D h𝒢₀) P t,
      ∫ ω, (∫ e, inner ℝ ((ex55Coeffs ν β₁ β₂ σc hc ε).h t (p.1 ω) p.2 e
            - (ex55Coeffs ν β₁ β₂ σc hc ε).h t (p'.1 ω) p'.2 e)
            ((p.1 ω).2.2.2 e - (p'.1 ω).2.2.2 e) ∂ν) ∂P
        ≤ -β₁ * ∫ ω, ‖(p.1 ω).2.2.2 - (p'.1 ω).2.2.2‖ ^ 2 ∂P)
    ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 β₁ β₂
        (ex55Coeffs ν β₁ β₂ σc hc ε)

/-- Example 5.5, well-posedness at every `ε ≥ 0`. In the setting of `ex_dealer`, (1.1) with the
coefficients of Example 5.5 and the initial datum `ξ₀` has a solution in `ℍ`, and any two
solutions are equal in `ℍ`: their `X` and their `Y` are indistinguishable on `[0, T]`, and
`𝔼 ∫_0^T |Z¹_t − Z²_t|² dt = 0` and `𝔼 ∫_0^T ‖U¹_t − U²_t‖²_{L²(ν)} dt = 0`. -/
def ex_dealer_wp : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ →
    ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
      (ε : ℝ), 0 ≤ ε →
    ∀ ξ₀ : Ω → EuclideanSpace ℝ (Fin 1),
    StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₀ → MemLp ξ₀ 2 P →
    (∃ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U : Fin 1 → ℝ → Ω → E → ℝ),
      Solution D h𝒢₀ hind₀ T (ex55Coeffs ν β₁ β₂ σc hc ε) ξ₀ X Y Z U)
    ∧ ∀ (X₁ X₂ : Fin 1 → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U₁ U₂ : Fin 1 → ℝ → Ω → E → ℝ),
      Solution D h𝒢₀ hind₀ T (ex55Coeffs ν β₁ β₂ σc hc ε) ξ₀ X₁ Y₁ Z₁ U₁ →
      Solution D h𝒢₀ hind₀ T (ex55Coeffs ν β₁ β₂ σc hc ε) ξ₀ X₂ Y₂ Z₂ U₂ →
      (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
        ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
        ∧ (∀ k j, LevyStochCalc.Brownian.Ito.energy P T
            (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
        ∧ ∀ k, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0

/-- Example 5.5, the crowding correction is no function of the mean, over every σ-finite `ν`.
For `ν` σ-finite on a countably generated space, there is no `Φ` with
`A_λ(u) = Φ(∫ v λ(dv), u)` for every `λ ∈ P₂(L²(ν))` and `u ∈ L²(ν)`. -/
def ex_dealer_mean : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E],
    ¬ ∃ Φ : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν → Lp (EuclideanSpace ℝ (Fin 1)) 2 ν
        → Lp (EuclideanSpace ℝ (Fin 1)) 2 ν,
      ∀ (Λ : P2 (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)) (u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
        ex55Crowd Λ.law u = Φ (∫ v, v ∂Λ.law) u

/-- Example 5.5, the crowding correction is no function of the mean when the fibre is
nontrivial: `ex_dealer_mean` with `L²(ν)` not reduced to `0` (for `ν ≠ 0`). -/
def ex_dealer_mean_corr : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E],
    (∃ u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν, u ≠ 0) →
    ¬ ∃ Φ : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν → Lp (EuclideanSpace ℝ (Fin 1)) 2 ν
        → Lp (EuclideanSpace ℝ (Fin 1)) 2 ν,
      ∀ (Λ : P2 (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)) (u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
        ex55Crowd Λ.law u = Φ (∫ v, v ∂Λ.law) u

end Dissertation.PaperSpec.A
