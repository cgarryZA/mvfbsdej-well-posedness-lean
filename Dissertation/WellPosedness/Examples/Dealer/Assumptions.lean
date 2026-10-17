/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.Dealer.Coeffs

/-!
# Example 5.5: the Lipschitz bound of the mean-field dealer market

On the tuple space `H = ℝⁿ × ℝⁿ × ℝ^{n×d} × L²(ν; ℝⁿ)`, fix `β₁, β₂ ≥ 0`, `σ_c ∈ ℝ^{n×d}`,
`h_c ∈ L²(ν; ℝⁿ)` and `ε ≥ 0`. The dealer system `dealerCoeffs β₁ β₂ σ_c h_c ε`,

`b = −β₁ y`, `σ = σ_c − β₁ z`, `h = h_c − β₁ u − ε A_{μ^U}(u)`, `f = β₂ x`, `g(x, ρ) = x`,

has, since `‖A_{μ^U}(u) − A_{μ'^U}(u')‖ ≤ ‖u − u'‖ + W₂(μ^U, μ'^U)`, at every time, pair of
points and pair of laws,

`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf|
  ≤ β₂ |δx| + β₁ |δy| + β₁ |δz|_F + (β₁ + ε) ‖δu‖ + ε W₂(μ^U, μ'^U)`.

Marginal projection is `1`-Lipschitz for `W₂`, so this is Assumption 2.3 with
`L = max{β₁ + ε, β₂, 1}`, for the Hilbert-norm `W₂` on `P₂(H)`; the terminal function is that of
Example 5.1(i).

## Main statements

* `norm_dealer_sub_le` — the pointwise Lipschitz bound for any law distance dominating
  `W₂(μ^U, μ'^U)`.
* `diagonalLipschitzH_dealer`, `terminalLipschitz_dealer` — Assumption 2.3 with
  `L = max{β₁ + ε, β₂, 1}`.
-/

open MeasureTheory Filter Dissertation.Law

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {n d : ℕ} {β₁ β₂ ε : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}

/-- **The pointwise Lipschitz bound of the dealer system.** For `β₁, β₂, ε ≥ 0` and any `W`
dominating `W₂(μ^U, μ'^U)`,
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ max{β₁ + ε, β₂, 1} (|δx| + |δy| + |δz|_F + ‖δu‖ + W)`. -/
theorem norm_dealer_sub_le (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hε : 0 ≤ ε) (t : ℝ)
    (θ θ' : TupleH ν n n d) (μ μ' : P2 (TupleH ν n n d)) {W : ℝ}
    (hW : w2P μ.margU μ'.margU ≤ W) :
    ‖(dealerCoeffs β₁ β₂ σc hc ε).b t θ μ - (dealerCoeffs β₁ β₂ σc hc ε).b t θ' μ'‖
        + ‖(dealerCoeffs β₁ β₂ σc hc ε).σ t θ μ - (dealerCoeffs β₁ β₂ σc hc ε).σ t θ' μ'‖
        + ‖(dealerCoeffs β₁ β₂ σc hc ε).h t θ μ - (dealerCoeffs β₁ β₂ σc hc ε).h t θ' μ'‖
        + ‖(dealerCoeffs β₁ β₂ σc hc ε).f t θ μ - (dealerCoeffs β₁ β₂ σc hc ε).f t θ' μ'‖
      ≤ max (max (β₁ + ε) β₂) 1 * (tupleNorm (θ - θ') + W) := by
  set A := crowdOp μ.margU.law θ.2.2.2
  set A' := crowdOp μ'.margU.law θ'.2.2.2
  set L := max (max (β₁ + ε) β₂) 1 with hLdef
  have hA : ‖A - A'‖ ≤ ‖θ.2.2.2 - θ'.2.2.2‖ + W :=
    (norm_crowdOp_margU_sub_le θ θ' μ μ').trans (by linarith)
  have eb : (dealerCoeffs β₁ β₂ σc hc ε).b t θ μ - (dealerCoeffs β₁ β₂ σc hc ε).b t θ' μ'
      = -(β₁ • (θ.2.1 - θ'.2.1)) := by
    simp only [dealerCoeffs, Coeffs.perturb, crowdPert, affineCoeffs, add_zero, smul_sub]
    abel
  have eσ : (dealerCoeffs β₁ β₂ σc hc ε).σ t θ μ - (dealerCoeffs β₁ β₂ σc hc ε).σ t θ' μ'
      = -(β₁ • (θ.2.2.1 - θ'.2.2.1)) := by
    simp only [dealerCoeffs, Coeffs.perturb, crowdPert, affineCoeffs, add_zero, smul_sub]
    abel
  have eh : (dealerCoeffs β₁ β₂ σc hc ε).h t θ μ - (dealerCoeffs β₁ β₂ σc hc ε).h t θ' μ'
      = -(β₁ • (θ.2.2.2 - θ'.2.2.2)) - ε • (A - A') := by
    rw [dealerCoeffs_h, dealerCoeffs_h, smul_sub, smul_sub]
    abel
  have ef : (dealerCoeffs β₁ β₂ σc hc ε).f t θ μ - (dealerCoeffs β₁ β₂ σc hc ε).f t θ' μ'
      = β₂ • (θ.1 - θ'.1) := by
    simp only [dealerCoeffs, Coeffs.perturb, crowdPert, affineCoeffs, add_zero, smul_sub]
  have hh : ‖-(β₁ • (θ.2.2.2 - θ'.2.2.2)) - ε • (A - A')‖
      ≤ β₁ * ‖θ.2.2.2 - θ'.2.2.2‖ + ε * (‖θ.2.2.2 - θ'.2.2.2‖ + W) := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_neg, norm_smul, Real.norm_of_nonneg hβ₁]
    · rw [norm_smul, Real.norm_of_nonneg hε]
      exact mul_le_mul_of_nonneg_left hA hε
  rw [eb, eσ, eh, ef, norm_neg, norm_neg, norm_smul, norm_smul, norm_smul,
    Real.norm_of_nonneg hβ₁, Real.norm_of_nonneg hβ₂]
  have htn : tupleNorm (θ - θ')
      = ‖θ.1 - θ'.1‖ + ‖θ.2.1 - θ'.2.1‖ + ‖θ.2.2.1 - θ'.2.2.1‖ + ‖θ.2.2.2 - θ'.2.2.2‖ := rfl
  rw [htn]
  have hW0 : 0 ≤ W := (w2P_nonneg _ _).trans hW
  have hL₁ : β₁ + ε ≤ L := (le_max_left _ _).trans (le_max_left _ _)
  have hL₂ : β₂ ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  have hLβ : β₁ ≤ L := by linarith
  have hLε : ε ≤ L := by linarith
  have h1 := norm_nonneg (θ.1 - θ'.1)
  have h2 := norm_nonneg (θ.2.1 - θ'.2.1)
  have h3 := norm_nonneg (θ.2.2.1 - θ'.2.2.1)
  have h4 := norm_nonneg (θ.2.2.2 - θ'.2.2.2)
  nlinarith [mul_le_mul_of_nonneg_right hL₂ h1, mul_le_mul_of_nonneg_right hLβ h2,
    mul_le_mul_of_nonneg_right hLβ h3, mul_le_mul_of_nonneg_right hL₁ h4,
    mul_le_mul_of_nonneg_right hLε hW0]

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **Assumption 2.3, interior, along the diagonal, for the dealer system**, with the
Hilbert-norm `W₂` on `P₂(H)` and the constant `L = max{β₁ + ε, β₂, 1}`, for `β₁, β₂, ε ≥ 0`. -/
theorem diagonalLipschitzH_dealer (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hε : 0 ≤ ε) :
    DiagonalLipschitzH ℱ P T (max (max (β₁ + ε) β₂) 1) (dealerCoeffs β₁ β₂ σc hc ε) :=
  Eventually.of_forall fun t Θ Θ' _ _ _ _ => Eventually.of_forall fun ω =>
    norm_dealer_sub_le hβ₁ hβ₂ hε t (Θ ω) (Θ' ω) _ _ (w2P_margU_le_w2H _ _)

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **Assumption 2.3, terminal, along the diagonal, for the dealer system**, with the constant
`L = max{β₁ + ε, β₂, 1}`: the terminal function is `g(x, ρ) = x`. -/
theorem terminalLipschitz_dealer :
    TerminalLipschitz ℱ P T (max (max (β₁ + ε) β₂) 1) (dealerCoeffs β₁ β₂ σc hc ε).g :=
  (terminalLipschitz_affine (β₁ := β₁) (β₂ := β₂) (σc := σc) (hc := hc)
    (le_max_right _ 1)).perturb

end Dissertation.WellPosedness.Existence
