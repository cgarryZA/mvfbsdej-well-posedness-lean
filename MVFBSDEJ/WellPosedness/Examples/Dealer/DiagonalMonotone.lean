/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Examples.Dealer.Assumptions
import MVFBSDEJ.WellPosedness.Examples.Dealer.Monotone

/-!
# Example 5.5: the assumptions of the mean-field dealer market together

For `β₁, β₂ > 0`, `σ_c ∈ ℝ^{n×d}`, `h_c ∈ L²(ν; ℝⁿ)` and every interaction strength `ε ≥ 0`, the
dealer system `dealerCoeffs β₁ β₂ σ_c h_c ε` of Example 5.5,

`b = −β₁ y`, `σ = σ_c − β₁ z`, `h = h_c − β₁ u − ε A_{μ^U}(u)`, `f = β₂ x`, `g(x, ρ) = x`,

satisfies, over any filtration, (2.3) for `b, σ, h, f` with the Hilbert-norm `W₂` on `P₂(H)`,
the origin values of Assumption 2.2, Assumption 2.3 with `L = max{β₁ + ε, β₂, 1}`, and the
interior and terminal halves of Assumption 2.5 with `G = I`, `α = 1` and the constants `β₁, β₂`
of Example 5.1(i). Along two square-integrable tuples `Θ, Θ'` with laws `μ, μ'`, the jump
pairing written over the marks obeys

`𝔼 ∫_E ⟨δh(e), δU(e)⟩ ν(de) ≤ −β₁ 𝔼 ‖δU‖²_{L²(ν)}`.

## Main statements

* `integral_jump_dealer_le` — the jump pairing over the marks is at most `−β₁ 𝔼 ‖δU‖²`.
* `terminalMonotone_dealer` — Assumption 2.5, terminal, with `G = I` and `α = 1`.
* `dealer_assumptions` — (2.3), the origin values and Assumptions 2.3 and 2.5 together, for
  every `ε ≥ 0`.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped RealInnerProductSpace

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {n d : ℕ} {β₁ β₂ ε : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}
  {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **The jump pairing of the dealer system over the marks.** For `ε ≥ 0` and two
square-integrable tuples `Θ, Θ'` with laws `μ, μ'`,
`𝔼 ∫_E ⟨δh(e), δU(e)⟩ ν(de) ≤ −β₁ 𝔼 ‖δU‖²_{L²(ν)}`, with `δh = h(t, Θ, μ) − h(t, Θ', μ')`. -/
theorem integral_jump_dealer_le (hε : 0 ≤ ε) (t : ℝ) {Θ Θ' : Ω → TupleH ν n n d}
    (hΘ : MemLp Θ 2 P) (hΘ' : MemLp Θ' 2 P) :
    ∫ ω, (∫ e, ⟪(dealerCoeffs β₁ β₂ σc hc ε).h t (Θ ω) (lawP2 P Θ) e
        - (dealerCoeffs β₁ β₂ σc hc ε).h t (Θ' ω) (lawP2 P Θ') e,
        (Θ ω).2.2.2 e - (Θ' ω).2.2.2 e⟫ ∂ν) ∂P
      ≤ -β₁ * ∫ ω, ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2 ∂P := by
  refine le_of_eq_of_le (integral_congr_ae (ae_of_all _ fun ω => ?_))
    (integral_inner_jump_dealer_le (β₂ := β₂) (σc := σc) (hc := hc) hε t hΘ hΘ')
  simp only
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub ((dealerCoeffs β₁ β₂ σc hc ε).h t (Θ ω) (lawP2 P Θ))
      ((dealerCoeffs β₁ β₂ σc hc ε).h t (Θ' ω) (lawP2 P Θ')),
    Lp.coeFn_sub (Θ ω).2.2.2 (Θ' ω).2.2.2] with e h₁ h₂
  rw [h₁, h₂, Pi.sub_apply, Pi.sub_apply]

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **Assumption 2.5, terminal, along the diagonal, for the dealer system**, with `G = I` and
`α = 1`: `𝔼|δX_T|² = 𝔼⟨δg_T, δX_T⟩`. -/
theorem terminalMonotone_dealer :
    TerminalMonotone ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) 1 (dealerCoeffs β₁ β₂ σc hc ε).g :=
  terminalMonotone_affine (β₁ := β₁) (β₂ := β₂) (σc := σc) (hc := hc)

/-- **Example 5.5, the assumptions, at every interaction strength.** Let `β₁, β₂ > 0` and
`ε ≥ 0`. Over any filtration, the dealer system `dealerCoeffs β₁ β₂ σ_c h_c ε` satisfies (2.3)
for `b, σ, h, f` with the Hilbert-norm `W₂`; the origin values of Assumption 2.2; Assumption 2.3
along the diagonal with the Hilbert-norm `W₂` and at the terminal time, with the constant
`L = max{β₁ + ε, β₂, 1}`; and Assumption 2.5 with `G = I`, `α = 1` and the admissible constants
`β₁, β₂`. -/
theorem dealer_assumptions (T : ℝ) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (hε : 0 ≤ ε) :
    CoeffBorelW2 T (dealerCoeffs β₁ β₂ σc hc ε)
      ∧ CoeffOrigin T (dealerCoeffs β₁ β₂ σc hc ε)
      ∧ DiagonalLipschitzH ℱ P T (max (max (β₁ + ε) β₂) 1) (dealerCoeffs β₁ β₂ σc hc ε)
      ∧ TerminalLipschitz ℱ P T (max (max (β₁ + ε) β₂) 1) (dealerCoeffs β₁ β₂ σc hc ε).g
      ∧ Constants n n 1 β₁ β₂
      ∧ DiagonalMonotone ℱ P T 1 β₁ β₂ (dealerCoeffs β₁ β₂ σc hc ε)
      ∧ TerminalMonotone ℱ P T 1 1 (dealerCoeffs β₁ β₂ σc hc ε).g :=
  ⟨coeffBorelW2_dealer T, coeffOrigin_dealer T, diagonalLipschitzH_dealer hβ₁.le hβ₂.le hε,
    terminalLipschitz_dealer, constants_dealer hβ₁ hβ₂, diagonalMonotone_dealer hε,
    terminalMonotone_dealer⟩

end MVFBSDEJ.WellPosedness.Existence
