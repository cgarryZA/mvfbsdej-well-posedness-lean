/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.Dealer.ExposureCoeffs
import Dissertation.WellPosedness.Examples.Dealer.Monotone

/-!
# Example 5.5: monotonicity of the exposure-sensitive dealer market

The exposure-sensitive dealer system `dealerExpCoeffs β₁ β₂ σ_c h_c h_x ε`,

`b = −β₁ y`, `σ = σ_c − β₁ z`, `h = h_c + h_x x − β₁ u − ε A_{μ^U}(u)`,
`f = β₂ x + ⟨h_x, u⟩_{L²(ν)}`, `g(x, ρ) = x`,

is the dealer system perturbed by the exposure terms `p_h = h_x x`, `p_f = ⟨h_x, u⟩_{L²(ν)}`.
Along two inputs the exposure terms enter the interior pairing of (2.7) at `G = I` only through

`⟨h_x δX, δU⟩_{L²(ν)} − ⟨⟨h_x, δU⟩_{L²(ν)}, δX⟩ = 0`,

the pairing being the adjoint of the exposure operator. So the interior pairing is that of the
dealer system, pointwise, and the crowding correction improves it as there: for two
square-integrable tuples with laws `μ, μ'`,

`𝔼[∫_E ⟨δh(e), δU(e)⟩ ν(de) + ⟨−δf, δX⟩] ≤ −β₁ 𝔼 ‖δU‖²_{L²(ν)} − β₂ 𝔼 |δX|²`,

and (2.7) holds with `G = I` and the constants `β₁, β₂` of Example 5.1(i), for every `ε ≥ 0` and
every exposure profile `h_x ∈ L²(ν)`. The terminal function is that of Example 5.1(i).

## Main statements

* `interiorPairing_exposurePert` — the interior pairing of the exposure terms at `G = I`
  vanishes.
* `interiorPairing_dealerExp` — the interior pairing of the exposure-sensitive dealer system is
  that of the dealer system.
* `integrable_inner_jump_dealer` — the jump pairing of the dealer system is integrable.
* `integral_jump_driver_dealerExp_le` — the jump and driver pairing is at most
  `−β₁ 𝔼 ‖δU‖² − β₂ 𝔼 |δX|²`.
* `diagonalMonotone_dealerExp` — Assumption 2.5, interior, with `G = I` and the constants
  `β₁, β₂`, for every `ε ≥ 0` and every `h_x`.
* `terminalMonotone_dealerExp` — the terminal half with `α = 1`.
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.System Dissertation.Law

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {n d : ℕ} {β₁ β₂ ε : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}
  {hx : Lp ℝ 2 ν}

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The exposure terms cancel in the interior pairing**: at `G = I` the interior pairing of the
exposure perturbation is `⟨h_x δx, δu⟩_{L²(ν)} − ⟨⟨h_x, δu⟩_{L²(ν)}, δx⟩ = 0`. -/
theorem interiorPairing_exposurePert (t : ℝ) (θ θ' : TupleH ν n n d)
    (μ μ' : P2 (TupleH ν n n d)) :
    interiorPairing (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν)
        (diagDiff (exposurePert (d := d) hx) t θ θ' μ μ') = 0 := by
  have h := inner_exposureOp_sub_inner_exposurePair hx (θ.1 - θ'.1) (θ.2.2.2 - θ'.2.2.2)
  simp only [interiorPairing, diagDiff, exposurePert, GX_one, GZ_one, GU_one,
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply, sub_self, inner_zero_left,
    zero_add, ← map_sub, inner_neg_left]
  linarith

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The interior pairing of the exposure-sensitive dealer system** at `G = I` is that of the
dealer system: the exposure terms cancel. -/
theorem interiorPairing_dealerExp (t : ℝ) (θ θ' : TupleH ν n n d) (μ μ' : P2 (TupleH ν n n d)) :
    interiorPairing (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν)
        (diagDiff (dealerExpCoeffs β₁ β₂ σc hc hx ε) t θ θ' μ μ')
      = interiorPairing (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν)
        (diagDiff (dealerCoeffs β₁ β₂ σc hc ε) t θ θ' μ μ') := by
  rw [interiorPairing_diagDiff_perturb, interiorPairing_exposurePert, add_zero]

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- The jump pairing of the dealer system along two square-integrable tuples `Θ, Θ'` with laws
`μ, μ'` is integrable: `ω ↦ ⟨h(t, Θ, μ) − h(t, Θ', μ'), U − U'⟩_{L²(ν)}`. -/
theorem integrable_inner_jump_dealer (t : ℝ) {Θ Θ' : Ω → TupleH ν n n d} (hΘ : MemLp Θ 2 P)
    (hΘ' : MemLp Θ' 2 P) :
    Integrable (fun ω => ⟪(dealerCoeffs β₁ β₂ σc hc ε).h t (Θ ω) (lawP2 P Θ)
        - (dealerCoeffs β₁ β₂ σc hc ε).h t (Θ' ω) (lawP2 P Θ'), (Θ ω).2.2.2 - (Θ' ω).2.2.2⟫) P := by
  have hsq : Integrable (fun ω => ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2) P :=
    (hΘ.snd.snd.snd.sub hΘ'.snd.snd.snd).integrable_norm_pow two_ne_zero
  have hA := integrable_inner_crowdOp_margU_sub hΘ hΘ'
  refine ((hsq.const_mul (-β₁)).sub (hA.const_mul ε)).congr (Eventually.of_forall fun ω => ?_)
  simp only [Pi.sub_apply]
  rw [dealerCoeffs_h, dealerCoeffs_h]
  have e : hc - β₁ • (Θ ω).2.2.2 - ε • crowdOp (lawP2 P Θ).margU.law (Θ ω).2.2.2
      - (hc - β₁ • (Θ' ω).2.2.2 - ε • crowdOp (lawP2 P Θ').margU.law (Θ' ω).2.2.2)
      = -(β₁ • ((Θ ω).2.2.2 - (Θ' ω).2.2.2)) - ε • (crowdOp (lawP2 P Θ).margU.law (Θ ω).2.2.2
        - crowdOp (lawP2 P Θ').margU.law (Θ' ω).2.2.2) := by
    rw [smul_sub, smul_sub]
    abel
  rw [e]
  generalize crowdOp (lawP2 P Θ).margU.law (Θ ω).2.2.2
    - crowdOp (lawP2 P Θ').margU.law (Θ' ω).2.2.2 = a
  generalize (Θ ω).2.2.2 - (Θ' ω).2.2.2 = w
  rw [inner_sub_left, inner_neg_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  ring

/-- **The jump and driver pairing of the exposure-sensitive dealer system.** For `ε ≥ 0`, every
exposure profile `h_x` and two square-integrable tuples `Θ, Θ'` with laws `μ, μ'`,
`𝔼[∫_E ⟨δh(e), δU(e)⟩ ν(de) + ⟨−δf, δX⟩] ≤ −β₁ 𝔼 ‖δU‖²_{L²(ν)} − β₂ 𝔼 |δX|²`, with
`δψ = ψ(t, Θ, μ) − ψ(t, Θ', μ')`. -/
theorem integral_jump_driver_dealerExp_le (hε : 0 ≤ ε) (t : ℝ) {Θ Θ' : Ω → TupleH ν n n d}
    (hΘ : MemLp Θ 2 P) (hΘ' : MemLp Θ' 2 P) :
    ∫ ω, (⟪(dealerExpCoeffs β₁ β₂ σc hc hx ε).h t (Θ ω) (lawP2 P Θ)
          - (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t (Θ' ω) (lawP2 P Θ'),
          (Θ ω).2.2.2 - (Θ' ω).2.2.2⟫
        + ⟪-((dealerExpCoeffs β₁ β₂ σc hc hx ε).f t (Θ ω) (lawP2 P Θ)
          - (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t (Θ' ω) (lawP2 P Θ')), (Θ ω).1 - (Θ' ω).1⟫) ∂P
      ≤ -β₁ * ∫ ω, ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2 ∂P
        - β₂ * ∫ ω, ‖(Θ ω).1 - (Θ' ω).1‖ ^ 2 ∂P := by
  have hX : Integrable (fun ω => ‖(Θ ω).1 - (Θ' ω).1‖ ^ 2) P :=
    (hΘ.fst.sub hΘ'.fst).integrable_norm_pow two_ne_zero
  have hJ := integrable_inner_jump_dealer (β₁ := β₁) (β₂ := β₂) (σc := σc) (hc := hc) (ε := ε) t
    hΘ hΘ'
  have hle := integral_inner_jump_dealer_le (β₁ := β₁) (β₂ := β₂) (σc := σc) (hc := hc) hε t
    hΘ hΘ'
  have e : ∀ ω, ⟪(dealerExpCoeffs β₁ β₂ σc hc hx ε).h t (Θ ω) (lawP2 P Θ)
          - (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t (Θ' ω) (lawP2 P Θ'),
          (Θ ω).2.2.2 - (Θ' ω).2.2.2⟫
        + ⟪-((dealerExpCoeffs β₁ β₂ σc hc hx ε).f t (Θ ω) (lawP2 P Θ)
          - (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t (Θ' ω) (lawP2 P Θ')), (Θ ω).1 - (Θ' ω).1⟫
      = ⟪(dealerCoeffs β₁ β₂ σc hc ε).h t (Θ ω) (lawP2 P Θ)
          - (dealerCoeffs β₁ β₂ σc hc ε).h t (Θ' ω) (lawP2 P Θ'), (Θ ω).2.2.2 - (Θ' ω).2.2.2⟫
        - β₂ * ‖(Θ ω).1 - (Θ' ω).1‖ ^ 2 := by
    intro ω
    have hcan := inner_exposureOp_sub_inner_exposurePair hx ((Θ ω).1 - (Θ' ω).1)
      ((Θ ω).2.2.2 - (Θ' ω).2.2.2)
    have eh : (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t (Θ ω) (lawP2 P Θ)
        - (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t (Θ' ω) (lawP2 P Θ')
        = ((dealerCoeffs β₁ β₂ σc hc ε).h t (Θ ω) (lawP2 P Θ)
          - (dealerCoeffs β₁ β₂ σc hc ε).h t (Θ' ω) (lawP2 P Θ'))
          + exposureOp hx ((Θ ω).1 - (Θ' ω).1) := by
      change (dealerCoeffs β₁ β₂ σc hc ε).h t (Θ ω) (lawP2 P Θ) + exposureOp hx (Θ ω).1
        - ((dealerCoeffs β₁ β₂ σc hc ε).h t (Θ' ω) (lawP2 P Θ') + exposureOp hx (Θ' ω).1) = _
      rw [map_sub]
      abel
    have ef : (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t (Θ ω) (lawP2 P Θ)
        - (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t (Θ' ω) (lawP2 P Θ')
        = β₂ • ((Θ ω).1 - (Θ' ω).1) + exposurePair hx ((Θ ω).2.2.2 - (Θ' ω).2.2.2) := by
      rw [dealerExpCoeffs_f, dealerExpCoeffs_f, map_sub, smul_sub]
      abel
    rw [eh, ef, inner_add_left, neg_add, inner_add_left, inner_neg_left, inner_neg_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith
  rw [integral_congr_ae (Eventually.of_forall e), integral_sub hJ (hX.const_mul _),
    integral_const_mul]
  linarith

/-- **Assumption 2.5, interior, along the diagonal, for the exposure-sensitive dealer system**,
at every interaction strength `ε ≥ 0` and every exposure profile `h_x ∈ L²(ν)`: with `G = I` and
the constants `β₁, β₂` of Example 5.1(i),
`𝔼[⟨δb, δY⟩ + ⟨δσ, δZ⟩_F − ⟨δf, δX⟩ + ∫_E ⟨δh(e), δU(e)⟩ ν(de)]
  ≤ −β₁ 𝔼[|δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}] − β₂ 𝔼|δX|²`. -/
theorem diagonalMonotone_dealerExp (hε : 0 ≤ ε) :
    DiagonalMonotone ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) β₁ β₂
      (dealerExpCoeffs β₁ β₂ σc hc hx ε) := by
  filter_upwards [diagonalMonotone_dealer (ℱ := ℱ) (P := P) (T := T) (β₁ := β₁) (β₂ := β₂)
    (σc := σc) (hc := hc) hε] with t ht Θ Θ' h1 h2 h3 h4
  simp_rw [interiorPairing_dealerExp, dissipation_diagDiff_perturb]
  exact ht Θ Θ' h1 h2 h3 h4

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **Assumption 2.5, terminal, along the diagonal, for the exposure-sensitive dealer system**,
with `G = I` and `α = 1`: `𝔼|δX_T|² = 𝔼⟨δg_T, δX_T⟩`. -/
theorem terminalMonotone_dealerExp :
    TerminalMonotone ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) 1
      (dealerExpCoeffs β₁ β₂ σc hc hx ε).g :=
  terminalMonotone_affine (β₁ := β₁) (β₂ := β₂) (σc := σc) (hc := hc)

end Dissertation.WellPosedness.Existence
