/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.Dealer.Assumptions
import Dissertation.WellPosedness.Examples.Dealer.DiagonalMonotone
import Dissertation.WellPosedness.Examples.Dealer.Marks

/-!
# Example 5.5: the exposure-sensitive dealer market

On the tuple space `H = ℝ × ℝ × ℝ^{1×d} × L²(ν)`, fix `β₁, β₂ ≥ 0`, `σ_c ∈ ℝ^{1×d}`,
`h_c, h_x ∈ L²(ν)` and `ε ≥ 0`. The exposure-sensitive dealer system
`dealerExpCoeffs β₁ β₂ σ_c h_c h_x ε`,

`b = −β₁ y`, `σ = σ_c − β₁ z`, `h = h_c + h_x x − β₁ u − ε A_{μ^U}(u)`,
`f = β₂ x + ⟨h_x, u⟩_{L²(ν)}`, `g(x, ρ) = x`,

is the dealer system of `dealerCoeffs` perturbed by the exposure terms `p_h = h_x x` and
`p_f = ⟨h_x, u⟩`. The exposure terms cancel in the interior pairing,
`⟨h_x δx, δu⟩ − ⟨h_x, δu⟩ δx = 0`, so the system satisfies Assumption 2.5 with the constants of
Example 5.1(i), and they enlarge the Lipschitz constant to
`L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`.

## Main definitions

* `exposurePert` — the exposure terms `p_h = h_x x`, `p_f = ⟨h_x, u⟩`, as a perturbation.
* `dealerExpCoeffs` — the exposure-sensitive dealer system.

## Main statements

* `dealerExpCoeffs_zero` — at `h_x = 0` it is the dealer system of `dealerCoeffs`.
* `dealerExpCoeffs_h`, `dealerExpCoeffs_f`, `dealerExpCoeffs_h_origin` — the jump coefficient and
  the driver, and the origin value `h_c` of the jump coefficient.
* `interiorPairing_exposurePert` — the exposure terms do not enter the interior pairing.
* `dealerExp_assumptions` — (2.3), Assumptions 2.2, 2.3 and 2.5.
-/

open MeasureTheory Filter Dissertation.Law
open scoped RealInnerProductSpace

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {d : ℕ}

/-! ### The coefficients -/

/-- The exposure terms of Example 5.5 as a perturbation: for `h_x ∈ L²(ν)`, at
`θ = (x, y, z, u)`, `p_h = h_x x` and `p_f = ⟨h_x, u⟩_{L²(ν)}`, with `p_b = p_σ = 0`; its
terminal function `0` is not used. -/
noncomputable def exposurePert (hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) : Coeffs ν 1 1 d where
  b _ _ _ := 0
  σ _ _ _ := 0
  h _ θ _ := θ.1 0 • hx
  f _ θ _ := PiLp.single 2 0 ⟪hx, θ.2.2.2⟫
  g _ _ := 0

/-- The exposure-sensitive dealer system of Example 5.5: for `θ = (x, y, z, u)`, `b = −β₁ y`,
`σ = σ_c − β₁ z`, `h = h_c + h_x x − β₁ u − ε A_{μ^U}(u)`, `f = β₂ x + ⟨h_x, u⟩` and
`g(x, ρ) = x`, the dealer system `dealerCoeffs` perturbed by the exposure terms. -/
noncomputable abbrev dealerExpCoeffs (β₁ β₂ : ℝ) (σc : EuclideanSpace ℝ (Fin 1 × Fin d))
    (hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) (ε : ℝ) : Coeffs ν 1 1 d :=
  (dealerCoeffs β₁ β₂ σc hc ε).perturb (exposurePert hx)

variable {β₁ β₂ ε : ℝ} {σc : EuclideanSpace ℝ (Fin 1 × Fin d)}
  {hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν}

/-- **At `h_x = 0` the exposure-sensitive system is the dealer system.** -/
theorem dealerExpCoeffs_zero (β₁ β₂ : ℝ) (σc : EuclideanSpace ℝ (Fin 1 × Fin d))
    (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) (ε : ℝ) :
    dealerExpCoeffs β₁ β₂ σc hc 0 ε = dealerCoeffs β₁ β₂ σc hc ε := by
  have h0 : (PiLp.single 2 (0 : Fin 1) (0 : ℝ) : EuclideanSpace ℝ (Fin 1)) = 0 := by simp
  simp only [dealerExpCoeffs, Coeffs.perturb, exposurePert, smul_zero, add_zero, inner_zero_left,
    h0]

/-- The jump coefficient of the exposure-sensitive system,
`h(t, θ, μ) = h_c − β₁ u − ε A_{μ^U}(u) + h_x x`. -/
theorem dealerExpCoeffs_h (t : ℝ) (θ : TupleH ν 1 1 d) (μ : P2 (TupleH ν 1 1 d)) :
    (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t θ μ
      = hc - β₁ • θ.2.2.2 - ε • crowdOp μ.margU.law θ.2.2.2 + θ.1 0 • hx := by
  change (dealerCoeffs β₁ β₂ σc hc ε).h t θ μ + θ.1 0 • hx = _
  rw [dealerCoeffs_h]

/-- The driver of the exposure-sensitive system, `f(t, θ, μ) = β₂ x + ⟨h_x, u⟩`. -/
theorem dealerExpCoeffs_f (t : ℝ) (θ : TupleH ν 1 1 d) (μ : P2 (TupleH ν 1 1 d)) :
    (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t θ μ
      = β₂ • θ.1 + PiLp.single 2 0 ⟪hx, θ.2.2.2⟫ := by
  simp only [dealerExpCoeffs, Coeffs.perturb, dealerCoeffs, crowdPert, affineCoeffs, exposurePert,
    add_zero]

/-- **The origin value of the jump coefficient is `h_c`**: `h(t, 0, δ₀) = h_c`. -/
theorem dealerExpCoeffs_h_origin (t : ℝ) :
    (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t 0 (P2.dirac 0) = hc := by
  change (dealerCoeffs β₁ β₂ σc hc ε).h t 0 (P2.dirac 0) + (0 : TupleH ν 1 1 d).1 0 • hx = hc
  rw [dealerCoeffs_h_origin]
  simp

/-- **Assumption 2.2 for the exposure terms**: their origin values vanish. -/
theorem coeffOrigin_exposurePert (T : ℝ) :
    CoeffOrigin T (exposurePert (ν := ν) (d := d) hx) := by
  have h : (fun t => (exposurePert (ν := ν) (d := d) hx).h t 0 (P2.dirac 0)) = fun _ => 0 :=
    funext fun _ => by simp [exposurePert]
  have hf : (fun t => (exposurePert (ν := ν) (d := d) hx).f t 0 (P2.dirac 0)) = fun _ => 0 :=
    funext fun _ => by simp [exposurePert]
  unfold CoeffOrigin
  rw [h, hf]
  exact originIntegrable_const T 0 0 0 0

/-- **Assumption 2.2 for the exposure-sensitive system.** -/
theorem coeffOrigin_dealerExp (T : ℝ) : CoeffOrigin T (dealerExpCoeffs β₁ β₂ σc hc hx ε) :=
  coeffOrigin_perturb (coeffOrigin_dealer T) (coeffOrigin_exposurePert T)

/-! ### (2.3) -/

/-- **(2.3) for the exposure terms, with the Hilbert-norm `W₂` on `P₂(H)`**: they are
continuous in the tuple. -/
theorem coeffBorelW2_exposurePert (T : ℝ) :
    CoeffBorelW2 T (exposurePert (ν := ν) (d := d) hx) where
  b_meas := Continuous.borel_measurable continuous_const
  σ_meas := Continuous.borel_measurable continuous_const
  h_meas := Continuous.borel_measurable (by
    simp only [exposurePert]
    exact (((PiLp.continuous_apply 2 _ 0).comp continuous_fst).comp
      (continuous_fst.comp continuous_snd)).smul continuous_const)
  f_meas := Continuous.borel_measurable (by
    simp only [exposurePert]
    exact continuous_euclideanSingle_zero.comp (continuous_const.inner
      (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp
        (continuous_fst.comp continuous_snd))))))

/-- **(2.3) for the exposure-sensitive system, with the Hilbert-norm `W₂` on `P₂(H)`.** -/
theorem coeffBorelW2_dealerExp (T : ℝ) : CoeffBorelW2 T (dealerExpCoeffs β₁ β₂ σc hc hx ε) :=
  (coeffBorelW2_dealer T).perturb (coeffBorelW2_exposurePert T)

/-! ### Assumption 2.3 -/

/-- **The pointwise Lipschitz bound of the exposure-sensitive system.** For `β₁, β₂, ε ≥ 0` and
any `W` dominating `W₂(μ^U, μ'^U)`,
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ L (|δx| + |δy| + |δz|_F + ‖δu‖ + W)` with
`L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`. -/
theorem norm_dealerExp_sub_le (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hε : 0 ≤ ε) (t : ℝ)
    (θ θ' : TupleH ν 1 1 d) (μ μ' : P2 (TupleH ν 1 1 d)) {W : ℝ}
    (hW : w2P μ.margU μ'.margU ≤ W) :
    ‖(dealerExpCoeffs β₁ β₂ σc hc hx ε).b t θ μ - (dealerExpCoeffs β₁ β₂ σc hc hx ε).b t θ' μ'‖
        + ‖(dealerExpCoeffs β₁ β₂ σc hc hx ε).σ t θ μ
          - (dealerExpCoeffs β₁ β₂ σc hc hx ε).σ t θ' μ'‖
        + ‖(dealerExpCoeffs β₁ β₂ σc hc hx ε).h t θ μ
          - (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t θ' μ'‖
        + ‖(dealerExpCoeffs β₁ β₂ σc hc hx ε).f t θ μ
          - (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t θ' μ'‖
      ≤ max (max (β₁ + ε + ‖hx‖) (β₂ + ‖hx‖)) 1 * (tupleNorm (θ - θ') + W) := by
  set A := crowdOp μ.margU.law θ.2.2.2
  set A' := crowdOp μ'.margU.law θ'.2.2.2
  set L := max (max (β₁ + ε + ‖hx‖) (β₂ + ‖hx‖)) 1 with hLdef
  have hA : ‖A - A'‖ ≤ ‖θ.2.2.2 - θ'.2.2.2‖ + W :=
    (norm_crowdOp_margU_sub_le θ θ' μ μ').trans (by linarith)
  have eb : (dealerExpCoeffs β₁ β₂ σc hc hx ε).b t θ μ
      - (dealerExpCoeffs β₁ β₂ σc hc hx ε).b t θ' μ' = -(β₁ • (θ.2.1 - θ'.2.1)) := by
    simp only [dealerExpCoeffs, dealerCoeffs, Coeffs.perturb, crowdPert, affineCoeffs,
      exposurePert, add_zero, smul_sub]
    abel
  have eσ : (dealerExpCoeffs β₁ β₂ σc hc hx ε).σ t θ μ
      - (dealerExpCoeffs β₁ β₂ σc hc hx ε).σ t θ' μ' = -(β₁ • (θ.2.2.1 - θ'.2.2.1)) := by
    simp only [dealerExpCoeffs, dealerCoeffs, Coeffs.perturb, crowdPert, affineCoeffs,
      exposurePert, add_zero, smul_sub]
    abel
  have eh : (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t θ μ
      - (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t θ' μ'
      = -(β₁ • (θ.2.2.2 - θ'.2.2.2)) - ε • (A - A') + (θ.1 0 - θ'.1 0) • hx := by
    rw [dealerExpCoeffs_h, dealerExpCoeffs_h, smul_sub, smul_sub, sub_smul]
    abel
  have ef : (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t θ μ
      - (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t θ' μ'
      = β₂ • (θ.1 - θ'.1) + PiLp.single 2 0 ⟪hx, θ.2.2.2 - θ'.2.2.2⟫ := by
    rw [dealerExpCoeffs_f, dealerExpCoeffs_f, inner_sub_right, smul_sub, PiLp.single_sub]
    abel
  have hx0 : |θ.1 0 - θ'.1 0| ≤ ‖θ.1 - θ'.1‖ := by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le (θ.1 - θ'.1) 0).trans_eq' (by rw [PiLp.sub_apply])
  have hh : ‖-(β₁ • (θ.2.2.2 - θ'.2.2.2)) - ε • (A - A') + (θ.1 0 - θ'.1 0) • hx‖
      ≤ β₁ * ‖θ.2.2.2 - θ'.2.2.2‖ + ε * (‖θ.2.2.2 - θ'.2.2.2‖ + W)
        + ‖hx‖ * ‖θ.1 - θ'.1‖ := by
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_neg, norm_smul, Real.norm_of_nonneg hβ₁]
    · rw [norm_smul, Real.norm_of_nonneg hε]
      exact mul_le_mul_of_nonneg_left hA hε
    · rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_left hx0 (norm_nonneg _)
  have hf : ‖β₂ • (θ.1 - θ'.1) + PiLp.single 2 0 ⟪hx, θ.2.2.2 - θ'.2.2.2⟫‖
      ≤ β₂ * ‖θ.1 - θ'.1‖ + ‖hx‖ * ‖θ.2.2.2 - θ'.2.2.2‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_of_nonneg hβ₂]
    · rw [PiLp.norm_single, Real.norm_eq_abs]
      exact abs_real_inner_le_norm _ _
  rw [eb, eσ, eh, ef, norm_neg, norm_neg, norm_smul, norm_smul, Real.norm_of_nonneg hβ₁]
  have htn : tupleNorm (θ - θ')
      = ‖θ.1 - θ'.1‖ + ‖θ.2.1 - θ'.2.1‖ + ‖θ.2.2.1 - θ'.2.2.1‖ + ‖θ.2.2.2 - θ'.2.2.2‖ := rfl
  rw [htn]
  have hW0 : 0 ≤ W := (w2P_nonneg _ _).trans hW
  have hL₁ : β₁ + ε + ‖hx‖ ≤ L := (le_max_left _ _).trans (le_max_left _ _)
  have hL₂ : β₂ + ‖hx‖ ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  have hn := norm_nonneg hx
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

/-- **Assumption 2.3, interior, along the diagonal, for the exposure-sensitive system**, with
the Hilbert-norm `W₂` on `P₂(H)` and `L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`. -/
theorem diagonalLipschitzH_dealerExp (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hε : 0 ≤ ε) :
    DiagonalLipschitzH ℱ P T (max (max (β₁ + ε + ‖hx‖) (β₂ + ‖hx‖)) 1)
      (dealerExpCoeffs β₁ β₂ σc hc hx ε) :=
  Eventually.of_forall fun t Θ Θ' _ _ _ _ => Eventually.of_forall fun ω =>
    norm_dealerExp_sub_le hβ₁ hβ₂ hε t (Θ ω) (Θ' ω) _ _ (w2P_margU_le_w2H _ _)

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **Assumption 2.3, terminal, for the exposure-sensitive system**: the terminal function is
`g(x, ρ) = x`. -/
theorem terminalLipschitz_dealerExp :
    TerminalLipschitz ℱ P T (max (max (β₁ + ε + ‖hx‖) (β₂ + ‖hx‖)) 1)
      (dealerExpCoeffs β₁ β₂ σc hc hx ε).g :=
  ((terminalLipschitz_affine (β₁ := β₁) (β₂ := β₂) (σc := σc) (hc := hc)
    (le_max_right _ 1)).perturb).perturb

/-! ### Assumption 2.5 -/

/-- **The exposure terms do not enter the interior pairing**: at `G = I`,
`⟨h_x δx, δu⟩ − ⟨h_x, δu⟩ δx = 0`. -/
theorem interiorPairing_exposurePert (t : ℝ) (θ θ' : TupleH ν 1 1 d)
    (μ μ' : P2 (TupleH ν 1 1 d)) :
    interiorPairing (GX (1 : Matrix (Fin 1) (Fin 1) ℝ)) (GZ 1) (GU 1 ν)
      (diagDiff (exposurePert (d := d) hx) t θ θ' μ μ') = 0 := by
  have ef : (PiLp.single 2 (0 : Fin 1) ⟪hx, θ.2.2.2⟫ : EuclideanSpace ℝ (Fin 1))
      - PiLp.single 2 0 ⟪hx, θ'.2.2.2⟫
      = (PiLp.single 2 (0 : Fin 1) ⟪hx, θ.2.2.2 - θ'.2.2.2⟫ : EuclideanSpace ℝ (Fin 1)) := by
    rw [inner_sub_right, PiLp.single_sub]
  have eh : θ.1 0 • hx - θ'.1 0 • hx = (θ.1 - θ'.1) 0 • hx := by
    rw [PiLp.sub_apply, sub_smul]
  simp only [interiorPairing, diagDiff, exposurePert, GX_one, GZ_one, GU_one,
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply, sub_self, inner_zero_left,
    zero_add, ef, eh, inner_neg_left, real_inner_smul_left, PiLp.inner_apply, PiLp.single_apply,
    Fin.sum_univ_one, if_true, RCLike.inner_apply, conj_trivial]
  ring

/-- **The interior pairing of the exposure-sensitive system** at `G = I` is that of the dealer
system. -/
theorem interiorPairing_dealerExp (t : ℝ) (θ θ' : TupleH ν 1 1 d) (μ μ' : P2 (TupleH ν 1 1 d)) :
    interiorPairing (GX (1 : Matrix (Fin 1) (Fin 1) ℝ)) (GZ 1) (GU 1 ν)
        (diagDiff (dealerExpCoeffs β₁ β₂ σc hc hx ε) t θ θ' μ μ')
      = interiorPairing (GX (1 : Matrix (Fin 1) (Fin 1) ℝ)) (GZ 1) (GU 1 ν)
        (diagDiff (dealerCoeffs β₁ β₂ σc hc ε) t θ θ' μ μ') := by
  rw [interiorPairing_diagDiff_perturb, interiorPairing_exposurePert, add_zero]

/-- **Assumption 2.5, interior, along the diagonal, for the exposure-sensitive system**, at every
interaction strength `ε ≥ 0`, with `G = I` and the constants `β₁, β₂` of Example 5.1(i). -/
theorem diagonalMonotone_dealerExp (hε : 0 ≤ ε) :
    DiagonalMonotone ℱ P T (1 : Matrix (Fin 1) (Fin 1) ℝ) β₁ β₂
      (dealerExpCoeffs β₁ β₂ σc hc hx ε) := by
  have h := diagonalMonotone_dealer (ℱ := ℱ) (P := P) (T := T) (β₁ := β₁) (β₂ := β₂)
    (σc := σc) (hc := hc) hε
  refine h.mono fun t ht Θ Θ' hΘt hΘ't hΘ hΘ' => ?_
  simp_rw [interiorPairing_dealerExp, dissipation_diagDiff_perturb]
  exact ht Θ Θ' hΘt hΘ't hΘ hΘ'

/-- **The jump and driver channels of the exposure-sensitive system.** The exposure terms cancel
between the two channels:
`⟨δh, δu⟩ + ⟨−δf, δx⟩ = −β₁ ‖δu‖² − ε ⟨A_{μ^U}(u) − A_{μ'^U}(u'), δu⟩ − β₂ |δx|²`. -/
theorem inner_jump_driver_dealerExp (t : ℝ) (θ θ' : TupleH ν 1 1 d)
    (μ μ' : P2 (TupleH ν 1 1 d)) :
    ⟪(dealerExpCoeffs β₁ β₂ σc hc hx ε).h t θ μ - (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t θ' μ',
        θ.2.2.2 - θ'.2.2.2⟫
      + ⟪-((dealerExpCoeffs β₁ β₂ σc hc hx ε).f t θ μ
          - (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t θ' μ'), θ.1 - θ'.1⟫
      = -β₁ * ‖θ.2.2.2 - θ'.2.2.2‖ ^ 2
        - ε * ⟪crowdOp μ.margU.law θ.2.2.2 - crowdOp μ'.margU.law θ'.2.2.2, θ.2.2.2 - θ'.2.2.2⟫
        - β₂ * ‖θ.1 - θ'.1‖ ^ 2 := by
  have eh : (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t θ μ
      - (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t θ' μ'
      = -(β₁ • (θ.2.2.2 - θ'.2.2.2))
        - ε • (crowdOp μ.margU.law θ.2.2.2 - crowdOp μ'.margU.law θ'.2.2.2)
        + (θ.1 - θ'.1) 0 • hx := by
    rw [dealerExpCoeffs_h, dealerExpCoeffs_h, smul_sub, smul_sub, PiLp.sub_apply, sub_smul]
    abel
  have ef : (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t θ μ
      - (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t θ' μ'
      = β₂ • (θ.1 - θ'.1) + PiLp.single 2 0 ⟪hx, θ.2.2.2 - θ'.2.2.2⟫ := by
    rw [dealerExpCoeffs_f, dealerExpCoeffs_f, inner_sub_right, smul_sub, PiLp.single_sub]
    abel
  have hs : ⟪(PiLp.single 2 (0 : Fin 1) ⟪hx, θ.2.2.2 - θ'.2.2.2⟫ : EuclideanSpace ℝ (Fin 1)),
      θ.1 - θ'.1⟫ = ⟪hx, θ.2.2.2 - θ'.2.2.2⟫ * (θ.1 - θ'.1) 0 := by
    simp [PiLp.inner_apply, PiLp.single_apply, Fin.sum_univ_one, RCLike.inner_apply,
      conj_trivial, mul_comm]
  rw [eh, ef, inner_add_left, inner_sub_left, inner_neg_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq, inner_neg_left,
    inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hs]
  ring

/-- **The jump and driver channels of the exposure-sensitive system in expectation.** For
`ε ≥ 0` and two square-integrable tuples `Θ, Θ'` with laws `μ, μ'`,
`𝔼[⟨δh, δU⟩_{L²(ν)} + ⟨−δf, δX⟩] ≤ −β₁ 𝔼 ‖δU‖²_{L²(ν)} − β₂ 𝔼 |δX|²`. -/
theorem integral_jump_driver_dealerExp_le (hε : 0 ≤ ε) (t : ℝ) {Θ Θ' : Ω → TupleH ν 1 1 d}
    (hΘ : MemLp Θ 2 P) (hΘ' : MemLp Θ' 2 P) :
    ∫ ω, (⟪(dealerExpCoeffs β₁ β₂ σc hc hx ε).h t (Θ ω) (lawP2 P Θ)
          - (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t (Θ' ω) (lawP2 P Θ'),
          (Θ ω).2.2.2 - (Θ' ω).2.2.2⟫
        + ⟪-((dealerExpCoeffs β₁ β₂ σc hc hx ε).f t (Θ ω) (lawP2 P Θ)
          - (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t (Θ' ω) (lawP2 P Θ')), (Θ ω).1 - (Θ' ω).1⟫) ∂P
      ≤ -β₁ * ∫ ω, ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2 ∂P
        - β₂ * ∫ ω, ‖(Θ ω).1 - (Θ' ω).1‖ ^ 2 ∂P := by
  have hsqU : Integrable (fun ω => ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2) P :=
    (hΘ.snd.snd.snd.sub hΘ'.snd.snd.snd).integrable_norm_pow two_ne_zero
  have hsqX : Integrable (fun ω => ‖(Θ ω).1 - (Θ' ω).1‖ ^ 2) P :=
    (hΘ.fst.sub hΘ'.fst).integrable_norm_pow two_ne_zero
  have hA := integrable_inner_crowdOp_margU_sub hΘ hΘ'
  have hA0 := integral_inner_crowdOp_margU_sub_nonneg hΘ hΘ'
  simp_rw [inner_jump_driver_dealerExp]
  have e : ∫ ω, (-β₁ * ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2
        - ε * ⟪crowdOp (lawP2 P Θ).margU.law (Θ ω).2.2.2
          - crowdOp (lawP2 P Θ').margU.law (Θ' ω).2.2.2, (Θ ω).2.2.2 - (Θ' ω).2.2.2⟫
        - β₂ * ‖(Θ ω).1 - (Θ' ω).1‖ ^ 2) ∂P
      = -β₁ * ∫ ω, ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2 ∂P
        - ε * ∫ ω, ⟪crowdOp (lawP2 P Θ).margU.law (Θ ω).2.2.2
          - crowdOp (lawP2 P Θ').margU.law (Θ' ω).2.2.2, (Θ ω).2.2.2 - (Θ' ω).2.2.2⟫ ∂P
        - β₂ * ∫ ω, ‖(Θ ω).1 - (Θ' ω).1‖ ^ 2 ∂P := by
    have h12 : Integrable (fun ω => -β₁ * ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2
        - ε * ⟪crowdOp (lawP2 P Θ).margU.law (Θ ω).2.2.2
          - crowdOp (lawP2 P Θ').margU.law (Θ' ω).2.2.2, (Θ ω).2.2.2 - (Θ' ω).2.2.2⟫) P :=
      (hsqU.const_mul _).sub (hA.const_mul _)
    rw [integral_sub h12 (hsqX.const_mul _), integral_sub (hsqU.const_mul _) (hA.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [e]
  nlinarith [mul_nonneg hε hA0]

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **Assumption 2.5, terminal, for the exposure-sensitive system**, with `G = I` and `α = 1`. -/
theorem terminalMonotone_dealerExp :
    TerminalMonotone ℱ P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1
      (dealerExpCoeffs β₁ β₂ σc hc hx ε).g :=
  terminalMonotone_dealer (β₁ := β₁) (β₂ := β₂) (σc := σc) (hc := hc) (ε := ε)

/-- **Example 5.5, the assumptions, at every interaction strength and exposure.** Let
`β₁, β₂ > 0` and `ε ≥ 0`. Over any filtration, the exposure-sensitive dealer system satisfies
(2.3) with the Hilbert-norm `W₂`; Assumption 2.2; Assumption 2.3 along the diagonal and at the
terminal time with `L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`; and Assumption 2.5 with `G = I`,
`α = 1` and the admissible constants `β₁, β₂`. -/
theorem dealerExp_assumptions (T : ℝ) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) (hε : 0 ≤ ε) :
    CoeffBorelW2 T (dealerExpCoeffs β₁ β₂ σc hc hx ε)
      ∧ CoeffOrigin T (dealerExpCoeffs β₁ β₂ σc hc hx ε)
      ∧ DiagonalLipschitzH ℱ P T (max (max (β₁ + ε + ‖hx‖) (β₂ + ‖hx‖)) 1)
          (dealerExpCoeffs β₁ β₂ σc hc hx ε)
      ∧ TerminalLipschitz ℱ P T (max (max (β₁ + ε + ‖hx‖) (β₂ + ‖hx‖)) 1)
          (dealerExpCoeffs β₁ β₂ σc hc hx ε).g
      ∧ Constants 1 1 1 β₁ β₂
      ∧ DiagonalMonotone ℱ P T 1 β₁ β₂ (dealerExpCoeffs β₁ β₂ σc hc hx ε)
      ∧ TerminalMonotone ℱ P T 1 1 (dealerExpCoeffs β₁ β₂ σc hc hx ε).g :=
  ⟨coeffBorelW2_dealerExp T, coeffOrigin_dealerExp T,
    diagonalLipschitzH_dealerExp hβ₁.le hβ₂.le hε, terminalLipschitz_dealerExp,
    constants_dealer hβ₁ hβ₂, diagonalMonotone_dealerExp hε, terminalMonotone_dealerExp⟩

end Dissertation.WellPosedness.Existence
