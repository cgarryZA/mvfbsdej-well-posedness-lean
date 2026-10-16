/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Dissertation.Law.Mixture
import Dissertation.WellPosedness.Examples.Dealer.Coeffs

/-!
# Example 5.5: the coefficients of the exposure-sensitive dealer market

On the tuple space `H = ℝⁿ × ℝⁿ × ℝ^{n×d} × L²(ν; ℝⁿ)`, fix `β₁, β₂ ≥ 0`, `σ_c ∈ ℝ^{n×d}`,
`h_c ∈ L²(ν; ℝⁿ)`, an interaction strength `ε ≥ 0` and a real exposure profile `h_x ∈ L²(ν)`.
The exposure operator `x ↦ h_x x`, `(h_x x)(e) = h_x(e) x`, is continuous and linear from `ℝⁿ` to
`L²(ν; ℝⁿ)` with norm at most `‖h_x‖`, and its adjoint is the pairing

`⟨h_x, u⟩_{L²(ν)} = ∫_E h_x(e) u(e) ν(de) ∈ ℝⁿ`.

With `A_λ(u) = ∫ ∇V(u − v) λ(dv)` the crowding operator and `μ^U` the `U`-marginal of the measure
argument, the exposure-sensitive dealer system of Example 5.5 of the well-posedness paper is

`b = −β₁ y`, `σ = σ_c − β₁ z`, `h = h_c + h_x x − β₁ u − ε A_{μ^U}(u)`,
`f = β₂ x + ⟨h_x, u⟩_{L²(ν)}`, `g(x, ρ) = x`,

the dealer system of `dealerCoeffs` perturbed by the exposure terms `p_h = h_x x`,
`p_f = ⟨h_x, u⟩_{L²(ν)}`. At `h_x = 0` it is the dealer system, and at `ε = 0`, `h_x = 0` it is
Example 5.1(i).

The exposure terms are adjoint to each other, so they cancel in the interior pairing:

`⟨h_x δx, δu⟩_{L²(ν)} − ⟨⟨h_x, δu⟩_{L²(ν)}, δx⟩ = 0`.

They vanish at the origin, so Assumption 2.2 is that of the dealer system. At every time, pair of
points and pair of laws,

`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf|
  ≤ (β₂ + ‖h_x‖) |δx| + β₁ |δy| + β₁ |δz|_F + (β₁ + ε + ‖h_x‖) ‖δu‖ + ε W₂(μ, μ')`,

which is Assumption 2.3 with `L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`, both for the Hilbert-norm
`W₂` on `P₂(H)` and for that of the maximum of the channel norms. The coefficients are continuous
on `H × P₂(H)`, which gives (2.3).

The crowding correction is nonlinear in the valuation curve `u`, but affine in the law:
`A_{s λ₁ + (1 − s) λ₂} = s A_{λ₁} + (1 − s) A_{λ₂}` for `s ∈ [0, 1]`.

## Main definitions

* `exposureOp` — the exposure operator `x ↦ h_x x`.
* `exposurePair` — the pairing `u ↦ ⟨h_x, u⟩_{L²(ν)}`, the adjoint of `exposureOp`.
* `exposurePert` — the exposure terms `p_h = h_x x`, `p_f = ⟨h_x, u⟩_{L²(ν)}`, as a perturbation.
* `dealerExpCoeffs` — the exposure-sensitive dealer system of Example 5.5.

## Main statements

* `Dissertation.Law.crowdOp_smul_add_smul` — the crowding operator is affine in the law.
* `coeFn_exposureOp`, `inner_exposureOp`, `exposurePair_eq_integral` — the exposure operator and
  the pairing as integrals over the marks.
* `inner_exposureOp_sub_inner_exposurePair` — the cancellation of the exposure terms.
* `dealerExpCoeffs_zero`, `dealerExpCoeffs_zero_zero` — at `h_x = 0` the dealer system, and at
  `ε = 0`, `h_x = 0` Example 5.1(i).
* `dealerExpCoeffs_h`, `dealerExpCoeffs_f` — the jump coefficient and the driver.
* `coeffOrigin_dealerExp` — Assumption 2.2.
* `norm_dealerExp_sub_le` — the pointwise Lipschitz bound for any law distance dominating
  `W₂(μ^U, μ'^U)`.
* `lipschitzCoefficientsP2_dealerExp`, `diagonalLipschitz_dealerExp`,
  `diagonalLipschitzH_dealerExp`, `terminalLipschitz_dealerExp` — Assumption 2.3 with
  `L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`.
* `coeffBorelW2_dealerExp`, `coeffBorel_dealerExp`, `coeffRegular_dealerExp` — (2.3), and (2.5)
  along every progressive tuple.
-/

open MeasureTheory Filter Dissertation.Law
open scoped RealInnerProductSpace

namespace Dissertation.Law

/-! ### The crowding operator is affine in the law -/

section Affine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- **The crowding operator is affine in the law**: for finite measures `Λ₁, Λ₂` on `F` and
`s ∈ [0, 1]`, `A_{s Λ₁ + (1 − s) Λ₂}(u) = s A_{Λ₁}(u) + (1 − s) A_{Λ₂}(u)`. -/
theorem crowdOp_smul_add_smul (Λ₁ Λ₂ : Measure F) [IsFiniteMeasure Λ₁] [IsFiniteMeasure Λ₂]
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (u : F) :
    crowdOp (ENNReal.ofReal s • Λ₁ + ENNReal.ofReal (1 - s) • Λ₂) u
      = s • crowdOp Λ₁ u + (1 - s) • crowdOp Λ₂ u := by
  rw [crowdOp, integral_add_measure
    ((integrable_crowdGrad_sub Λ₁ u).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_crowdGrad_sub Λ₂ u).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hs.1,
    ENNReal.toReal_ofReal (by linarith [hs.2])]
  rfl

end Affine

end Dissertation.Law

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n d : ℕ}

/-! ### The exposure operator and its adjoint -/

section Exposure

/-- The exposure operator of a real profile `h_x ∈ L²(ν)`: the continuous linear map
`x ↦ h_x x` from `ℝⁿ` to `L²(ν; ℝⁿ)`, `(h_x x)(e) = h_x(e) x`. -/
noncomputable def exposureOp (hx : Lp ℝ 2 ν) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] Lp (EuclideanSpace ℝ (Fin n)) 2 ν :=
  (ContinuousLinearMap.compLpL₂ 2 ν
    (ContinuousLinearMap.lsmul ℝ ℝ :
      ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).flip).flip hx

/-- The exposure pairing of a real profile `h_x ∈ L²(ν)`: the continuous linear map
`u ↦ ⟨h_x, u⟩_{L²(ν)} = ∫_E h_x(e) u(e) ν(de)` from `L²(ν; ℝⁿ)` to `ℝⁿ`, the adjoint of the
exposure operator. -/
noncomputable def exposurePair (hx : Lp ℝ 2 ν) :
    Lp (EuclideanSpace ℝ (Fin n)) 2 ν →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.adjoint (exposureOp hx)

variable (hx : Lp ℝ 2 ν)

/-- The exposure operator at `x` is the composition of `h_x` with `t ↦ t x`. -/
theorem exposureOp_apply (x : EuclideanSpace ℝ (Fin n)) :
    exposureOp hx x = (ContinuousLinearMap.toSpanSingleton ℝ x).compLp hx := by
  simp [exposureOp]

/-- **The exposure operator is multiplication by the profile**: `(h_x x)(e) = h_x(e) x` for
`ν`-almost every mark `e`. -/
theorem coeFn_exposureOp (x : EuclideanSpace ℝ (Fin n)) :
    exposureOp hx x =ᵐ[ν] fun e => hx e • x := by
  rw [exposureOp_apply]
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ x).coeFn_compLp hx] with e he
  rw [he, ContinuousLinearMap.toSpanSingleton_apply]

/-- The exposure operator of the zero profile vanishes. -/
@[simp]
theorem exposureOp_zero : exposureOp (n := n) (0 : Lp ℝ 2 ν) = 0 := by
  simp [exposureOp]

/-- The exposure pairing of the zero profile vanishes. -/
@[simp]
theorem exposurePair_zero : exposurePair (n := n) (0 : Lp ℝ 2 ν) = 0 := by
  rw [exposurePair, exposureOp_zero, map_zero]

/-- The exposure operator is bounded by the profile: `‖h_x x‖_{L²(ν)} ≤ ‖h_x‖ |x|`. -/
theorem norm_exposureOp_apply_le (x : EuclideanSpace ℝ (Fin n)) :
    ‖exposureOp hx x‖ ≤ ‖hx‖ * ‖x‖ := by
  rw [exposureOp_apply, mul_comm]
  refine ((ContinuousLinearMap.toSpanSingleton ℝ x).norm_compLp_le hx).trans ?_
  rw [ContinuousLinearMap.norm_toSpanSingleton]

/-- The operator norm of the exposure operator is at most `‖h_x‖`. -/
theorem norm_exposureOp_le : ‖exposureOp (n := n) hx‖ ≤ ‖hx‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (norm_exposureOp_apply_le hx)

/-- The exposure pairing is bounded by the profile: `|⟨h_x, u⟩_{L²(ν)}| ≤ ‖h_x‖ ‖u‖_{L²(ν)}`. -/
theorem norm_exposurePair_apply_le (u : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    ‖exposurePair hx u‖ ≤ ‖hx‖ * ‖u‖ := by
  refine ((exposurePair hx).le_opNorm u).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg u))
  rw [exposurePair, LinearIsometryEquiv.norm_map]
  exact norm_exposureOp_le hx

/-- The exposure pairing is adjoint to the exposure operator:
`⟨⟨h_x, u⟩_{L²(ν)}, x⟩ = ⟨u, h_x x⟩_{L²(ν)}`. -/
theorem inner_exposurePair (u : Lp (EuclideanSpace ℝ (Fin n)) 2 ν)
    (x : EuclideanSpace ℝ (Fin n)) : ⟪exposurePair hx u, x⟫ = ⟪u, exposureOp hx x⟫ :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

/-- **The exposure terms cancel**: `⟨h_x x, u⟩_{L²(ν)} − ⟨⟨h_x, u⟩_{L²(ν)}, x⟩ = 0`. -/
theorem inner_exposureOp_sub_inner_exposurePair (x : EuclideanSpace ℝ (Fin n))
    (u : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    ⟪exposureOp hx x, u⟫ - ⟪exposurePair hx u, x⟫ = 0 := by
  rw [inner_exposurePair, real_inner_comm, sub_self]

/-- The pairing of `h_x x` with `u` as an integral over the marks:
`⟨h_x x, u⟩_{L²(ν)} = ∫_E h_x(e) ⟨x, u(e)⟩ ν(de)`. -/
theorem inner_exposureOp (x : EuclideanSpace ℝ (Fin n)) (u : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    ⟪exposureOp hx x, u⟫ = ∫ e, hx e * ⟪x, u e⟫ ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_exposureOp hx x] with e he
  rw [he, real_inner_smul_left]

/-- The product `e ↦ h_x(e) u(e)` of two square-integrable functions is integrable. -/
theorem integrable_smul_exposure (u : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    Integrable (fun e => hx e • u e) ν :=
  memLp_one_iff_integrable.1 ((Lp.memLp u).smul (Lp.memLp hx))

/-- **The exposure pairing is the integral over the marks**:
`⟨h_x, u⟩_{L²(ν)} = ∫_E h_x(e) u(e) ν(de)`. -/
theorem exposurePair_eq_integral (u : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    exposurePair hx u = ∫ e, hx e • u e ∂ν := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_exposurePair, real_inner_comm, inner_exposureOp, real_inner_comm,
    ← integral_inner (integrable_smul_exposure hx u)]
  refine integral_congr_ae (Eventually.of_forall fun e => ?_)
  simp only [real_inner_smul_right]

end Exposure

/-! ### The coefficients -/

section Coefficients

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- The exposure terms of Example 5.5 as a perturbation: `p_h(t, θ, μ) = h_x x` and
`p_f(t, θ, μ) = ⟨h_x, u⟩_{L²(ν)}` for `θ = (x, y, z, u)`, and `p_b = p_σ = 0`; its terminal
function `0` is not used. -/
noncomputable def exposurePert (hx : Lp ℝ 2 ν) : Coeffs ν n n d where
  b _ _ _ := 0
  σ _ _ _ := 0
  h _ θ _ := exposureOp hx θ.1
  f _ θ _ := exposurePair hx θ.2.2.2
  g _ _ := 0

/-- The exposure-sensitive dealer system of Example 5.5: for `θ = (x, y, z, u)`, `b = −β₁ y`,
`σ = σ_c − β₁ z`, `h = h_c + h_x x − β₁ u − ε A_{μ^U}(u)`, `f = β₂ x + ⟨h_x, u⟩_{L²(ν)}` and
`g(x, ρ) = x`, the dealer system perturbed by the exposure terms `exposurePert h_x`. -/
noncomputable abbrev dealerExpCoeffs (β₁ β₂ : ℝ) (σc : EuclideanSpace ℝ (Fin n × Fin d))
    (hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) (hx : Lp ℝ 2 ν) (ε : ℝ) : Coeffs ν n n d :=
  (dealerCoeffs β₁ β₂ σc hc ε).perturb (exposurePert hx)

variable {β₁ β₂ ε : ℝ} {σc : EuclideanSpace ℝ (Fin n × Fin d)}
  {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν} {hx : Lp ℝ 2 ν}

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **At `h_x = 0` the exposure-sensitive dealer system is the dealer system.** -/
theorem dealerExpCoeffs_zero (β₁ β₂ : ℝ) (σc : EuclideanSpace ℝ (Fin n × Fin d))
    (hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) (ε : ℝ) :
    dealerExpCoeffs β₁ β₂ σc hc 0 ε = dealerCoeffs β₁ β₂ σc hc ε := by
  simp only [dealerExpCoeffs, Coeffs.perturb, exposurePert, exposureOp_zero, exposurePair_zero,
    _root_.zero_apply, add_zero]

/-- **At `ε = 0` and `h_x = 0` the exposure-sensitive dealer system is Example 5.1(i).** -/
theorem dealerExpCoeffs_zero_zero (β₁ β₂ : ℝ) (σc : EuclideanSpace ℝ (Fin n × Fin d))
    (hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    dealerExpCoeffs β₁ β₂ σc hc 0 0 = affineCoeffs β₁ β₂ σc hc := by
  rw [dealerExpCoeffs_zero, dealerCoeffs_zero]

/-- The jump coefficient of the exposure-sensitive dealer system,
`h(t, θ, μ) = h_c + h_x x − β₁ u − ε A_{μ^U}(u)`. -/
theorem dealerExpCoeffs_h (t : ℝ) (θ : TupleH ν n n d) (μ : P2 (TupleH ν n n d)) :
    (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t θ μ
      = hc + exposureOp hx θ.1 - β₁ • θ.2.2.2 - ε • crowdOp μ.margU.law θ.2.2.2 := by
  change (dealerCoeffs β₁ β₂ σc hc ε).h t θ μ + exposureOp hx θ.1 = _
  rw [dealerCoeffs_h]
  abel

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The driver of the exposure-sensitive dealer system, `f(t, θ, μ) = β₂ x + ⟨h_x, u⟩_{L²(ν)}`. -/
theorem dealerExpCoeffs_f (t : ℝ) (θ : TupleH ν n n d) (μ : P2 (TupleH ν n n d)) :
    (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t θ μ = β₂ • θ.1 + exposurePair hx θ.2.2.2 := by
  simp only [dealerExpCoeffs, dealerCoeffs, Coeffs.perturb, crowdPert, exposurePert,
    affineCoeffs, add_zero]

/-- **Assumption 2.2 for the exposure terms**: their origin values vanish. -/
theorem coeffOrigin_exposurePert (T : ℝ) (hx : Lp ℝ 2 ν) :
    CoeffOrigin T (exposurePert (n := n) (d := d) hx) := by
  have hh : (fun t => (exposurePert (n := n) (d := d) hx).h t 0 (P2.dirac 0)) = fun _ => 0 :=
    funext fun _ => by simp [exposurePert]
  have hf : (fun t => (exposurePert (n := n) (d := d) hx).f t 0 (P2.dirac 0)) = fun _ => 0 :=
    funext fun _ => by simp [exposurePert]
  unfold CoeffOrigin
  rw [hh, hf]
  exact originIntegrable_const T 0 0 0 0

/-- **Assumption 2.2 for the exposure-sensitive dealer system**: the origin values are
`0, σ_c, h_c, 0`. -/
theorem coeffOrigin_dealerExp (T : ℝ) : CoeffOrigin T (dealerExpCoeffs β₁ β₂ σc hc hx ε) :=
  coeffOrigin_perturb (coeffOrigin_dealer T) (coeffOrigin_exposurePert T hx)

/-! ### Assumption 2.3 -/

/-- **The pointwise Lipschitz bound of the exposure-sensitive dealer system.** For
`β₁, β₂, ε ≥ 0` and any `W` dominating `W₂(μ^U, μ'^U)`,
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf|
  ≤ max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1} (|δx| + |δy| + |δz|_F + ‖δu‖ + W)`. -/
theorem norm_dealerExp_sub_le (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hε : 0 ≤ ε) (t : ℝ)
    (θ θ' : TupleH ν n n d) (μ μ' : P2 (TupleH ν n n d)) {W : ℝ}
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
    simp only [dealerExpCoeffs, dealerCoeffs, Coeffs.perturb, crowdPert, exposurePert,
      affineCoeffs, add_zero, smul_sub]
    abel
  have eσ : (dealerExpCoeffs β₁ β₂ σc hc hx ε).σ t θ μ
      - (dealerExpCoeffs β₁ β₂ σc hc hx ε).σ t θ' μ' = -(β₁ • (θ.2.2.1 - θ'.2.2.1)) := by
    simp only [dealerExpCoeffs, dealerCoeffs, Coeffs.perturb, crowdPert, exposurePert,
      affineCoeffs, add_zero, smul_sub]
    abel
  have eh : (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t θ μ
      - (dealerExpCoeffs β₁ β₂ σc hc hx ε).h t θ' μ'
      = exposureOp hx (θ.1 - θ'.1) - β₁ • (θ.2.2.2 - θ'.2.2.2) - ε • (A - A') := by
    rw [dealerExpCoeffs_h, dealerExpCoeffs_h, map_sub, smul_sub, smul_sub]
    abel
  have ef : (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t θ μ
      - (dealerExpCoeffs β₁ β₂ σc hc hx ε).f t θ' μ'
      = β₂ • (θ.1 - θ'.1) + exposurePair hx (θ.2.2.2 - θ'.2.2.2) := by
    rw [dealerExpCoeffs_f, dealerExpCoeffs_f, map_sub, smul_sub]
    abel
  have hh : ‖exposureOp hx (θ.1 - θ'.1) - β₁ • (θ.2.2.2 - θ'.2.2.2) - ε • (A - A')‖
      ≤ ‖hx‖ * ‖θ.1 - θ'.1‖ + β₁ * ‖θ.2.2.2 - θ'.2.2.2‖
        + ε * (‖θ.2.2.2 - θ'.2.2.2‖ + W) := by
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · exact norm_exposureOp_apply_le hx _
    · rw [norm_smul, Real.norm_of_nonneg hβ₁]
    · rw [norm_smul, Real.norm_of_nonneg hε]
      exact mul_le_mul_of_nonneg_left hA hε
  have hf : ‖β₂ • (θ.1 - θ'.1) + exposurePair hx (θ.2.2.2 - θ'.2.2.2)‖
      ≤ β₂ * ‖θ.1 - θ'.1‖ + ‖hx‖ * ‖θ.2.2.2 - θ'.2.2.2‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_exposurePair_apply_le hx _))
    rw [norm_smul, Real.norm_of_nonneg hβ₂]
  rw [eb, eσ, eh, ef, norm_neg, norm_neg, norm_smul, norm_smul, Real.norm_of_nonneg hβ₁]
  have htn : tupleNorm (θ - θ')
      = ‖θ.1 - θ'.1‖ + ‖θ.2.1 - θ'.2.1‖ + ‖θ.2.2.1 - θ'.2.2.1‖ + ‖θ.2.2.2 - θ'.2.2.2‖ := rfl
  rw [htn]
  have hW0 : 0 ≤ W := (w2P_nonneg _ _).trans hW
  have hK := norm_nonneg hx
  have hL₁ : β₁ + ε + ‖hx‖ ≤ L := (le_max_left _ _).trans (le_max_left _ _)
  have hL₂ : β₂ + ‖hx‖ ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  have hLβ : β₁ ≤ L := by linarith
  have hLε : ε ≤ L := by linarith
  have h1 := norm_nonneg (θ.1 - θ'.1)
  have h2 := norm_nonneg (θ.2.1 - θ'.2.1)
  have h3 := norm_nonneg (θ.2.2.1 - θ'.2.2.1)
  have h4 := norm_nonneg (θ.2.2.2 - θ'.2.2.2)
  nlinarith [mul_le_mul_of_nonneg_right hL₂ h1, mul_le_mul_of_nonneg_right hLβ h2,
    mul_le_mul_of_nonneg_right hLβ h3, mul_le_mul_of_nonneg_right hL₁ h4,
    mul_le_mul_of_nonneg_right hLε hW0]

/-- **Assumption 2.3, interior, pointwise, for the exposure-sensitive dealer system**, with the
maximum-norm `W₂` on `P₂(H)` and the constant `L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`, for
`β₁, β₂, ε ≥ 0`. -/
theorem lipschitzCoefficientsP2_dealerExp (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hε : 0 ≤ ε) :
    LipschitzCoefficientsP2 (max (max (β₁ + ε + ‖hx‖) (β₂ + ‖hx‖)) 1)
      (dealerExpCoeffs β₁ β₂ σc hc hx ε).b (dealerExpCoeffs β₁ β₂ σc hc hx ε).σ
      (dealerExpCoeffs β₁ β₂ σc hc hx ε).h (dealerExpCoeffs β₁ β₂ σc hc hx ε).f :=
  fun t θ θ' μ μ' => norm_dealerExp_sub_le hβ₁ hβ₂ hε t θ θ' μ μ' (w2P_margU_le μ μ')

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **Assumption 2.3, interior, along the diagonal, for the exposure-sensitive dealer system**,
with the maximum-norm `W₂` and the constant `L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`. -/
theorem diagonalLipschitz_dealerExp (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hε : 0 ≤ ε) :
    DiagonalLipschitz ℱ P T (max (max (β₁ + ε + ‖hx‖) (β₂ + ‖hx‖)) 1)
      (dealerExpCoeffs β₁ β₂ σc hc hx ε) :=
  diagonalLipschitz_of_lipschitzCoefficientsP2 (lipschitzCoefficientsP2_dealerExp hβ₁ hβ₂ hε)

/-- **Assumption 2.3, interior, along the diagonal, for the exposure-sensitive dealer system**,
with the Hilbert-norm `W₂` on `P₂(H)` and the constant
`L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`. -/
theorem diagonalLipschitzH_dealerExp (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hε : 0 ≤ ε) :
    DiagonalLipschitzH ℱ P T (max (max (β₁ + ε + ‖hx‖) (β₂ + ‖hx‖)) 1)
      (dealerExpCoeffs β₁ β₂ σc hc hx ε) :=
  Eventually.of_forall fun t Θ Θ' _ _ _ _ => Eventually.of_forall fun ω =>
    norm_dealerExp_sub_le hβ₁ hβ₂ hε t (Θ ω) (Θ' ω) _ _ (w2P_margU_le_w2H _ _)

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **Assumption 2.3, terminal, along the diagonal, for the exposure-sensitive dealer system**,
with the constant `L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`: the terminal function is
`g(x, ρ) = x`. -/
theorem terminalLipschitz_dealerExp :
    TerminalLipschitz ℱ P T (max (max (β₁ + ε + ‖hx‖) (β₂ + ‖hx‖)) 1)
      (dealerExpCoeffs β₁ β₂ σc hc hx ε).g :=
  (terminalLipschitz_affine (β₁ := β₁) (β₂ := β₂) (σc := σc) (hc := hc)
    (le_max_right _ 1)).perturb.perturb

end Coefficients

/-! ### (2.3) -/

section Measurability

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {β₁ β₂ ε : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}
  {hx : Lp ℝ 2 ν}

/-- **(2.3) for the exposure terms, with the Hilbert-norm `W₂` on `P₂(H)`**: `h_x x` and
`⟨h_x, u⟩_{L²(ν)}` are continuous in the tuple, and the other coefficients vanish. -/
theorem coeffBorelW2_exposurePert (T : ℝ) (hx : Lp ℝ 2 ν) :
    CoeffBorelW2 T (exposurePert (n := n) (d := d) hx) where
  b_meas := Continuous.borel_measurable continuous_const
  σ_meas := Continuous.borel_measurable continuous_const
  h_meas := Continuous.borel_measurable (by
    exact (exposureOp hx).continuous.comp (continuous_fst.comp (continuous_fst.comp
      continuous_snd)))
  f_meas := Continuous.borel_measurable (by
    exact (exposurePair hx).continuous.comp (continuous_snd.comp (continuous_snd.comp
      (continuous_snd.comp (continuous_fst.comp continuous_snd)))))

/-- **(2.3) for the exposure-sensitive dealer system, with the Hilbert-norm `W₂` on `P₂(H)`**:
its coefficients are Borel measurable on `[0, T] × H × P₂(H)`. -/
theorem coeffBorelW2_dealerExp (T : ℝ) : CoeffBorelW2 T (dealerExpCoeffs β₁ β₂ σc hc hx ε) :=
  (coeffBorelW2_dealer T).perturb (coeffBorelW2_exposurePert T hx)

/-- (2.3) for the exposure-sensitive dealer system, with the evaluation σ-algebra on `P₂(H)`. -/
theorem coeffBorel_dealerExp (T : ℝ) : CoeffBorel T (dealerExpCoeffs β₁ β₂ σc hc hx ε) :=
  (coeffBorelW2_dealerExp T).toCoeffBorel

/-- **(2.5) for the exposure-sensitive dealer system**: along every progressive tuple its
coefficient processes are jointly and progressively measurable, the jump coefficient through a
jointly measurable, marked progressively measurable representative. -/
theorem coeffRegular_dealerExp {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) :
    CoeffRegular ℱ P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) :=
  (coeffBorel_dealerExp T).coeffRegular ℱ P

end Measurability

end Dissertation.WellPosedness.Existence
