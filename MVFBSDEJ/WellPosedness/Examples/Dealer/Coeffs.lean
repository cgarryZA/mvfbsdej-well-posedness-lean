/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Law.CrowdGrad
import MVFBSDEJ.Law.TupleMarginal
import MVFBSDEJ.WellPosedness.Examples.FullLawBeyond
import MVFBSDEJ.WellPosedness.Robustness.Regular
import MVFBSDEJ.WellPosedness.Existence.AffineExample

/-!
# Example 5.5: the coefficients of the mean-field dealer market

On the tuple space `H = ℝⁿ × ℝⁿ × ℝ^{n×d} × L²(ν; ℝⁿ)`, fix `β₁, β₂ ≥ 0`, `σ_c ∈ ℝ^{n×d}`,
`h_c ∈ L²(ν; ℝⁿ)` and an interaction strength `ε ≥ 0`. With `A_λ(u) = ∫ ∇V(u − v) λ(dv)` the
crowding operator of `MVFBSDEJ.Law.crowdOp` and `μ^U` the `U`-marginal of the measure
argument, the dealer system of Example 5.5 of the paper is

`b = −β₁ y`, `σ = σ_c − β₁ z`, `h = h_c − β₁ u − ε A_{μ^U}(u)`, `f = β₂ x`, `g(x, ρ) = x`,

the affine system of Example 5.1(i) perturbed in its jump coefficient by the crowding correction
`p_h(t, θ, μ) = −ε A_{μ^U}(u)`. At `ε = 0` it is Example 5.1(i).

Since `∇V(0) = 0`, the origin value `h(·, 0, δ₀) = h_c` is that of Example 5.1(i), so Assumption
2.2 holds. The crowding operator is jointly Lipschitz,
`‖A_{μ^U}(u) − A_{μ'^U}(u')‖ ≤ ‖u − u'‖ + W₂(μ^U, μ'^U)`, and marginal projection is
`1`-Lipschitz for `W₂`, (2.11), so the crowding correction is Lipschitz, hence continuous, on
`H × P₂(H)` with the Hilbert-norm `W₂`. This gives (2.3) with the Hilbert-norm `W₂` and with the
evaluation σ-algebra on `P₂(H)`.

## Main definitions

* `crowdPert` — the crowding correction `p_h = −ε A_{μ^U}(u)`, as a perturbation.
* `dealerCoeffs` — the dealer system of Example 5.5.

## Main statements

* `dealerCoeffs_zero` — at `ε = 0` the dealer system is Example 5.1(i).
* `dealerCoeffs_h`, `dealerCoeffs_h_origin` — the jump coefficient, and its origin value `h_c`.
* `continuous_crowdOp_margU` — `(θ, μ) ↦ A_{μ^U}(u)` is continuous on `H × P₂(H)`.
* `coeffOrigin_dealer` — Assumption 2.2.
* `norm_crowdOp_margU_sub_le` — `(θ, μ) ↦ A_{μ^U}(u)` is Lipschitz in the tuple and the law.
* `coeffBorelW2_dealer`, `coeffBorel_dealer` — (2.3).
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped RealInnerProductSpace

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n d : ℕ}

/-! ### The coefficients -/

section Coefficients

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- The crowding correction of Example 5.5 as a perturbation of the jump coefficient:
`p_h(t, θ, μ) = −ε A_{μ^U}(u)` for `θ = (x, y, z, u)`, with `μ^U` the `U`-marginal of `μ`, and
`p_b = p_σ = p_f = 0`; its terminal function `0` is not used. -/
noncomputable def crowdPert (ε : ℝ) : Coeffs ν n n d where
  b _ _ _ := 0
  σ _ _ _ := 0
  h _ θ μ := -(ε • crowdOp μ.margU.law θ.2.2.2)
  f _ _ _ := 0
  g _ _ := 0

/-- The dealer system of Example 5.5: for `θ = (x, y, z, u)`, `b = −β₁ y`, `σ = σ_c − β₁ z`,
`h = h_c − β₁ u − ε A_{μ^U}(u)`, `f = β₂ x` and `g(x, ρ) = x`, the affine system of Example 5.1(i)
perturbed by the crowding correction `crowdPert ε`. -/
noncomputable abbrev dealerCoeffs (β₁ β₂ : ℝ) (σc : EuclideanSpace ℝ (Fin n × Fin d))
    (hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) (ε : ℝ) : Coeffs ν n n d :=
  (affineCoeffs β₁ β₂ σc hc).perturb (crowdPert ε)

variable {β₁ β₂ ε : ℝ} {σc : EuclideanSpace ℝ (Fin n × Fin d)}
  {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}

/-- **At `ε = 0` the dealer system is Example 5.1(i).** -/
theorem dealerCoeffs_zero (β₁ β₂ : ℝ) (σc : EuclideanSpace ℝ (Fin n × Fin d))
    (hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    dealerCoeffs β₁ β₂ σc hc 0 = affineCoeffs β₁ β₂ σc hc := by
  simp only [dealerCoeffs, Coeffs.perturb, crowdPert, zero_smul, neg_zero, add_zero]

/-- The jump coefficient of the dealer system, `h(t, θ, μ) = h_c − β₁ u − ε A_{μ^U}(u)`. -/
theorem dealerCoeffs_h (t : ℝ) (θ : TupleH ν n n d) (μ : P2 (TupleH ν n n d)) :
    (dealerCoeffs β₁ β₂ σc hc ε).h t θ μ = hc - β₁ • θ.2.2.2 - ε • crowdOp μ.margU.law θ.2.2.2 := by
  simp only [dealerCoeffs, Coeffs.perturb, crowdPert, affineCoeffs, sub_eq_add_neg]

/-- The crowding correction vanishes at the origin and the Dirac mass there. -/
theorem crowdPert_h_origin (t : ℝ) :
    (crowdPert (ν := ν) (n := n) (d := d) ε).h t 0 (P2.dirac 0) = 0 := by
  simp only [crowdPert]
  rw [margU_dirac]
  simp [P2.dirac, crowdOp_dirac_zero]

/-- **The origin value of the jump coefficient is `h_c`**, that of Example 5.1(i):
`h(t, 0, δ₀) = h_c`, since `∇V(0) = 0`. -/
theorem dealerCoeffs_h_origin (t : ℝ) :
    (dealerCoeffs β₁ β₂ σc hc ε).h t 0 (P2.dirac 0) = hc := by
  change (affineCoeffs β₁ β₂ σc hc).h t 0 (P2.dirac 0) + (crowdPert ε).h t 0 (P2.dirac 0) = hc
  rw [crowdPert_h_origin]
  simp [affineCoeffs]

/-- **Assumption 2.2 for the crowding correction**: its origin values vanish. -/
theorem coeffOrigin_crowdPert (T ε : ℝ) :
    CoeffOrigin T (crowdPert (ν := ν) (n := n) (d := d) ε) := by
  have h : (fun t => (crowdPert (ν := ν) (n := n) (d := d) ε).h t 0 (P2.dirac 0)) = fun _ => 0 :=
    funext crowdPert_h_origin
  unfold CoeffOrigin
  rw [h]
  exact originIntegrable_const T 0 0 0 0

/-- **Assumption 2.2 for the dealer system**: the origin values are `0, σ_c, h_c, 0`. -/
theorem coeffOrigin_dealer (T : ℝ) : CoeffOrigin T (dealerCoeffs β₁ β₂ σc hc ε) :=
  coeffOrigin_perturb (coeffOrigin_affine T) (coeffOrigin_crowdPert T ε)

/-! ### Assumption 2.3 -/

/-- **The crowding correction is Lipschitz in the tuple and the law**:
`‖A_{μ^U}(u) − A_{μ'^U}(u')‖ ≤ ‖u − u'‖ + W₂(μ^U, μ'^U)`. -/
theorem norm_crowdOp_margU_sub_le (θ θ' : TupleH ν n n d) (μ μ' : P2 (TupleH ν n n d)) :
    ‖crowdOp μ.margU.law θ.2.2.2 - crowdOp μ'.margU.law θ'.2.2.2‖
      ≤ ‖θ.2.2.2 - θ'.2.2.2‖ + w2P μ.margU μ'.margU :=
  norm_crowdOp_sub_le μ.margU μ'.margU θ.2.2.2 θ'.2.2.2

end Coefficients

/-! ### (2.3) -/

section Measurability

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {β₁ β₂ ε : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}

/-- **The crowding correction is continuous on `H × P₂(H)`**, with the Hilbert-norm `W₂` on
`P₂(H)`: `(θ, μ) ↦ A_{μ^U}(u)` is `2`-Lipschitz for the maximum of the two distances. -/
theorem continuous_crowdOp_margU :
    Continuous fun p : TupleH ν n n d × TupleP2WH ν n n d =>
      crowdOp p.2.toP2.margU.law p.1.2.2.2 := by
  refine (LipschitzWith.of_dist_le_mul (K := 2) fun p q => ?_).continuous
  rw [dist_eq_norm, NNReal.coe_ofNat]
  have h := norm_crowdOp_margU_sub_le p.1 q.1 p.2.toP2 q.2.toP2
  have h1 : ‖p.1.2.2.2 - q.1.2.2.2‖ ≤ dist p q := by
    calc ‖p.1.2.2.2 - q.1.2.2.2‖ = ‖projUH (p.1 - q.1)‖ := by rw [map_sub]; rfl
      _ ≤ ‖p.1 - q.1‖ := norm_projUH_le _
      _ = dist p.1 q.1 := (dist_eq_norm _ _).symm
      _ ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h2 : w2P p.2.toP2.margU q.2.toP2.margU ≤ dist p q := by
    calc w2P p.2.toP2.margU q.2.toP2.margU ≤ w2H p.2.toP2 q.2.toP2 := w2P_margU_le_w2H _ _
      _ = dist p.2 q.2 := (P2WH.dist_toP2WH _ _).symm
      _ ≤ dist p q := by rw [Prod.dist_eq]; exact le_max_right _ _
  linarith

/-- **(2.3) for the crowding correction, with the Hilbert-norm `W₂` on `P₂(H)`**: its jump
coefficient is continuous on `[0, T] × H × P₂(H)`, and its other coefficients vanish. -/
theorem coeffBorelW2_crowdPert (T ε : ℝ) :
    CoeffBorelW2 T (crowdPert (ν := ν) (n := n) (d := d) ε) where
  b_meas := Continuous.borel_measurable continuous_const
  σ_meas := Continuous.borel_measurable continuous_const
  h_meas := Continuous.borel_measurable (by
    exact ((continuous_crowdOp_margU.comp continuous_snd).const_smul ε).neg)
  f_meas := Continuous.borel_measurable continuous_const

/-- **(2.3) for the dealer system, with the Hilbert-norm `W₂` on `P₂(H)`**: its coefficients are
Borel measurable on `[0, T] × H × P₂(H)`. -/
theorem coeffBorelW2_dealer (T : ℝ) : CoeffBorelW2 T (dealerCoeffs β₁ β₂ σc hc ε) :=
  (coeffBorelW2_affine T).perturb (coeffBorelW2_crowdPert T ε)

/-- (2.3) for the dealer system, with the evaluation σ-algebra on `P₂(H)`. -/
theorem coeffBorel_dealer (T : ℝ) : CoeffBorel T (dealerCoeffs β₁ β₂ σc hc ε) :=
  (coeffBorelW2_dealer T).toCoeffBorel

end Measurability

end MVFBSDEJ.WellPosedness.Existence
