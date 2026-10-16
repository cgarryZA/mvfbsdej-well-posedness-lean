/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.DiagonalAt
import Dissertation.WellPosedness.Existence.CoeffBorelW2
import Dissertation.WellPosedness.Existence.OriginBound
import Dissertation.WellPosedness.Robustness.CouplingNorm

/-!
# The linear monotone generator

The linear generator at `θ = (x, y, z, u)` is

`(b, σ, h, f) = (−β₁ Gᵀ y, −β₁ Gᵀ z, −β₁ Gᵀ u, β₂ G x)`,

with `G` acting on each channel as in Assumption 2.5. It is linear, so Lipschitz: with `‖G‖` the
operator norm of `G` on `ℝⁿ`, which bounds `G` and `Gᵀ` on all three channels,

`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ max(β₁ ‖G‖, β₂ ‖G‖) (|δx| + |δy| + |δz|_F + ‖δu‖_{L²(ν)})`;

and it meets the interior inequality (2.7) with equality, pointwise:
`⟨δb, Gᵀ δy⟩ + ⟨δσ, Gᵀ δz⟩_F − ⟨δf, G δx⟩ + ⟨δh, Gᵀ δu⟩_{L²(ν)}
  = −β₁ (|Gᵀ δy|² + |Gᵀ δz|²_F + ‖Gᵀ δu‖²_{L²(ν)}) − β₂ |G δx|²`.
Its origin values vanish. As a complete coefficient system it carries the terminal function
`g(x, ρ) = G x`, which satisfies (2.6) with constant `‖G‖` and the terminal half of
Assumption 2.5 with `α = 1`, with equality.

## Main definitions

* `linearGenerator` — the coefficients `(−β₁ Gᵀ y, −β₁ Gᵀ z, −β₁ Gᵀ u, β₂ G x, G x)`.

## Main statements

* `interiorPairing_linearGenerator` — (2.7) with equality, pointwise.
* `norm_sum_linearGenerator_le` — the Lipschitz bound with constant `max(β₁ ‖G‖, β₂ ‖G‖)`.
* `diagonalLipschitzHAt_linearGenerator`, `diagonalMonotoneAt_linearGenerator` — the interior
  conditions at every time.
* `terminalLipschitz_linearGenerator`, `terminalMonotone_linearGenerator` — the terminal ones.
* `linearGenerator_origin`, `coeffOrigin_linearGenerator`, `coeffBorelW2_linearGenerator` — the
  origin values vanish; Assumption 2.2 and (2.3).
-/

open MeasureTheory Filter Dissertation.Law Dissertation.WellPosedness
  Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence

namespace Dissertation.WellPosedness

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}

/-! ### The linear generator -/

section Generator

/-- **The linear monotone generator** for a coupling matrix
`G ∈ ℝ^{m×n}`: at `θ = (x, y, z, u)`, `b = −β₁ Gᵀ y`, `σ = −β₁ Gᵀ z`, `h = −β₁ Gᵀ u`,
`f = β₂ G x`, independent of time and law, with terminal function `g(x, ρ) = G x`. -/
noncomputable def linearGenerator (G : Matrix (Fin m) (Fin n) ℝ) (β₁ β₂ : ℝ) :
    Coeffs ν n m d where
  b _ θ _ := -(β₁ • ContinuousLinearMap.adjoint (GX G) θ.2.1)
  σ _ θ _ := -(β₁ • ContinuousLinearMap.adjoint (GZ G) θ.2.2.1)
  h _ θ _ := -(β₁ • ContinuousLinearMap.adjoint (GU G ν) θ.2.2.2)
  f _ θ _ := β₂ • GX G θ.1
  g x _ := GX G x

variable {G : Matrix (Fin m) (Fin n) ℝ} {β₁ β₂ : ℝ}

/-- The four channel differences of the linear generator. -/
theorem linearGenerator_sub (t : ℝ) (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)) :
    (linearGenerator G β₁ β₂).b t θ μ - (linearGenerator G β₁ β₂).b t θ' μ'
        = -(β₁ • ContinuousLinearMap.adjoint (GX G) (θ.2.1 - θ'.2.1))
      ∧ (linearGenerator G β₁ β₂).σ t θ μ - (linearGenerator G β₁ β₂).σ t θ' μ'
        = -(β₁ • ContinuousLinearMap.adjoint (GZ G) (θ.2.2.1 - θ'.2.2.1))
      ∧ (linearGenerator G β₁ β₂).h t θ μ - (linearGenerator G β₁ β₂).h t θ' μ'
        = -(β₁ • ContinuousLinearMap.adjoint (GU G ν) (θ.2.2.2 - θ'.2.2.2))
      ∧ (linearGenerator G β₁ β₂).f t θ μ - (linearGenerator G β₁ β₂).f t θ' μ'
        = β₂ • GX G (θ.1 - θ'.1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [linearGenerator, map_sub, smul_sub]; try abel)

/-- **The linear generator meets (2.7) with equality**, pointwise:
`⟨δb, Gᵀ δy⟩ + ⟨δσ, Gᵀ δz⟩_F − ⟨δf, G δx⟩ + ⟨δh, Gᵀ δu⟩_{L²(ν)}
  = −β₁ (|Gᵀ δy|² + |Gᵀ δz|²_F + ‖Gᵀ δu‖²_{L²(ν)}) − β₂ |G δx|²`. -/
theorem interiorPairing_linearGenerator (t : ℝ) (θ θ' : TupleH ν n m d)
    (μ μ' : P2 (TupleH ν n m d)) :
    interiorPairing (GX G) (GZ G) (GU G ν) (diagDiff (linearGenerator G β₁ β₂) t θ θ' μ μ')
      = dissipation (GX G) (GZ G) (GU G ν) β₁ β₂
        (diagDiff (linearGenerator G β₁ β₂) t θ θ' μ μ') := by
  obtain ⟨e₁, e₂, e₃, e₄⟩ := linearGenerator_sub (G := G) (β₁ := β₁) (β₂ := β₂) t θ θ' μ μ'
  simp only [interiorPairing, dissipation, diagDiff, e₁, e₂, e₃, e₄, inner_neg_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

/-- `β ‖A w‖ ≤ K ‖w‖` for an operator `A` of norm at most `c` and `0 ≤ β`, `β c ≤ K`. -/
theorem mul_norm_apply_le {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] (A : F →L[ℝ] F') {β c K : ℝ} (hβ : 0 ≤ β)
    (hA : ‖A‖ ≤ c) (hβK : β * c ≤ K) (w : F) : β * ‖A w‖ ≤ K * ‖w‖ :=
  calc β * ‖A w‖ ≤ β * (c * ‖w‖) :=
        mul_le_mul_of_nonneg_left ((A.le_opNorm w).trans
          (mul_le_mul_of_nonneg_right hA (norm_nonneg w))) hβ
    _ = β * c * ‖w‖ := by ring
    _ ≤ K * ‖w‖ := mul_le_mul_of_nonneg_right hβK (norm_nonneg w)

/-- **The Lipschitz bound of the linear generator**: for `β₁, β₂ ≥ 0`,
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ max(β₁ ‖G‖, β₂ ‖G‖) (|δx| + |δy| + |δz|_F + ‖δu‖_{L²(ν)})`,
with `‖G‖` the operator norm of `G` on `ℝⁿ`. -/
theorem norm_sum_linearGenerator_le (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (t : ℝ)
    (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)) :
    ‖(linearGenerator G β₁ β₂).b t θ μ - (linearGenerator G β₁ β₂).b t θ' μ'‖
        + ‖(linearGenerator G β₁ β₂).σ t θ μ - (linearGenerator G β₁ β₂).σ t θ' μ'‖
        + ‖(linearGenerator G β₁ β₂).h t θ μ - (linearGenerator G β₁ β₂).h t θ' μ'‖
        + ‖(linearGenerator G β₁ β₂).f t θ μ - (linearGenerator G β₁ β₂).f t θ' μ'‖
      ≤ max (β₁ * ‖GX G‖) (β₂ * ‖GX G‖) * tupleNorm (θ - θ') := by
  obtain ⟨e₁, e₂, e₃, e₄⟩ := linearGenerator_sub (G := G) (β₁ := β₁) (β₂ := β₂) t θ θ' μ μ'
  rw [e₁, e₂, e₃, e₄]
  simp only [norm_neg, norm_smul, Real.norm_of_nonneg hβ₁, Real.norm_of_nonneg hβ₂]
  set K := max (β₁ * ‖GX G‖) (β₂ * ‖GX G‖)
  have hK₁ : β₁ * ‖GX G‖ ≤ K := le_max_left _ _
  have hK₂ : β₂ * ‖GX G‖ ≤ K := le_max_right _ _
  have h1 := mul_norm_apply_le _ hβ₁ (norm_adjoint_GX G).le hK₁ (θ.2.1 - θ'.2.1)
  have h2 := mul_norm_apply_le _ hβ₁ (norm_adjoint_GZ_le (d := d) G) hK₁ (θ.2.2.1 - θ'.2.2.1)
  have h3 := mul_norm_apply_le _ hβ₁ (norm_adjoint_GU_le G ν) hK₁ (θ.2.2.2 - θ'.2.2.2)
  have h4 := mul_norm_apply_le (GX G) hβ₂ le_rfl hK₂ (θ.1 - θ'.1)
  have htn : tupleNorm (θ - θ')
      = ‖θ.1 - θ'.1‖ + ‖θ.2.1 - θ'.2.1‖ + ‖θ.2.2.1 - θ'.2.2.1‖ + ‖θ.2.2.2 - θ'.2.2.2‖ := rfl
  rw [htn]
  linarith

/-- The origin values of the linear generator vanish. -/
theorem linearGenerator_origin (t : ℝ) (μ : P2 (TupleH ν n m d)) :
    (linearGenerator G β₁ β₂).b t 0 μ = 0 ∧ (linearGenerator G β₁ β₂).σ t 0 μ = 0
      ∧ (linearGenerator G β₁ β₂).h t 0 μ = 0 ∧ (linearGenerator G β₁ β₂).f t 0 μ = 0 := by
  simp only [linearGenerator, Prod.fst_zero, Prod.snd_zero, map_zero, smul_zero, neg_zero,
    and_self]

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **Assumption 2.2 for the linear generator**: its origin values are the constant `0`. -/
theorem coeffOrigin_linearGenerator (T : ℝ) : CoeffOrigin T (linearGenerator G β₁ β₂ :
    Coeffs ν n m d) := by
  have h := originIntegrable_const T (0 : EuclideanSpace ℝ (Fin n))
    (0 : EuclideanSpace ℝ (Fin n × Fin d)) (0 : Lp (EuclideanSpace ℝ (Fin n)) 2 ν)
    (0 : EuclideanSpace ℝ (Fin m))
  unfold CoeffOrigin
  simp only [(linearGenerator_origin _ _).1, (linearGenerator_origin _ _).2.1,
    (linearGenerator_origin _ _).2.2.1, (linearGenerator_origin _ _).2.2.2]
  exact h

/-- **(2.3) for the linear generator**: its coefficients are continuous linear in the tuple and
independent of the time and the law, so Borel measurable on `[0, T] × H × P₂(H)`. -/
theorem coeffBorelW2_linearGenerator (T : ℝ) :
    CoeffBorelW2 T (linearGenerator G β₁ β₂ : Coeffs ν n m d) where
  b_meas := measurable_borelW2_of_measurable (ψ := (linearGenerator G β₁ β₂).b) (by
    simp only [linearGenerator]; fun_prop)
  σ_meas := measurable_borelW2_of_measurable (ψ := (linearGenerator G β₁ β₂).σ) (by
    simp only [linearGenerator]; fun_prop)
  h_meas := measurable_borelW2_of_measurable (ψ := (linearGenerator G β₁ β₂).h) (by
    simp only [linearGenerator]; fun_prop)
  f_meas := measurable_borelW2_of_measurable (ψ := (linearGenerator G β₁ β₂).f) (by
    simp only [linearGenerator]; fun_prop)

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T L : ℝ}

/-- **Assumption 2.3, interior, for the linear generator at every time**, with any constant
`L ≥ max(β₁ ‖G‖, β₂ ‖G‖)`, `β₁, β₂ ≥ 0`. -/
theorem diagonalLipschitzHAt_linearGenerator (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hL : max (β₁ * ‖GX G‖) (β₂ * ‖GX G‖) ≤ L) (t : ℝ) :
    DiagonalLipschitzHAt ℱ P t L (linearGenerator G β₁ β₂ : Coeffs ν n m d) := by
  intro Θ Θ' _ _ _ _
  refine ae_of_all _ fun ω => (norm_sum_linearGenerator_le hβ₁ hβ₂ t _ _ _ _).trans ?_
  have hK : 0 ≤ max (β₁ * ‖GX G‖) (β₂ * ‖GX G‖) :=
    (mul_nonneg hβ₁ (norm_nonneg _)).trans (le_max_left _ _)
  have htn : 0 ≤ tupleNorm (Θ ω - Θ' ω) := by unfold tupleNorm; positivity
  have hw := w2H_nonneg (lawP2 P Θ) (lawP2 P Θ')
  calc max (β₁ * ‖GX G‖) (β₂ * ‖GX G‖) * tupleNorm (Θ ω - Θ' ω)
      ≤ L * tupleNorm (Θ ω - Θ' ω) := mul_le_mul_of_nonneg_right hL htn
    _ ≤ L * (tupleNorm (Θ ω - Θ' ω) + w2H (lawP2 P Θ) (lawP2 P Θ')) :=
        mul_le_mul_of_nonneg_left (by linarith) (hK.trans hL)

/-- **Assumption 2.5, interior, for the linear generator at every time**, with equality. -/
theorem diagonalMonotoneAt_linearGenerator (t : ℝ) :
    DiagonalMonotoneAt ℱ P t G β₁ β₂ (linearGenerator G β₁ β₂ : Coeffs ν n m d) :=
  fun _ _ _ _ _ _ => le_of_eq (integral_congr_ae
    (ae_of_all _ fun _ => interiorPairing_linearGenerator t _ _ _ _))

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **(2.6) for the terminal function `g(x, ρ) = G x`** of the linear generator, with any
constant `L ≥ ‖G‖`. -/
theorem terminalLipschitz_linearGenerator (hL : ‖GX G‖ ≤ L) :
    TerminalLipschitz ℱ P T L (linearGenerator G β₁ β₂ : Coeffs ν n m d).g := by
  intro ξ ξ' _ _ _ _
  refine ae_of_all _ fun ω => ?_
  simp only [linearGenerator, ← map_sub]
  have hw := w2P_nonneg (lawP2 P ξ) (lawP2 P ξ')
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hL
  calc ‖GX G (ξ ω - ξ' ω)‖ ≤ ‖GX G‖ * ‖ξ ω - ξ' ω‖ := (GX G).le_opNorm _
    _ ≤ L * ‖ξ ω - ξ' ω‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ ≤ L * (‖ξ ω - ξ' ω‖ + w2P (lawP2 P ξ) (lawP2 P ξ')) :=
        mul_le_mul_of_nonneg_left (by linarith) hL0

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The terminal half of Assumption 2.5 for `g(x, ρ) = G x`**, with `α = 1`, with equality. -/
theorem terminalMonotone_linearGenerator :
    TerminalMonotone ℱ P T G 1 (linearGenerator G β₁ β₂ : Coeffs ν n m d).g := by
  intro ξ ξ' _ _ _ _
  refine le_of_eq ?_
  simp only [linearGenerator, ← map_sub, real_inner_self_eq_norm_sq, one_mul]

end Generator

end Dissertation.WellPosedness
