/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Robustness.JumpMargin
import Dissertation.WellPosedness.System.FullRank

/-!
# Dissipativity margins obtained from Assumption 2.5

Remark 2.11 of the well-posedness paper records the margins that Assumption 2.5 supplies. The
right-hand side of (2.7) satisfies, pointwise and for every `c`,

`−β̄₁ (|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²) − β̄₂ |G δX|²`
`  = −(β̄₁ − c)(|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²) − (β̄₂ − c) |G δX|² − c Q_G`,

with `Q_G = |Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖² + |G δX|²` the weighted quantity of (2.12). Both
sides are integrable along square-integrable tuples, so (2.7) with the constants `β̄₁, β̄₂` is
(2.12) with the constants `β̄₁ − c, β̄₂ − c` and margin `c`.

**The unweighted form.** Let `m = n` and let `G` satisfy both bounds of Assumption 2.4 with a
constant `c_G`. The backward bound on `ℝⁿ` extends column by column to `ℝ^{n×d}` and mark by mark
to `L²(ν; ℝⁿ)`, so the unweighted quantity `Q = |δX|² + |δY|² + |δZ|²_F + ‖δU‖²` of (2.13)
satisfies `Q ≤ c_G Q_G`, and (2.12) with margin `c ≥ 0` gives (2.13) with margin `c / c_G`. For
`G` of full rank, `c_G = s_min(G)⁻²` and the unweighted margin is `c s_min(G)²`. At `G = I`,
`Q = Q_G`, and (2.12) and (2.13) coincide.

**The margin `c / c_G` is sharp.** Take `n = m = 1`, `G = 1/2`, so `s_min(G) = 1/2` and
`c_G = 4`, and the affine system `b = −(β̄₁/2) y`, `σ = σ_c − (β̄₁/2) z`, `h = h_c − (β̄₁/2) u`,
`f = (β̄₂/2) x`. Its interior pairing equals the right-hand side of (2.7) with the constants
`β̄₁, β̄₂`, so (2.12) holds with `β̄₁ − c, β̄₂ − c` and margin `c`, with equality. Since
`Q_G = Q / 4`, (2.13) with the constants `β̄₁ − c, β̄₂ − c` holds with margin `c / 4` and, on a
horizon `T > 0`, with no larger margin: at the deterministic inputs `(x, 0, 0, 0)` and `0`,
`|x| = 1`, it reads `c' ≤ c / 4`. In particular for `c > 0` the unweighted margin `c` fails.

## Main statements

* `dissipation_eq_sub_gWeightSq`, `integral_dissipation_diagDiff_eq_sub` — the identity above.
* `diagonalMonotone_iff_weightedMargin_sub` — (2.7) with `β̄₁, β̄₂` is (2.12) with
  `β̄₁ − c, β̄₂ − c` and margin `c`.
* `gCoerciveBackward_GZ`, `gCoerciveBackward_GU` — the backward bound of Assumption 2.4 on the
  `Z` and `U` channels.
* `channelSq_le_mul_gWeightSq` — `Q ≤ c_G Q_G`.
* `DiagonalMonotoneWeightedMargin.unweighted`, `DiagonalMonotoneWeightedMargin.unweighted_of_rank`
  — the unweighted margin `c / c_G = c s_min(G)²`.
* `diagonalMonotoneWeightedMargin_one_iff` — at `G = I` the two margins coincide.
* `GX_smul`, `GZ_smul`, `GU_smul`, `sMin_half` — the coupling operators of `a G`, and
  `s_min(1/2) = 1/2`.
* `interiorPairing_affine_smul`, `diagonalMonotone_affine_smul` — the scaled affine system
  satisfies (2.7) with equality at `G = a I`.
* `margin_affine_half`, `not_diagonalMonotoneMargin_affine_half` — at `G = 1/2` the unweighted
  margin is exactly `c / 4`.
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal Matrix

namespace Dissertation.WellPosedness.System

/-! ### The identity behind the reduced constants -/

section Identity

variable {HX HY HZX HZY HUX HUY : Type*}
  [NormedAddCommGroup HX] [InnerProductSpace ℝ HX] [CompleteSpace HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [CompleteSpace HY]
  [NormedAddCommGroup HZX] [InnerProductSpace ℝ HZX] [CompleteSpace HZX]
  [NormedAddCommGroup HZY] [InnerProductSpace ℝ HZY] [CompleteSpace HZY]
  [NormedAddCommGroup HUX] [InnerProductSpace ℝ HUX] [CompleteSpace HUX]
  [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY] [CompleteSpace HUY]
  (A : HX →L[ℝ] HY) (AZ : HZX →L[ℝ] HZY) (AU : HUX →L[ℝ] HUY)

/-- **The right-hand side of (2.7) with the constants reduced by `c`**: for every `c`, the
dissipation at `β₁, β₂` is that at `β₁ − c, β₂ − c` minus `c` times the weighted quantity of
(2.12). -/
theorem dissipation_eq_sub_gWeightSq (β₁ β₂ c : ℝ) (q : ChannelDiff HX HY HZX HZY HUX HUY) :
    dissipation A AZ AU β₁ β₂ q
      = dissipation A AZ AU (β₁ - c) (β₂ - c) q - c * gWeightSq A AZ AU q := by
  simp only [dissipation, gWeightSq]
  ring

end Identity

section Reduced

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Θ Θ' : Ω → TupleH ν n m d}

/-- **The expected dissipation with the constants reduced by `c`**: along two square-integrable
tuples,
`𝔼[−β₁ (…) − β₂ |G δX|²] = 𝔼[−(β₁ − c)(…) − (β₂ − c) |G δX|²] − c 𝔼 Q_G`. -/
theorem integral_dissipation_diagDiff_eq_sub (G : Matrix (Fin m) (Fin n) ℝ) (β₁ β₂ c : ℝ)
    (C : Coeffs ν n m d) (t : ℝ) (μ μ' : P2 (TupleH ν n m d)) (hΘ : MemLp Θ 2 P)
    (hΘ' : MemLp Θ' 2 P) :
    ∫ ω, dissipation (GX G) (GZ G) (GU G ν) β₁ β₂ (diagDiff C t (Θ ω) (Θ' ω) μ μ') ∂P
      = ∫ ω, dissipation (GX G) (GZ G) (GU G ν) (β₁ - c) (β₂ - c)
          (diagDiff C t (Θ ω) (Θ' ω) μ μ') ∂P
        - c * ∫ ω, gWeightSq (GX G) (GZ G) (GU G ν) (diagDiff C t (Θ ω) (Θ' ω) μ μ') ∂P := by
  rw [← integral_const_mul, ← integral_sub
    (integrable_dissipation_diagDiff _ _ _ _ _ C t μ μ' hΘ hΘ')
    ((integrable_gWeightSq_diagDiff _ _ _ C t μ μ' hΘ hΘ').const_mul c)]
  exact integral_congr_ae (ae_of_all _ fun ω => dissipation_eq_sub_gWeightSq _ _ _ _ _ _ _)

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} [IsProbabilityMeasure P] {T α β₁ β₂ c : ℝ}
  {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d}

/-- **Assumption 2.5, interior, is (2.12) with reduced constants** (Remark 2.11): for every `c`,
(2.7) with the constants `β₁, β₂` holds along the diagonal if and only if (2.12) with the
constants `β₁ − c, β₂ − c` and margin `c` does. -/
theorem diagonalMonotone_iff_weightedMargin_sub (c : ℝ) :
    DiagonalMonotone ℱ P T G β₁ β₂ C
      ↔ DiagonalMonotoneWeightedMargin ℱ P T G (β₁ - c) (β₂ - c) c C := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
    rw [← integral_dissipation_diagDiff_eq_sub G β₁ β₂ c C t _ _ hΘ2 hΘ2']
    exact ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  · filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
    rw [integral_dissipation_diagDiff_eq_sub G β₁ β₂ c C t _ _ hΘ2 hΘ2']
    exact ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'

end Reduced

/-! ### Assumption 2.4 on the `Z` and `U` channels -/

section Coercive

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}
  {G : Matrix (Fin m) (Fin n) ℝ} {cG : ℝ}

omit [MeasurableSpace E] in
/-- **The backward bound of Assumption 2.4 on `ℝ^{m×d}`**: if `|y|² ≤ c_G |Gᵀ y|²` on `ℝᵐ`, then
`|z|²_F ≤ c_G |Gᵀ z|²_F` for every `z ∈ ℝ^{m×d}`, column by column. -/
theorem gCoerciveBackward_GZ (h : GCoerciveBackward (GX G) cG) :
    GCoerciveBackward (GZ (d := d) G) cG := by
  have hc := (gCoerciveBackward_GX_iff G cG).mp h
  intro z
  have e1 : ‖z‖ ^ 2 = ∑ j : Fin d, (fun k => z (k, j)) ⬝ᵥ (fun k => z (k, j)) := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type_right]
    simp [dotProduct, sq]
  have e2 : ‖ContinuousLinearMap.adjoint (GZ G) z‖ ^ 2
      = ∑ j : Fin d, (Gᵀ *ᵥ fun k => z (k, j)) ⬝ᵥ (Gᵀ *ᵥ fun k => z (k, j)) := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := adjoint_GZ_toLp_apply G (WithLp.ofLp z) i j
    rw [WithLp.toLp_ofLp] at this
    rw [this, Real.norm_eq_abs, sq_abs, sq]
  rw [e1, e2]
  exact hc.sum_le Finset.univ _

/-- **The backward bound of Assumption 2.4 on `L²(ν; ℝᵐ)`**: if `|y|² ≤ c_G |Gᵀ y|²` on `ℝᵐ`,
then `‖u‖²_{L²(ν)} ≤ c_G ‖Gᵀ u‖²_{L²(ν)}` for every `u ∈ L²(ν; ℝᵐ)`, mark by mark. -/
theorem gCoerciveBackward_GU (h : GCoerciveBackward (GX G) cG) :
    GCoerciveBackward (GU G ν) cG := by
  intro u
  have hsq : ∀ {k : ℕ} (v : Lp (EuclideanSpace ℝ (Fin k)) 2 ν), ‖v‖ ^ 2 = ∫ e, ‖v e‖ ^ 2 ∂ν :=
    fun v => by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp_rw [real_inner_self_eq_norm_sq]
  rw [hsq, hsq, ← integral_const_mul]
  refine integral_mono_ae ((Lp.memLp u).integrable_norm_pow two_ne_zero)
    (((Lp.memLp _).integrable_norm_pow two_ne_zero).const_mul cG) ?_
  filter_upwards [coeFn_adjoint_GU G ν u] with e he
  rw [he, ← adjoint_GX]
  exact h (u e)

/-- **The unweighted quantity is controlled by the weighted one**: if `G` satisfies both bounds of
Assumption 2.4 with the constant `c_G`, then
`|δX|² + |δY|² + |δZ|²_F + ‖δU‖² ≤ c_G (|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖² + |G δX|²)`. -/
theorem channelSq_le_mul_gWeightSq (hf : GCoerciveForward (GX G) cG)
    (hb : GCoerciveBackward (GX G) cG) (C : Coeffs ν n m d) (t : ℝ) (θ θ' : TupleH ν n m d)
    (μ μ' : P2 (TupleH ν n m d)) :
    channelSq (θ - θ') ≤ cG * gWeightSq (GX G) (GZ G) (GU G ν) (diagDiff C t θ θ' μ μ') := by
  have h1 := hf (θ.1 - θ'.1)
  have h2 := hb (θ.2.1 - θ'.2.1)
  have h3 := gCoerciveBackward_GZ (d := d) hb (θ.2.2.1 - θ'.2.2.1)
  have h4 := gCoerciveBackward_GU (ν := ν) hb (θ.2.2.2 - θ'.2.2.2)
  simp only [channelSq, gWeightSq, diagDiff, Prod.fst_sub, Prod.snd_sub]
  linarith

end Coercive

/-! ### The unweighted margin -/

section Unweighted

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}
  {Ω : Type*} [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T α β₁ β₂ c cG : ℝ}

/-- **The unweighted margin from the weighted one**: if `G` satisfies both bounds of
Assumption 2.4 with a constant `c_G ≥ 0`, then (2.12) with margin `c ≥ 0` gives (2.13) with the
same constants and margin `c / c_G`. -/
theorem DiagonalMonotoneWeightedMargin.unweighted {G : Matrix (Fin m) (Fin n) ℝ}
    {C : Coeffs ν n m d} (h : DiagonalMonotoneWeightedMargin ℱ P T G β₁ β₂ c C) (hc : 0 ≤ c)
    (hcG : 0 ≤ cG) (hf : GCoerciveForward (GX G) cG) (hb : GCoerciveBackward (GX G) cG) :
    DiagonalMonotoneMargin ℱ P T G β₁ β₂ (c / cG) C := by
  filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  have key := ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  have hgi := integrable_gWeightSq_diagDiff (GX G) (GZ G) (GU G ν) C t (lawP2 P Θ) (lawP2 P Θ')
    hΘ2 hΘ2'
  have hle : ∫ ω, channelSq (Θ ω - Θ' ω) ∂P
      ≤ cG * ∫ ω, gWeightSq (GX G) (GZ G) (GU G ν)
        (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P := by
    rw [← integral_const_mul]
    exact integral_mono (integrable_channelSq_sub hΘ2 hΘ2') (hgi.const_mul cG)
      fun ω => channelSq_le_mul_gWeightSq hf hb C t _ _ _ _
  have hW : 0 ≤ ∫ ω, gWeightSq (GX G) (GZ G) (GU G ν)
      (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P :=
    integral_nonneg fun ω => gWeightSq_nonneg _ _ _ _
  have hcmp : c / cG * ∫ ω, channelSq (Θ ω - Θ' ω) ∂P
      ≤ c * ∫ ω, gWeightSq (GX G) (GZ G) (GU G ν)
        (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P := by
    rcases hcG.eq_or_lt with h0 | hpos
    · rw [← h0, div_zero, zero_mul]
      exact mul_nonneg hc hW
    · calc c / cG * ∫ ω, channelSq (Θ ω - Θ' ω) ∂P
          ≤ c / cG * (cG * ∫ ω, gWeightSq (GX G) (GZ G) (GU G ν)
            (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P) :=
            mul_le_mul_of_nonneg_left hle (div_nonneg hc hpos.le)
        _ = c * ∫ ω, gWeightSq (GX G) (GZ G) (GU G ν)
            (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P := by
            field_simp
  linarith

/-- **The unweighted margin is `c s_min(G)²`** (Remark 2.11, `m = n`): for `G ∈ ℝ^{n×n}` of full
rank, (2.12) with margin `c ≥ 0` gives (2.13) with the same constants and margin
`c / c_G = c s_min(G)²`, `c_G = s_min(G)⁻²`. -/
theorem DiagonalMonotoneWeightedMargin.unweighted_of_rank {G : Matrix (Fin n) (Fin n) ℝ}
    {C : Coeffs ν n n d} (hG : G.rank = n)
    (h : DiagonalMonotoneWeightedMargin ℱ P T G β₁ β₂ c C) (hc : 0 ≤ c) :
    DiagonalMonotoneMargin ℱ P T G β₁ β₂ (c * sMin G ^ 2) C := by
  have hG' : G.rank = min n n := by rw [min_self, hG]
  have h' := h.unweighted hc (inv_nonneg.mpr (sq_nonneg _)) (gCoerciveForward_of_rank hG' le_rfl)
    (gCoerciveBackward_of_rank hG' le_rfl)
  rwa [div_inv_eq_mul] at h'

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- At `G = I` the weighted quantity of (2.12) is the unweighted quantity of (2.13). -/
theorem gWeightSq_one (C : Coeffs ν n n d) (t : ℝ) (θ θ' : TupleH ν n n d)
    (μ μ' : P2 (TupleH ν n n d)) :
    gWeightSq (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν) (diagDiff C t θ θ' μ μ')
      = channelSq (θ - θ') := by
  simp only [gWeightSq, diagDiff, GX_one, GZ_one, GU_one, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_apply, channelSq, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **At `G = I` the weighted and unweighted margins coincide**: (2.12) and (2.13) are the same
condition, with the same constants and margin. -/
theorem diagonalMonotoneWeightedMargin_one_iff {C : Coeffs ν n n d} :
    DiagonalMonotoneWeightedMargin ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) β₁ β₂ c C
      ↔ DiagonalMonotoneMargin ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) β₁ β₂ c C := by
  simp only [DiagonalMonotoneWeightedMargin, DiagonalMonotoneMargin, gWeightSq_one]

end Unweighted

/-! ### Sharpness at `G = 1/2` -/

section Scaled

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}

omit [MeasurableSpace E] in
/-- The forward coupling operator of `a G` is `a` times that of `G`. -/
theorem GX_smul (a : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) : GX (a • G) = a • GX G := by
  unfold GX
  rw [map_smul, map_smul]

omit [MeasurableSpace E] in
/-- The coupling operator of `a G` on `n × d` matrices is `a` times that of `G`. -/
theorem GZ_smul (a : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) : GZ (d := d) (a • G) = a • GZ G := by
  unfold GZ
  rw [Matrix.kronecker, Matrix.smul_kronecker, map_smul, map_smul]

/-- The coupling operator of `a G` on `L²(ν; ℝⁿ)` is `a` times that of `G`. -/
theorem GU_smul (a : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) : GU (a • G) ν = a • GU G ν := by
  rw [GU, GX_smul, ContinuousLinearMap.smul_compLpL, GU]

/-- The smallest singular value of the `1 × 1` matrix `1/2` is `1/2`, so `c_G = 4`. -/
theorem sMin_half : sMin ((2⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) = 2⁻¹ := by
  have h := (Matrix.isHermitian_conjTranspose_mul_self
    ((2⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))).trace_eq_sum_eigenvalues
  rw [Fin.sum_univ_one] at h
  unfold sMin
  rw [if_pos le_rfl, ciInf_unique]
  have ht : ((((2⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))ᴴ
      * ((2⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)))).trace = 4⁻¹ := by
    simp [Matrix.trace]
    norm_num
  rw [ht] at h
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [show (default : Fin 1) = 0 from rfl, ← h,
    show (4⁻¹ : ℝ) = 2⁻¹ ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The adjoint of the forward coupling operator of `a I` is `a` times the identity. -/
theorem adjoint_GX_smul_one (a : ℝ) :
    ContinuousLinearMap.adjoint (GX (a • (1 : Matrix (Fin n) (Fin n) ℝ)))
      = a • ContinuousLinearMap.id ℝ _ := by
  rw [adjoint_GX, Matrix.transpose_smul, Matrix.transpose_one, GX_smul, GX_one]

/-- The adjoint of the coupling operator of `a I` on `n × d` matrices is `a` times the
identity. -/
theorem adjoint_GZ_smul_one (a : ℝ) :
    ContinuousLinearMap.adjoint (GZ (d := d) (a • (1 : Matrix (Fin n) (Fin n) ℝ)))
      = a • ContinuousLinearMap.id ℝ _ := by
  rw [adjoint_GZ, Matrix.transpose_smul, Matrix.transpose_one, GZ_smul, GZ_one]

/-- The adjoint of the coupling operator of `a I` on `L²(ν; ℝⁿ)` is `a` times the identity. -/
theorem adjoint_GU_smul_one (a : ℝ) :
    ContinuousLinearMap.adjoint (GU (a • (1 : Matrix (Fin n) (Fin n) ℝ)) ν)
      = a • ContinuousLinearMap.id ℝ _ := by
  rw [adjoint_GU, Matrix.transpose_smul, Matrix.transpose_one, GU_smul, GU_one]

variable {β₁ β₂ : ℝ} {σc : EuclideanSpace ℝ (Fin n × Fin d)}
  {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}

/-- **The scaled affine system satisfies (2.7) with equality at `G = a I`**: for the affine
system of Example 5.1(i) with constants `a β₁, a β₂`, pointwise,
`⟨δb, a δY⟩ + ⟨δσ, a δZ⟩_F − ⟨δf, a δX⟩ + ⟨δh, a δU⟩_{L²(ν)}
  = −β₁ (|a δY|² + |a δZ|²_F + ‖a δU‖²_{L²(ν)}) − β₂ |a δX|²`. -/
theorem interiorPairing_affine_smul (a : ℝ) (t : ℝ) (θ θ' : TupleH ν n n d)
    (μ μ' : P2 (TupleH ν n n d)) :
    interiorPairing (GX (a • (1 : Matrix (Fin n) (Fin n) ℝ))) (GZ (a • 1)) (GU (a • 1) ν)
        (diagDiff (Existence.affineCoeffs (a * β₁) (a * β₂) σc hc) t θ θ' μ μ')
      = dissipation (GX (a • (1 : Matrix (Fin n) (Fin n) ℝ))) (GZ (a • 1)) (GU (a • 1) ν) β₁ β₂
        (diagDiff (Existence.affineCoeffs (a * β₁) (a * β₂) σc hc) t θ θ' μ μ') := by
  have e₁ : -((a * β₁) • θ.2.1) - -((a * β₁) • θ'.2.1) = -((a * β₁) • (θ.2.1 - θ'.2.1)) := by
    rw [smul_sub]; abel
  have e₂ : σc - (a * β₁) • θ.2.2.1 - (σc - (a * β₁) • θ'.2.2.1)
      = -((a * β₁) • (θ.2.2.1 - θ'.2.2.1)) := by
    rw [smul_sub]; abel
  have e₃ : hc - (a * β₁) • θ.2.2.2 - (hc - (a * β₁) • θ'.2.2.2)
      = -((a * β₁) • (θ.2.2.2 - θ'.2.2.2)) := by
    rw [smul_sub]; abel
  simp only [interiorPairing, dissipation, diagDiff, adjoint_GX_smul_one, adjoint_GZ_smul_one,
    adjoint_GU_smul_one]
  simp only [Existence.affineCoeffs, e₁, e₂, e₃, ← smul_sub, GX_smul, GX_one,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, inner_neg_left,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **Assumption 2.5, interior, for the scaled affine system at `G = a I`**, with the constants
`β₁, β₂`, with equality. -/
theorem diagonalMonotone_affine_smul (a : ℝ) :
    DiagonalMonotone ℱ P T (a • (1 : Matrix (Fin n) (Fin n) ℝ)) β₁ β₂
      (Existence.affineCoeffs (a * β₁) (a * β₂) σc hc) :=
  Eventually.of_forall fun t Θ Θ' _ _ _ _ => le_of_eq (integral_congr_ae
    (Eventually.of_forall fun ω => interiorPairing_affine_smul a t (Θ ω) (Θ' ω) _ _))

variable {σ₁ : EuclideanSpace ℝ (Fin 1 × Fin d)} {h₁ : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν}

/-- **The unweighted margin at `G = 1/2` is exactly `c / 4`.** For `n = m = 1`, `G = 1/2`
(`c_G = s_min(G)⁻² = 4`) and the affine system of Example 5.1(i) with constants `β₁/2, β₂/2`:
Assumption 2.5, interior, holds with the constants `β₁, β₂`; for every `c`, (2.12) holds with
the constants `β₁ − c, β₂ − c` and margin `c`; for `c ≥ 0`, (2.13) holds with those constants and
margin `c / 4`; and on a horizon `T > 0`, (2.13) with those constants fails for every margin
`c' > c / 4`. -/
theorem margin_affine_half (hT : 0 < T) (c : ℝ) (hc : 0 ≤ c) :
    DiagonalMonotone ℱ P T ((2⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) β₁ β₂
        (Existence.affineCoeffs (2⁻¹ * β₁) (2⁻¹ * β₂) σ₁ h₁)
      ∧ DiagonalMonotoneWeightedMargin ℱ P T ((2⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (β₁ - c) (β₂ - c) c (Existence.affineCoeffs (2⁻¹ * β₁) (2⁻¹ * β₂) σ₁ h₁)
      ∧ DiagonalMonotoneMargin ℱ P T ((2⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (β₁ - c) (β₂ - c) (c / 4) (Existence.affineCoeffs (2⁻¹ * β₁) (2⁻¹ * β₂) σ₁ h₁)
      ∧ ∀ c' : ℝ, c / 4 < c' → ¬ DiagonalMonotoneMargin ℱ P T
        ((2⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) (β₁ - c) (β₂ - c) c'
        (Existence.affineCoeffs (2⁻¹ * β₁) (2⁻¹ * β₂) σ₁ h₁) := by
  have hM := diagonalMonotone_affine_smul (ℱ := ℱ) (P := P) (T := T) (β₁ := β₁) (β₂ := β₂)
    (σc := σ₁) (hc := h₁) (2⁻¹ : ℝ)
  have hW := (diagonalMonotone_iff_weightedMargin_sub c).mp hM
  have hrank : ((2⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).rank = 1 := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (by simp)),
      Fintype.card_fin]
  refine ⟨hM, hW, ?_, fun c' hc' hM' => ?_⟩
  · have hU := hW.unweighted_of_rank hrank hc
    rwa [sMin_half, show c * (2⁻¹ : ℝ) ^ 2 = c / 4 by ring] at hU
  · haveI : (ae (volume.restrict (Set.Icc (0 : ℝ) T))).NeBot := by
      rw [ae_restrict_neBot, Real.volume_Icc, sub_zero]
      exact ENNReal.ofReal_ne_zero_iff.mpr hT
    obtain ⟨t, ht⟩ := hM'.dirac.exists
    set x : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
    have hx : ‖x‖ = 1 := by simp [x]
    have key := ht ((x, 0, 0, 0) : TupleH ν 1 1 d) 0
    rw [interiorPairing_affine_smul] at key
    simp only [dissipation, diagDiff, adjoint_GX_smul_one, adjoint_GZ_smul_one,
      adjoint_GU_smul_one] at key
    simp only [channelSq, GX_smul, GX_one, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.id_apply, sub_zero, Prod.fst_zero, Prod.snd_zero, smul_zero, norm_zero,
      norm_smul, Real.norm_eq_abs, hx] at key
    norm_num at key
    linarith

/-- **The unweighted margin `c` fails at `G = 1/2`**: for `n = m = 1`, `G = 1/2`, a horizon
`T > 0` and `c > 0`, the affine system of Example 5.1(i) with constants `β₁/2, β₂/2` satisfies
(2.12) with the constants `β₁ − c, β₂ − c` and margin `c`, but not (2.13) with the same constants
and margin. -/
theorem not_diagonalMonotoneMargin_affine_half (hT : 0 < T) {c : ℝ} (hc : 0 < c) :
    DiagonalMonotoneWeightedMargin ℱ P T ((2⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (β₁ - c) (β₂ - c) c (Existence.affineCoeffs (2⁻¹ * β₁) (2⁻¹ * β₂) σ₁ h₁)
      ∧ ¬ DiagonalMonotoneMargin ℱ P T ((2⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (β₁ - c) (β₂ - c) c (Existence.affineCoeffs (2⁻¹ * β₁) (2⁻¹ * β₂) σ₁ h₁) := by
  obtain ⟨-, hW, -, hno⟩ := margin_affine_half (ℱ := ℱ) (P := P) (β₁ := β₁) (β₂ := β₂)
    (σ₁ := σ₁) (h₁ := h₁) hT c hc.le
  exact ⟨hW, hno c (by linarith)⟩

end Scaled

end Dissertation.WellPosedness.System
