/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.Operators

/-!
# The operator norm of the coupling matrix on the three channels

Write `‖G‖` for the operator norm of the coupling matrix `G ∈ ℝ^{m×n}` acting on `ℝⁿ`, the norm of
`GX G`. Acting column by column on `ℝ^{n×d}` with the Frobenius norm, `GZ G`, and mark by mark on
`L²(ν; ℝⁿ)`, `GU G ν`, the matrix has operator norm at most `‖G‖`:

`|G σ|²_F = ∑_j |G σ_{· j}|² ≤ ‖G‖² ∑_j |σ_{· j}|² = ‖G‖² |σ|²_F`,
`‖G u‖²_{L²(ν)} = ∫_E |G u(e)|² ν(de) ≤ ‖G‖² ‖u‖²_{L²(ν)}`.

An operator and its adjoint have the same norm, so the three adjoints `Gᵀ` are bounded by `‖G‖` as
well. By Cauchy–Schwarz in each of its four terms, the interior pairing of (2.7) then satisfies

`|⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F − ⟨δf, G δX⟩ + ⟨δh, Gᵀ δU⟩_{L²(ν)}|`
`  ≤ ‖G‖ (|δb| |δY| + |δσ|_F |δZ|_F + |δf| |δX| + ‖δh‖_{L²(ν)} ‖δU‖_{L²(ν)})`.

## Main statements

* `norm_adjoint_GX` — `‖Gᵀ‖ = ‖G‖` on the forward channel.
* `norm_GZ_apply_sq_le`, `norm_GZ_le`, `norm_adjoint_GZ_le` — `G` and `Gᵀ` on the Brownian
  channel have norm at most `‖G‖`.
* `norm_GU_le`, `norm_adjoint_GU_le` — `G` and `Gᵀ` on the jump channel have norm at most `‖G‖`.
* `abs_interiorPairing_le` — the Cauchy–Schwarz bound of the interior pairing.
-/

open MeasureTheory Matrix WithLp
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

variable {n m d : ℕ} (G : Matrix (Fin m) (Fin n) ℝ)

/-- **`‖Gᵀ‖ = ‖G‖`** on the forward channel. -/
theorem norm_adjoint_GX : ‖ContinuousLinearMap.adjoint (GX G)‖ = ‖GX G‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- **`|G σ|²_F ≤ ‖G‖² |σ|²_F`** on `n × d` matrices, with `‖G‖` the operator norm of `GX`. -/
theorem norm_GZ_apply_sq_le (z : EuclideanSpace ℝ (Fin n × Fin d)) :
    ‖GZ G z‖ ^ 2 ≤ ‖GX G‖ ^ 2 * ‖z‖ ^ 2 := by
  rw [← toLp_ofLp 2 z]
  set w := ofLp z
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [GZ_toLp_apply, Real.norm_eq_abs, sq_abs, Fintype.sum_prod_type]
  have hj : ∀ j : Fin d, ∑ k, (G *ᵥ fun i => w (i, j)) k ^ 2
      ≤ ‖GX G‖ ^ 2 * ∑ i, w (i, j) ^ 2 := fun j => by
    have h := mulVec_dotProduct_le G (fun i => w (i, j))
    simpa only [dotProduct, sq] using h
  calc ∑ k, ∑ j, (G *ᵥ fun i => w (i, j)) k ^ 2
      = ∑ j, ∑ k, (G *ᵥ fun i => w (i, j)) k ^ 2 := Finset.sum_comm
    _ ≤ ∑ j, ‖GX G‖ ^ 2 * ∑ i, w (i, j) ^ 2 := Finset.sum_le_sum fun j _ => hj j
    _ = ‖GX G‖ ^ 2 * ∑ i, ∑ j, w (i, j) ^ 2 := by rw [← Finset.mul_sum, Finset.sum_comm]

/-- **`‖G‖` bounds `G` on `n × d` matrices** with the Frobenius norm. -/
theorem norm_GZ_le : ‖GZ (d := d) G‖ ≤ ‖GX G‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun z => ?_
  have h := norm_GZ_apply_sq_le G z
  rw [← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- **`‖G‖` bounds `Gᵀ` on `m × d` matrices** with the Frobenius norm. -/
theorem norm_adjoint_GZ_le : ‖ContinuousLinearMap.adjoint (GZ (d := d) G)‖ ≤ ‖GX G‖ := by
  rw [LinearIsometryEquiv.norm_map]
  exact norm_GZ_le G

variable {E : Type*} [MeasurableSpace E] (ν : Measure E)

/-- **`‖G‖` bounds `G` on `L²(ν; ℝⁿ)`.** -/
theorem norm_GU_le : ‖GU G ν‖ ≤ ‖GX G‖ :=
  ContinuousLinearMap.norm_compLpL_le _

/-- **`‖G‖` bounds `Gᵀ` on `L²(ν; ℝᵐ)`.** -/
theorem norm_adjoint_GU_le : ‖ContinuousLinearMap.adjoint (GU G ν)‖ ≤ ‖GX G‖ := by
  rw [LinearIsometryEquiv.norm_map]
  exact norm_GU_le G ν

/-- `|⟨a, B b⟩| ≤ K |a| |b|` for an operator `B` of norm at most `K`. -/
theorem abs_inner_apply_le {F F' : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] (B : F' →L[ℝ] F) {K : ℝ} (hB : ‖B‖ ≤ K) (a : F)
    (b : F') : |inner ℝ a (B b)| ≤ K * (‖a‖ * ‖b‖) := by
  calc |inner ℝ a (B b)| ≤ ‖a‖ * ‖B b‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖a‖ * (K * ‖b‖) :=
        mul_le_mul_of_nonneg_left ((B.le_opNorm b).trans
          (mul_le_mul_of_nonneg_right hB (norm_nonneg _))) (norm_nonneg _)
    _ = K * (‖a‖ * ‖b‖) := by ring

/-- **The Cauchy–Schwarz bound of the interior pairing**:
`|⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F − ⟨δf, G δX⟩ + ⟨δh, Gᵀ δU⟩_{L²(ν)}|
  ≤ ‖G‖ (|δb| |δY| + |δσ|_F |δZ|_F + |δf| |δX| + ‖δh‖_{L²(ν)} ‖δU‖_{L²(ν)})`. -/
theorem abs_interiorPairing_le
    (c : ChannelDiff (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin n × Fin d)) (EuclideanSpace ℝ (Fin m × Fin d))
      (Lp (EuclideanSpace ℝ (Fin n)) 2 ν) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)) :
    |interiorPairing (GX G) (GZ G) (GU G ν) c|
      ≤ ‖GX G‖ * (‖c.δb‖ * ‖c.δY‖ + ‖c.δσ‖ * ‖c.δZ‖ + ‖c.δf‖ * ‖c.δX‖
        + ‖c.δh‖ * ‖c.δU‖) := by
  have h1 := abs_inner_apply_le _ (norm_adjoint_GX G).le c.δb c.δY
  have h2 := abs_inner_apply_le _ (norm_adjoint_GZ_le G) c.δσ c.δZ
  have h3 := abs_inner_apply_le (GX G) le_rfl (-c.δf) c.δX
  have h4 := abs_inner_apply_le _ (norm_adjoint_GU_le G ν) c.δh c.δU
  rw [norm_neg] at h3
  unfold interiorPairing
  have e1 := abs_add_le (inner ℝ c.δb (ContinuousLinearMap.adjoint (GX G) c.δY)
    + inner ℝ c.δσ (ContinuousLinearMap.adjoint (GZ G) c.δZ) + inner ℝ (-c.δf) (GX G c.δX))
    (inner ℝ c.δh (ContinuousLinearMap.adjoint (GU G ν) c.δU))
  have e2 := abs_add_le (inner ℝ c.δb (ContinuousLinearMap.adjoint (GX G) c.δY)
    + inner ℝ c.δσ (ContinuousLinearMap.adjoint (GZ G) c.δZ)) (inner ℝ (-c.δf) (GX G c.δX))
  have e3 := abs_add_le (inner ℝ c.δb (ContinuousLinearMap.adjoint (GX G) c.δY))
    (inner ℝ c.δσ (ContinuousLinearMap.adjoint (GZ G) c.δZ))
  linarith

end MVFBSDEJ.WellPosedness.System
