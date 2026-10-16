/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Function.L2Space
import Dissertation.WellPosedness.Stability.Coercive

/-!
# The coupling operators of Assumptions 2.4 and 2.5

The coupling matrix `G ∈ ℝ^{m×n}` of the well-posedness paper acts on three channels of the
tuple space: on a forward state `x ∈ ℝⁿ` as `G x ∈ ℝᵐ`, on an `n × d` matrix `σ` column by
column as `G σ ∈ ℝ^{m×d}`, and on `u ∈ L²(ν; ℝⁿ)` mark by mark as `e ↦ G u(e) ∈ L²(ν; ℝᵐ)`.
In the row-major coordinates `(i, j)` of `ℝ^{n×d}` the second is the Kronecker product
`G ⊗ I_d`. The pairings of Assumption 2.5 use the adjoints `Gᵀ y`, `Gᵀ z`, `e ↦ Gᵀ v(e)`.

This file defines the three operators `GX`, `GZ`, `GU` as continuous linear maps and identifies
each adjoint with the operator built from `Gᵀ`. For `GU` this is an instance of a general fact:
the adjoint of the operator `u ↦ L ∘ u` induced on `L²(ν; F)` by a continuous linear map `L`
between Hilbert spaces is the operator induced by `L*`, since

`⟪L ∘ u, v⟫ = ∫_E ⟪L u(e), v(e)⟫ ν(de) = ∫_E ⟪u(e), L* v(e)⟫ ν(de) = ⟪u, L* ∘ v⟫`.

In coordinates, `|G x|² ≤ ‖G‖² |x|²` and `|Gᵀ y|² ≤ ‖G‖² |y|²` with `‖G‖` the operator norm of
`GX`, and the two coercivity bounds of Assumption 2.4 on `GX` are the coordinate bounds
`ForwardCoercive` and `BackwardCoercive`.

## Main definitions

* `GX` — `x ↦ G x` on `ℝⁿ`.
* `GZ` — `σ ↦ G σ` on `ℝ^{n×d}`.
* `GU` — `u ↦ G u(·)` on `L²(ν; ℝⁿ)`.

## Main statements

* `adjoint_compLpL` — the adjoint of the operator induced on `L²(ν)`.
* `adjoint_GX`, `adjoint_GZ`, `adjoint_GU` — the adjoints are the operators of `Gᵀ`.
* `GX_toLp`, `adjoint_GX_toLp`, `GZ_toLp_apply`, `adjoint_GZ_toLp_apply`, `coeFn_GU`,
  `coeFn_adjoint_GU` — the operators and their adjoints in coordinates.
* `mulVec_dotProduct_le`, `transpose_mulVec_dotProduct_le` — `|G x|² ≤ ‖G‖² |x|²` and
  `|Gᵀ y|² ≤ ‖G‖² |y|²`.
* `gCoerciveForward_GX_iff`, `gCoerciveBackward_GX_iff` — Assumption 2.4 in coordinates.
-/

open MeasureTheory Matrix WithLp
open scoped ENNReal

namespace Dissertation.WellPosedness.System

/-! ### The adjoint of an operator induced on `L²(ν)` -/

section CompLpL

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {𝕜 F F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']

/-- **The adjoint of the operator induced on `L²(ν)`**: for a continuous linear map `L : F → F'`
between Hilbert spaces, the adjoint of `u ↦ L ∘ u` on `L²(ν; F)` is `v ↦ L* ∘ v`. -/
theorem adjoint_compLpL (L : F →L[𝕜] F') :
    ContinuousLinearMap.adjoint (L.compLpL 2 ν)
      = (ContinuousLinearMap.adjoint L).compLpL 2 ν := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (ContinuousLinearMap.adjoint L) u,
    ContinuousLinearMap.coeFn_compLpL L v] with e h₁ h₂
  rw [h₁, h₂, ContinuousLinearMap.adjoint_inner_left]

end CompLpL

/-! ### Coordinate vectors -/

section Coordinates

variable {ι : Type*} [Fintype ι]

/-- The squared Euclidean norm of a coordinate vector is its dot product with itself. -/
theorem norm_toLp_sq_eq_dotProduct (v : ι → ℝ) :
    ‖(toLp 2 v : EuclideanSpace ℝ ι)‖ ^ 2 = v ⬝ᵥ v := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]

end Coordinates

variable {n m d : ℕ} (G : Matrix (Fin m) (Fin n) ℝ)

/-! ### The forward channel -/

/-- The coupling matrix acting on the forward state, `x ↦ G x`, `ℝⁿ → ℝᵐ`. -/
noncomputable def GX : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin G)

/-- `GX` in coordinates. -/
theorem GX_toLp (x : Fin n → ℝ) : GX G (toLp 2 x) = toLp 2 (G *ᵥ x) :=
  rfl

/-- **The adjoint of `GX`** is `y ↦ Gᵀ y`. -/
theorem adjoint_GX : ContinuousLinearMap.adjoint (GX G) = GX Gᵀ := by
  unfold GX
  rw [← conjTranspose_eq_transpose_of_trivial, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact (LinearMap.adjoint_toContinuousLinearMap _).symm

/-- The adjoint of `GX` in coordinates. -/
theorem adjoint_GX_toLp (y : Fin m → ℝ) :
    ContinuousLinearMap.adjoint (GX G) (toLp 2 y) = toLp 2 (Gᵀ *ᵥ y) := by
  rw [adjoint_GX]
  rfl

/-- **`|G x|² ≤ ‖G‖² |x|²`**, with `‖G‖` the operator norm of `GX`. -/
theorem mulVec_dotProduct_le (x : Fin n → ℝ) :
    (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ ‖GX G‖ ^ 2 * (x ⬝ᵥ x) := by
  rw [← norm_toLp_sq_eq_dotProduct, ← norm_toLp_sq_eq_dotProduct, ← GX_toLp, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((GX G).le_opNorm _) 2

/-- **Assumption 2.4, forward branch, in coordinates**: `|x|² ≤ c_G |G x|²` on `ℝⁿ` is
`ForwardCoercive`. -/
theorem gCoerciveForward_GX_iff (cG : ℝ) :
    GCoerciveForward (GX G) cG ↔ Stability.ForwardCoercive G cG := by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · have hx := h (toLp 2 x)
    rwa [GX_toLp, norm_toLp_sq_eq_dotProduct, norm_toLp_sq_eq_dotProduct] at hx
  · have hx := h (ofLp x)
    rwa [← norm_toLp_sq_eq_dotProduct, ← norm_toLp_sq_eq_dotProduct, ← GX_toLp, toLp_ofLp]
      at hx

/-- **Assumption 2.4, backward branch, in coordinates**: `|y|² ≤ c_G |Gᵀ y|²` on `ℝᵐ` is
`BackwardCoercive`. -/
theorem gCoerciveBackward_GX_iff (cG : ℝ) :
    GCoerciveBackward (GX G) cG ↔ Stability.BackwardCoercive G cG := by
  refine ⟨fun h y => ?_, fun h y => ?_⟩
  · have hy := h (toLp 2 y)
    rwa [adjoint_GX_toLp, norm_toLp_sq_eq_dotProduct, norm_toLp_sq_eq_dotProduct] at hy
  · have hy := h (ofLp y)
    rwa [← norm_toLp_sq_eq_dotProduct, ← norm_toLp_sq_eq_dotProduct, ← adjoint_GX_toLp,
      toLp_ofLp] at hy

/-! ### The Brownian channel -/

/-- The coupling matrix acting column by column on `n × d` matrices, `σ ↦ G σ`,
`ℝ^{n×d} → ℝ^{m×d}`: the Kronecker product `G ⊗ I_d` in the coordinates `(i, j)`. -/
noncomputable def GZ :
    EuclideanSpace ℝ (Fin n × Fin d) →L[ℝ] EuclideanSpace ℝ (Fin m × Fin d) :=
  LinearMap.toContinuousLinearMap
    (Matrix.toEuclideanLin (G.kronecker (1 : Matrix (Fin d) (Fin d) ℝ)))

/-- `GZ` in coordinates: the `(k, j)` entry of `G σ` is `(G σ_{· j})_k`. -/
theorem GZ_toLp_apply (z : Fin n × Fin d → ℝ) (k : Fin m) (j : Fin d) :
    GZ G (toLp 2 z) (k, j) = (G *ᵥ fun i => z (i, j)) k := by
  change ((G.kronecker (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ z) (k, j) = _
  simp [mulVec, dotProduct, kronecker, kroneckerMap_apply, one_apply, Fintype.sum_prod_type]

/-- **The adjoint of `GZ`** is `z ↦ Gᵀ z`. -/
theorem adjoint_GZ : ContinuousLinearMap.adjoint (GZ (d := d) G) = GZ Gᵀ := by
  unfold GZ
  have hK : (Gᵀ.kronecker (1 : Matrix (Fin d) (Fin d) ℝ))
      = (G.kronecker (1 : Matrix (Fin d) (Fin d) ℝ))ᴴ := by
    rw [conjTranspose_eq_transpose_of_trivial, kronecker, kronecker, ← kroneckerMap_transpose,
      transpose_one]
  rw [hK, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  exact (LinearMap.adjoint_toContinuousLinearMap _).symm

/-- The adjoint of `GZ` in coordinates: the `(i, j)` entry of `Gᵀ z` is `(Gᵀ z_{· j})_i`. -/
theorem adjoint_GZ_toLp_apply (z : Fin m × Fin d → ℝ) (i : Fin n) (j : Fin d) :
    ContinuousLinearMap.adjoint (GZ G) (toLp 2 z) (i, j) = (Gᵀ *ᵥ fun k => z (k, j)) i := by
  rw [adjoint_GZ, GZ_toLp_apply]

/-! ### The jump channel -/

variable {E : Type*} [MeasurableSpace E] (ν : Measure E)

/-- The coupling matrix acting mark by mark on `L²(ν; ℝⁿ)`, `u ↦ (e ↦ G u(e))`. -/
noncomputable def GU : Lp (EuclideanSpace ℝ (Fin n)) 2 ν →L[ℝ] Lp (EuclideanSpace ℝ (Fin m)) 2 ν :=
  (GX G).compLpL 2 ν

/-- **The adjoint of `GU`** is `v ↦ (e ↦ Gᵀ v(e))`. -/
theorem adjoint_GU : ContinuousLinearMap.adjoint (GU G ν) = GU Gᵀ ν := by
  rw [GU, adjoint_compLpL, adjoint_GX, GU]

/-- `GU` acts mark by mark, `ν`-almost everywhere. -/
theorem coeFn_GU (u : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    GU G ν u =ᵐ[ν] fun e => GX G (u e) :=
  ContinuousLinearMap.coeFn_compLpL (GX G) u

/-- The adjoint of `GU` acts mark by mark as `Gᵀ`, `ν`-almost everywhere. -/
theorem coeFn_adjoint_GU (v : Lp (EuclideanSpace ℝ (Fin m)) 2 ν) :
    ContinuousLinearMap.adjoint (GU G ν) v =ᵐ[ν] fun e => GX Gᵀ (v e) := by
  rw [adjoint_GU]
  exact coeFn_GU Gᵀ ν v

end Dissertation.WellPosedness.System
