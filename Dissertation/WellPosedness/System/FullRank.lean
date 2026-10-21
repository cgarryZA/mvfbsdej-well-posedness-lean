/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.Operators

/-!
# Assumption 2.4 from the full rank of the coupling matrix

Assumption 2.4 of the well-posedness paper takes a coupling matrix `G ∈ ℝ^{m×n}` of full rank,
writes `s_min(G) > 0` for its smallest singular value and sets `c_G := s_min(G)⁻²`; then

`|x|² ≤ c_G |G x|²` (`m ≥ n`),   `|y|² ≤ c_G |Gᵀ y|²` (`n ≥ m`).

The singular values of `G` are the square roots of the `min(m, n)` largest eigenvalues of `Gᵀ G`,
equivalently of `G Gᵀ`, so the smallest one is the square root of the least eigenvalue of `Gᵀ G`
when `n ≤ m` and of `G Gᵀ` when `m ≤ n`; for a square matrix the two agree, since `Gᵀ G` and
`G Gᵀ` have the same characteristic polynomial. For real `G`, `Gᵀ = Gᴴ`.

The bounds rest on the Rayleigh bound `λ_min(A) |x|² ≤ ⟨x, A x⟩` for a symmetric `A`, obtained by
expanding `x` in an orthonormal eigenbasis, applied to `A = Gᵀ G`, for which `⟨x, A x⟩ = |G x|²`,
and to `A = G Gᵀ`, for which `⟨y, A y⟩ = |Gᵀ y|²`. Full rank makes the relevant product
invertible: `rank(Gᵀ G) = rank G = n` when `n ≤ m`, and `rank(G Gᵀ) = rank G = m` when `m ≤ n`,
so every eigenvalue of that product is nonzero, and it is nonnegative, so `s_min(G) > 0`.

## Main definitions

* `sMin` — the smallest singular value `s_min(G)`.

## Main statements

* `iInf_eigenvalues_mul_dotProduct_le` — the Rayleigh bound for a symmetric matrix.
* `sMin_nonneg`, `sMin_pos` — `s_min(G) ≥ 0`, and `s_min(G) > 0` for full rank.
* `forwardCoercive_of_rank`, `backwardCoercive_of_rank` — Assumption 2.4 in coordinates, with
  `c_G = s_min(G)⁻²`.
* `gCoerciveForward_of_rank`, `gCoerciveBackward_of_rank` — Assumption 2.4 for the operator
  `x ↦ G x`, with `c_G = s_min(G)⁻²`, for `G` of full rank `rank G = min(m, n)`.
* `GX_one`, `GZ_one`, `GU_one` — the coupling operators of the identity matrix are the identity.
* `rank_one_eq_min`, `sMin_one` — the identity matrix has full rank and `s_min(I) = 1`.
-/

open Matrix WithLp
open scoped InnerProductSpace

namespace Dissertation.WellPosedness.System

/-! ### The Rayleigh bound -/

section Rayleigh

variable {k : ℕ}

/-- **The Rayleigh bound**: for a symmetric real matrix `A` with least eigenvalue `λ_min`,
`λ_min |x|² ≤ ⟨x, A x⟩`. -/
theorem iInf_eigenvalues_mul_dotProduct_le {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.IsHermitian)
    (x : Fin k → ℝ) : (⨅ i, hA.eigenvalues i) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  set b := hA.eigenvectorBasis
  set y : EuclideanSpace ℝ (Fin k) := toLp 2 x
  set T := Matrix.toEuclideanLin A
  have hTb : ∀ j, T (b j) = hA.eigenvalues j • b j := fun j =>
    congrArg (toLp 2) (hA.mulVec_eigenvectorBasis j)
  have hTy : T y = ∑ j, (⟪b j, y⟫_ℝ * hA.eigenvalues j) • b j := by
    conv_lhs => rw [← b.sum_repr' y]
    simp only [map_sum, map_smul, hTb, smul_smul]
  have hq : x ⬝ᵥ (A *ᵥ x) = ⟪y, T y⟫_ℝ := by
    change x ⬝ᵥ (A *ᵥ x) = ⟪toLp 2 x, toLp 2 (A *ᵥ x)⟫_ℝ
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
  have hn : x ⬝ᵥ x = ∑ j, ⟪b j, y⟫_ℝ * ⟪b j, y⟫_ℝ := by
    have h1 : x ⬝ᵥ x = ⟪y, y⟫_ℝ := by
      change x ⬝ᵥ x = ⟪toLp 2 x, toLp 2 x⟫_ℝ
      rw [EuclideanSpace.inner_toLp_toLp, star_trivial]
    rw [h1, ← b.sum_inner_mul_inner y y]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm]
  rw [hq, hTy, hn, inner_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [inner_smul_right, real_inner_comm]
  have hle : (⨅ i, hA.eigenvalues i) ≤ hA.eigenvalues j :=
    ciInf_le (Set.finite_range _).bddBelow j
  nlinarith [mul_self_nonneg ⟪b j, y⟫_ℝ]

/-- The least eigenvalue of a positive semidefinite matrix is nonnegative. -/
theorem iInf_eigenvalues_nonneg {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosSemidef) :
    0 ≤ ⨅ i, hA.1.eigenvalues i :=
  Real.iInf_nonneg fun i => hA.eigenvalues_nonneg i

/-- The least eigenvalue of a positive semidefinite matrix of full rank `k ≠ 0` is positive. -/
theorem iInf_eigenvalues_pos {A : Matrix (Fin k) (Fin k) ℝ} (hA : A.PosSemidef)
    (hrank : A.rank = k) (hk : k ≠ 0) : 0 < ⨅ i, hA.1.eigenvalues i := by
  have hne : ∀ i, hA.1.eigenvalues i ≠ 0 := by
    intro i hi
    have hlt := Fintype.card_subtype_lt (p := fun j => hA.1.eigenvalues j ≠ 0) (x := i)
      (not_not.mpr hi)
    rw [← hA.1.rank_eq_card_non_zero_eigs, hrank, Fintype.card_fin] at hlt
    exact lt_irrefl k hlt
  haveI : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun j => hA.1.eigenvalues j)
  rw [← hi]
  exact lt_of_le_of_ne (hA.eigenvalues_nonneg i) (hne i).symm

end Rayleigh

/-! ### The smallest singular value -/

variable {n m : ℕ} (G : Matrix (Fin m) (Fin n) ℝ)

/-- The smallest singular value `s_min(G)` of `G ∈ ℝ^{m×n}`: the square root of the least
eigenvalue of `Gᵀ G` when `n ≤ m`, and of `G Gᵀ` when `m < n`. -/
noncomputable def sMin : ℝ :=
  √(if n ≤ m then ⨅ i, (isHermitian_conjTranspose_mul_self G).eigenvalues i
    else ⨅ i, (isHermitian_mul_conjTranspose_self G).eigenvalues i)

/-- The smallest singular value is nonnegative. -/
theorem sMin_nonneg : 0 ≤ sMin G :=
  Real.sqrt_nonneg _

/-- For `n ≤ m`, `s_min(G)²` is the least eigenvalue of `Gᵀ G`. -/
theorem sMin_sq_of_le (h : n ≤ m) :
    sMin G ^ 2 = ⨅ i, (isHermitian_conjTranspose_mul_self G).eigenvalues i := by
  rw [sMin, if_pos h, Real.sq_sqrt (iInf_eigenvalues_nonneg (posSemidef_conjTranspose_mul_self G))]

/-- For `m ≤ n`, `s_min(G)²` is the least eigenvalue of `G Gᵀ`. -/
theorem sMin_sq_of_ge (h : m ≤ n) :
    sMin G ^ 2 = ⨅ i, (isHermitian_mul_conjTranspose_self G).eigenvalues i := by
  rcases h.lt_or_eq with hlt | heq
  · rw [sMin, if_neg (not_le.mpr hlt),
      Real.sq_sqrt (iInf_eigenvalues_nonneg (posSemidef_self_mul_conjTranspose G))]
  · subst heq
    rw [sMin_sq_of_le G le_rfl,
      ((isHermitian_conjTranspose_mul_self G).eigenvalues_eq_eigenvalues_iff
        (isHermitian_mul_conjTranspose_self G)).mpr (charpoly_mul_comm _ _)]

/-- **`s_min(G) > 0` for `G` of full rank**, `rank G = min(m, n)`, with `m, n ≥ 1`. -/
theorem sMin_pos (hG : G.rank = min m n) (hn : n ≠ 0) (hm : m ≠ 0) : 0 < sMin G := by
  have hsq : 0 < sMin G ^ 2 := by
    rcases le_total n m with h | h
    · rw [sMin_sq_of_le G h]
      exact iInf_eigenvalues_pos (posSemidef_conjTranspose_mul_self G)
        (by rw [rank_conjTranspose_mul_self, hG, min_eq_right h]) hn
    · rw [sMin_sq_of_ge G h]
      exact iInf_eigenvalues_pos (posSemidef_self_mul_conjTranspose G)
        (by rw [rank_self_mul_conjTranspose, hG, min_eq_left h]) hm
  exact lt_of_le_of_ne (sMin_nonneg G) fun h0 => by
    rw [← h0] at hsq
    norm_num at hsq

/-! ### Assumption 2.4 -/

variable {G}

/-- `|x|² ≤ s⁻¹ |v|²` from `s |x|² ≤ |v|²`, `s ≥ 0`, when `s > 0` or `x = 0`. -/
private theorem le_inv_mul_of_mul_le {s a q : ℝ} (hs : 0 ≤ s) (hq : 0 ≤ q) (h : s * a ≤ q)
    (hpos : s = 0 → a = 0) : a ≤ s⁻¹ * q := by
  rcases hs.lt_or_eq with hs | hs
  · rwa [le_inv_mul_iff₀ hs]
  · rw [hpos hs.symm]
    exact mul_nonneg (inv_nonneg.mpr hs.le) hq

/-- **Assumption 2.4, forward branch, from full rank**: for `n ≤ m` and `rank G = n`,
`|x|² ≤ s_min(G)⁻² |G x|²` for every `x ∈ ℝⁿ`. -/
theorem forwardCoercive_of_rank (h : n ≤ m) (hG : G.rank = n) :
    Stability.ForwardCoercive G (sMin G ^ 2)⁻¹ := by
  intro x
  have hx := iInf_eigenvalues_mul_dotProduct_le (isHermitian_conjTranspose_mul_self G) x
  have hq : x ⬝ᵥ ((Gᴴ * G) *ᵥ x) = (G *ᵥ x) ⬝ᵥ (G *ᵥ x) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, conjTranspose_eq_transpose_of_trivial,
      vecMul_transpose]
  rw [hq, ← sMin_sq_of_le G h] at hx
  refine le_inv_mul_of_mul_le (sq_nonneg _) (dotProduct_self_star_nonneg _) hx fun h0 => ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [dotProduct]
  · exact ((pow_pos (sMin_pos G (by rw [hG, min_eq_right h]) hn.ne' (by omega)) 2).ne'
      h0).elim

/-- **Assumption 2.4, backward branch, from full rank**: for `m ≤ n` and `rank G = m`,
`|y|² ≤ s_min(G)⁻² |Gᵀ y|²` for every `y ∈ ℝᵐ`. -/
theorem backwardCoercive_of_rank (h : m ≤ n) (hG : G.rank = m) :
    Stability.BackwardCoercive G (sMin G ^ 2)⁻¹ := by
  intro y
  have hy := iInf_eigenvalues_mul_dotProduct_le (isHermitian_mul_conjTranspose_self G) y
  have hq : y ⬝ᵥ ((G * Gᴴ) *ᵥ y) = (Gᵀ *ᵥ y) ⬝ᵥ (Gᵀ *ᵥ y) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose,
      conjTranspose_eq_transpose_of_trivial]
  rw [hq, ← sMin_sq_of_ge G h] at hy
  refine le_inv_mul_of_mul_le (sq_nonneg _) (dotProduct_self_star_nonneg _) hy fun h0 => ?_
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [dotProduct]
  · exact ((pow_pos (sMin_pos G (by rw [hG, min_eq_left h]) (by omega) hm.ne') 2).ne'
      h0).elim

/-- **Assumption 2.4, forward branch, from full rank**: for `G` of full rank,
`rank G = min(m, n)`, and `n ≤ m`, the operator `x ↦ G x` satisfies `|x|² ≤ c_G |G x|²` with
`c_G = s_min(G)⁻²`. -/
theorem gCoerciveForward_of_rank (hG : G.rank = min m n) (h : n ≤ m) :
    GCoerciveForward (GX G) (sMin G ^ 2)⁻¹ :=
  (gCoerciveForward_GX_iff G _).mpr (forwardCoercive_of_rank h (by rw [hG, min_eq_right h]))

/-- **Assumption 2.4, backward branch, from full rank**: for `G` of full rank,
`rank G = min(m, n)`, and `m ≤ n`, the operator `x ↦ G x` satisfies `|y|² ≤ c_G |Gᵀ y|²` with
`c_G = s_min(G)⁻²`. -/
theorem gCoerciveBackward_of_rank (hG : G.rank = min m n) (h : m ≤ n) :
    GCoerciveBackward (GX G) (sMin G ^ 2)⁻¹ :=
  (gCoerciveBackward_GX_iff G _).mpr (backwardCoercive_of_rank h (by rw [hG, min_eq_left h]))

/-! ### The identity matrix -/

section Identity

open MeasureTheory

variable {E : Type*} [MeasurableSpace E] {n d : ℕ}

/-- The coupling operator of the identity matrix is the identity. -/
theorem GX_one : GX (1 : Matrix (Fin n) (Fin n) ℝ) = ContinuousLinearMap.id ℝ _ := by
  ext x : 1
  rw [← WithLp.toLp_ofLp 2 x, GX_toLp, Matrix.one_mulVec]
  rfl

/-- The coupling operator of the identity matrix on `n × d` matrices is the identity. -/
theorem GZ_one :
    GZ (d := d) (1 : Matrix (Fin n) (Fin n) ℝ) = ContinuousLinearMap.id ℝ _ := by
  ext z : 1
  refine PiLp.ext fun p => ?_
  rw [← toLp_ofLp 2 z, GZ_toLp_apply, Matrix.one_mulVec]
  rfl

variable (ν : Measure E) in
/-- The coupling operator of the identity matrix on `L²(ν; ℝⁿ)` is the identity. -/
theorem GU_one :
    GU (1 : Matrix (Fin n) (Fin n) ℝ) ν = ContinuousLinearMap.id ℝ _ := by
  ext u : 1
  refine Lp.ext ?_
  filter_upwards [coeFn_GU (1 : Matrix (Fin n) (Fin n) ℝ) ν u] with e he
  rw [he, GX_one]
  rfl

/-- The identity matrix has full rank. -/
theorem rank_one_eq_min : (1 : Matrix (Fin n) (Fin n) ℝ).rank = min n n := by
  rw [Matrix.rank_one, Fintype.card_fin, min_self]

/-- **`s_min(I) = 1`** for the identity matrix of size `n ≥ 1`: every eigenvalue of `Iᵀ I = I`
lies in the spectrum `{1}`. -/
theorem sMin_one [NeZero n] : sMin (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  have h : ∀ i,
      (isHermitian_conjTranspose_mul_self (1 : Matrix (Fin n) (Fin n) ℝ)).eigenvalues i = 1 := by
    intro i
    have hs : spectrum ℝ ((1 : Matrix (Fin n) (Fin n) ℝ)ᴴ * 1) = {1} := by
      rw [conjTranspose_one, one_mul, spectrum.one_eq]
    have hi := (isHermitian_conjTranspose_mul_self
      (1 : Matrix (Fin n) (Fin n) ℝ)).eigenvalues_mem_spectrum_real i
    rw [hs] at hi
    exact hi
  rw [sMin, if_pos le_rfl]
  simp only [h, ciInf_const, Real.sqrt_one]

end Identity

end Dissertation.WellPosedness.System
