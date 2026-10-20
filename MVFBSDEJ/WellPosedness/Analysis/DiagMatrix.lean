/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The diagonal matrix of full rank

The `m × n` matrix `G` with ones on the diagonal `i = j` and zeros elsewhere satisfies
`G Gᵀ = 1` when `m ≤ n` and `Gᵀ G = 1` when `n ≤ m`, so it has rank `min(m, n)`.

## Main definitions

* `diagMatrix m n` — the `m × n` matrix with ones on the diagonal.

## Main statements

* `diagMatrix_mul_transpose`, `transpose_mul_diagMatrix` — `G Gᵀ = 1` for `m ≤ n`, `Gᵀ G = 1`
  for `n ≤ m`.
* `rank_diagMatrix` — `rank G = min(m, n)`.
-/

namespace MVFBSDEJ.WellPosedness

/-- The `m × n` matrix with ones on the diagonal `i = j` and zeros elsewhere. -/
def diagMatrix (m n : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = j then 1 else 0

/-- For `m ≤ n`, `G Gᵀ = 1` for the diagonal matrix `G`. -/
theorem diagMatrix_mul_transpose {m n : ℕ} (h : m ≤ n) :
    diagMatrix m n * (diagMatrix m n).transpose = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, diagMatrix, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨i, lt_of_lt_of_le i.isLt h⟩ : Fin n)]
  · by_cases hik : i = k
    · subst hik; simp
    · have : (k : ℕ) ≠ i := fun h' => hik (Fin.ext h'.symm)
      simp [hik, this]
  · intro j _ hj
    have : (i : ℕ) ≠ j := fun h' => hj (Fin.ext h'.symm)
    simp [this]
  · simp

/-- For `n ≤ m`, `Gᵀ G = 1` for the diagonal matrix `G`. -/
theorem transpose_mul_diagMatrix {m n : ℕ} (h : n ≤ m) :
    (diagMatrix m n).transpose * diagMatrix m n = 1 := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, diagMatrix, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨j, lt_of_lt_of_le j.isLt h⟩ : Fin m)]
  · by_cases hjk : j = k
    · subst hjk; simp
    · have : (j : ℕ) ≠ k := fun h' => hjk (Fin.ext h')
      simp [hjk, this]
  · intro i _ hi
    have : (i : ℕ) ≠ j := fun h' => hi (Fin.ext h')
    simp [this]
  · simp

/-- The diagonal matrix has full rank `min(m, n)`. -/
theorem rank_diagMatrix (m n : ℕ) :
    (diagMatrix m n).rank = min m n := by
  refine le_antisymm (le_min (Matrix.rank_le_height _) (Matrix.rank_le_width _)) ?_
  rcases le_total m n with h | h
  · rw [min_eq_left h]
    have := Matrix.rank_mul_le_left (diagMatrix m n) (diagMatrix m n).transpose
    rwa [diagMatrix_mul_transpose h, Matrix.rank_one, Fintype.card_fin] at this
  · rw [min_eq_right h]
    have := Matrix.rank_mul_le_left (diagMatrix m n).transpose (diagMatrix m n)
    rwa [transpose_mul_diagMatrix h, Matrix.rank_one, Fintype.card_fin,
      Matrix.rank_transpose] at this

end MVFBSDEJ.WellPosedness
