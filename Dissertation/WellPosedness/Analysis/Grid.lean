/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The uniform time grid

The uniform grid `t_i = i τ`, `τ = T / N`, of the horizon `[0, T]` has the cells
`[t_i, t_{i+1}]`, `0 ≤ i < N`. The cells cover `[0, T]` and overlap only at the nodes, so a lower
Lebesgue integral over `[0, T]` is the sum of those over the cells.

## Main definitions

* `gridPt T N i` — the node `t_i = i T / N`.

## Main statements

* `Icc_gridPt_subset` — each cell lies in the horizon.
* `sum_setLIntegral_Icc_mul` — the lower integral over `[0, N τ]` is the sum over the cells
  `[i τ, (i + 1) τ]`.
* `sum_setLIntegral_cells` — the lower integral over `[0, T]` is the sum over the grid cells.
-/

open MeasureTheory
open scoped ENNReal

namespace Dissertation.WellPosedness

/-- The node `t_i = i T / N` of the uniform grid with `N` steps on the horizon `[0, T]`. -/
noncomputable def gridPt (T : ℝ) (N i : ℕ) : ℝ := i * (T / N)

variable {T : ℝ} {N i : ℕ}

theorem gridPt_zero (T : ℝ) (N : ℕ) : gridPt T N 0 = 0 := by simp [gridPt]

theorem gridPt_self (T : ℝ) {N : ℕ} (hN : N ≠ 0) : gridPt T N N = T := by
  unfold gridPt
  field_simp

theorem gridPt_succ (T : ℝ) (N i : ℕ) : gridPt T N (i + 1) = gridPt T N i + T / N := by
  simp only [gridPt, Nat.cast_add, Nat.cast_one]
  ring

theorem gridPt_succ_sub (T : ℝ) (N i : ℕ) : gridPt T N (i + 1) - gridPt T N i = T / N := by
  rw [gridPt_succ]
  ring

theorem gridPt_nonneg (hT : 0 ≤ T) (N i : ℕ) : 0 ≤ gridPt T N i :=
  mul_nonneg (Nat.cast_nonneg i) (div_nonneg hT (Nat.cast_nonneg N))

theorem gridPt_mono (hT : 0 ≤ T) (N : ℕ) {i j : ℕ} (hij : i ≤ j) : gridPt T N i ≤ gridPt T N j :=
  mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (div_nonneg hT (Nat.cast_nonneg N))

theorem gridPt_le (hT : 0 ≤ T) (hi : i ≤ N) : gridPt T N i ≤ T := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [gridPt, hT]
  · calc gridPt T N i ≤ gridPt T N N := gridPt_mono hT N hi
      _ = T := gridPt_self T hN.ne'

/-- Each cell `[t_i, t_{i+1}]`, `i < N`, lies in the horizon `[0, T]`. -/
theorem Icc_gridPt_subset (hT : 0 ≤ T) (hi : i < N) :
    Set.Icc (gridPt T N i) (gridPt T N (i + 1)) ⊆ Set.Icc 0 T :=
  Set.Icc_subset_Icc (gridPt_nonneg hT N i) (gridPt_le hT hi)

/-- The Lebesgue measure of a cell is the step `T / N`. -/
theorem volume_Icc_gridPt (T : ℝ) (N i : ℕ) :
    volume (Set.Icc (gridPt T N i) (gridPt T N (i + 1))) = ENNReal.ofReal (T / N) := by
  rw [Real.volume_Icc, gridPt_succ_sub]

/-- **The cells cover the horizon**: for `τ ≥ 0`, the lower integral over `[0, N τ]` is the sum
of those over the cells `[i τ, (i + 1) τ]`, `i < N`. -/
theorem sum_setLIntegral_Icc_mul {τ : ℝ} (hτ : 0 ≤ τ) (f : ℝ → ℝ≥0∞) (N : ℕ) :
    ∑ i ∈ Finset.range N, ∫⁻ s in Set.Icc ((i : ℝ) * τ) ((i + 1 : ℕ) * τ), f s
      = ∫⁻ s in Set.Icc (0 : ℝ) (N * τ), f s := by
  have hIco : ∀ a b : ℝ, ∫⁻ s in Set.Icc a b, f s = ∫⁻ s in Set.Ico a b, f s := fun a b =>
    (setLIntegral_congr Ico_ae_eq_Icc).symm
  simp_rw [hIco]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, ← lintegral_union measurableSet_Ico]
    · rw [Set.Ico_union_Ico_eq_Ico (mul_nonneg (Nat.cast_nonneg N) hτ)
        (mul_le_mul_of_nonneg_right (by norm_num) hτ)]
    · exact Set.Ico_disjoint_Ico_same

/-- **The grid cells cover the horizon**: for `T ≥ 0` and `N ≥ 1`, the lower integral over
`[0, T]` is the sum of those over the cells `[t_i, t_{i+1}]`, `i < N`. -/
theorem sum_setLIntegral_cells (hT : 0 ≤ T) (hN : N ≠ 0) (f : ℝ → ℝ≥0∞) :
    ∑ i ∈ Finset.range N, ∫⁻ s in Set.Icc (gridPt T N i) (gridPt T N (i + 1)), f s
      = ∫⁻ s in Set.Icc (0 : ℝ) T, f s := by
  have h := sum_setLIntegral_Icc_mul (div_nonneg hT (Nat.cast_nonneg N)) f N
  rw [show (N : ℝ) * (T / N) = T by field_simp] at h
  exact h

end Dissertation.WellPosedness
