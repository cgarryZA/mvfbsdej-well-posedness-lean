/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# A scalar Riccati equation

For `c, α ≥ 0` the scalar Riccati equation `a' = α − c a²`, `a(0) = 1`, has on `u ≥ 0` the
solution `a = y / w`, where `(y, w)` solves the linear system `y' = α w`, `w' = c y`,
`y(0) = w(0) = 1`. With `k = √(c α)` and `shc(k, u) = sinh(k u) / k`, extended by
`shc(0, u) = u`,

`y(u) = cosh(k u) + α shc(k, u)`, `w(u) = cosh(k u) + c shc(k, u)`.

The formula is uniform in `c, α ≥ 0`, including the degenerate cases `c α = 0`. Both `y` and `w`
are smooth on `ℝ` and at least `1` on `u ≥ 0`, so `a` is positive there and has a two-sided
derivative at every `u ≥ 0`, including `u = 0`.

## Main definitions

* `Riccati.shc` — `sinh(k u) / k`, extended by `u` at `k = 0`.
* `Riccati.num`, `Riccati.den` — the solution `(y, w)` of the linear system.
* `Riccati.sol` — the quotient `a = y / w`.

## Main statements

* `Riccati.hasDerivAt_num`, `Riccati.hasDerivAt_den` — `y' = α w` and `w' = c y`.
* `Riccati.hasDerivAt_sol` — `a' = α − c a²` at every `u ≥ 0`.
* `Riccati.sol_zero`, `Riccati.sol_pos` — `a(0) = 1`, and `a > 0` on `u ≥ 0`.
* `Riccati.contDiff_num`, `Riccati.contDiff_den`, `Riccati.one_le_den` — `y` and `w` are smooth,
  and `w ≥ 1` on `u ≥ 0`.
-/

open Real

namespace Dissertation.WellPosedness.Riccati

/-- `sinh(k u) / k`, extended by `u` at `k = 0`. -/
noncomputable def shc (k u : ℝ) : ℝ := if k = 0 then u else sinh (k * u) / k

theorem shc_zero_right (k : ℝ) : shc k 0 = 0 := by
  unfold shc
  split_ifs <;> simp

/-- The derivative of `shc(k, ·)` is `cosh(k ·)`. -/
theorem hasDerivAt_shc (k u : ℝ) : HasDerivAt (shc k) (cosh (k * u)) u := by
  by_cases hk : k = 0
  · subst hk
    have : shc 0 = id := funext fun u => by simp [shc]
    rw [this]
    simpa using hasDerivAt_id u
  · have : shc k = fun u => sinh (k * u) / k := funext fun u => by simp [shc, hk]
    rw [this]
    refine ((((hasDerivAt_id u).const_mul k).sinh).div_const k).congr_deriv ?_
    simp only [id_eq, mul_one]
    field_simp

/-- The derivative of `cosh(k ·)` is `k² shc(k, ·)`. -/
theorem hasDerivAt_cosh_mul (k u : ℝ) :
    HasDerivAt (fun u => cosh (k * u)) (k ^ 2 * shc k u) u := by
  refine ((hasDerivAt_id u).const_mul k).cosh.congr_deriv ?_
  by_cases hk : k = 0
  · simp [hk]
  · simp only [shc, hk, if_false, id_eq, mul_one]
    field_simp

theorem shc_nonneg {k u : ℝ} (hk : 0 ≤ k) (hu : 0 ≤ u) : 0 ≤ shc k u := by
  unfold shc
  split_ifs
  · exact hu
  · exact div_nonneg (sinh_nonneg_iff.2 (mul_nonneg hk hu)) hk

theorem contDiff_shc (k : ℝ) {N : WithTop ℕ∞} : ContDiff ℝ N (shc k) := by
  by_cases hk : k = 0
  · have : shc k = id := funext fun u => by simp [shc, hk]
    rw [this]
    exact contDiff_id
  · have : shc k = fun u => sinh (k * u) / k := funext fun u => by simp [shc, hk]
    rw [this]
    exact (contDiff_sinh.comp (contDiff_const.mul contDiff_id)).div_const k

/-- The component `y(u) = cosh(√(c α) u) + α shc(√(c α), u)` of the linear system
`y' = α w`, `w' = c y`, `y(0) = w(0) = 1`. -/
noncomputable def num (c α u : ℝ) : ℝ := cosh (√(c * α) * u) + α * shc √(c * α) u

/-- The component `w(u) = cosh(√(c α) u) + c shc(√(c α), u)` of the linear system
`y' = α w`, `w' = c y`, `y(0) = w(0) = 1`. -/
noncomputable def den (c α u : ℝ) : ℝ := cosh (√(c * α) * u) + c * shc √(c * α) u

/-- The quotient `a = y / w`, a solution on `u ≥ 0` of the scalar Riccati equation
`a' = α − c a²`, `a(0) = 1`. -/
noncomputable def sol (c α u : ℝ) : ℝ := num c α u / den c α u

variable {c α : ℝ}

theorem hasDerivAt_num (hc : 0 ≤ c) (hα : 0 ≤ α) (u : ℝ) :
    HasDerivAt (num c α) (α * den c α u) u := by
  refine ((hasDerivAt_cosh_mul √(c * α) u).fun_add
    ((hasDerivAt_shc √(c * α) u).const_mul α)).congr_deriv ?_
  rw [sq_sqrt (mul_nonneg hc hα), den]
  ring

theorem hasDerivAt_den (hc : 0 ≤ c) (hα : 0 ≤ α) (u : ℝ) :
    HasDerivAt (den c α) (c * num c α u) u := by
  refine ((hasDerivAt_cosh_mul √(c * α) u).fun_add
    ((hasDerivAt_shc √(c * α) u).const_mul c)).congr_deriv ?_
  rw [sq_sqrt (mul_nonneg hc hα), num]
  ring

theorem contDiff_num {N : WithTop ℕ∞} : ContDiff ℝ N (num c α) :=
  (contDiff_cosh.comp (contDiff_const.mul contDiff_id)).add (contDiff_const.mul (contDiff_shc _))

theorem contDiff_den {N : WithTop ℕ∞} : ContDiff ℝ N (den c α) :=
  (contDiff_cosh.comp (contDiff_const.mul contDiff_id)).add (contDiff_const.mul (contDiff_shc _))

theorem one_le_num (hα : 0 ≤ α) {u : ℝ} (hu : 0 ≤ u) : 1 ≤ num c α u := by
  have := one_le_cosh (√(c * α) * u)
  have := mul_nonneg hα (shc_nonneg (sqrt_nonneg (c * α)) hu)
  unfold num
  linarith

theorem one_le_den (hc : 0 ≤ c) {u : ℝ} (hu : 0 ≤ u) : 1 ≤ den c α u := by
  have := one_le_cosh (√(c * α) * u)
  have := mul_nonneg hc (shc_nonneg (sqrt_nonneg (c * α)) hu)
  unfold den
  linarith

theorem sol_zero : sol c α 0 = 1 := by
  simp [sol, num, den, shc_zero_right]

theorem sol_pos (hc : 0 ≤ c) (hα : 0 ≤ α) {u : ℝ} (hu : 0 ≤ u) : 0 < sol c α u :=
  div_pos (zero_lt_one.trans_le (one_le_num hα hu)) (zero_lt_one.trans_le (one_le_den hc hu))

/-- **The scalar Riccati equation**: `a' = α − c a²` at every `u ≥ 0`. -/
theorem hasDerivAt_sol (hc : 0 ≤ c) (hα : 0 ≤ α) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (sol c α) (α - c * sol c α u ^ 2) u := by
  have hd : den c α u ≠ 0 := (zero_lt_one.trans_le (one_le_den hc hu)).ne'
  refine ((hasDerivAt_num hc hα u).div (hasDerivAt_den hc hα u) hd).congr_deriv ?_
  unfold sol
  field_simp

end Dissertation.WellPosedness.Riccati
