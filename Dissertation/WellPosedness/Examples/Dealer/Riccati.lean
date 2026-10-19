/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Riccati function of the dealer market

For `β₁, β₂ > 0` and `T > 0`, the Riccati equation `p' = β₁ p² − β₂` with `p(T) = 1` has the
solution

`p(t) = k (A e^{2 a (T − t)} + B) / (A e^{2 a (T − t)} − B)`,

`k = √(β₂ / β₁)`, `a = β₁ k`, `A = 1 + k`, `B = 1 − k`, which is positive on `[0, T]`; any two
solutions on `[0, T]` with the same terminal value agree there, the vector field
`x ↦ β₁ x² − β₂` being Lipschitz on bounded sets.

## Main statements

* `exists_pos_riccati` — the positive solution.
* `riccati_unique` — uniqueness on `[0, T]`.
-/

open Set Filter Topology

namespace Dissertation.WellPosedness.Existence

/-- **The positive Riccati function.** For `β₁, β₂, T > 0` there is `p` with
`p' = β₁ p² − β₂` at every `t ∈ [0, T]`, `p(T) = 1` and `p > 0` on `[0, T]`. -/
theorem exists_pos_riccati {β₁ β₂ T : ℝ} (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) :
    ∃ p : ℝ → ℝ, (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt p (β₁ * p t ^ 2 - β₂) t) ∧ p T = 1
      ∧ ∀ t ∈ Icc (0 : ℝ) T, 0 < p t := by
  set k := Real.sqrt (β₂ / β₁) with hk
  have hk0 : 0 < k := Real.sqrt_pos.mpr (div_pos hβ₂ hβ₁)
  have hk2 : β₂ = β₁ * k ^ 2 := by
    rw [hk, Real.sq_sqrt (div_pos hβ₂ hβ₁).le]
    field_simp
  set a := β₁ * k with ha
  set E : ℝ → ℝ := fun t => Real.exp (2 * a * (T - t)) with hE
  have hE1 : ∀ t ≤ T, 1 ≤ E t := fun t ht =>
    Real.one_le_exp (mul_nonneg (by positivity) (sub_nonneg.mpr ht))
  have hEd : ∀ t, HasDerivAt E (E t * (2 * a * (-1))) t := fun t => by
    have h := ((hasDerivAt_id t).const_sub T).const_mul (2 * a)
    simpa [hE, mul_comm] using h.exp
  set p : ℝ → ℝ := fun t => k * ((1 + k) * E t + (1 - k)) / ((1 + k) * E t - (1 - k)) with hp
  have hden : ∀ t ≤ T, 0 < (1 + k) * E t - (1 - k) := fun t ht => by
    nlinarith [hE1 t ht]
  have hnum : ∀ t ≤ T, 0 < (1 + k) * E t + (1 - k) := fun t ht => by
    nlinarith [hE1 t ht]
  refine ⟨p, fun t ht => ?_, ?_, fun t ht => ?_⟩
  · have hd := hden t ht.2
    have hN := (((hEd t).const_mul (1 + k)).add_const (1 - k)).const_mul k
    have hM := ((hEd t).const_mul (1 + k)).sub_const (1 - k)
    have h := hN.div hM hd.ne'
    refine h.congr_deriv ?_
    simp only [hp]
    rw [hk2, ha]
    field_simp
    ring
  · have hET : E T = 1 := by simp [hE]
    simp only [hp, hET]
    field_simp [hk0.ne']
    ring
  · exact div_pos (mul_pos hk0 (hnum t ht.2)) (hden t ht.2)

/-- **The Riccati function is unique.** Two functions `p, q` with `p' = β₁ p² − β₂` and
`q' = β₁ q² − β₂` at every `t ∈ [0, T]` and `p(T) = q(T)` agree on `[0, T]`. -/
theorem riccati_unique {β₁ β₂ T : ℝ} (hβ₁ : 0 ≤ β₁) {p q : ℝ → ℝ}
    (hp : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt p (β₁ * p t ^ 2 - β₂) t)
    (hq : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt q (β₁ * q t ^ 2 - β₂) t) (hT : p T = q T) :
    ∀ t ∈ Icc (0 : ℝ) T, p t = q t := by
  have hpc : ContinuousOn p (Icc (0 : ℝ) T) := fun t ht => (hp t ht).continuousAt.continuousWithinAt
  have hqc : ContinuousOn q (Icc (0 : ℝ) T) := fun t ht => (hq t ht).continuousAt.continuousWithinAt
  obtain ⟨Mp, hMp⟩ := isCompact_Icc.exists_bound_of_continuousOn hpc
  obtain ⟨Mq, hMq⟩ := isCompact_Icc.exists_bound_of_continuousOn hqc
  set M : ℝ := max (max Mp Mq) 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hpM : ∀ t ∈ Icc (0 : ℝ) T, p t ∈ Icc (-M) M := fun t ht => by
    have h := (hMp t ht).trans ((le_max_left Mp Mq).trans (le_max_left _ 0))
    rw [Real.norm_eq_abs] at h
    exact abs_le.mp h
  have hqM : ∀ t ∈ Icc (0 : ℝ) T, q t ∈ Icc (-M) M := fun t ht => by
    have h := (hMq t ht).trans ((le_max_right Mp Mq).trans (le_max_left _ 0))
    rw [Real.norm_eq_abs] at h
    exact abs_le.mp h
  have hLip : ∀ t ∈ Ioc (0 : ℝ) T,
      LipschitzOnWith ⟨2 * β₁ * M, by positivity⟩ (fun x : ℝ => β₁ * x ^ 2 - β₂) (Icc (-M) M) := by
    intro t _
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    simp only [Real.dist_eq, NNReal.coe_mk]
    have e : β₁ * x ^ 2 - β₂ - (β₁ * y ^ 2 - β₂) = β₁ * (x + y) * (x - y) := by ring
    rw [e, abs_mul, abs_mul, abs_of_nonneg hβ₁]
    have hxy : |x + y| ≤ 2 * M := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    calc β₁ * |x + y| * |x - y| ≤ β₁ * (2 * M) * |x - y| := by gcongr
      _ = 2 * β₁ * M * |x - y| := by ring
  have h := ODE_solution_unique_of_mem_Icc_left (v := fun _ x => β₁ * x ^ 2 - β₂)
    (s := fun _ => Icc (-M) M) hLip hpc
    (fun t ht => (hp t (Ioc_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hpM t (Ioc_subset_Icc_self ht)) hqc
    (fun t ht => (hq t (Ioc_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => hqM t (Ioc_subset_Icc_self ht)) hT
  exact fun t ht => h ht

end Dissertation.WellPosedness.Existence
