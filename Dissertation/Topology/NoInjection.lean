/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Continuous injections into spaces of smaller dimension

This file shows that there is no continuous injection from `ℝ^(k+1)` into `ℝ^k`, and that
consequently finitely many continuous real functions never separate the points of an
infinite-dimensional real normed space.

## Main statements

* `Dissertation.Topology.not_contDiffOn_retraction`: there is no `C¹` retraction of the closed
  unit ball of a finite-dimensional real inner product space onto the unit sphere.
* `Dissertation.Topology.exists_eq_zero_of_contDiff`: a `C¹` self-map `φ` of a
  finite-dimensional real inner product space with `‖φ x - x‖ < 1` on the closed unit ball has a
  zero in the closed unit ball.
* `Dissertation.Topology.not_injective_of_finrank_lt`: a continuous map from a
  finite-dimensional real inner product space to one of strictly smaller dimension is not
  injective.
* `Dissertation.Topology.not_injective_of_continuous`: a continuous map
  `EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin k)` is not injective.
* `Dissertation.Topology.not_injective_of_continuous_of_infinite_dimensional`: a continuous map
  from an infinite-dimensional real normed space to `Fin k → ℝ` is not injective.

## Implementation notes

The absence of a `C¹` retraction `r` follows from the change of variables formula: for small
`t ≥ 0` the map `x ↦ x + t • (r x - x)` is a bijection of the open unit ball, so the integral of
`det (1 + t • (Dr x - 1))` over the ball equals its volume. This integrand is a polynomial of
degree at most the dimension in `t`, hence by Lagrange interpolation its value at `t = 1` is an
affine combination of its values at small `t`; but `det (Dr x)` vanishes because `r` takes values
in the sphere.

A `C¹` map `φ` with `‖φ x - x‖ < 1` and no zero in the ball yields a `C¹` retraction, sending
`x` to the point where the ray from `x` in the direction of `φ x` meets the sphere.

Given a continuous injection `F : E → Y` with `finrank ℝ Y < finrank ℝ E`, the Stone-Weierstrass
theorem gives a `C¹` map `G : Y → E` with `G ∘ F` uniformly close to the identity on the closed
unit ball, and a `C¹` map `F'` uniformly close to `F` there. The range of `G` has dense
complement, so for a small vector `v` outside it the map `G ∘ F' - v` contradicts the previous
statement.
-/

open Metric Set MeasureTheory Filter Topology Polynomial Module
open scoped RealInnerProductSpace

namespace Dissertation.Topology

/-! ### Determinants of perturbations of the identity -/

section Determinant

/-- The determinant of `X • M + 1` evaluated at `s` is the determinant of `s • M + 1`. -/
theorem eval_det_X_smul_add_one {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (s : ℝ) :
    (Matrix.det ((X : ℝ[X]) • M.map C + (1 : Matrix (Fin N) (Fin N) ℝ).map C)).eval s =
      Matrix.det (s • M + 1) := by
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply]
  split_ifs <;> simp [mul_comm]

/-- For an endomorphism `L` of a finite-dimensional real vector space and pairwise distinct nodes
`t 0, …, t N`, where `N` is the dimension, `det (1 + L)` is the combination of the values
`det (1 + t j • L)` with the Lagrange weights of the nodes at `1`. -/
theorem det_one_add_eq_sum {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (t : Fin (finrank ℝ V + 1) → ℝ) (ht : Function.Injective t) (L : V →ₗ[ℝ] V) :
    LinearMap.det (1 + L) =
      ∑ j, (Lagrange.basis Finset.univ t j).eval 1 * LinearMap.det (1 + t j • L) := by
  set b := Module.finBasis ℝ V
  set M := LinearMap.toMatrix b b L
  set P : ℝ[X] := Matrix.det ((X : ℝ[X]) • M.map C + (1 : Matrix _ _ ℝ).map C) with hPdef
  have hP : ∀ s : ℝ, P.eval s = LinearMap.det (1 + s • L) := by
    intro s
    rw [hPdef, eval_det_X_smul_add_one, ← LinearMap.det_toMatrix b, map_add, map_smul,
      LinearMap.toMatrix_one, add_comm]
  have hdeg : P.degree < (Finset.univ : Finset (Fin (finrank ℝ V + 1))).card := by
    have h1 := natDegree_det_X_add_C_le M (1 : Matrix _ _ ℝ)
    rw [Fintype.card_fin] at h1
    rw [Finset.card_univ, Fintype.card_fin]
    refine (degree_le_natDegree).trans_lt ?_
    exact_mod_cast Nat.lt_succ_of_le h1
  have hI := Lagrange.eq_interpolate (s := Finset.univ) (Set.injOn_of_injective ht) hdeg
  have h1 := congrArg (Polynomial.eval 1) hI
  rw [Lagrange.interpolate_apply, eval_finsetSum] at h1
  rw [← one_smul ℝ L, ← hP 1]
  simp only [one_smul]
  rw [h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, hP, mul_comm]

/-- The Lagrange weights at `1` of pairwise distinct nodes sum to `1`. -/
theorem sum_eval_basis_one {N : ℕ} (t : Fin (N + 1) → ℝ) (ht : Function.Injective t) :
    ∑ j, (Lagrange.basis Finset.univ t j).eval 1 = 1 := by
  rw [← eval_finsetSum, Lagrange.sum_basis (Set.injOn_of_injective ht) Finset.univ_nonempty,
    eval_one]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- If `r` takes values in the unit sphere on an open set `U`, then its derivative at a point of
`U` has zero determinant. -/
theorem det_fderiv_eq_zero_of_norm_eq_one {r : E → E} {U : Set E} (hU : IsOpen U)
    {x : E} (hx : x ∈ U) {A : E →L[ℝ] E} (hA : HasFDerivAt r A x)
    (hnorm : ∀ y ∈ U, ‖r y‖ = 1) : A.det = 0 := by
  have h1 : HasFDerivAt (fun y => ‖r y‖ ^ 2) (2 • (innerSL ℝ (r x)).comp A) x := hA.norm_sq
  have h2 : HasFDerivAt (fun y => ‖r y‖ ^ 2) (0 : E →L[ℝ] ℝ) x := by
    refine (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hx] with y hy
    simp [hnorm y hy]
  have h3 := h1.unique h2
  by_contra hne
  rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
    LinearMap.ker_eq_bot, LinearMap.injective_iff_surjective] at hne
  obtain ⟨h, hh⟩ := hne (r x)
  have h4 : ⟪r x, A h⟫ = 0 := by
    simpa using congrArg (fun L : E →L[ℝ] ℝ => L h) h3
  have h5 : A h = r x := hh
  rw [h5, real_inner_self_eq_norm_sq, hnorm x hx] at h4
  norm_num at h4

/-- The determinant of `1 + B` is nonzero when `‖B‖ < 1`. -/
theorem det_one_add_ne_zero {B : E →L[ℝ] E} (hB : ‖B‖ < 1) : (1 + B).det ≠ 0 := by
  intro hdet
  rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot] at hdet
  obtain ⟨h, hh, hne⟩ := (Submodule.ne_bot_iff _).mp hdet
  have h1 : h + B h = 0 := hh
  have h2 : ‖h‖ ≤ ‖B‖ * ‖h‖ := by
    calc ‖h‖ = ‖B h‖ := by rw [← norm_neg (B h), ← eq_neg_of_add_eq_zero_left h1]
      _ ≤ ‖B‖ * ‖h‖ := B.le_opNorm h
  have h3 : ‖h‖ = 0 := by nlinarith [norm_nonneg h, norm_nonneg B]
  exact hne (norm_eq_zero.mp h3)

/-- The determinant of `1 + t • B` is positive when `0 ≤ t` and `t * ‖B‖ < 1`. -/
theorem det_one_add_smul_pos {B : E →L[ℝ] E} {t : ℝ} (ht : 0 ≤ t) (htB : t * ‖B‖ < 1) :
    0 < (1 + t • B).det := by
  by_contra hneg
  push Not at hneg
  have hc : ContinuousOn (fun s : ℝ => (1 + s • B).det) (Icc 0 t) :=
    (ContinuousLinearMap.continuous_det.comp (by fun_prop)).continuousOn
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' ht hc ⟨hneg, by
    simp only [zero_smul, add_zero, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_one,
      map_one, zero_le_one]⟩
  refine det_one_add_ne_zero ?_ hs0
  rw [norm_smul, Real.norm_of_nonneg hs.1]
  calc s * ‖B‖ ≤ t * ‖B‖ := by gcongr; exact hs.2
    _ < 1 := htB

end Determinant

/-! ### The closed unit ball does not retract onto the unit sphere -/

section Retraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If `g` is `M`-Lipschitz on the closed unit ball and vanishes on the unit sphere, then
`‖g x‖ ≤ M * ‖x - y‖` for `x` in the closed ball and `y` outside it. -/
theorem norm_le_of_lipschitzOn_closedBall {g : E → E} {M : ℝ}
    (hg : ∀ x ∈ closedBall (0 : E) 1, ∀ y ∈ closedBall (0 : E) 1, ‖g y - g x‖ ≤ M * ‖y - x‖)
    (hM : 0 ≤ M) (hs : ∀ z ∈ sphere (0 : E) 1, g z = 0) {x y : E} (hx : ‖x‖ ≤ 1)
    (hy : 1 < ‖y‖) : ‖g x‖ ≤ M * ‖x - y‖ := by
  obtain ⟨s, hs01, hs1⟩ : ∃ s ∈ Icc (0 : ℝ) 1, ‖x + s • (y - x)‖ = 1 := by
    have hc : ContinuousOn (fun s : ℝ => ‖x + s • (y - x)‖) (Icc 0 1) := by fun_prop
    exact intermediate_value_Icc zero_le_one hc ⟨by simpa using hx, by simpa using hy.le⟩
  set z := x + s • (y - x) with hzdef
  have hz : z ∈ sphere (0 : E) 1 := by simpa using hs1
  have h1 := hg x (by simpa using hx) z (sphere_subset_closedBall hz)
  rw [hs z hz, zero_sub, norm_neg] at h1
  calc ‖g x‖ ≤ M * ‖z - x‖ := h1
    _ = M * (s * ‖x - y‖) := by
        rw [hzdef, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs01.1, norm_sub_rev]
    _ ≤ M * ‖x - y‖ := by
        gcongr
        nlinarith [hs01.2, norm_nonneg (x - y)]

variable [FiniteDimensional ℝ E]

/-- Let `w` be `M`-Lipschitz, vanish outside the open unit ball, and satisfy `‖x + w x‖ ≤ 1` on
it. If `0 ≤ t` and `t * M ≤ 1 / 2`, then `x ↦ x + t • w x` is injective and maps the open unit
ball onto itself. -/
theorem image_ball_eq_and_injective {w : E → E} {M t : ℝ} (ht : 0 ≤ t) (htM : t * M ≤ 1 / 2)
    (hM : 1 ≤ M) (hlip : ∀ x y, ‖w x - w y‖ ≤ M * ‖x - y‖) (hw : ∀ x, 1 ≤ ‖x‖ → w x = 0)
    (hball : ∀ x ∈ ball (0 : E) 1, ‖x + w x‖ ≤ 1) :
    (fun x => x + t • w x) '' ball (0 : E) 1 = ball (0 : E) 1 ∧
      Function.Injective (fun x => x + t • w x) := by
  have ht1 : t < 1 := by nlinarith
  refine ⟨Subset.antisymm ?_ ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    rw [mem_ball_zero_iff]
    calc ‖x + t • w x‖ = ‖(1 - t) • x + t • (x + w x)‖ := by
          congr 1
          rw [smul_add, sub_smul, one_smul]
          abel
      _ ≤ (1 - t) * ‖x‖ + t * ‖x + w x‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg ht]
      _ < 1 := by nlinarith [hball x hx, norm_nonneg (x + w x)]
  · intro y hy
    have hy' : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
    set T : E → E := fun z => y - t • w z with hTdef
    have hK : Real.toNNReal (t * M) < 1 := by
      rw [Real.toNNReal_lt_one]
      linarith
    have hT : ContractingWith (Real.toNNReal (t * M)) T := by
      refine ⟨hK, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
      simp only [hTdef, dist_eq_norm]
      rw [sub_sub_sub_cancel_left, ← smul_sub, norm_smul, Real.norm_of_nonneg ht,
        Real.coe_toNNReal _ (by positivity), mul_assoc]
      gcongr
      rw [norm_sub_rev a b]
      exact hlip b a
    set z := ContractingWith.fixedPoint T hT
    have hz : T z = z := ContractingWith.fixedPoint_isFixedPt (f := T) hT
    have hfz : z + t • w z = y := by
      have h' : y - t • w z = z := hz
      rw [sub_eq_iff_eq_add] at h'
      exact h'.symm
    have hzb : ‖z‖ < 1 := by
      by_contra hcon
      push Not at hcon
      rw [hw z hcon, smul_zero, add_zero] at hfz
      rw [hfz] at hcon
      linarith
    exact ⟨z, mem_ball_zero_iff.mpr hzb, hfz⟩
  · intro x y hxy
    have h1 : x - y = t • (w y - w x) := by
      have : x + t • w x = y + t • w y := hxy
      rw [smul_sub]
      linear_combination (norm := module) this
    have h2 : ‖x - y‖ ≤ t * M * ‖x - y‖ := by
      calc ‖x - y‖ = t * ‖w y - w x‖ := by rw [h1, norm_smul, Real.norm_of_nonneg ht]
        _ ≤ t * (M * ‖y - x‖) := by gcongr; exact hlip y x
        _ = t * M * ‖x - y‖ := by rw [norm_sub_rev]; ring
    have h3 : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h3)

/-- There is no `C¹` map from a neighbourhood of the closed unit ball to the unit sphere which
restricts to the identity on the sphere. -/
theorem not_contDiffOn_retraction [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {r : E → E} {U : Set E} (hU : IsOpen U)
    (hBU : closedBall (0 : E) 1 ⊆ U) (hr : ContDiffOn ℝ 1 r U) (hnorm : ∀ x ∈ U, ‖r x‖ = 1)
    (hid : ∀ x ∈ sphere (0 : E) 1, r x = x) : False := by
  set A : E → E →L[ℝ] E := fderiv ℝ r with hAdef
  have hA : ∀ x ∈ U, HasFDerivAt r (A x) x := fun x hx =>
    (((hr.differentiableOn one_ne_zero) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hAc : ContinuousOn A U := hr.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨M0, hM0⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn
    ((hAc.mono hBU).sub continuousOn_const (g := fun _ => (1 : E →L[ℝ] E)))
  set M := max M0 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMb : ∀ x ∈ closedBall (0 : E) 1, ‖A x - 1‖ ≤ M := fun x hx =>
    (hM0 x hx).trans (le_max_left _ _)
  -- the map `r - id` is `M`-Lipschitz on the closed ball
  have hlipB : ∀ x ∈ closedBall (0 : E) 1, ∀ y ∈ closedBall (0 : E) 1,
      ‖(r y - y) - (r x - x)‖ ≤ M * ‖y - x‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun z => r z - z) (f' := fun z => A z - 1)
      (fun z hz => ((hA z (hBU hz)).sub (hasFDerivAt_id z)).hasFDerivWithinAt) hMb
      (convex_closedBall (0 : E) 1) hx hy
  have hvs : ∀ z ∈ sphere (0 : E) 1, r z - z = 0 := fun z hz => by rw [hid z hz, sub_self]
  -- its extension by zero is `M`-Lipschitz on the whole space
  set w : E → E := fun x => if ‖x‖ ≤ 1 then r x - x else 0 with hwdef
  have hlip : ∀ x y : E, ‖w x - w y‖ ≤ M * ‖x - y‖ := by
    intro x y
    by_cases hx : ‖x‖ ≤ 1 <;> by_cases hy : ‖y‖ ≤ 1
    · simp only [hwdef, if_pos hx, if_pos hy]
      exact hlipB y (by simpa using hy) x (by simpa using hx)
    · simp only [hwdef, if_pos hx, if_neg hy, sub_zero]
      exact norm_le_of_lipschitzOn_closedBall (g := fun z => r z - z) hlipB (by linarith) hvs hx
        (lt_of_not_ge hy)
    · simp only [hwdef]
      rw [if_neg hx, if_pos hy, zero_sub, norm_neg, norm_sub_rev x y]
      exact norm_le_of_lipschitzOn_closedBall (g := fun z => r z - z) hlipB (by linarith) hvs hy
        (lt_of_not_ge hx)
    · simp only [hwdef, if_neg hx, if_neg hy, sub_zero, norm_zero]
      positivity
  have hw : ∀ x : E, 1 ≤ ‖x‖ → w x = 0 := by
    intro x hx
    by_cases h1 : ‖x‖ ≤ 1
    · simp only [hwdef, if_pos h1]
      exact hvs x (by simpa using le_antisymm h1 hx)
    · simp only [hwdef, if_neg h1]
  have hball : ∀ x ∈ ball (0 : E) 1, ‖x + w x‖ ≤ 1 := by
    intro x hx
    simp only [hwdef, if_pos (mem_ball_zero_iff.mp hx).le, add_sub_cancel]
    exact (hnorm x (hBU (ball_subset_closedBall hx))).le
  -- the change of variables formula for the perturbations of the identity
  have hcov : ∀ t : ℝ, 0 ≤ t → t * M ≤ 1 / 2 →
      ∫ x in ball (0 : E) 1, |(1 + t • (A x - 1)).det| ∂μ = μ.real (ball (0 : E) 1) := by
    intro t ht htM
    obtain ⟨himage, hinj⟩ := image_ball_eq_and_injective ht htM hM1 hlip hw hball
    have hderiv : ∀ x ∈ ball (0 : E) 1,
        HasFDerivAt (fun x => x + t • w x) (1 + t • (A x - 1)) x := by
      intro x hx
      have hev : w =ᶠ[𝓝 x] fun z => r z - z := by
        filter_upwards [isOpen_ball.mem_nhds hx] with z hz
        simp [hwdef, (mem_ball_zero_iff.mp hz).le]
      have h1 : HasFDerivAt w (A x - 1) x :=
        ((hA x (hBU (ball_subset_closedBall hx))).sub (hasFDerivAt_id x)).congr_of_eventuallyEq
          hev
      exact (hasFDerivAt_id x).add (h1.const_smul t)
    have h := integral_image_eq_integral_abs_det_fderiv_smul μ measurableSet_ball
      (fun x hx => (hderiv x hx).hasFDerivWithinAt) hinj.injOn (fun _ => (1 : ℝ))
    rw [himage, setIntegral_const] at h
    simpa using h.symm
  -- nodes for Lagrange interpolation
  set N := finrank ℝ E with hN
  set t : Fin (N + 1) → ℝ := fun j => ((j : ℕ) + 1 : ℝ) / (2 * M * (N + 1)) with htdef
  have hden : 0 < 2 * M * (N + 1) := by positivity
  have ht0 : ∀ j, 0 ≤ t j := fun j => by positivity
  have htM : ∀ j, t j * M ≤ 1 / 2 := by
    intro j
    have hj : ((j : ℕ) : ℝ) + 1 ≤ N + 1 := by
      have : (j : ℕ) + 1 ≤ N + 1 := by omega
      exact_mod_cast this
    simp only [htdef]
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  have htinj : Function.Injective t := by
    intro i j hij
    simp only [htdef] at hij
    rw [div_left_inj' hden.ne'] at hij
    have : (i : ℕ) = j := by exact_mod_cast (by linarith : ((i : ℕ) : ℝ) = (j : ℕ))
    exact Fin.ext this
  -- the integrals of `det (1 + t j • (A x - 1))` all equal the volume of the ball
  have hval : ∀ j, ∫ x in ball (0 : E) 1, (1 + t j • (A x - 1)).det ∂μ =
      μ.real (ball (0 : E) 1) := by
    intro j
    rw [← hcov (t j) (ht0 j) (htM j)]
    refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
    refine (abs_of_pos (det_one_add_smul_pos (ht0 j) ?_)).symm
    calc t j * ‖A x - 1‖ ≤ t j * M := by
          gcongr
          exact hMb x (ball_subset_closedBall hx)
      _ < 1 := by linarith [htM j]
  have hint : ∀ j, IntegrableOn (fun x => (1 + t j • (A x - 1)).det) (ball (0 : E) 1) μ := by
    intro j
    refine (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : E) 1) ?_).mono_set
      ball_subset_closedBall
    have hAc' : ContinuousOn A (closedBall (0 : E) 1) := hAc.mono hBU
    exact ContinuousLinearMap.continuous_det.comp_continuousOn (by fun_prop)
  set wt : Fin (N + 1) → ℝ := fun j => (Lagrange.basis Finset.univ t j).eval 1 with hwt
  -- by interpolation, the combination of these integrands with the weights `wt` is `det (A x)`
  have hpt : ∀ x ∈ ball (0 : E) 1, ∑ j, wt j * (1 + t j • (A x - 1)).det = 0 := by
    intro x hx
    have h1 := det_one_add_eq_sum t htinj ((A x - 1 : E →L[ℝ] E) : E →ₗ[ℝ] E)
    have h2 : (A x).det = 0 := det_fderiv_eq_zero_of_norm_eq_one hU
      (hBU (ball_subset_closedBall hx)) (hA x (hBU (ball_subset_closedBall hx))) hnorm
    rw [ContinuousLinearMap.det] at h2
    have h3 : (1 : E →ₗ[ℝ] E) + ((A x - 1 : E →L[ℝ] E) : E →ₗ[ℝ] E) = (A x : E →ₗ[ℝ] E) := by
      ext v
      simp
    rw [h3, h2] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
  have htot : ∫ x in ball (0 : E) 1, ∑ j, wt j * (1 + t j • (A x - 1)).det ∂μ =
      μ.real (ball (0 : E) 1) := by
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul, hval]
      rw [← Finset.sum_mul, hwt, sum_eval_basis_one t htinj, one_mul]
    · intro j _
      exact (hint j).const_mul (wt j)
  have hzero : ∫ x in ball (0 : E) 1, ∑ j, wt j * (1 + t j • (A x - 1)).det ∂μ = 0 := by
    rw [setIntegral_congr_fun measurableSet_ball hpt]
    simp
  have hpos : 0 < μ.real (ball (0 : E) 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  linarith

/-- A `C¹` map which moves every point of the closed unit ball by less than `1` has a zero in
the closed unit ball. -/
theorem exists_eq_zero_of_contDiff {φ : E → E} (hφ : ContDiff ℝ 1 φ)
    (h : ∀ x ∈ closedBall (0 : E) 1, ‖φ x - x‖ < 1) : ∃ x ∈ closedBall (0 : E) 1, φ x = 0 := by
  by_contra hne
  push Not at hne
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  -- `r x = x + lam x • φ x` is the point where the ray from `x` in the direction `φ x` meets
  -- the unit sphere
  set b : E → ℝ := fun x => ⟪x, φ x⟫ with hb
  set a : E → ℝ := fun x => ‖φ x‖ ^ 2 with ha
  set D : E → ℝ := fun x => b x ^ 2 + a x * (1 - ‖x‖ ^ 2) with hD
  set lam : E → ℝ := fun x => (-b x + Real.sqrt (D x)) / a x with hlam
  set r : E → E := fun x => x + lam x • φ x with hr
  set U : Set E := {x | 0 < D x} ∩ {x | φ x ≠ 0} with hU
  have hbc : ContDiff ℝ 1 b := contDiff_id.inner ℝ hφ
  have hac : ContDiff ℝ 1 a := hφ.norm_sq ℝ
  have hDc : ContDiff ℝ 1 D :=
    (hbc.pow 2).add (hac.mul (contDiff_const.sub (contDiff_norm_sq ℝ)))
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const hDc.continuous).inter
      (isOpen_ne_fun hφ.continuous continuous_const)
  have hapos : ∀ x, φ x ≠ 0 → 0 < a x := fun x hx => by
    simp only [ha]
    exact pow_pos (norm_pos_iff.mpr hx) 2
  have hbpos : ∀ x ∈ sphere (0 : E) 1, 0 < b x := by
    intro x hx
    have hx1 : ‖x‖ = 1 := by simpa using hx
    have h1 := h x (sphere_subset_closedBall hx)
    have h2 : ⟪x, x - φ x⟫ ≤ ‖x‖ * ‖x - φ x‖ := real_inner_le_norm _ _
    have h3 : ⟪x, φ x⟫ = ‖x‖ ^ 2 - ⟪x, x - φ x⟫ := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
      ring
    rw [norm_sub_rev] at h2
    simp only [hb]
    rw [h3, hx1] at *
    nlinarith
  have hBU : closedBall (0 : E) 1 ⊆ U := by
    intro x hx
    refine ⟨?_, hne x hx⟩
    have hx1 : ‖x‖ ≤ 1 := by simpa using hx
    rcases hx1.lt_or_eq with hlt | heq
    · have ha0 := hapos x (hne x hx)
      have h1 : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      simp only [hD, mem_setOf_eq]
      nlinarith [sq_nonneg (b x), mul_pos ha0 h1]
    · have h1 := hbpos x (by simpa using heq)
      simp only [hD, mem_setOf_eq, heq]
      nlinarith
  have hrc : ContDiffOn ℝ 1 r U := by
    intro x hx
    refine ContDiffAt.contDiffWithinAt ?_
    have hax : a x ≠ 0 := (hapos x hx.2).ne'
    have hsq : ContDiffAt ℝ 1 (fun y => Real.sqrt (D y)) x := hDc.contDiffAt.sqrt hx.1.ne'
    have hl : ContDiffAt ℝ 1 lam x := (hbc.contDiffAt.neg.add hsq).div hac.contDiffAt hax
    exact contDiffAt_id.add (hl.smul hφ.contDiffAt)
  have hnorm : ∀ x ∈ U, ‖r x‖ = 1 := by
    intro x hx
    have hax : 0 < a x := hapos x hx.2
    have hsqrt : Real.sqrt (D x) ^ 2 = D x := Real.sq_sqrt hx.1.le
    have h1 : ‖r x‖ ^ 2 = ‖x‖ ^ 2 + 2 * lam x * b x + lam x ^ 2 * a x := by
      simp only [hr, ha, hb]
      rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    have h2 : lam x * a x = -b x + Real.sqrt (D x) := by
      simp only [hlam]
      field_simp
    have h3 : (‖x‖ ^ 2 + 2 * lam x * b x + lam x ^ 2 * a x) * a x = 1 * a x := by
      have e : (‖x‖ ^ 2 + 2 * lam x * b x + lam x ^ 2 * a x) * a x =
          ‖x‖ ^ 2 * a x + 2 * b x * (lam x * a x) + (lam x * a x) ^ 2 := by ring
      rw [e, h2]
      simp only [hD] at hsqrt
      linear_combination hsqrt
    have h4 := mul_right_cancel₀ hax.ne' h3
    rw [← h1] at h4
    nlinarith [norm_nonneg (r x)]
  have hid : ∀ x ∈ sphere (0 : E) 1, r x = x := by
    intro x hx
    have hx1 : ‖x‖ = 1 := by simpa using hx
    have hbx := hbpos x hx
    have hDx : D x = b x ^ 2 := by
      simp only [hD, hx1]
      ring
    have hlx : lam x = 0 := by
      simp only [hlam]
      rw [hDx, Real.sqrt_sq hbx.le]
      simp
    simp only [hr, hlx, zero_smul, add_zero]
  exact not_contDiffOn_retraction Measure.addHaar hUo hBU hrc hnorm hid

end Retraction

/-! ### Uniform approximation by `C¹` functions -/

section Approximation

variable {Z Y : Type*} [TopologicalSpace Z] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- The subalgebra of `C(Z, ℝ)` consisting of the functions `H ∘ e` with `H` of class `C¹`. -/
def contDiffCompSubalgebra (e : C(Z, Y)) : Subalgebra ℝ C(Z, ℝ) where
  carrier := {g | ∃ H : Y → ℝ, ContDiff ℝ 1 H ∧ ∀ z, g z = H (e z)}
  mul_mem' := by
    rintro g₁ g₂ ⟨H₁, hH₁, h₁⟩ ⟨H₂, hH₂, h₂⟩
    exact ⟨fun y => H₁ y * H₂ y, hH₁.mul hH₂, fun z => by simp [h₁, h₂]⟩
  add_mem' := by
    rintro g₁ g₂ ⟨H₁, hH₁, h₁⟩ ⟨H₂, hH₂, h₂⟩
    exact ⟨fun y => H₁ y + H₂ y, hH₁.add hH₂, fun z => by simp [h₁, h₂]⟩
  algebraMap_mem' c := ⟨fun _ => c, contDiff_const, fun z => by simp⟩

/-- A continuous real function is uniformly approximated on a compact set by functions `H ∘ e`
with `H` of class `C¹`, when `e` is a continuous injection into a real inner product space. -/
theorem exists_contDiff_near (e : Z → Y) (he : Continuous e) (hinj : Function.Injective e)
    (f : Z → ℝ) (hf : Continuous f) {K : Set Z} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Y → ℝ, ContDiff ℝ 1 H ∧ ∀ x ∈ K, |H (e x) - f x| < ε := by
  set A := contDiffCompSubalgebra ⟨e, he⟩
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have hne : e x - e y ≠ 0 := sub_ne_zero.mpr (hinj.ne hxy)
    refine ⟨fun z => ⟪e x - e y, e z⟫,
      ⟨⟨fun z => ⟪e x - e y, e z⟫, continuous_const.inner he⟩,
        ⟨fun w => ⟪e x - e y, w⟫, contDiff_const.inner ℝ contDiff_id, fun z => rfl⟩, rfl⟩, ?_⟩
    intro hxy'
    have : ⟪e x - e y, e x - e y⟫ = 0 := by
      rw [inner_sub_right]
      exact sub_eq_zero.mpr hxy'
    exact hne (inner_self_eq_zero.mp this)
  obtain ⟨g, ⟨H, hH, hgH⟩, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints hsep
      ⟨f, hf⟩ hK hε
  refine ⟨H, hH, fun x hx => ?_⟩
  have := hg x hx
  rw [hgH x] at this
  simpa [Real.norm_eq_abs] using this

end Approximation

/-! ### No continuous injection into a space of smaller dimension -/

section Injection

variable {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A combination of the vectors of an orthonormal basis with coefficients of absolute value
less than `δ` has norm at most the cardinality of the basis times `δ`. -/
theorem norm_sum_smul_le {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (c : ι → ℝ)
    {δ : ℝ} (hc : ∀ i, |c i| < δ) : ‖∑ i, c i • b i‖ ≤ Fintype.card ι * δ := by
  calc ‖∑ i, c i • b i‖ ≤ ∑ i, ‖c i • b i‖ := norm_sum_le _ _
    _ = ∑ i, |c i| := by simp [norm_smul, b.orthonormal.1]
    _ ≤ ∑ _i : ι, δ := Finset.sum_le_sum fun i _ => (hc i).le
    _ = Fintype.card ι * δ := by simp

variable [FiniteDimensional ℝ E] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [FiniteDimensional ℝ Y]

/-- There is no continuous injection from a finite-dimensional real inner product space into one
of strictly smaller dimension. -/
theorem not_injective_of_finrank_lt (hdim : finrank ℝ Y < finrank ℝ E) (F : E → Y)
    (hF : Continuous F) : ¬ Function.Injective F := by
  intro hinj
  set bE := stdOrthonormalBasis ℝ E
  set bY := stdOrthonormalBasis ℝ Y
  -- a `C¹` map `Gv : Y → E` with `Gv ∘ F` uniformly close to the identity on the closed ball
  have hε1 : (0 : ℝ) < 1 / (3 * (finrank ℝ E + 1)) := by positivity
  choose G hG hGa using fun i : Fin (finrank ℝ E) => exists_contDiff_near F hF hinj
    (fun x => ⟪bE i, x⟫) (continuous_const.inner continuous_id) (isCompact_closedBall (0 : E) 1)
    hε1
  set Gv : Y → E := fun y => ∑ i, G i y • bE i with hGvdef
  have hGv : ContDiff ℝ 1 Gv := ContDiff.sum fun i _ => (hG i).smul contDiff_const
  have hGvF : ∀ x ∈ closedBall (0 : E) 1, ‖Gv (F x) - x‖ < 1 / 3 := by
    intro x hx
    have h1 : Gv (F x) - x = ∑ i, (G i (F x) - ⟪bE i, x⟫) • bE i := by
      simp only [hGvdef, sub_smul, Finset.sum_sub_distrib, bE.sum_repr' x]
    rw [h1]
    refine (norm_sum_smul_le bE _ fun i => hGa i x hx).trans_lt ?_
    rw [Fintype.card_fin, mul_one_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- a small vector outside the range of `Gv`
  obtain ⟨v, hv, hvb⟩ := (hGv.dense_compl_range_of_finrank_lt_finrank hdim).exists_mem_open
    (isOpen_ball : IsOpen (ball (0 : E) (1 / 3))) (nonempty_ball.mpr (by norm_num))
  -- uniform continuity of `Gv` near the image of the closed ball
  set K := cthickening 1 (F '' closedBall (0 : E) 1) with hK
  have hKc : IsCompact K := ((isCompact_closedBall (0 : E) 1).image hF).cthickening
  obtain ⟨δ, hδ, hδG⟩ := Metric.uniformContinuousOn_iff.mp
    (hKc.uniformContinuousOn_of_continuous hGv.continuous.continuousOn) (1 / 3) (by norm_num)
  -- a `C¹` map `Fv : E → Y` uniformly close to `F` on the closed ball
  set η := min δ 1 with hη
  have hη0 : 0 < η := lt_min hδ one_pos
  have hε2 : 0 < η / (finrank ℝ Y + 1) := by positivity
  choose H hH hHa using fun j : Fin (finrank ℝ Y) => exists_contDiff_near (id : E → E)
    continuous_id Function.injective_id (fun x => ⟪bY j, F x⟫) (continuous_const.inner hF)
    (isCompact_closedBall (0 : E) 1) hε2
  set Fv : E → Y := fun z => ∑ j, H j z • bY j with hFvdef
  have hFv : ContDiff ℝ 1 Fv := ContDiff.sum fun j _ => (hH j).smul contDiff_const
  have hFvF : ∀ x ∈ closedBall (0 : E) 1, ‖Fv x - F x‖ < η := by
    intro x hx
    have h1 : Fv x - F x = ∑ j, (H j x - ⟪bY j, F x⟫) • bY j := by
      simp only [hFvdef, sub_smul, Finset.sum_sub_distrib, bY.sum_repr' (F x)]
    rw [h1]
    refine (norm_sum_smul_le bY _ fun j => hHa j x hx).trans_lt ?_
    rw [Fintype.card_fin, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  -- the map `Gv ∘ Fv - v` has no zero but moves points of the closed ball by less than `1`
  set φ : E → E := fun z => Gv (Fv z) - v with hφdef
  have hφ : ContDiff ℝ 1 φ := (hGv.comp hFv).sub contDiff_const
  have hφx : ∀ x ∈ closedBall (0 : E) 1, ‖φ x - x‖ < 1 := by
    intro x hx
    have hFxK : F x ∈ K := self_subset_cthickening _ ⟨x, hx, rfl⟩
    have hFvK : Fv x ∈ K := mem_cthickening_of_dist_le (Fv x) (F x) 1 _ ⟨x, hx, rfl⟩
      (by rw [dist_eq_norm]; linarith [hFvF x hx, min_le_right δ 1])
    have h1 : dist (Gv (Fv x)) (Gv (F x)) < 1 / 3 := hδG _ hFvK _ hFxK
      (by rw [dist_eq_norm]; exact (hFvF x hx).trans_le (min_le_left _ _))
    have h2 := hGvF x hx
    have h3 : ‖v‖ < 1 / 3 := by simpa using hvb
    rw [dist_eq_norm] at h1
    calc ‖φ x - x‖ = ‖(Gv (Fv x) - Gv (F x)) + (Gv (F x) - x) - v‖ := by
          simp only [hφdef]
          congr 1
          abel
      _ ≤ ‖Gv (Fv x) - Gv (F x)‖ + ‖Gv (F x) - x‖ + ‖v‖ :=
          (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ < 1 := by linarith
  obtain ⟨x, -, hx0⟩ := exists_eq_zero_of_contDiff hφ hφx
  exact hv ⟨Fv x, by simpa [hφdef, sub_eq_zero] using hx0⟩

end Injection

/-- There is no continuous injection from `ℝ^{k+1}` into `ℝ^k`. -/
theorem not_injective_of_continuous {k : ℕ}
    (F : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin k)) (hF : Continuous F) :
    ¬ Function.Injective F :=
  not_injective_of_finrank_lt (by simp) F hF

/-- Finitely many continuous functionals do not separate the points of an infinite-dimensional
real normed space. -/
theorem not_injective_of_continuous_of_infinite_dimensional (H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] (hH : ¬ FiniteDimensional ℝ H) (k : ℕ)
    (F : H → (Fin k → ℝ)) (hF : Continuous F) : ¬ Function.Injective F := by
  intro hinj
  have hrank : ((k + 1 : ℕ) : Cardinal) ≤ Module.rank ℝ H := by
    have h1 : ¬ Module.rank ℝ H < Cardinal.aleph0 := fun h =>
      hH (Module.rank_lt_aleph0_iff.mp h)
    exact (Cardinal.natCast_lt_aleph0).le.trans (not_lt.mp h1)
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_rank hrank
  set L : EuclideanSpace ℝ (Fin (k + 1)) → H := fun c => ∑ i, c i • b i with hL
  have hLc : Continuous L := by
    simp only [hL]
    fun_prop
  have hLi : Function.Injective L := by
    intro c d hcd
    have h1 : ∑ i, (c i - d i) • b i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr hcd
    have h0 := Fintype.linearIndependent_iff.mp hb (fun i => c i - d i) h1
    ext i
    exact sub_eq_zero.mp (h0 i)
  set e := (EuclideanSpace.equiv (Fin k) ℝ).symm
  exact not_injective_of_continuous (fun c => e (F (L c))) (e.continuous.comp (hF.comp hLc))
    (e.injective.comp (hinj.comp hLi))

end Dissertation.Topology
