/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.Convex.Jensen
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Real.Basic

/-!
# Functions affine along the segments of a convex set

A real function `f` on a real vector space is *affine along the segments* of a set `A` when
`f((1 − t) x + t y) = (1 − t) f(x) + t f(y)` for all `x, y ∈ A` and `t ∈ [0, 1]`. On a convex set
such a function is both convex and concave, so it commutes with convex combinations. In finite
dimension it agrees on `A` with an affine function `x ↦ a + ℓ x`: after translating a point of `A`
to the origin, a basis of the span of `A` chosen inside `A` fixes `ℓ`, and every point of `A` lies
on a segment of `A` through a point that is a convex combination of the basis and the origin with
positive weights.

## Main statements

* `Dissertation.Law.map_sum_of_affine_segments` — on a convex set containing the origin, a
  function affine along its segments and vanishing at the origin commutes with combinations of
  points of the set with nonnegative weights of sum at most one.
* `Dissertation.Law.exists_linearMap_eq_of_affine_segments` — such a function agrees on the set
  with a linear functional, in finite dimension.
* `Dissertation.Law.exists_affine_eq_of_affine_segments` — a function affine along the segments of
  a convex set agrees on it with an affine function, in finite dimension.
-/

open Finset Module

namespace Dissertation.Law

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A real function on a convex set containing the origin, affine along its segments and vanishing
at the origin, commutes with sub-convex combinations of points of the set. -/
theorem map_sum_of_affine_segments {A : Set V} (hA : Convex ℝ A) (h0 : (0 : V) ∈ A)
    {g : V → ℝ} (hg0 : g 0 = 0)
    (hg : ∀ x ∈ A, ∀ y ∈ A, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      g ((1 - t) • x + t • y) = (1 - t) * g x + t * g y)
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (p : ι → V) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i ≤ 1) (hp : ∀ i ∈ s, p i ∈ A) :
    ∑ i ∈ s, w i • p i ∈ A ∧ g (∑ i ∈ s, w i • p i) = ∑ i ∈ s, w i * g (p i) := by
  classical
  set w' : Option ι → ℝ := fun o => o.elim (1 - ∑ i ∈ s, w i) w with hw'
  set p' : Option ι → V := fun o => o.elim 0 p with hp'
  have hw'0 : ∀ o ∈ s.insertNone, 0 ≤ w' o := by
    intro o ho
    cases o with
    | none => simp [hw']; linarith
    | some i => exact hw i (by simpa using ho)
  have hw'1 : ∑ o ∈ s.insertNone, w' o = 1 := by
    rw [sum_insertNone]
    simp [hw']
  have hp'A : ∀ o ∈ s.insertNone, p' o ∈ A := by
    intro o ho
    cases o with
    | none => exact h0
    | some i => exact hp i (by simpa using ho)
  have hsum : ∑ o ∈ s.insertNone, w' o • p' o = ∑ i ∈ s, w i • p i := by
    rw [sum_insertNone]
    simp [hw', hp']
  have hgsum : ∑ o ∈ s.insertNone, w' o • g (p' o) = ∑ i ∈ s, w i * g (p i) := by
    rw [sum_insertNone]
    simp [hw', hp', hg0]
  have hconv : ConvexOn ℝ A g := ⟨hA, fun x hx y hy a b ha hb hab => by
    have e : a = 1 - b := by linarith
    subst e
    rw [hg x hx y hy b hb (by linarith), smul_eq_mul, smul_eq_mul]⟩
  have hconc : ConcaveOn ℝ A g := ⟨hA, fun x hx y hy a b ha hb hab => by
    have e : a = 1 - b := by linarith
    subst e
    rw [hg x hx y hy b hb (by linarith), smul_eq_mul, smul_eq_mul]⟩
  refine ⟨?_, ?_⟩
  · rw [← hsum]
    exact hA.sum_mem hw'0 hw'1 hp'A
  · rw [← hsum, ← hgsum]
    exact le_antisymm (hconv.map_sum_le hw'0 hw'1 hp'A) (hconc.le_map_sum hw'0 hw'1 hp'A)

/-- **A real function affine along the segments of a convex set is linear there**: on a
finite-dimensional real vector space, a function on a convex set containing the origin, affine
along its segments and vanishing at the origin, agrees on the set with a linear functional. -/
theorem exists_linearMap_eq_of_affine_segments [FiniteDimensional ℝ V] {A : Set V}
    (hA : Convex ℝ A) (h0 : (0 : V) ∈ A) {g : V → ℝ} (hg0 : g 0 = 0)
    (hg : ∀ x ∈ A, ∀ y ∈ A, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      g ((1 - t) • x + t • y) = (1 - t) * g x + t * g y) :
    ∃ ℓ : V →ₗ[ℝ] ℝ, ∀ y ∈ A, g y = ℓ y := by
  classical
  obtain ⟨b, hbA, hspan, hli⟩ := exists_linearIndependent ℝ A
  haveI : Fintype b := hli.setFinite.fintype
  set B := Basis.span hli with hBdef
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend (B.constr ℝ fun x : b => g x)
  refine ⟨ℓ, fun y hy => ?_⟩
  have hℓb : ∀ x : b, ℓ x = g x := by
    intro x
    have h1 := congrArg (fun F => F (B x)) hℓ
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      Basis.constr_basis] at h1
    rwa [hBdef, Basis.span_apply] at h1
  have hyspan : y ∈ Submodule.span ℝ (Set.range (Subtype.val : b → V)) := by
    rw [Subtype.range_coe, hspan]
    exact Submodule.subset_span hy
  set c := B.repr ⟨y, hyspan⟩ with hc
  have hyexp : y = ∑ x : b, c x • (x : V) := by
    have h := congrArg Subtype.val (B.sum_repr ⟨y, hyspan⟩)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul, hBdef, Basis.span_apply] at h
    exact h.symm
  set N : ℝ := (Fintype.card b : ℝ) with hN
  set K : ℝ := N + 1 with hK
  have hK0 : 0 < K := by positivity
  set S : ℝ := ∑ x : b, |c x| with hS
  have hS0 : 0 ≤ S := sum_nonneg fun x _ => abs_nonneg _
  have hcS : ∀ x : b, |c x| ≤ S := fun x =>
    single_le_sum (f := fun x : b => |c x|) (fun x _ => abs_nonneg _) (mem_univ x)
  set ε : ℝ := min (1 / 2) (1 / (2 * K * (S + 1))) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε1 : ε ≤ 1 / 2 := min_le_left _ _
  have hε2 : ε * (2 * K * (S + 1)) ≤ 1 := by
    have h := min_le_right (1 / 2 : ℝ) (1 / (2 * K * (S + 1)))
    rw [← hεdef] at h
    calc ε * (2 * K * (S + 1)) ≤ 1 / (2 * K * (S + 1)) * (2 * K * (S + 1)) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = 1 := by field_simp
  have hεSK : ε * S * K ≤ 1 / 2 := by nlinarith
  have hsumw : ∑ _x : b, 1 / K = N / K := by
    rw [sum_const, card_univ, nsmul_eq_mul, hN]
    ring
  -- the barycentre of `b`
  obtain ⟨hb0A, hgb0⟩ := map_sum_of_affine_segments hA h0 hg0 hg univ (fun _ : b => 1 / K)
    (fun x : b => (x : V)) (fun _ _ => by positivity)
    (by rw [hsumw, div_le_one hK0]; linarith) (fun x _ => hbA x.2)
  set b0 : V := ∑ x : b, (1 / K) • (x : V) with hb0
  have hℓb0 : ℓ b0 = ∑ x : b, 1 / K * g x := by
    rw [hb0, map_sum]
    exact sum_congr rfl fun x _ => by rw [map_smul, hℓb, smul_eq_mul]
  -- the point `(1 − ε) b0 + ε y` as a sub-convex combination of `b`
  set w : b → ℝ := fun x => (1 - ε) / K + ε * c x with hw
  have hw0 : ∀ x ∈ (univ : Finset b), 0 ≤ w x := by
    intro x _
    have h1 : -S ≤ c x := by have := hcS x; rw [abs_le] at this; linarith [this.1]
    have h2' : ε * K * (-S) ≤ ε * K * c x := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h2 : ε * c x * K ≥ -(1 / 2) := by nlinarith [h2', hεSK]
    have h3 : 0 ≤ ((1 - ε) / K + ε * c x) * K := by
      rw [add_mul, div_mul_cancel₀ _ hK0.ne']
      linarith
    exact nonneg_of_mul_nonneg_left h3 hK0
  have hw1 : ∑ x : b, w x ≤ 1 := by
    have hsc : ∑ x : b, c x ≤ S := sum_le_sum fun x _ => le_abs_self _
    have e : ∑ x : b, w x = (1 - ε) * (N / K) + ε * ∑ x : b, c x := by
      rw [hw]
      simp only
      rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, hN]
      ring
    rw [e]
    have h1 : (1 - ε) * (N / K) ≤ N / K := by
      have : 0 ≤ N / K := by positivity
      nlinarith
    have h2 : N / K + 1 / K = 1 := by
      rw [← add_div, show N + 1 = K from hK.symm, div_self hK0.ne']
    have h3 : ε * ∑ x : b, c x ≤ 1 / (2 * K) := by
      have : ε * ∑ x : b, c x ≤ ε * S := mul_le_mul_of_nonneg_left hsc hε0.le
      have h4 : ε * S ≤ 1 / (2 * K) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      linarith
    have h5 : 1 / (2 * K) ≤ 1 / K := by
      apply one_div_le_one_div_of_le hK0
      linarith
    linarith
  obtain ⟨hzA, hgz⟩ := map_sum_of_affine_segments hA h0 hg0 hg univ w
    (fun x : b => (x : V)) hw0 hw1 (fun x _ => hbA x.2)
  have hz : ∑ x : b, w x • (x : V) = (1 - ε) • b0 + ε • y := by
    rw [hb0, hyexp, smul_sum, smul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [hw, smul_smul, smul_smul, ← add_smul]
    congr 1
    ring
  have hℓz : ℓ (∑ x : b, w x • (x : V)) = ∑ x : b, w x * g x := by
    rw [map_sum]
    exact sum_congr rfl fun x _ => by rw [map_smul, hℓb, smul_eq_mul]
  rw [hz] at hgz hℓz
  have hseg := hg b0 hb0A y hy ε hε0.le (by linarith)
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hℓb0] at hℓz
  rw [hseg, hgb0] at hgz
  have : ε * g y = ε * ℓ y := by linarith
  exact mul_left_cancel₀ hε0.ne' this

/-- **A real function affine along the segments of a convex set is affine there**: on a
finite-dimensional real vector space, a function affine along the segments of a convex set agrees
on the set with `x ↦ a + ℓ x` for a constant `a` and a linear functional `ℓ`. -/
theorem exists_affine_eq_of_affine_segments [FiniteDimensional ℝ V] {A : Set V}
    (hA : Convex ℝ A) {f : V → ℝ}
    (hf : ∀ x ∈ A, ∀ y ∈ A, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f ((1 - t) • x + t • y) = (1 - t) * f x + t * f y) :
    ∃ (a : ℝ) (ℓ : V →ₗ[ℝ] ℝ), ∀ x ∈ A, f x = a + ℓ x := by
  rcases A.eq_empty_or_nonempty with hA0 | ⟨p, hp⟩
  · exact ⟨0, 0, fun x hx => by simp [hA0] at hx⟩
  set A' : Set V := (fun y => p + y) ⁻¹' A with hA'
  have hA'c : Convex ℝ A' := hA.translate_preimage_right p
  have h0 : (0 : V) ∈ A' := by simpa [hA'] using hp
  have hcomb : ∀ (x y : V) (t : ℝ),
      p + ((1 - t) • x + t • y) = (1 - t) • (p + x) + t • (p + y) := fun x y t => by
    rw [smul_add, smul_add, add_add_add_comm, ← add_smul, sub_add_cancel, one_smul]
  obtain ⟨ℓ, hℓ⟩ := exists_linearMap_eq_of_affine_segments hA'c h0 (g := fun y => f (p + y) - f p)
    (by simp) (fun x hx y hy t ht0 ht1 => by
      rw [hcomb, hf _ hx _ hy t ht0 ht1]
      ring)
  refine ⟨f p - ℓ p, ℓ, fun x hx => ?_⟩
  have h : f (p + (x - p)) - f p = ℓ (x - p) := hℓ (x - p) (by simpa [hA'] using hx)
  rw [add_sub_cancel, map_sub] at h
  linarith

end Dissertation.Law
