/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Robustness.JumpMargin

/-!
# The `β₁` dichotomy in the jump channel

Remark 2.10 of the paper reads Assumption 2.5 along two diagonal inputs that differ in the jump
channel only. With `δX = δY = δZ = 0` the interior inequality (2.7) reduces to

`𝔼 ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de) ≤ −β₁ 𝔼 ‖Gᵀ δU‖²_{L²(ν)}`,

so `β₁ > 0` makes the jump coefficient strictly `U`-dissipative. A jump coefficient of the
additive form `h = h(t, x, e)` has `δh = 0` along such inputs. If some `u ∈ L²(ν; ℝᵐ)` has
`Gᵀ u ≠ 0`, the deterministic inputs `(0, 0, 0, u)` and `0` give `0 ≤ −β₁ ‖Gᵀ u‖²` at almost
every time of a horizon `T > 0`, so `β₁ ≤ 0`, and `β₁ = 0` for admissible constants. The
admissible pattern then forces `n ≤ m` and `α, β₂ > 0`; when `m < n`, admissibility forces
`β₁ > 0`, and the jump coefficient cannot have the additive form.

Such a `u` exists when `ν ≠ 0` and `G ≠ 0`: take `Gᵀ v ≠ 0` for a basis vector `v ∈ ℝᵐ` and
`u = 1_S v` on a set `S` with `0 < ν(S) < ∞`. A full-rank `G` with `n, m ≥ 1` is nonzero.

At `ν = 0` the space `L²(ν; ℝⁿ)` is a single point, so every jump coefficient, that of
Example 5.1(i) among them, has the additive form.

## Main statements

* `DiagonalMonotone.diagonalMonotoneMargin_zero` — Assumption 2.5, interior, is (2.13) with
  margin `0`.
* `DiagonalMonotone.jump_reduction_dirac` — the reduction of (2.7) to the jump channel at
  deterministic inputs.
* `exists_adjoint_GU_ne_zero`, `ne_zero_of_rank` — some `u ∈ L²(ν; ℝᵐ)` has `Gᵀ u ≠ 0`.
* `beta1_nonpos_of_dirac`, `beta1_nonpos_of_additive` — a jump coefficient without
  `U`-feedback forces `β₁ ≤ 0`.
* `Constants.rank_of_beta1_eq_zero` — `β₁ = 0` forces `n ≤ m` and `α, β₂ > 0`.
* `jump_dichotomy` — an additive jump coefficient forces `β₁ = 0`, `n ≤ m` and `α, β₂ > 0`.
* `not_additive_of_lt` — when `m < n` the jump coefficient is not additive.
* `additive_affine_nu_zero` — at `ν = 0`, Example 5.1(i) has an additive jump coefficient.
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal Matrix

namespace Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}

/-! ### The reduction to the jump channel -/

section Reduction

variable {Ω : Type*} [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d}

/-- **Assumption 2.5, interior, is (2.13) with margin `0`.** -/
theorem DiagonalMonotone.diagonalMonotoneMargin_zero (h : DiagonalMonotone ℱ P T G β₁ β₂ C) :
    DiagonalMonotoneMargin ℱ P T G β₁ β₂ 0 C := by
  filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  simpa only [zero_mul, sub_zero] using ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'

/-- **The reduction of (2.7) to the jump channel at deterministic inputs**: for almost every
`t ∈ [0, T]`, all `x, y, z` and all `u, u' ∈ L²(ν; ℝᵐ)`, with `θ = (x, y, z, u)` and
`θ' = (x, y, z, u')`,
`⟨h(t, θ, δ_θ) − h(t, θ', δ_θ'), Gᵀ (u − u')⟩_{L²(ν)} ≤ −β₁ ‖Gᵀ (u − u')‖²_{L²(ν)}`. -/
theorem DiagonalMonotone.jump_reduction_dirac (h : DiagonalMonotone ℱ P T G β₁ β₂ C) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ (x : EuclideanSpace ℝ (Fin n))
      (y : EuclideanSpace ℝ (Fin m)) (z : EuclideanSpace ℝ (Fin m × Fin d))
      (u u' : Lp (EuclideanSpace ℝ (Fin m)) 2 ν),
      inner ℝ (C.h t (x, y, z, u) (P2.dirac ((x, y, z, u) : TupleH ν n m d))
          - C.h t (x, y, z, u') (P2.dirac ((x, y, z, u') : TupleH ν n m d)))
          (ContinuousLinearMap.adjoint (GU G ν) (u - u'))
        ≤ -β₁ * ‖ContinuousLinearMap.adjoint (GU G ν) (u - u')‖ ^ 2 := by
  simpa only [zero_mul, sub_zero] using h.diagonalMonotoneMargin_zero.jump_dissipative_dirac

end Reduction

/-! ### A jump direction seen by `Gᵀ` -/

section Direction

omit [MeasurableSpace E] in
/-- A full-rank matrix `G ∈ ℝ^{m×n}`, `rank G = min(m, n)`, with `n, m ≥ 1` is nonzero. -/
theorem ne_zero_of_rank {G : Matrix (Fin m) (Fin n) ℝ} (hG : G.rank = min m n) (hn : 0 < n)
    (hm : 0 < m) : G ≠ 0 := by
  rintro rfl
  rw [Matrix.rank_zero] at hG
  omega

/-- **Some jump direction is seen by `Gᵀ`**: for `ν ≠ 0` σ-finite and `G ≠ 0` there is
`u ∈ L²(ν; ℝᵐ)` with `Gᵀ u ≠ 0`. -/
theorem exists_adjoint_GU_ne_zero [SigmaFinite ν] {G : Matrix (Fin m) (Fin n) ℝ} (hν : ν ≠ 0)
    (hG : G ≠ 0) :
    ∃ u : Lp (EuclideanSpace ℝ (Fin m)) 2 ν, ContinuousLinearMap.adjoint (GU G ν) u ≠ 0 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, G i j ≠ 0 := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    exact hG (Matrix.ext hcon)
  obtain ⟨k, hk⟩ : ∃ k, ν (spanningSets ν k) ≠ 0 := by
    by_contra hcon
    simp only [ne_eq, not_exists, not_not] at hcon
    apply hν
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets ν]
    exact measure_iUnion_null hcon
  set S := spanningSets ν k
  have hS : MeasurableSet S := measurableSet_spanningSets ν k
  have hSf : ν S ≠ ⊤ := (measure_spanningSets_lt_top ν k).ne
  set v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (Pi.single i 1)
  set w : EuclideanSpace ℝ (Fin n) := GX Gᵀ v
  have hw : w ≠ 0 := fun h0 => by
    have hj := congrArg (fun a : EuclideanSpace ℝ (Fin n) => a j) h0
    simp only [w, v, GX_toLp, Matrix.mulVec_single_one] at hj
    exact hij (by simpa using hj)
  refine ⟨indicatorConstLp 2 hS hSf v, fun h0 => ?_⟩
  have heq : ContinuousLinearMap.adjoint (GU G ν) (indicatorConstLp 2 hS hSf v)
      = indicatorConstLp 2 hS hSf w := by
    refine Lp.ext ?_
    filter_upwards [coeFn_adjoint_GU G ν (indicatorConstLp 2 hS hSf v),
      indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hSf) (c := v),
      indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hSf) (c := w)] with e h1 h2 h3
    rw [h1, h2, h3]
    by_cases he : e ∈ S <;> simp [he, w]
  rw [heq] at h0
  have hn := congrArg norm h0
  rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_zero] at hn
  have hpos : 0 < ν.real S := ENNReal.toReal_pos hk hSf
  rcases mul_eq_zero.mp hn with h | h
  · exact hw (norm_eq_zero.mp h)
  · exact (Real.rpow_pos_of_pos hpos _).ne' h

end Direction

/-! ### The dichotomy -/

section Dichotomy

variable {Ω : Type*} [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d}

/-- **A jump coefficient without `U`-feedback forces `β₁ ≤ 0`.** Let the horizon be `T > 0`,
`ν ≠ 0` and `G ≠ 0`, and let the jump coefficient not depend on `u` along deterministic inputs:
`h(t, (x, y, z, u), δ_{(x,y,z,u)}) = h(t, (x, y, z, u'), δ_{(x,y,z,u')})`. Then Assumption 2.5,
interior, forces `β₁ ≤ 0`. -/
theorem beta1_nonpos_of_dirac (hT : 0 < T) (hν : ν ≠ 0) (hG : G ≠ 0)
    (hind : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m))
      (z : EuclideanSpace ℝ (Fin m × Fin d)) (u u' : Lp (EuclideanSpace ℝ (Fin m)) 2 ν),
      C.h t (x, y, z, u) (P2.dirac ((x, y, z, u) : TupleH ν n m d))
        = C.h t (x, y, z, u') (P2.dirac ((x, y, z, u') : TupleH ν n m d)))
    (h : DiagonalMonotone ℱ P T G β₁ β₂ C) : β₁ ≤ 0 := by
  obtain ⟨u, hu⟩ := exists_adjoint_GU_ne_zero hν hG
  haveI : (ae (volume.restrict (Set.Icc (0 : ℝ) T))).NeBot := by
    rw [ae_restrict_neBot, Real.volume_Icc, sub_zero]
    exact ENNReal.ofReal_ne_zero_iff.mpr hT
  obtain ⟨t, ht⟩ := h.jump_reduction_dirac.exists
  have key := ht 0 0 0 u 0
  rw [hind t 0 0 0 u 0, sub_self, inner_zero_left, sub_zero] at key
  have hpos : 0 < ‖ContinuousLinearMap.adjoint (GU G ν) u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu) 2
  by_contra hβ
  nlinarith [not_le.mp hβ]

/-- **An additive jump coefficient forces `β₁ ≤ 0`** (Remark 2.10): if `h(t, θ, μ)` depends on
`t` and the forward state `x` only, `T > 0`, `ν ≠ 0` and `G ≠ 0`, then Assumption 2.5, interior,
forces `β₁ ≤ 0`. -/
theorem beta1_nonpos_of_additive (hT : 0 < T) (hν : ν ≠ 0) (hG : G ≠ 0)
    (hadd : ∀ (t : ℝ) (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)), θ.1 = θ'.1 →
      C.h t θ μ = C.h t θ' μ')
    (h : DiagonalMonotone ℱ P T G β₁ β₂ C) : β₁ ≤ 0 :=
  beta1_nonpos_of_dirac hT hν hG (fun t _ _ _ _ _ => hadd t _ _ _ _ rfl) h

omit [MeasurableSpace E] in
/-- **`β₁ = 0` forces the `G`-injective branch**: for admissible constants with `β₁ = 0`,
`n ≤ m` and `α, β₂ > 0`. -/
theorem _root_.Dissertation.WellPosedness.Constants.rank_of_beta1_eq_zero
    (h : Constants n m α β₁ β₂) (h0 : β₁ = 0) : n ≤ m ∧ 0 < α ∧ 0 < β₂ := by
  refine ⟨not_lt.mp fun hlt => (h.rank_lt hlt).ne' h0, ?_, ?_⟩
  · have := h.terminal_or_backward
    linarith
  · have := h.backward_or_forward
    linarith

/-- **The `β₁` dichotomy for an additive jump coefficient** (Remark 2.10). Let `T > 0`, `ν ≠ 0`,
`n, m ≥ 1`, `G` of full rank `min(m, n)`, and let `h(t, θ, μ)` depend on `t` and the forward
state `x` only. If Assumption 2.5, interior, holds with admissible constants `α, β₁, β₂`, then
`β₁ = 0`, `n ≤ m` and `α, β₂ > 0`. -/
theorem jump_dichotomy (hT : 0 < T) (hν : ν ≠ 0) (hG : G.rank = min m n) (hn : 0 < n)
    (hm : 0 < m)
    (hadd : ∀ (t : ℝ) (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)), θ.1 = θ'.1 →
      C.h t θ μ = C.h t θ' μ')
    (h : DiagonalMonotone ℱ P T G β₁ β₂ C) (hc : Constants n m α β₁ β₂) :
    β₁ = 0 ∧ n ≤ m ∧ 0 < α ∧ 0 < β₂ := by
  have h0 : β₁ = 0 :=
    le_antisymm (beta1_nonpos_of_additive hT hν (ne_zero_of_rank hG hn hm) hadd h) hc.β₁_nonneg
  exact ⟨h0, hc.rank_of_beta1_eq_zero h0⟩

/-- **When `m < n` the jump coefficient is not additive**: for `T > 0`, `ν ≠ 0`, `m ≥ 1`, `G` of
full rank and Assumption 2.5, interior, with admissible constants, some `h(t, θ, μ)` and
`h(t, θ', μ')` with `θ, θ'` of equal forward state differ. -/
theorem not_additive_of_lt (hT : 0 < T) (hν : ν ≠ 0) (hG : G.rank = min m n) (hm : 0 < m)
    (hlt : m < n) (h : DiagonalMonotone ℱ P T G β₁ β₂ C) (hc : Constants n m α β₁ β₂) :
    ¬ ∀ (t : ℝ) (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)), θ.1 = θ'.1 →
      C.h t θ μ = C.h t θ' μ' := fun hadd =>
  (jump_dichotomy hT hν hG (hm.trans hlt) hm hadd h hc).2.1.not_gt hlt

end Dichotomy

/-! ### Zero intensity -/

section Zero

variable [MeasurableSpace.CountablyGenerated E] {β₁ β₂ : ℝ} {σc : EuclideanSpace ℝ (Fin n × Fin d)}
  {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 (0 : Measure E)}

omit [MeasurableSpace.CountablyGenerated E] in
/-- **At `ν = 0` every jump coefficient is additive**: `L²(0; ℝⁿ)` is a single point, so the jump
coefficient of Example 5.1(i) is independent of the tuple and of the law. -/
theorem additive_affine_nu_zero (t : ℝ) (θ θ' : TupleH (0 : Measure E) n n d)
    (μ μ' : P2 (TupleH (0 : Measure E) n n d)) :
    (Existence.affineCoeffs β₁ β₂ σc hc).h t θ μ = (Existence.affineCoeffs β₁ β₂ σc hc).h t θ' μ' :=
  Lp.ext_iff.2 (by simp [Filter.EventuallyEq])

end Zero

end Dissertation.WellPosedness.System
