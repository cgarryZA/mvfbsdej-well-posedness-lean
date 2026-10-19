/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import MVFBSDEJ.WellPosedness.Assumptions

/-!
# The coupling-matrix coercivity of Assumption 2.4 in coordinates

For a full-rank coupling matrix `G ∈ ℝ^{m×n}` Assumption 2.4 of the well-posedness paper gives

`|x|² ≤ c_G |G x|²` (`m ≥ n`),   `|y|² ≤ c_G |Gᵀ y|²` (`n ≥ m`),

and, when `Gᵀ` is injective, the second bound on the matrix- and `L²(ν)`-valued arguments,
`|Z|²_F ≤ c_G |Gᵀ Z|²_F` and `‖U‖²_{L²(ν)} ≤ c_G ‖Gᵀ U‖²_{L²(ν)}`. This file states the two
bounds on coordinate vectors `Fin n → ℝ`, `Fin m → ℝ` with the dot product, derives the two
extensions — the Frobenius norm is the sum over the columns `Z_{· j}` and the `L²(ν)` norm the
integral over the marks — and selects the rank case of the closure step of Lemma 4.3: given the
admissible constants of Assumption 2.5 and each bound on its rank branch, either `β₁ > 0` and
`Gᵀ` is coercive (Case A), or `α, β₂ > 0` and `G` is coercive (Case B).

## Main definitions

* `ForwardCoercive` — `|x|² ≤ c_G |G x|²` for every `x ∈ ℝⁿ`.
* `BackwardCoercive` — `|y|² ≤ c_G |Gᵀ y|²` for every `y ∈ ℝᵐ`.
* `RankCase` — Case A or Case B of the closure step.

## Main statements

* `sum_le_mul_sum_of_le`, `integral_le_mul_integral_of_le` — a pointwise quadratic bound extends
  to finite sums and to integrals.
* `BackwardCoercive.sum_le`, `BackwardCoercive.integral_le` — the Frobenius and `L²(ν)`
  extensions.
* `Constants.rankCase` — the rank-case selector.
-/

open MeasureTheory Matrix
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.Stability

variable {n m : ℕ}

/-- **Assumption 2.4, forward branch, in coordinates**: `|x|² ≤ c_G |G x|²` for every
`x ∈ ℝⁿ`. -/
def ForwardCoercive (G : Matrix (Fin m) (Fin n) ℝ) (cG : ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ⬝ᵥ x ≤ cG * ((G *ᵥ x) ⬝ᵥ (G *ᵥ x))

/-- **Assumption 2.4, backward branch, in coordinates**: `|y|² ≤ c_G |Gᵀ y|²` for every
`y ∈ ℝᵐ`. -/
def BackwardCoercive (G : Matrix (Fin m) (Fin n) ℝ) (cG : ℝ) : Prop :=
  ∀ y : Fin m → ℝ, y ⬝ᵥ y ≤ cG * ((Gᵀ *ᵥ y) ⬝ᵥ (Gᵀ *ᵥ y))

/-- **The rank case of the closure step of Lemma 4.3.** Case A: `β₁ > 0` and `Gᵀ` is coercive,
so the `β₁`-block controls `(δY, δZ, δU)`. Case B: `α, β₂ > 0` and `G` is coercive, so the
`α`- and `β₂`-blocks control `δX_T` and `δX`. -/
def RankCase (G : Matrix (Fin m) (Fin n) ℝ) (cG α β₁ β₂ : ℝ) : Prop :=
  (0 < β₁ ∧ BackwardCoercive G cG) ∨ (0 < α ∧ 0 < β₂ ∧ ForwardCoercive G cG)

/-! ### Extending a pointwise quadratic bound -/

section Extension

variable {V : Type*} {F H : V → ℝ} {c : ℝ}

/-- A pointwise bound `F ≤ c H` extends to finite sums. -/
theorem sum_le_mul_sum_of_le (hFH : ∀ v, F v ≤ c * H v) {ι : Type*} (s : Finset ι)
    (z : ι → V) : ∑ j ∈ s, F (z j) ≤ c * ∑ j ∈ s, H (z j) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => hFH (z j)

/-- A pointwise bound `0 ≤ F ≤ c H` extends to Bochner integrals, provided `H ∘ u` is
integrable. -/
theorem integral_le_mul_integral_of_le (hF : ∀ v, 0 ≤ F v) (hFH : ∀ v, F v ≤ c * H v)
    {E : Type*} [MeasurableSpace E] {ν : Measure E} {u : E → V}
    (hH : Integrable (fun e => H (u e)) ν) :
    ∫ e, F (u e) ∂ν ≤ c * ∫ e, H (u e) ∂ν := by
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun e => hF (u e))
    (hH.const_mul c) (Filter.Eventually.of_forall fun e => hFH (u e))

end Extension

/-! ### The Frobenius and `L²(ν)` extensions of the backward bound -/

variable {G : Matrix (Fin m) (Fin n) ℝ} {cG : ℝ}

/-- **The Frobenius extension**: `|Z|²_F ≤ c_G |Gᵀ Z|²_F` for a family of columns
`Z_{· j} ∈ ℝᵐ`. -/
theorem BackwardCoercive.sum_le (h : BackwardCoercive G cG) {ι : Type*} (s : Finset ι)
    (z : ι → Fin m → ℝ) :
    ∑ j ∈ s, z j ⬝ᵥ z j ≤ cG * ∑ j ∈ s, (Gᵀ *ᵥ z j) ⬝ᵥ (Gᵀ *ᵥ z j) :=
  sum_le_mul_sum_of_le (F := fun y => y ⬝ᵥ y) h s z

/-- **The `L²(ν)` extension**: `∫_E |U(e)|² ν(de) ≤ c_G ∫_E |Gᵀ U(e)|² ν(de)`, when
`e ↦ |Gᵀ U(e)|²` is integrable. -/
theorem BackwardCoercive.integral_le (h : BackwardCoercive G cG) {E : Type*}
    [MeasurableSpace E] {ν : Measure E} {u : E → Fin m → ℝ}
    (hu : Integrable (fun e => (Gᵀ *ᵥ u e) ⬝ᵥ (Gᵀ *ᵥ u e)) ν) :
    ∫ e, u e ⬝ᵥ u e ∂ν ≤ cG * ∫ e, (Gᵀ *ᵥ u e) ⬝ᵥ (Gᵀ *ᵥ u e) ∂ν :=
  integral_le_mul_integral_of_le (F := fun y => y ⬝ᵥ y) (fun y => dotProduct_self_star_nonneg y)
    h hu

/-! ### The rank-case selector -/

variable {α β₁ β₂ : ℝ}

/-- **The rank-case selector.** Under the admissible constants of Assumption 2.5, with the
forward bound of Assumption 2.4 when `n ≤ m` and the backward bound when `m ≤ n`, Case A or
Case B of the closure step holds. -/
theorem _root_.MVFBSDEJ.WellPosedness.Constants.rankCase
    (h : MVFBSDEJ.WellPosedness.Constants n m α β₁ β₂)
    (hf : n ≤ m → ForwardCoercive G cG) (hb : m ≤ n → BackwardCoercive G cG) :
    RankCase G cG α β₁ β₂ := by
  rcases le_total m n with hmn | hnm
  · rcases h.dichotomy with hβ | ⟨hβ, hα, hβ₂⟩
    · exact Or.inl ⟨hβ, hb hmn⟩
    · rcases hmn.lt_or_eq with hlt | heq
      · exact absurd (h.rank_lt hlt) (by rw [hβ]; exact lt_irrefl 0)
      · exact Or.inr ⟨hα, hβ₂, hf heq.ge⟩
  · rcases hnm.lt_or_eq with hlt | heq
    · obtain ⟨hα, hβ₂⟩ := h.rank_gt hlt
      exact Or.inr ⟨hα, hβ₂, hf hnm⟩
    · rcases h.dichotomy with hβ | ⟨_, hα, hβ₂⟩
      · exact Or.inl ⟨hβ, hb heq.ge⟩
      · exact Or.inr ⟨hα, hβ₂, hf hnm⟩

end MVFBSDEJ.WellPosedness.Stability
