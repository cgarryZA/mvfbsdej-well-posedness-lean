/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.Coefficients
import MVFBSDEJ.WellPosedness.System.HilbertW2

/-!
# Assumption 2.3 with the 2-Wasserstein distance of the Hilbert norm

Assumption 2.3 of the well-posedness paper bounds the coefficient differences along two diagonal
inputs `(Θ, μ)`, `(Θ', μ')` at time `t` by

`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ L (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + W₂(μ, μ'))`,

with `W₂` the 2-Wasserstein distance on `P₂(H)` for the Hilbert norm
`|θ|_H = (|x|² + |y|² + |z|²_F + ‖u‖²_{L²(ν)})^{1/2}` of the tuple space, which is `w2H`.
`DiagonalLipschitzH` states it with that distance. `DiagonalLipschitz` states the same bound with
`w2P`, the 2-Wasserstein distance for the maximum of the four channel norms. Since
`w2P ≤ w2H ≤ 2 w2P`, the two conditions define the same class of coefficients, with the constant
moving within a factor `2`: `DiagonalLipschitz` at `L` gives `DiagonalLipschitzH` at `L`, and
`DiagonalLipschitzH` at `L` gives `DiagonalLipschitz` at `2L`.

The terminal half (2.6), `|δg_T| ≤ L (|X_T − X'_T| + W₂(ρ, ρ'))`, has its `W₂` on `P₂(ℝⁿ)` for the
Euclidean norm, which is `w2P` on `ℝⁿ`; it is `TerminalLipschitz`. Its constant can be doubled.

## Main definitions

* `DiagonalLipschitzH` — Assumption 2.3, interior, along the diagonal, with `W₂ = w2H`.

## Main statements

* `DiagonalLipschitz.diagonalLipschitzH` — `DiagonalLipschitz` at `L` gives
  `DiagonalLipschitzH` at `L`.
* `DiagonalLipschitzH.diagonalLipschitz` — `DiagonalLipschitzH` at `L` gives
  `DiagonalLipschitz` at `2L`.
* `TerminalLipschitz.two_mul` — (2.6) at `L` gives (2.6) at `2L`.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

/-! ### Comparing the right-hand sides -/

section Real

variable {a t w w' L : ℝ}

/-- A bound `a ≤ L (t + w)` with `0 ≤ a`, `0 ≤ t`, `0 ≤ w ≤ w' ≤ 2 w` gives `a ≤ L (t + w')`. -/
theorem le_mul_add_of_le_mul_add_of_le (ha : 0 ≤ a) (ht : 0 ≤ t) (hw : 0 ≤ w) (hww : w ≤ w')
    (hw' : w' ≤ 2 * w) (h : a ≤ L * (t + w)) : a ≤ L * (t + w') := by
  rcases le_or_gt 0 L with hL | hL
  · exact h.trans (mul_le_mul_of_nonneg_left (by linarith) hL)
  · have h0 : t + w = 0 := by nlinarith
    have hw'0 : w' = 0 := by linarith
    have ht0 : t = 0 := by linarith
    rw [hw'0, ht0, add_zero, mul_zero]
    rw [h0, mul_zero] at h
    exact h

/-- A bound `a ≤ L (t + w')` with `0 ≤ a`, `0 ≤ t`, `0 ≤ w ≤ w' ≤ 2 w` gives
`a ≤ 2L (t + w)`. -/
theorem le_two_mul_mul_add_of_le (ha : 0 ≤ a) (ht : 0 ≤ t) (hw : 0 ≤ w) (hww : w ≤ w')
    (hw' : w' ≤ 2 * w) (h : a ≤ L * (t + w')) : a ≤ 2 * L * (t + w) := by
  rcases le_or_gt 0 L with hL | hL
  · refine h.trans ?_
    nlinarith
  · have h0 : t + w' = 0 := by nlinarith
    have ht0 : t = 0 := by linarith
    have hw0 : w = 0 := by linarith
    rw [ht0, hw0, add_zero, mul_zero]
    have h' := h
    rw [h0, mul_zero] at h'
    exact h'

end Real

/-! ### Assumption 2.3 with the Hilbert-norm `W₂` -/

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}
  {Ω : Type*} [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **Assumption 2.3, interior, along the diagonal, with the Hilbert-norm `W₂`**: for almost
every `t ∈ [0, T]` and any two strongly `ℱ_t`-measurable square-integrable tuples `Θ, Θ'` with
laws `μ, μ'`, almost surely
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ L (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + W₂(μ, μ'))`,
with `W₂` the 2-Wasserstein distance on `P₂(H)` for the Hilbert norm of `H`. -/
def DiagonalLipschitzH (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T L : ℝ) (C : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ Θ Θ' : Ω → TupleH ν n m d,
    StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
    ∀ᵐ ω ∂P, ‖C.b t (Θ ω) (lawP2 P Θ) - C.b t (Θ' ω) (lawP2 P Θ')‖
        + ‖C.σ t (Θ ω) (lawP2 P Θ) - C.σ t (Θ' ω) (lawP2 P Θ')‖
        + ‖C.h t (Θ ω) (lawP2 P Θ) - C.h t (Θ' ω) (lawP2 P Θ')‖
        + ‖C.f t (Θ ω) (lawP2 P Θ) - C.f t (Θ' ω) (lawP2 P Θ')‖
      ≤ L * (tupleNorm (Θ ω - Θ' ω) + w2H (lawP2 P Θ) (lawP2 P Θ'))

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T L : ℝ} {C : Coeffs ν n m d}

/-- **`DiagonalLipschitz` at `L` gives `DiagonalLipschitzH` at `L`**, since `w2P ≤ w2H ≤ 2 w2P`. -/
theorem DiagonalLipschitz.diagonalLipschitzH (h : DiagonalLipschitz ℱ P T L C) :
    DiagonalLipschitzH ℱ P T L C := by
  filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  filter_upwards [ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'] with ω hω
  exact le_mul_add_of_le_mul_add_of_le (by positivity) (by unfold tupleNorm; positivity)
    (w2P_nonneg _ _) (w2P_le_w2H _ _) (w2H_le_two_mul_w2P _ _) hω

/-- **`DiagonalLipschitzH` at `L` gives `DiagonalLipschitz` at `2L`**, since
`w2P ≤ w2H ≤ 2 w2P`. -/
theorem DiagonalLipschitzH.diagonalLipschitz (h : DiagonalLipschitzH ℱ P T L C) :
    DiagonalLipschitz ℱ P T (2 * L) C := by
  filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  filter_upwards [ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'] with ω hω
  exact le_two_mul_mul_add_of_le (by positivity) (by unfold tupleNorm; positivity)
    (w2P_nonneg _ _) (w2P_le_w2H _ _) (w2H_le_two_mul_w2P _ _) hω

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **(2.6) at `L` gives (2.6) at `2L`.** -/
theorem TerminalLipschitz.two_mul
    {g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)}
    (h : TerminalLipschitz ℱ P T L g) : TerminalLipschitz ℱ P T (2 * L) g := by
  intro ξ ξ' hξ hξ' hξ2 hξ2'
  filter_upwards [h ξ ξ' hξ hξ' hξ2 hξ2'] with ω hω
  have h0 := norm_nonneg (g (ξ ω) (lawP2 P ξ) - g (ξ' ω) (lawP2 P ξ'))
  linarith

end MVFBSDEJ.WellPosedness.System
