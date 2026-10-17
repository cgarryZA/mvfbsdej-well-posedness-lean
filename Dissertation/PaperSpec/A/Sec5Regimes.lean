/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec5

/-!
# Remark 5.7 of the well-posedness paper: the dealer interaction

Statement numbers refer to arXiv 2608.23203v1. Remark 5.7 says that Example 5.5 shows a genuinely
nonlinear `U`-law interaction of arbitrary strength when its geometry is monotone. The crowding
correction `A_λ(u) = ∫ ∇V(u − v) λ(dv)` of Example 5.5 is affine in the law `λ`; it is nonlinear in
the valuation curve `u` and no function of the mean of `λ`.

## Main definitions

* `Dissertation.PaperSpec.A.rem_regimes_law_nonlinear` — the crowding correction is not affine in
  the law.
* `Dissertation.PaperSpec.A.rem_regimes_corr` — the crowding correction is affine in the law, no
  function of its mean, and not affine in the valuation curve.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.Law

universe v

/-- Remark 5.7, the dealer interaction is a genuinely nonlinear `U`-law interaction, read as: for
`ν` σ-finite on a countably generated space, the crowding correction of Example 5.5 is not affine
in the law, `A_{s λ₁ + (1 − s) λ₂}(u) ≠ s A_{λ₁}(u) + (1 − s) A_{λ₂}(u)` for some
`λ₁, λ₂ ∈ P₂(L²(ν))`, `s ∈ [0, 1]` and `u ∈ L²(ν)`. -/
def rem_regimes_law_nonlinear : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E],
    ∃ (Λ₁ Λ₂ : P2 (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν,
        ex55Crowd (ENNReal.ofReal s • Λ₁.law + ENNReal.ofReal (1 - s) • Λ₂.law) u
          ≠ s • ex55Crowd Λ₁.law u + (1 - s) • ex55Crowd Λ₂.law u

/-- Remark 5.7, the dealer interaction, corrected. For `ν` σ-finite on a countably generated space
with `L²(ν)` not reduced to `0`, the crowding correction of Example 5.5 is affine in the law,
`A_{s λ₁ + (1 − s) λ₂}(u) = s A_{λ₁}(u) + (1 − s) A_{λ₂}(u)` for `λ₁, λ₂ ∈ P₂(L²(ν))` and
`s ∈ [0, 1]`; there is no `Φ` with `A_λ(u) = Φ(∫ v λ(dv), u)` for every `λ` and `u`; and for some
`λ ∈ P₂(L²(ν))` the map `u ↦ A_λ(u)` is not affine. -/
def rem_regimes_corr : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E],
    (∃ u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν, u ≠ 0) →
    (∀ (Λ₁ Λ₂ : P2 (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν,
      ex55Crowd (ENNReal.ofReal s • Λ₁.law + ENNReal.ofReal (1 - s) • Λ₂.law) u
        = s • ex55Crowd Λ₁.law u + (1 - s) • ex55Crowd Λ₂.law u)
    ∧ (¬ ∃ Φ : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν → Lp (EuclideanSpace ℝ (Fin 1)) 2 ν
        → Lp (EuclideanSpace ℝ (Fin 1)) 2 ν,
      ∀ (Λ : P2 (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)) (u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
        ex55Crowd Λ.law u = Φ (∫ v, v ∂Λ.law) u)
    ∧ ∃ Λ : P2 (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
      ¬ ∃ (A : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
        (c : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν), ∀ u, ex55Crowd Λ.law u = A u + c

end Dissertation.PaperSpec.A
