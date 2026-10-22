/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec4Coeff

/-!
# Steps of the proof of Lemma 4.2 of the well-posedness paper

Statement and equation numbers refer to the well-posedness paper at `1f67672`. Step 3 of the proof
of Lemma 4.2 bounds the difference `δξ̄ = λ (g(X̄¹_T, Law X̄¹_T) − g(X̄²_T, Law X̄²_T))` of the
terminal values of two frozen steps by the terminal bound (2.6) and the coupling bound (2.9).

## Main definitions

* `MVFBSDEJ.PaperSpec.eq_terdiff` — (4.11).
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace MVFBSDEJ.PaperSpec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.Law

universe u

/-- **(4.11).** On every filtered probability space, if the terminal function `g` satisfies the
terminal bound (2.6) of Assumption 2.3 with the constant `L`, then for every `λ ∈ ℝ` and all
`ℱ_T`-measurable square-integrable `X¹_T, X²_T`, with
`δξ = λ (g(X¹_T, Law X¹_T) − g(X²_T, Law X²_T))`, `δX_T = X¹_T − X²_T` and
`W₂ = W₂(Law X¹_T, Law X²_T)`,
`𝔼|δξ|² ≤ λ² L² 𝔼(|δX_T| + W₂)² ≤ 2 λ² L² (𝔼|δX_T|² + W₂²) ≤ C_g λ² 𝔼|δX_T|²` with
`C_g = 4 L²`, the expectations read in `[0, ∞]`. -/
def eq_terdiff : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ) (P : Measure Ω)
    [IsProbabilityMeasure P] (n m : ℕ) (T L lam : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)),
    LipTerminal ℱ P T L g → ∀ X₁ X₂ : Ω → EuclideanSpace ℝ (Fin n),
    StronglyMeasurable[ℱ T] X₁ → StronglyMeasurable[ℱ T] X₂ → MemLp X₁ 2 P → MemLp X₂ 2 P →
    (∫⁻ ω, ‖lam • (g (X₁ ω) (lawP2 P X₁) - g (X₂ ω) (lawP2 P X₂))‖ₑ ^ 2 ∂P
        ≤ ENNReal.ofReal (lam ^ 2 * L ^ 2)
          * ∫⁻ ω, (‖X₁ ω - X₂ ω‖ₑ + ENNReal.ofReal (w2P (lawP2 P X₁) (lawP2 P X₂))) ^ 2 ∂P)
    ∧ ENNReal.ofReal (lam ^ 2 * L ^ 2)
          * ∫⁻ ω, (‖X₁ ω - X₂ ω‖ₑ + ENNReal.ofReal (w2P (lawP2 P X₁) (lawP2 P X₂))) ^ 2 ∂P
        ≤ ENNReal.ofReal (2 * lam ^ 2 * L ^ 2) * (∫⁻ ω, ‖X₁ ω - X₂ ω‖ₑ ^ 2 ∂P
          + ENNReal.ofReal (w2P (lawP2 P X₁) (lawP2 P X₂) ^ 2))
    ∧ ENNReal.ofReal (2 * lam ^ 2 * L ^ 2) * (∫⁻ ω, ‖X₁ ω - X₂ ω‖ₑ ^ 2 ∂P
          + ENNReal.ofReal (w2P (lawP2 P X₁) (lawP2 P X₂) ^ 2))
        ≤ ENNReal.ofReal (4 * L ^ 2 * lam ^ 2) * ∫⁻ ω, ‖X₁ ω - X₂ ω‖ₑ ^ 2 ∂P

end MVFBSDEJ.PaperSpec
