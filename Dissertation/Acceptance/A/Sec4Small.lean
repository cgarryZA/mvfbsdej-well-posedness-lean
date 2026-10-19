/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4Small
import Dissertation.Acceptance.A.Witness

/-!
# Steps of the proof of Lemma 4.2: proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`.

## Main statements

* `Dissertation.Acceptance.A.eq_terdiff` — (4.11).
* `Dissertation.Acceptance.A.eq_terdiff_hypotheses` — its hypotheses at the terminal function of
  Example 5.1(i), at the terminal values `0` and `e₁`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.Law

universe u w

/-- (4.11). -/
theorem eq_terdiff : PaperSpec.A.eq_terdiff.{u} := by
  intro Ω mΩ ℱ P _ n m T L lam g hg X₁ X₂ h₁ h₂ hX₁ hX₂
  set W := w2P (lawP2 P X₁) (lawP2 P X₂) with hWdef
  have hW0 : 0 ≤ W := w2P_nonneg _ _
  have hpt := hg X₁ X₂ h₁ h₂ hX₁ hX₂
  have e2 : ∀ y : ℝ, ENNReal.ofReal (2 * y) = 2 * ENNReal.ofReal y := fun y => by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  refine ⟨?_, ?_, ?_⟩
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hpt] with ω hω
    set v := g (X₁ ω) (lawP2 P X₁) - g (X₂ ω) (lawP2 P X₂)
    have hv := norm_nonneg v
    have hx := norm_nonneg (X₁ ω - X₂ ω)
    have hsq : ‖v‖ ^ 2 ≤ L ^ 2 * (‖X₁ ω - X₂ ω‖ + W) ^ 2 := by
      have := pow_le_pow_left₀ hv hω 2
      nlinarith
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_add hx hW0, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity), norm_smul, Real.norm_eq_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_pow, sq_abs]
    nlinarith [sq_nonneg lam]
  · have hpt2 : ∀ ω, (‖X₁ ω - X₂ ω‖ₑ + ENNReal.ofReal W) ^ 2
        ≤ 2 * (‖X₁ ω - X₂ ω‖ₑ ^ 2 + ENNReal.ofReal (W ^ 2)) := fun ω => by
      have hx := norm_nonneg (X₁ ω - X₂ ω)
      rw [← ofReal_norm, ← ENNReal.ofReal_add hx hW0, ← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_pow hx, ← ENNReal.ofReal_add (by positivity) (by positivity), ← e2]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (‖X₁ ω - X₂ ω‖ - W)])
    calc ENNReal.ofReal (lam ^ 2 * L ^ 2)
          * ∫⁻ ω, (‖X₁ ω - X₂ ω‖ₑ + ENNReal.ofReal W) ^ 2 ∂P
        ≤ ENNReal.ofReal (lam ^ 2 * L ^ 2)
          * ∫⁻ ω, 2 * (‖X₁ ω - X₂ ω‖ₑ ^ 2 + ENNReal.ofReal (W ^ 2)) ∂P := by
          gcongr with ω
          exact hpt2 ω
      _ = ENNReal.ofReal (2 * lam ^ 2 * L ^ 2)
          * (∫⁻ ω, ‖X₁ ω - X₂ ω‖ₑ ^ 2 ∂P + ENNReal.ofReal (W ^ 2)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
            lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            mul_assoc 2, e2]
          ring
  · have hW2 : ENNReal.ofReal (W ^ 2) ≤ ∫⁻ ω, ‖X₁ ω - X₂ ω‖ₑ ^ 2 ∂P := by
      refine (ofReal_w2P_lawP2_sq_le hX₁ hX₂).trans_eq (lintegral_congr fun ω => ?_)
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    calc ENNReal.ofReal (2 * lam ^ 2 * L ^ 2)
          * (∫⁻ ω, ‖X₁ ω - X₂ ω‖ₑ ^ 2 ∂P + ENNReal.ofReal (W ^ 2))
        ≤ ENNReal.ofReal (2 * lam ^ 2 * L ^ 2)
          * (∫⁻ ω, ‖X₁ ω - X₂ ω‖ₑ ^ 2 ∂P + ∫⁻ ω, ‖X₁ ω - X₂ ω‖ₑ ^ 2 ∂P) := by
          gcongr
      _ = ENNReal.ofReal (4 * L ^ 2 * lam ^ 2) * ∫⁻ ω, ‖X₁ ω - X₂ ω‖ₑ ^ 2 ∂P := by
          rw [show 4 * L ^ 2 * lam ^ 2 = 2 * (2 * lam ^ 2 * L ^ 2) by ring, e2]
          ring

/-- **The hypotheses of (4.11) hold at Example 5.1(i).** At the instance of
`thm_cwp_hypotheses` (a Lévy driver with `d = 1`, `ν = δ₀`, `𝒢₀ = ⊥`, `n = m = 1`, `T = 1`), the
terminal function `g(x, ρ) = x` of the system of Example 5.1(i) satisfies the terminal bound
(2.6) with `L = 1`, and the terminal values `0` and `e₁` are `ℱ_1`-measurable and square
integrable. -/
theorem eq_terdiff_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ))),
      LipTerminal (enlJoint ⊥ D bot_le) P 1 1
        (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 1 1 0 0).g
      ∧ StronglyMeasurable[enlJoint ⊥ D bot_le 1]
          (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1)))
      ∧ StronglyMeasurable[enlJoint ⊥ D bot_le 1]
          (fun _ : Ω => (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)))
      ∧ MemLp (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1))) 2 P
      ∧ MemLp (fun _ : Ω => (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1))) 2 P := by
  obtain ⟨Ω, _, P, _, D, -, -, -, h23, -, -⟩ := thm_cwp_hypotheses.{w}
  exact ⟨Ω, inferInstance, P, inferInstance, D, h23.terminal, stronglyMeasurable_const,
    stronglyMeasurable_const, memLp_const _, memLp_const _⟩

end Dissertation.Acceptance.A
