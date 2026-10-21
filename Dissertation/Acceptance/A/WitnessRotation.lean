/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Acceptance.A.Sec3
import Dissertation.Acceptance.A.Sec3Rem34
import Dissertation.WellPosedness.Examples.Rotation

/-!
# Two distinct solutions of a Lipschitz system

Statement and equation numbers refer to the well-posedness paper at `1f67672`. Over a probability
space carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`, `n = m = 1` and the
horizon `T = π/4`, the system of Example 5.1(i) with `σ_c = h_c = 0`, `β₂ = 1` and the reversed
sign `β₁ = −1` (`b = y`, `σ = z`, `h = u`, `f = x`, `g = x`) satisfies (2.3) and Assumption 2.3
with `L = 1`, and from the initial datum `0` it has the two solutions
`(X, Y, Z, U) = (sin t, cos t, 0, 0)` and the zero tuple. They differ, so by Theorem 3.3 the system
satisfies Assumption 2.5 for no coupling matrix of full rank.

## Main statements

* `Dissertation.Acceptance.A.rem_uniq_lip_hypotheses` — the hypotheses of the Lipschitz-only
  steps of the proof of Theorem 3.3, at two distinct solutions.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.PaperSpec.A
  Dissertation.WellPosedness.Stability LevyStochCalc

universe w

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `σ_c = h_c = 0`, `β₂ = 1` and
`β₁ = −1`. -/
local notation "rotW" =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) (-1) 1 0 0

/-- The solution for `a` of the system `rotW` on the horizon `π/4`, from the initial datum `0`,
in `ℍ²`. -/
theorem weakSolution_rotation {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1
      (Measure.dirac (0 : ℝ)))
    (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P) (a : ℝ) :
    WeakSolution D bot_le hind₀ (Real.pi / 4) rotW (fun _ => 0)
      (fun _ t _ => a * Real.sin t) (fun _ t _ => a * Real.cos t) 0 0 := by
  refine ⟨⟨0, ?_⟩, fun i ω t _ => ?_, fun k ω t _ => ?_⟩
  · have h := paperWeakSolutionIntAug_rotation D a
    have e : (fun i ω => ((fun _ => (0 : EuclideanSpace ℝ (Fin 1))) ω) i)
        = (0 : Fin 1 → Ω → ℝ) := by
      funext i ω
      simp
    rw [e]
    exact paperWeakSolutionInt_congr_filtration (enlJoint_bot D).symm h
  · exact ⟨_, ((continuous_const.mul Real.continuous_sin).tendsto t).mono_left
      nhdsWithin_le_nhds⟩
  · exact ⟨_, ((continuous_const.mul Real.continuous_cos).tendsto t).mono_left
      nhdsWithin_le_nhds⟩

/-- **The hypotheses of the Lipschitz-only steps of the proof of Theorem 3.3 hold at two distinct
solutions.** Over a probability space carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`,
with `𝒢₀ = ⊥`, `n = m = 1` and `T = π/4`: the system of Example 5.1(i) with `σ_c = h_c = 0`,
`β₂ = 1` and `β₁ = −1` satisfies (2.3) and Assumption 2.3 with `L = 1`; the tuples
`(sin t, cos t, 0, 0)` and `(0, 0, 0, 0)` satisfy (1.1) in `ℍ²` from the initial datum `0`;
their differences are `δX_t = sin t` and `δY_t = cos t`; and the system satisfies Assumption 2.5
for no matrix `G` of full rank and no constants `α, β₁, β₂`. -/
theorem rem_uniq_lip_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel (Real.pi / 4) rotW
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P (Real.pi / 4) 1 rotW
      ∧ ∃ (X₁ X₂ : Fin 1 → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ)
          (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U₁ U₂ : Fin 1 → ℝ → Ω → ℝ → ℝ),
          WeakSolution D bot_le hind₀ (Real.pi / 4) rotW (fun _ => 0) X₁ Y₁ Z₁ U₁
          ∧ WeakSolution D bot_le hind₀ (Real.pi / 4) rotW (fun _ => 0) X₂ Y₂ Z₂ U₂
          ∧ (∀ i t ω, X₁ i t ω - X₂ i t ω = Real.sin t)
          ∧ (∀ k t ω, Y₁ k t ω - Y₂ k t ω = Real.cos t)
          ∧ ∀ (G : Matrix (Fin 1) (Fin 1) ℝ) (α β₁ β₂ : ℝ), G.rank = min 1 1 →
              ¬ Assumption25 (enlJoint ⊥ D bot_le) P (Real.pi / 4) G α β₁ β₂ rotW := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  have hT : (0 : ℝ) < Real.pi / 4 := by positivity
  have hJ : JointBorel (Real.pi / 4) rotW :=
    jointBorel_iff.mpr ⟨coeffBorelW2_affine _, continuous_fst.borel_measurable⟩
  have h23 : Assumption23 (enlJoint ⊥ D bot_le) P (Real.pi / 4) 1 rotW :=
    ⟨zero_le_one, LipInterior.of_diagonalLipschitz (diagonalLipschitz_of_lipschitzCoefficientsP2
      (lipschitzCoefficientsP2_affine_abs (by norm_num))), terminalLipschitz_affine le_rfl⟩
  have hw₁ := weakSolution_rotation D hind₀ 1
  have hw₀ := weakSolution_rotation D hind₀ 0
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hJ, h23, _, _, _, _, _, _, _, _, hw₁, hw₀,
    fun i t ω => by ring, fun k t ω => by ring, fun G α β₁ β₂ hG h25 => ?_⟩
  obtain ⟨⟨hX, -⟩, -⟩ := thm_uniq.{0, 0, w} ⊥ (Measure.dirac (0 : ℝ)) 1 1 1 P D bot_le hind₀
    one_pos one_pos one_pos (Real.pi / 4) hT 1 α β₁ β₂ G rotW hJ h23 hG h25 (fun _ => 0) _ _ _ _
    _ _ _ _ hw₁ hw₀
  obtain ⟨ω, hω⟩ := (hX 0).exists
  have h := hω (Real.pi / 4) ⟨hT.le, le_rfl⟩
  simp only [one_mul, zero_mul, Real.sin_pi_div_four] at h
  have hs : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
  linarith

end Dissertation.Acceptance.A
