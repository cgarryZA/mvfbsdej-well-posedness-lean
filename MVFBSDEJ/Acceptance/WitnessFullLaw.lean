/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Acceptance.Witness

/-!
# An instance of Example 5.4 with every perturbation direction nonzero

Statement numbers refer to the well-posedness paper at `1f67672`. The baseline is that of
`MVFBSDEJ.Acceptance.cor_robust_hypotheses` (Example 5.1(i) with `β₁ = β₂ = 2`, margin
`c_diss = 1`); the perturbation of Example 5.4 has `ε = 1/8`, the profiles `min(|·|, 1)`, the
feature `min(‖u‖, 1)`, and the directions `w₀ = w₁ = v₀ = e₁` and `ĥ = e₁ ∈ L²(δ₀; ℝ¹)`, all of
norm `1`: then `L_p = 1/2` and (5.1) reads `1/2 < 1`.

## Main statements

* `MVFBSDEJ.Acceptance.ex_fulllaw_jump_hypotheses` — the instance.
-/

open MeasureTheory ProbabilityTheory

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.PaperSpec
  MVFBSDEJ.WellPosedness.Stability LevyStochCalc

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = 2`, `σ_c = 0` and
`h_c = 0`. -/
local notation "sysL" =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 2 2 0 0

/-- **The hypotheses of Example 5.4 hold with every perturbation direction nonzero.** The
baseline of `cor_robust_hypotheses` (Example 5.1(i) with `β₁ = β₂ = 2`, with (2.3) and
Assumptions 2.2–2.5 at `L₀ = 2`, `G = 1`, `α = β₁ = β₂ = 1`, and (2.13) with margin
`c_diss = 1`), and the data `ε = 1/8`, `𝔮 = 𝔮̃ = 𝔮̂ = min(|·|, 1)`, `Q(s) = min(|s₁|, 1)`,
`φ₁(u) = min(‖u‖, 1)`, the directions `w₀ = w₁ = v₀ = e₁` and `ĥ = e₁ ∈ L²(δ₀; ℝ¹)`, each
nonzero, with Lipschitz constants `1`: then `L_p = 1/2` and (5.1) reads `1/2 < 1`. -/
theorem ex_fulllaw_jump_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (_ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 sysL
      ∧ Assumption22 (enlJoint ⊥ D bot_le) P 1 sysL (fun _ => 0)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 2 sysL
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 sysL
      ∧ Margin213 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 sysL
      ∧ (0 : ℝ) < 1
      ∧ ∃ (ε : ℝ) (q qb qh : ℝ → ℝ) (Q : EuclideanSpace ℝ (Fin 1) → ℝ)
        (φ : Fin 1 → Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ)) → ℝ)
        (w₀ w₁ v₀ : EuclideanSpace ℝ (Fin 1))
        (hhat : Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ)))
        (Lq Lqb Lqh LQ : ℝ) (K : Fin 1 → ℝ),
        0 < ε ∧ 0 ≤ Lq ∧ 0 ≤ Lqb ∧ 0 ≤ Lqh ∧ 0 ≤ LQ
        ∧ (∀ r r', |q r - q r'| ≤ Lq * |r - r'|) ∧ (∀ r r', |qb r - qb r'| ≤ Lqb * |r - r'|)
        ∧ (∀ r r', |qh r - qh r'| ≤ Lqh * |r - r'|) ∧ (∀ v v', |Q v - Q v'| ≤ LQ * ‖v - v'‖)
        ∧ (∀ j u u', |φ j u - φ j u'| ≤ K j * ‖u - u'‖)
        ∧ ε * ‖GX (1 : Matrix (Fin 1) (Fin 1) ℝ)‖ * (‖w₀‖ * Lq + ‖v₀‖ * Lqb
          + ‖w₁‖ * (LQ * Real.sqrt (∑ j, K j ^ 2)) + ‖hhat‖ * Lqh) < 1
        ∧ w₀ ≠ 0 ∧ w₁ ≠ 0 ∧ v₀ ≠ 0 ∧ hhat ≠ 0 := by
  obtain ⟨Ω, _, P, _, D, hind, hJ, h22, h23, hG, h25, h213, h01, -⟩ := cor_robust_hypotheses
  have he : ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1))‖ = 1 := by simp
  have hGn : ‖GX (1 : Matrix (Fin 1) (Fin 1) ℝ)‖ = 1 := by
    rw [GX_one]
    exact ContinuousLinearMap.norm_id
  have hne : (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)) ≠ 0 := fun h => by
    rw [h, norm_zero] at he
    exact zero_ne_one he
  have hhne : Lp.const 2 (Measure.dirac (0 : ℝ)) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
      ≠ 0 := fun h => by
    have h1 := norm_const_single_dirac
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind, hJ, h22, h23, hG, h25, h213, h01, 1 / 8,
    fun r => min |r| 1, fun r => min |r| 1, fun r => min |r| 1, fun v => min |v 0| 1,
    fun _ u => min ‖u‖ 1, EuclideanSpace.single 0 1, EuclideanSpace.single 0 1,
    EuclideanSpace.single 0 1,
    Lp.const 2 (Measure.dirac (0 : ℝ)) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)), 1, 1, 1, 1,
    fun _ => 1, by norm_num, zero_le_one, zero_le_one, zero_le_one, zero_le_one,
    abs_minAbsOne_sub_le, abs_minAbsOne_sub_le, abs_minAbsOne_sub_le, abs_minCoordOne_sub_le,
    fun _ => abs_minNormOne_sub_le, ?_, hne, hne, hne, hhne⟩
  rw [hGn, he, norm_const_single_dirac]
  norm_num

end MVFBSDEJ.Acceptance
