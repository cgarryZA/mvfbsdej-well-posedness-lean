/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Acceptance.WitnessFrozen
import MVFBSDEJ.Acceptance.Sec4Frozen

/-!
# An instance of the hypotheses of the contraction chain of Lemma 4.2 of the well-posedness paper

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The instance is
that of `MVFBSDEJ.Acceptance.frozen_hypotheses`: a Lévy driver with `d = 1` and `ν = δ₀` on
`ℝ`, `𝒢₀ = ⊥`, `n = m = 1`, `T = 1`, the system of Example 5.1(i) with `β₁ = β₂ = 1`,
`σ_c = h_c = 0` and initial datum `0`, `λ = 1`, the zero forcing, and the two trials of `𝕊`, the
zero tuple and the constant tuple `(1, 1, 0, 0)`; their frozen steps exist by (4.8).

## Main statements

* `MVFBSDEJ.Acceptance.frozen_pair_hypotheses` — the hypotheses of (4.10), (4.12) and
  (4.13).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.PaperSpec
  MVFBSDEJ.WellPosedness.Stability LevyStochCalc

universe w

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = β`, `σ_c = 0` and
`h_c = 0`. -/
local notation "sys " β:max =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) β β 0 0

/-- **The hypotheses of the contraction chain of Lemma 4.2 hold at Example 5.1(i).** At the
instance of `frozen_hypotheses` — the system with initial datum `0`, (2.3) and Assumptions
2.2–2.3 with `L = 1`, the zero forcing, and the two distinct trials of `𝕊`, the zero tuple and
the constant tuple `(X, Y, Z, U) = (1, 1, 0, 0)` — each trial has a frozen step at `λ = 1`. -/
theorem frozen_pair_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 (sys 1)
      ∧ Assumption22 (enlJoint ⊥ D bot_le) P 1 (sys 1) (fun _ => 0)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 (sys 1)
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1
          (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (0 : Fin 1 → ℝ → Ω → ℝ → ℝ)
          (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → Ω → ℝ)
      ∧ HTuple (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1
          (fun (_ : Fin 1) _ _ => (0 : ℝ)) (fun (_ : Fin 1) _ _ => (0 : ℝ))
          (fun (_ : Fin 1) _ _ (_ : Fin 1) => (0 : ℝ)) (fun (_ : Fin 1) _ _ (_ : ℝ) => (0 : ℝ))
      ∧ HTuple (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1
          (fun (_ : Fin 1) _ _ => (1 : ℝ)) (fun (_ : Fin 1) _ _ => (1 : ℝ))
          (fun (_ : Fin 1) _ _ (_ : Fin 1) => (0 : ℝ)) (fun (_ : Fin 1) _ _ (_ : ℝ) => (0 : ℝ))
      ∧ ∃ (X₁' X₂' : Fin 1 → ℝ → Ω → ℝ) (Y₁' Y₂' : Fin 1 → ℝ → Ω → ℝ)
          (Z₁' Z₂' : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U₁' U₂' : Fin 1 → ℝ → Ω → ℝ → ℝ),
        FrozenStep D bot_le hind₀ 1 1 (sys 1) (fun _ => 0) 0 0 0 0 0
            (fun (_ : Fin 1) _ _ => (0 : ℝ)) (fun (_ : Fin 1) _ _ => (0 : ℝ))
            (fun (_ : Fin 1) _ _ (_ : Fin 1) => (0 : ℝ)) (fun (_ : Fin 1) _ _ (_ : ℝ) => (0 : ℝ))
            X₁' Y₁' Z₁' U₁'
          ∧ FrozenStep D bot_le hind₀ 1 1 (sys 1) (fun _ => 0) 0 0 0 0 0
            (fun (_ : Fin 1) _ _ => (1 : ℝ)) (fun (_ : Fin 1) _ _ => (1 : ℝ))
            (fun (_ : Fin 1) _ _ (_ : Fin 1) => (0 : ℝ)) (fun (_ : Fin 1) _ _ (_ : ℝ) => (0 : ℝ))
            X₂' Y₂' Z₂' U₂' := by
  obtain ⟨Ω, _, P, _, D, hind₀, hJ, h22, h23, hq, hH₀, hH₁⟩ := frozen_hypotheses.{w}
  obtain ⟨-, ⟨X₁', Y₁', Z₁', U₁', h₁⟩, -⟩ := eq_frozenbwd.{0, 0, w} ⊥ (Measure.dirac (0 : ℝ)) 1 1 1
    P D bot_le hind₀ one_pos one_pos one_pos 1 one_pos 1 (sys 1) (fun _ => 0) hJ h22 h23 1
    zero_le_one le_rfl 0 0 0 0 0 hq _ _ _ _ hH₀
  obtain ⟨-, ⟨X₂', Y₂', Z₂', U₂', h₂⟩, -⟩ := eq_frozenbwd.{0, 0, w} ⊥ (Measure.dirac (0 : ℝ)) 1 1 1
    P D bot_le hind₀ one_pos one_pos one_pos 1 one_pos 1 (sys 1) (fun _ => 0) hJ h22 h23 1
    zero_le_one le_rfl 0 0 0 0 0 hq _ _ _ _ hH₁
  exact ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hJ, h22, h23, hq, hH₀, hH₁, X₁', X₂', Y₁',
    Y₂', Z₁', Z₂', U₁', U₂', h₁, h₂⟩

end MVFBSDEJ.Acceptance
