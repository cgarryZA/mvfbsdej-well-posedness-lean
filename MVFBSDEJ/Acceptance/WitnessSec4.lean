/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Acceptance.Witness

/-!
# Instances of the hypotheses of Lemmas 4.3 and 4.4 of paper A

Statement numbers refer to the well-posedness paper at `1f67672`. Both instances are those of
`MVFBSDEJ.Acceptance.thm_cwp_hypotheses`: a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`,
`𝒢₀ = ⊥`, `n = m = 1`, `T = 1`, and the system of Example 5.1(i) with `β₁ = β₂ = 1`,
`σ_c = h_c = 0`.

## Main statements

* `MVFBSDEJ.Acceptance.lem_pert_two_data_hypotheses` — the hypotheses of Lemma 4.3 at
  `λ̲ = λ = 1`, zero forcings and the two initial data `0` and `e₁`, with the solutions of
  Theorem 3.5 from these data, whose data size in Lemma 4.3 is `1`.
* `MVFBSDEJ.Acceptance.lem_cont_hypotheses` — the hypotheses of Lemma 4.4 together with
  `WP(λ₀)` at `λ* = λ₀`, the constant of Lemma 4.2.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.PaperSpec
  MVFBSDEJ.WellPosedness.Stability LevyStochCalc

universe w

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = β`, `σ_c = 0` and
`h_c = 0`. -/
local notation "sys " β:max =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) β β 0 0

/-- The unit vector `e₁ ∈ ℝ¹`. -/
local notation "e₁" => (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1))

/-- **The hypotheses of Lemma 4.3 hold at Example 5.1(i), from two initial data.** At the
instance of `thm_cwp_hypotheses`, the system satisfies (2.3) and Assumptions 2.3–2.5; `λ̲ = λ = 1`;
the zero forcing is a forcing of (4.1) and the initial data `0` and `e₁` are `ℱ₀`-measurable; the
solutions of Theorem 3.5 from these data solve (4.1) at `λ = 1` with zero forcing in `ℍ_weak`;
their difference lies in `ℍ`; and the data size on the right of the estimate of Lemma 4.3 is
`𝔼|δξ₀|² = 1`. -/
theorem lem_pert_two_data_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 (sys 1)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 (sys 1)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 (sys 1)
      ∧ Measurable[enlJoint ⊥ D bot_le 0] (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1)))
      ∧ Measurable[enlJoint ⊥ D bot_le 0] (fun _ : Ω => e₁)
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1
          (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (0 : Fin 1 → ℝ → Ω → ℝ → ℝ)
          (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → Ω → ℝ)
      ∧ ∃ (X₁ X₂ : Fin 1 → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ)
          (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U₁ U₂ : Fin 1 → ℝ → Ω → ℝ → ℝ),
          WeakForcedSolution D bot_le hind₀ 1 1 (sys 1) (fun _ => 0) 0 0 0 0 0 X₁ Y₁ Z₁ U₁
          ∧ WeakForcedSolution D bot_le hind₀ 1 1 (sys 1) (fun _ => e₁) 0 0 0 0 0 X₂ Y₂ Z₂ U₂
          ∧ supSize P (Measure.dirac (0 : ℝ)) 1 (fun i t ω => X₁ i t ω - X₂ i t ω)
              (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
              (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤
          ∧ dataSize P (Measure.dirac (0 : ℝ)) 1
              (fun i ω => (0 : EuclideanSpace ℝ (Fin 1)) i - e₁ i)
              (fun i ω s => (0 : Fin 1 → Ω → ℝ → ℝ) i ω s - (0 : Fin 1 → Ω → ℝ → ℝ) i ω s)
              (fun i s ω j => (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) i s ω j
                - (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) i s ω j)
              (fun i s ω e => (0 : Fin 1 → ℝ → Ω → ℝ → ℝ) i s ω e
                - (0 : Fin 1 → ℝ → Ω → ℝ → ℝ) i s ω e)
              (fun k ω s => (0 : Fin 1 → Ω → ℝ → ℝ) k ω s - (0 : Fin 1 → Ω → ℝ → ℝ) k ω s)
              (fun k ω => (0 : Fin 1 → Ω → ℝ) k ω - (0 : Fin 1 → Ω → ℝ) k ω) = 1 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨hJ, h22, h23, hG, h25⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (0 : EuclideanSpace ℝ (Fin 1))
  obtain ⟨-, h22', -, -, -⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos e₁
  have e : max (max (1 : ℝ) 1) 1 = 1 := by norm_num
  rw [e] at h23
  obtain ⟨X₁, Y₁, Z₁, U₁, hs₁⟩ := (thm_cwp ⊥ _ 1 1 1 P D bot_le hind₀ one_pos one_pos
    one_pos 1 one_pos 1 1 1 1 1 _ _ hJ h22 h23 hG h25).1
  obtain ⟨X₂, Y₂, Z₂, U₂, hs₂⟩ := (thm_cwp ⊥ _ 1 1 1 P D bot_le hind₀ one_pos one_pos
    one_pos 1 one_pos 1 1 1 1 1 _ _ hJ h22' h23 hG h25).1
  obtain ⟨Cst, hC⟩ := thm_stab.{0, 0, w}
  have hle := hC ⊥ _ 1 1 1 P D bot_le hind₀ one_pos one_pos one_pos 1 one_pos 1 1 1 1 1 1 _ _ _ _
    hJ h22 h23 hG h25 hJ h22' h23 X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hs₁ hs₂
  have hdata : dataSize P (Measure.dirac (0 : ℝ)) 1
      (fun i ω => (0 : EuclideanSpace ℝ (Fin 1)) i - e₁ i)
      (fun i ω s => (0 : Fin 1 → Ω → ℝ → ℝ) i ω s - (0 : Fin 1 → Ω → ℝ → ℝ) i ω s)
      (fun i s ω j => (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) i s ω j
        - (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) i s ω j)
      (fun i s ω e => (0 : Fin 1 → ℝ → Ω → ℝ → ℝ) i s ω e
        - (0 : Fin 1 → ℝ → Ω → ℝ → ℝ) i s ω e)
      (fun k ω s => (0 : Fin 1 → Ω → ℝ → ℝ) k ω s - (0 : Fin 1 → Ω → ℝ → ℝ) k ω s)
      (fun k ω => (0 : Fin 1 → Ω → ℝ) k ω - (0 : Fin 1 → Ω → ℝ) k ω) = 1 := by
    simp [dataSize, esq, Brownian.Ito.energy, Poisson.Compensated.markedEnergy]
  obtain ⟨⟨⟨γ₁, h₁⟩, hX₁, hY₁⟩, -, -⟩ := hs₁
  obtain ⟨⟨⟨γ₂, h₂⟩, hX₂, hY₂⟩, -, -⟩ := hs₂
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hJ, h23, hG, h25, measurable_const,
    measurable_const, { toForcing := Forcing.zero, qh_pred := fun _ => measurable_const },
    X₁, X₂, Y₁, Y₂, Z₁, Z₂, U₁, U₂,
    ⟨⟨γ₁, paperWeakSolutionForcedInt_one_zero_iff.mpr h₁⟩, hX₁, hY₁⟩,
    ⟨⟨γ₂, paperWeakSolutionForcedInt_one_zero_iff.mpr h₂⟩, hX₂, hY₂⟩,
    lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_), hdata⟩
  simp only [sub_self]
  simp [dataSize, esq, Brownian.Ito.energy, Poisson.Compensated.markedEnergy]

/-- **The hypotheses of Lemma 4.4 hold at Example 5.1(i), with `WP(λ₀)`.** At the instance of
`thm_cwp_hypotheses`, the system with initial datum `0` satisfies (2.3) and Assumptions 2.2–2.5;
and for `λ*` and `λ₀` both equal to the constant `λ*(1, 1) ∈ (0, 1]` of Lemma 4.2, `WP(λ₀)`
holds. -/
theorem lem_cont_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 (sys 1)
      ∧ Assumption22 (enlJoint ⊥ D bot_le) P 1 (sys 1) (fun _ => 0)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 (sys 1)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 (sys 1)
      ∧ ∃ lamStar lam0 : ℝ, 0 < lamStar ∧ lamStar ≤ 1 ∧ lamStar ≤ lam0 ∧ lam0 ≤ 1
          ∧ WP D bot_le hind₀ 1 lam0 (sys 1) (fun _ => 0) := by
  obtain ⟨Ω, _, P, _, D, hind₀, hJ, h22, h23, hG, h25⟩ := thm_cwp_hypotheses.{w}
  obtain ⟨lamStar, hsmall⟩ := lem_small.{0, 0, w}
  obtain ⟨hpos, hle, hwp⟩ := hsmall ⊥ (Measure.dirac (0 : ℝ)) 1 1 1 P D bot_le hind₀ one_pos
    one_pos one_pos 1 one_pos 1 (sys 1) (fun _ => 0) hJ h22 h23
  exact ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hJ, h22, h23, hG, h25, lamStar 1 1,
    lamStar 1 1, hpos, hle, le_rfl, hle, hwp _ hpos.le le_rfl⟩

end MVFBSDEJ.Acceptance
