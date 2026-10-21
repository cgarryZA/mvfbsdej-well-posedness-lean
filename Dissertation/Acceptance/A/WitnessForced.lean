/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Acceptance.A.Sec4Continuation
import Dissertation.Acceptance.A.WitnessNonzero
import Dissertation.WellPosedness.Existence.ForcingAlgebra

/-!
# An instance of the hypotheses of Lemma 4.3 with two stochastic forcings

Statement numbers refer to the well-posedness paper at `1f67672`. The instance is that of
`Dissertation.Acceptance.A.thm_cwp_hypotheses`: a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`,
`𝒢₀ = ⊥`, `n = m = 1`, `T = 1`, and the system of Example 5.1(i) with `β₁ = β₂ = 1`,
`σ_c = h_c = 0`, whose diffusion coefficient is `σ = −z`. At `λ̲ = λ = 1` and the initial datum
`0`, the solutions of (4.1) in `ℍ` for the zero forcing and for the forcing with diffusion
component `q^σ = 1_{(0, 1]}`, which exist by `WP(1)` (the proof of Theorem 3.5), are two solutions
of Lemma 4.3 whose difference has `δZ ≠ 0` or `λ δσ + δq^σ ≠ 0`: the two add up to
`−1_{(0, 1]}`.

## Main statements

* `Dissertation.Acceptance.A.lem_pert_forced_hypotheses` — the instance.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.PaperSpec.A
  Dissertation.WellPosedness.Stability LevyStochCalc

universe w

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = β`, `σ_c = 0` and
`h_c = 0`. -/
local notation "sys " β:max =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) β β 0 0

/-- The diffusion process of Example 5.1(i) with `σ_c = 0` along a tuple is `−Z`, cut to
`[0, T]`. -/
theorem diffusionProc_affine {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : ℝ} {X Y : Fin 1 → ℝ → Ω → ℝ} {Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ}
    {U : Fin 1 → ℝ → Ω → ℝ → ℝ} (s : ℝ) (ω : Ω) :
    diffusionProc P T (sys 1) X Y Z U 0 s ω 0
      = (Set.Icc (0 : ℝ) T).indicator (fun s => -Z 0 s ω 0) s := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · simp [diffusionProc, Set.indicator_of_mem hs, affineCoeffs, tupleAt]
  · simp [diffusionProc, Set.indicator_of_notMem hs]

/-- **The hypotheses of Lemma 4.3 hold at Example 5.1(i) with two stochastic forcings.** At the
instance of `thm_cwp_hypotheses`, the system satisfies (2.3) and Assumptions 2.3–2.5; `λ̲ = λ = 1`;
the initial datum `0` is `ℱ₀`-measurable; the zero forcing and the forcing
`q = (0, 1_{(0, 1]}, 0, 0, 0)`, whose diffusion component is the window `1_{(0, 1]}`, are forcings
of (4.1); the solutions of (4.1) at `λ = 1` from the datum `0` with these forcings lie in
`ℍ_weak`, and their difference lies in `ℍ`; and the difference is not degenerate: `δZ` or the
forced diffusion difference `λ δσ + δq^σ` has nonzero energy. -/
theorem lem_pert_forced_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 (sys 1)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 (sys 1)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 (sys 1)
      ∧ Measurable[enlJoint ⊥ D bot_le 0] (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1)))
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1
          (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (0 : Fin 1 → ℝ → Ω → ℝ → ℝ)
          (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → Ω → ℝ)
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1
          (0 : Fin 1 → Ω → ℝ → ℝ) (fun (_ : Fin 1) s (_ : Ω) (_ : Fin 1) => unitWindow s)
          (0 : Fin 1 → ℝ → Ω → ℝ → ℝ)
          (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → Ω → ℝ)
      ∧ ∃ (X₁ X₂ : Fin 1 → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ)
          (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U₁ U₂ : Fin 1 → ℝ → Ω → ℝ → ℝ),
          WeakForcedSolution D bot_le hind₀ 1 1 (sys 1) (fun _ => 0) 0 0 0 0 0 X₁ Y₁ Z₁ U₁
          ∧ WeakForcedSolution D bot_le hind₀ 1 1 (sys 1) (fun _ => 0) 0
              (fun (_ : Fin 1) s (_ : Ω) (_ : Fin 1) => unitWindow s) 0 0 0 X₂ Y₂ Z₂ U₂
          ∧ supSize P (Measure.dirac (0 : ℝ)) 1 (fun i t ω => X₁ i t ω - X₂ i t ω)
              (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
              (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤
          ∧ (Brownian.Ito.energy P 1 (fun ω s => Z₁ 0 s ω 0 - Z₂ 0 s ω 0) ≠ 0
            ∨ Brownian.Ito.energy P 1 (fun ω s =>
                1 * (diffusionProc P 1 (sys 1) X₁ Y₁ Z₁ U₁ 0 s ω 0
                  - diffusionProc P 1 (sys 1) X₂ Y₂ Z₂ U₂ 0 s ω 0)
                + ((0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) 0 s ω 0 - unitWindow s)) ≠ 0) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  set ℱ := enlJoint ⊥ D bot_le with hℱdef
  obtain ⟨hJ, h22, h23, hG, h25⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := ℱ) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (0 : EuclideanSpace ℝ (Fin 1))
  have e : max (max (1 : ℝ) 1) 1 = 1 := by norm_num
  rw [e] at h23
  -- the two forcings
  have hq₀ : PredForcing ℱ P (Measure.dirac (0 : ℝ)) 1
      (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (0 : Fin 1 → ℝ → Ω → ℝ → ℝ)
      (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → Ω → ℝ) :=
    { toForcing := Forcing.zero, qh_pred := fun _ => measurable_const }
  have hE : Brownian.Ito.energy P 1 (fun (_ : Ω) s => unitWindow s) = 1 := by
    simp [Brownian.Ito.energy, setLIntegral_unitWindow_sq]
  have hZw : ∀ j : Fin 1, Probability.Predictable ℱ fun (_ : Ω) s => unitWindow s :=
    fun _ => predictable_unitWindow ℱ
  have hZv : ∀ (ω : Ω) s, s ∉ Set.Icc (0 : ℝ) 1 → (fun (_ : Fin 1) => unitWindow s) = 0 :=
    fun _ _ hs => funext fun _ => unitWindow_of_notMem hs
  have z := (Forcing.zero : Forcing ℱ P (Measure.dirac (0 : ℝ)) 1
      (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (0 : Fin 1 → ℝ → Ω → ℝ → ℝ)
      (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → Ω → ℝ))
  have hq₁ : PredForcing ℱ P (Measure.dirac (0 : ℝ)) 1
      (0 : Fin 1 → Ω → ℝ → ℝ) (fun (_ : Fin 1) s (_ : Ω) (_ : Fin 1) => unitWindow s)
          (0 : Fin 1 → ℝ → Ω → ℝ → ℝ)
      (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → Ω → ℝ) :=
    { qb_meas := z.qb_meas
      qb_prog := z.qb_prog
      qb_vanish := z.qb_vanish
      qb_sq := z.qb_sq
      qσ_meas := fun _ _ => measurable_unitWindow.comp measurable_snd
      qσ_prog := fun _ => progressivelyMeasurable_of_predictable_of_vanish
        (Z := fun s (_ : Ω) (_ : Fin 1) => unitWindow s) hZw hZv
      qσ_vanish := fun _ ω s hs => hZv ω s hs
      qσ_sq := fun _ _ => by rw [hE]; exact ENNReal.one_ne_top
      qh_meas := z.qh_meas
      qh_prog := z.qh_prog
      qh_vanish := z.qh_vanish
      qh_sq := z.qh_sq
      qf_meas := z.qf_meas
      qf_prog := z.qf_prog
      qf_vanish := z.qf_vanish
      qf_sq := z.qf_sq
      qg_meas := z.qg_meas
      qg_sq := z.qg_sq
      qh_pred := fun _ => measurable_const }
  -- `WP(1)`, from the proof of Theorem 3.5
  obtain ⟨lamStar, zeta0, hthm⟩ := sec45_proof_thm35.{0, 0, w}
  have hwp := (hthm ⊥ (Measure.dirac (0 : ℝ)) 1 1 1 P D bot_le hind₀ one_pos one_pos one_pos 1
    one_pos 1 1 1 1 1 (sys 1) (fun _ => 0) hJ h22 h23 hG h25).2.2.2.2.2.2.2.2.2
  obtain ⟨⟨X₁, Y₁, Z₁, U₁, hs₁⟩, -⟩ := hwp _ _ _ _ _ hq₀
  obtain ⟨⟨X₂, Y₂, Z₂, U₂, hs₂⟩, -⟩ := hwp _ _ _ _ _ hq₁
  have hsup := ForcedSolution.supSize_sub_lt_top one_pos hJ h22.origin h23 hJ h22.origin h23 hs₁
    hs₂
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hJ, h23, hG, h25, measurable_const, hq₀,
    hq₁, X₁, X₂, Y₁, Y₂, Z₁, Z₂, U₁, U₂, hs₁.1, hs₂.1, hsup, ?_⟩
  -- `δZ + (λ δσ + δq^σ) = −1_{(0, 1]}`
  obtain ⟨⟨γ₁, hp₁⟩, -, -⟩ := hs₁.1
  obtain ⟨⟨γ₂, hp₂⟩, -, -⟩ := hs₂.1
  have hZm : Measurable (Function.uncurry fun ω s => Z₁ 0 s ω 0 - Z₂ 0 s ω 0) :=
    (Brownian.Ito.measurable_uncurry_of_predictable (hp₁.Z_pred 0 0)).sub
      (Brownian.Ito.measurable_uncurry_of_predictable (hp₂.Z_pred 0 0))
  have hsum : (fun ω s => (Z₁ 0 s ω 0 - Z₂ 0 s ω 0)
      + (1 * (diffusionProc P 1 (sys 1) X₁ Y₁ Z₁ U₁ 0 s ω 0
          - diffusionProc P 1 (sys 1) X₂ Y₂ Z₂ U₂ 0 s ω 0)
        + ((0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) 0 s ω 0 - unitWindow s)))
      = fun (_ : Ω) s => -unitWindow s := by
    funext ω s
    rw [diffusionProc_affine, diffusionProc_affine]
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
    · simp only [Set.indicator_of_mem hs, Pi.zero_apply]
      ring
    · have h1 := congrFun (hp₁.Z_vanish 0 ω s hs) 0
      have h2 := congrFun (hp₂.Z_vanish 0 ω s hs) 0
      simp only [Pi.zero_apply] at h1 h2
      simp only [Set.indicator_of_notMem hs, h1, h2, unitWindow_of_notMem hs, Pi.zero_apply]
      ring
  have hneg : Brownian.Ito.energy P 1 (fun (_ : Ω) s => -unitWindow s) = 1 := by
    simp [Brownian.Ito.energy, nnnorm_neg, setLIntegral_unitWindow_sq]
  by_contra hcon
  simp only [ne_eq, not_or, not_not] at hcon
  have hle := energy_add_le (P := P) (T := 1) hZm (fun ω s =>
    1 * (diffusionProc P 1 (sys 1) X₁ Y₁ Z₁ U₁ 0 s ω 0
      - diffusionProc P 1 (sys 1) X₂ Y₂ Z₂ U₂ 0 s ω 0)
    + ((0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) 0 s ω 0 - unitWindow s))
  rw [hsum, hneg, hcon.1, hcon.2] at hle
  simp at hle

end Dissertation.Acceptance.A
