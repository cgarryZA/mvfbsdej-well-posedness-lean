/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4BackwardYoung
import Dissertation.WellPosedness.Spec.NotBackwardYoung
import Dissertation.Acceptance.A.Sec4

/-!
# The Young bound (4.25) of the proof of Lemma 4.3: the printed form and the corrected form

Statement and equation numbers refer to the well-posedness paper at `f598204`. The printed bound
(4.25), for every `ε > 0` with `C` independent of `ε`, is false: for the law-free system
`b = x − y`, `σ = −z`, `h = −u`, `f = x + y`, `g(x, ρ) = x` with `n = m = d = 1`, `ν = δ₀` on `ℝ`
and `T = 1`, which satisfies (2.3) and Assumptions 2.3–2.5 with `L = 2`, `G = 1` and
`α = β₁ = β₂ = 1`, the solutions `(0, e^{−t}, 0, 0)` and `0` of (4.1) at `λ = 1`, with initial
data `0` and the forcings `q^b_t = e^{−t}`, `q^g_T = e^{−T}`, resp. `0`, give
`2 e^{−2s} ≤ (C/ε) e^{−2s}` at every `s ∈ [0, 1]`, which fails for `ε = |C| + 1`. For
`ε ∈ (0, 1]` the bound holds with `C = 2 (10 (2L)²) + 3`.

## Main statements

* `Dissertation.Acceptance.A.eq_bwdyoung_corr` — (4.25) for `ε ∈ (0, 1]`.
* `Dissertation.Acceptance.A.eq_bwdyoung_corr_hypotheses` — the hypotheses of (4.25) at the
  system and the two solutions above, where the expectation `𝔼⟨δY_s, λ δf_s + δq^f_s⟩` is
  `e^{−2s}` at every `s ∈ [0, 1]`.
* `Dissertation.Acceptance.A.eq_bwdyoung_false` — (4.25) for every `ε > 0` is false.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.PaperSpec.A LevyStochCalc

universe u v w

/-- (4.25) for `ε ∈ (0, 1]`, with `C = 2 (10 (2L)²) + 3`. -/
theorem eq_bwdyoung_corr : PaperSpec.A.eq_bwdyoung_corr.{u, v, w} := by
  refine ⟨fun _ L _ _ _ _ _ _ => 2 * (10 * (2 * L) ^ 2) + 3, ?_⟩
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ _ ε hε hε1
  exact PaperWeakSolutionForcedInt.ae_backwardYoung_le h₁ h₂ hT.le (hlow.le.trans hlam) hlam1 hε
    hε1 h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone

/-- The system `b = x − y`, `σ = −z`, `h = −u`, `f = x + y`, `g(x, ρ) = x` with `n = d = 1` and
`ν = δ₀` on `ℝ`. -/
local notation "sk" => skewCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1)

/-- **The hypotheses of (4.25) hold at a pair of solutions with distinct backward components.**
Over a probability space carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`,
`n = m = 1` and `T = 1`: the system `b = x − y`, `σ = −z`, `h = −u`, `f = x + y`, `g(x, ρ) = x`
satisfies (2.3) and Assumptions 2.3–2.5 with `L = 2`, `G = 1` and `α = β₁ = β₂ = 1`; the initial
datum `0` is `ℱ₀`-measurable; the forcings `q^b_t = e^{−t}` on `[0, 1]`, `q^g_T = e^{−1}`,
`q^σ = q^h = q^f = 0` and `q = 0` are forcings of (4.1); `Θ¹ = (0, e^{−t}, 0, 0)` and `Θ² = 0`
solve (4.1) at `λ = 1` from `0` with these forcings in `ℍ_weak`, `Θ¹ − Θ² ∈ ℍ`; and at every
`s ∈ [0, 1]`, `𝔼⟨δY_s, λ δf_s + δq^f_s⟩ = e^{−2s}`. -/
theorem eq_bwdyoung_corr_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 sk
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 2 sk
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 sk
      ∧ Measurable[enlJoint ⊥ D bot_le 0] (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1)))
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 (skewQb 1 1)
          (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (0 : Fin 1 → ℝ → Ω → ℝ → ℝ) (0 : Fin 1 → Ω → ℝ → ℝ)
          (skewQg 1 1)
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 (skewQb 0 1)
          (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (0 : Fin 1 → ℝ → Ω → ℝ → ℝ) (0 : Fin 1 → Ω → ℝ → ℝ)
          (skewQg 0 1)
      ∧ WeakForcedSolution D bot_le hind₀ 1 1 sk (fun _ => 0) (skewQb 1 1) 0 0 0 (skewQg 1 1) 0
          (skewY 1) 0 0
      ∧ WeakForcedSolution D bot_le hind₀ 1 1 sk (fun _ => 0) (skewQb 0 1) 0 0 0 (skewQg 0 1) 0
          (skewY 0) 0 0
      ∧ supSize P (Measure.dirac (0 : ℝ)) 1
          (fun i t ω => (0 : Fin 1 → ℝ → Ω → ℝ) i t ω - (0 : Fin 1 → ℝ → Ω → ℝ) i t ω)
          (fun k t ω => skewY 1 k t ω - skewY 0 k t ω)
          (fun k t ω j => (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) k t ω j
            - (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) k t ω j)
          (fun k t ω e => (0 : Fin 1 → ℝ → Ω → ℝ → ℝ) k t ω e
            - (0 : Fin 1 → ℝ → Ω → ℝ → ℝ) k t ω e) < ⊤
      ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1,
          ∫ ω, ∑ k, (skewY 1 k s ω - skewY 0 k s ω)
              * (1 * (driverProc P 1 sk 0 (skewY 1) 0 0 k ω s
                  - driverProc P 1 sk 0 (skewY 0) 0 0 k ω s)
                + ((0 : Fin 1 → Ω → ℝ → ℝ) k ω s - (0 : Fin 1 → Ω → ℝ → ℝ) k ω s)) ∂P
            = Real.exp (-s) ^ 2 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨hJ, h23, hG, h25⟩ := skew_assumptions (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1)
    (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
  have hsol : ∀ a : ℝ, WeakForcedSolution D bot_le hind₀ 1 1 sk (fun _ => 0) (skewQb a 1) 0 0 0
      (skewQg a 1) 0 (skewY a) 0 0 := fun a =>
    (forcedSolution_of_paperSolutionForced (ξ₀ := fun _ => (0 : EuclideanSpace ℝ (Fin 1)))
      zero_le_one
      (skew_paperSolutionForced (crossWitnessEnl D bot_le hind₀) (hF0_enlJoint D bot_le)
        (fun _ hs h0 => measurableSet_enlJoint_of_null D bot_le hs h0) one_pos a)
      (fun _ _ _ _ => ⟨0, tendsto_const_nhds⟩)
      fun _ _ t _ => ⟨a * Real.exp (-t), ((by fun_prop : Continuous fun s : ℝ =>
        a * Real.exp (-s)).tendsto t).mono_left nhdsWithin_le_nhds⟩).1
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hJ, h23, hG, h25, measurable_const,
    skew_predForcing 1, skew_predForcing 0, hsol 1, hsol 0, supSize_skew_lt_top 1 0,
    fun s hs => ?_⟩
  rw [integral_pairing_skew 1 0 hs]
  simp

/-- (4.25) for every `ε > 0`, with `C` independent of `ε`, is false. -/
theorem eq_bwdyoung_false : ¬ PaperSpec.A.eq_bwdyoung.{0, 0, w} := by
  rintro ⟨K, hK⟩
  obtain ⟨Ω, _, P, _, D, hind₀, hJ, h23, hG, h25, hξ, hq₁, hq₂, hs₁, hs₂, hsup, -⟩ :=
    eq_bwdyoung_corr_hypotheses.{w}
  set c := K 1 2 ‖GX (1 : Matrix (Fin 1) (Fin 1) ℝ)‖ (sMin (1 : Matrix (Fin 1) (Fin 1) ℝ) ^ 2)⁻¹
    1 1 1 1 with hc
  have hε : (0 : ℝ) < |c| + 1 := by positivity
  have h := hK ⊥ (Measure.dirac (0 : ℝ)) 1 1 1 P D bot_le hind₀ one_pos one_pos one_pos 1
    one_pos 2 1 1 1 1 sk hJ h23 hG h25 1 1 one_pos le_rfl le_rfl le_rfl _ _ hξ hξ _ _ _ _ _ _ _ _
    _ _ hq₁ hq₂ _ _ _ _ _ _ _ _ hs₁ hs₂ hsup (|c| + 1) hε
  haveI : (ae (volume.restrict (Set.Icc (0 : ℝ) 1))).NeBot := by
    rw [ae_restrict_neBot, Real.volume_Icc]
    norm_num
  obtain ⟨s, hs, hsT⟩ := (h.and (ae_restrict_mem measurableSet_Icc)).exists
  rw [integral_pairing_skew 1 0 hsT, lintegral_esq_skewY_sub] at hs
  simp only [Pi.zero_apply, sub_self, esq, nnnorm_zero, ENNReal.coe_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, lintegral_const,
    zero_mul, add_zero, mul_zero] at hs
  set x : ℝ := ((1 : ℕ) : ℝ) * ((1 - 0) * Real.exp (-s)) ^ 2 with hx
  have hx0 : 0 < x := by
    rw [hx]
    positivity
  have hcε : c / (|c| + 1) ≤ 1 := (div_le_one hε).mpr (by linarith [le_abs_self c])
  have h1 : ENNReal.ofReal (c / (|c| + 1)) * ENNReal.ofReal x ≤ ENNReal.ofReal x :=
    mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.mpr hcε)
  have h2 : ENNReal.ofReal x < ENNReal.ofReal (2 * x) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  exact absurd (hs.trans h1) (not_le.mpr h2)

end Dissertation.Acceptance.A
