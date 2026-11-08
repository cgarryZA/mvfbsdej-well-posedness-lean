/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec4Davis
import MVFBSDEJ.WellPosedness.Martingale.DavisCompensated
import MVFBSDEJ.Acceptance.WitnessLocal
import MVFBSDEJ.Acceptance.WitnessPert

/-!
# A constant of Davis's inequality

`24` is a constant of the Burkholder–Davis–Gundy inequality at `p = 1` in quadratic-variation form
for the local stochastic integrals of the filtration of the paper (`PaperSpec.DavisValid`): for a
local Itô integral the inequality holds with `9`, by Doob's `L²` inequality and Lenglart's
argument (`MVFBSDEJ.WellPosedness.Martingale.IsLocalBrownianIntegral.lintegral_biSup_le`), and
for a local compensated integral of a marked predictable integrand with `24`, by Davis's
decomposition
(`MVFBSDEJ.WellPosedness.Martingale.IsLocalCompensatedIntegral.lintegral_biSup_le_count`).
With it, the hypotheses of the bounds of Lemma 4.1 and (4.18) that use the constant at `p = 1`
hold at the instances of `lem_bpbsde_nonzero_hypotheses`, `lem_pert_backward_window_hypotheses`
and `lem_pert_forward_window_hypotheses`.

## Main statements

* `MVFBSDEJ.Acceptance.davisValid_twentyFour` — `DavisValid 24`.
* `MVFBSDEJ.Acceptance.lem_bpbsde_nonzero_davis_hypotheses`,
  `MVFBSDEJ.Acceptance.lem_pert_backward_window_davis_hypotheses`,
  `MVFBSDEJ.Acceptance.lem_pert_forward_window_davis_hypotheses` — `DavisValid 24` with those
  instances.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped ENNReal Topology

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.PaperSpec
  MVFBSDEJ.WellPosedness.Stability MVFBSDEJ.WellPosedness.BrownianPoisson
  MVFBSDEJ.WellPosedness.Martingale MVFBSDEJ.Law LevyStochCalc

universe u v w

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = 1`, `σ_c = 0` and
`h_c = 0`. -/
local notation "sysW" =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 1 1 0 0

/-- **`24` is a constant of Davis's inequality** for the local Itô integrals and the local
compensated integrals of marked predictable integrands of the filtration of the paper. -/
theorem davisValid_twentyFour : PaperSpec.DavisValid.{u, v, w} 24 := by
  refine ⟨fun 𝒢₀ _ E _ ν _ _ d P _ D h𝒢₀ hind₀ T hT H M hM => ?_,
    fun 𝒢₀ _ E _ ν _ _ d P _ D h𝒢₀ hind₀ T hT φ hφ h0 M hM => ?_⟩
  · refine (hM.lintegral_biSup_le D.W (enlJoint 𝒢₀ D h𝒢₀)
      (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
      (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT).trans ?_
    gcongr
    rw [show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by norm_num]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  · rw [show ENNReal.ofReal 24 = (24 : ℝ≥0∞) by norm_num]
    exact hM.lintegral_biSup_le_count D.N (enlJoint 𝒢₀ D h𝒢₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
      (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT hφ h0

/-- **The hypotheses of `lem41_MW`, `lem41_M1` and `lem41_M1_bdg` hold at an instance.** `24` is a
constant of Davis's inequality, and over a probability space carrying a Lévy driver with `d = 1`
and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`, `m = 1` and `T = 1`, the instance of
`lem_bpbsde_nonzero_hypotheses` satisfies every hypothesis of Lemma 4.1. -/
theorem lem_bpbsde_nonzero_davis_hypotheses :
    PaperSpec.DavisValid.{0, 0, w} 24
      ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
        (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)
        (δξ : Ω → EuclideanSpace ℝ (Fin 1)) (φ : Fin 1 → Ω → ℝ → ℝ) (δY : Fin 1 → ℝ → Ω → ℝ)
        (δZ : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (δU : Fin 1 → ℝ → Ω → ℝ → ℝ)
        (hZ : ∀ k j, Probability.Predictable (enlJoint ⊥ D bot_le) fun ω s => δZ k s ω j)
        (hZv : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) 1 → δZ k s ω = 0)
        (hZs : ∀ k j, Brownian.Ito.energy P 1 (fun ω s => δZ k s ω j) ≠ ⊤)
        (hU : ∀ k, Probability.MarkedPredictable (enlJoint ⊥ D bot_le) (Measure.dirac (0 : ℝ))
          fun ω s e => δU k s ω e)
        (hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) 1 → δU k s ω e = 0)
        (hUs : ∀ k, Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1
          (fun ω s e => δU k s ω e) ≠ ⊤),
        Measurable[enlJoint ⊥ D bot_le 1] δξ ∧ MemLp δξ 2 P
        ∧ (∀ k, Measurable (Function.uncurry (φ k))) ∧ (∀ k, Brownian.Ito.energy P 1 (φ k) ≠ ⊤)
        ∧ (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) 1, Measurable[enlJoint ⊥ D bot_le t] (δY k t))
        ∧ (∀ k ω, ∀ t ∈ Set.Ico (0 : ℝ) 1,
            Filter.Tendsto (fun s => δY k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (δY k t ω)))
        ∧ (∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∃ l : ℝ,
            Filter.Tendsto (fun s => δY k s ω) (nhdsWithin t (Set.Iio t)) (nhds l))
        ∧ (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂P,
          δY k t ω = δξ ω k + (∫ s in Set.Icc t 1, φ k ω s)
            - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (enlJoint ⊥ D bot_le)
                  (isBrownianFiltration_enlJoint D bot_le hind₀) (δZ k)
                  (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
                  (progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k))
                  (BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k)) 1 ω
                - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
                  (enlJoint ⊥ D bot_le) (isBrownianFiltration_enlJoint D bot_le hind₀) (δZ k)
                  (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
                  (progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k))
                  (BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k)) t ω)
            - (Poisson.Compensated.stochasticIntegral D.N (enlJoint ⊥ D bot_le)
                  (isPoissonFiltration_enlJoint D bot_le hind₀) (fun ω' s e => δU k s ω' e)
                  ((hU k).mono (Probability.markedPredictableSigma_le _ _) le_rfl)
                  (hU k).markedProgressivelyMeasurable
                  (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) 1 ω
                - Poisson.Compensated.stochasticIntegral D.N (enlJoint ⊥ D bot_le)
                  (isPoissonFiltration_enlJoint D bot_le hind₀) (fun ω' s e => δU k s ω' e)
                  ((hU k).mono (Probability.markedPredictableSigma_le _ _) le_rfl)
                  (hU k).markedProgressivelyMeasurable
                  (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) t ω))
        ∧ Brownian.Ito.energy P 1 (fun ω s => δZ 0 s ω 0) = 1
        ∧ Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1
            (fun ω s e => δU 0 s ω e) = 1 :=
  ⟨davisValid_twentyFour, lem_bpbsde_nonzero_hypotheses⟩

/-- **The hypotheses of `eq_bdg4_XZ` and `eq_bdg4_XU` hold at an instance.** `24` is a constant
of Davis's inequality, and the instance of `lem_pert_backward_window_hypotheses` satisfies the
hypotheses of Lemma 4.3. -/
theorem lem_pert_backward_window_davis_hypotheses :
    PaperSpec.DavisValid.{0, 0, w} 24
      ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
        (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)
        (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin 1))
        (qb₁ qb₂ : Fin 1 → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
        (qh₁ qh₂ : Fin 1 → ℝ → Ω → ℝ → ℝ) (qf₁ qf₂ : Fin 1 → Ω → ℝ → ℝ) (qg₁ qg₂ : Fin 1 → Ω → ℝ)
        (X₁ X₂ Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
        (U₁ U₂ : Fin 1 → ℝ → Ω → ℝ → ℝ),
        JointBorel 1 sysW ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 sysW
        ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
        ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 sysW
        ∧ Measurable[enlJoint ⊥ D bot_le 0] ξ₁ ∧ Measurable[enlJoint ⊥ D bot_le 0] ξ₂
        ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb₁ qσ₁ qh₁ qf₁ qg₁
        ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb₂ qσ₂ qh₂ qf₂ qg₂
        ∧ WeakForcedSolution D bot_le hind₀ 1 1 sysW ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁
        ∧ WeakForcedSolution D bot_le hind₀ 1 1 sysW ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂
        ∧ supSize P (Measure.dirac (0 : ℝ)) 1 (fun i t ω => X₁ i t ω - X₂ i t ω)
            (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
            (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤
        ∧ Brownian.Ito.energy P 1 (fun ω s => ∑ k, ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun i =>
            if s ∈ Set.Ioc (0 : ℝ) 1 then leftLimProc (fun a t ω => X₁ a t ω - X₂ a t ω) i s ω
            else 0) k * (Z₁ k s ω 0 - Z₂ k s ω 0)) = 1
        ∧ Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1 (fun ω s e => ∑ k,
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun i => if s ∈ Set.Ioc (0 : ℝ) 1 then
              leftLimProc (fun a t ω => X₁ a t ω - X₂ a t ω) i s ω else 0) k
            * (U₁ k s ω e - U₂ k s ω e)) = 1 :=
  ⟨davisValid_twentyFour, lem_pert_backward_window_hypotheses⟩

/-- **The hypotheses of `eq_bdg4_sigmaY` and `eq_bdg4_hY` hold at an instance.** `24` is a
constant of Davis's inequality, and the instance of `lem_pert_forward_window_hypotheses`
satisfies the hypotheses of Lemma 4.3. -/
theorem lem_pert_forward_window_davis_hypotheses :
    PaperSpec.DavisValid.{0, 0, w} 24
      ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
        (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)
        (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin 1))
        (qb₁ qb₂ : Fin 1 → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
        (qh₁ qh₂ : Fin 1 → ℝ → Ω → ℝ → ℝ) (qf₁ qf₂ : Fin 1 → Ω → ℝ → ℝ) (qg₁ qg₂ : Fin 1 → Ω → ℝ)
        (X₁ X₂ Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
        (U₁ U₂ : Fin 1 → ℝ → Ω → ℝ → ℝ),
        JointBorel 1 sysW ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 sysW
        ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
        ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 sysW
        ∧ Measurable[enlJoint ⊥ D bot_le 0] ξ₁ ∧ Measurable[enlJoint ⊥ D bot_le 0] ξ₂
        ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb₁ qσ₁ qh₁ qf₁ qg₁
        ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 qb₂ qσ₂ qh₂ qf₂ qg₂
        ∧ WeakForcedSolution D bot_le hind₀ 1 1 sysW ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁
        ∧ WeakForcedSolution D bot_le hind₀ 1 1 sysW ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂
        ∧ supSize P (Measure.dirac (0 : ℝ)) 1 (fun i t ω => X₁ i t ω - X₂ i t ω)
            (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
            (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤
        ∧ Brownian.Ito.energy P 1 (fun ω s => ∑ k, ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun i =>
            1 * (diffusionProc P 1 sysW X₁ Y₁ Z₁ U₁ i s ω 0
              - diffusionProc P 1 sysW X₂ Y₂ Z₂ U₂ i s ω 0) + (qσ₁ i s ω 0 - qσ₂ i s ω 0)) k
            * (if s ∈ Set.Ioc (0 : ℝ) 1 then
                leftLimProc (fun a t ω => Y₁ a t ω - Y₂ a t ω) k s ω else 0)) = 1
        ∧ ∀ H : Fin 1 → Ω → ℝ → ℝ → ℝ,
          (∀ i, ∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P (Measure.dirac (0 : ℝ)) 1),
            H i p.1 p.2.1 p.2.2
              = 1 * (jumpProc 1 (coeffJump P 1 sysW (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
                  p.2.1 p.1 p.2.2
                - jumpProc 1 (coeffJump P 1 sysW (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
                  p.2.1 p.1 p.2.2) + (qh₁ i p.2.1 p.1 p.2.2 - qh₂ i p.2.1 p.1 p.2.2)) →
          Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1 (fun ω s e => ∑ k,
            ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ fun i => H i ω s e) k
            * (if s ∈ Set.Ioc (0 : ℝ) 1 then
                leftLimProc (fun a t ω => Y₁ a t ω - Y₂ a t ω) k s ω else 0)) = 1 :=
  ⟨davisValid_twentyFour, lem_pert_forward_window_hypotheses⟩

end MVFBSDEJ.Acceptance
