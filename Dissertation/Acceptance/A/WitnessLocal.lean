/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Acceptance.A.WitnessNonzero

/-!
# A nonzero instance of Lemma 4.1

Over a probability space carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`,
`m = 1` and `T = 1`, the integrands `δZ = δU = 1_{(0, 1]}` (each of energy `1`), `φ = 0`, the
process `δY_t = ∫_0^t δZ dW + ∫_0^t ∫_E δU Ñ(ds, de)` (everywhere càdlàg versions) and
`δξ = δY_1` satisfy every hypothesis of Lemma 4.1. This is the instance at which the local
martingales of its proof are not zero.

## Main statements

* `Dissertation.Acceptance.A.lem_bpbsde_nonzero_hypotheses` — the instance.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Enlarged
  Dissertation.WellPosedness.Spec LevyStochCalc

/-- **The hypotheses of Lemma 4.1 hold at a nonzero instance.** Over a probability space
carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`, `m = 1` and `T = 1`: the
integrands `δZ = δU = 1_{(0, 1]}`, of energy `1` each, `φ = 0`, the sum `δY` of everywhere-càdlàg
versions of `∫_0^t δZ dW` and `∫_0^t ∫_E δU Ñ(ds, de)`, and `δξ = δY_1` satisfy every hypothesis of
Lemma 4.1. -/
theorem lem_bpbsde_nonzero_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
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
          (fun ω s e => δU 0 s ω e) = 1 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  set ℱ := enlJoint ⊥ D bot_le with hℱdef
  have hW := isBrownianFiltration_enlJoint D bot_le hind₀
  have hN := isPoissonFiltration_enlJoint D bot_le hind₀
  have hrc : ℱ.rightCont = ℱ := MeasureTheory.Filtration.IsRightContinuous.eq
  have hF0 := hF0_enlJoint D (bot_le : (⊥ : MeasurableSpace Ω) ≤ _)
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D bot_le hs h0
  set δZ : Fin 1 → ℝ → Ω → Fin 1 → ℝ := fun _ s _ _ => unitWindow s with hδZ
  set δU : Fin 1 → ℝ → Ω → ℝ → ℝ := fun _ s _ _ => unitWindow s with hδU
  have hE : Brownian.Ito.energy P 1 (fun (_ : Ω) s => unitWindow s) = 1 := by
    simp [Brownian.Ito.energy, setLIntegral_unitWindow_sq]
  have hEm : Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1
      (fun (_ : Ω) s (_ : ℝ) => unitWindow s) = 1 := by
    simp [Poisson.Compensated.markedEnergy, setLIntegral_unitWindow_sq]
  have hZ : ∀ k j, Probability.Predictable ℱ fun ω s => δZ k s ω j :=
    fun _ _ => predictable_unitWindow ℱ
  have hZv : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) 1 → δZ k s ω = 0 :=
    fun _ _ _ hs => funext fun _ => unitWindow_of_notMem hs
  have hZs : ∀ k j, Brownian.Ito.energy P 1 (fun ω s => δZ k s ω j) ≠ ⊤ :=
    fun _ _ => by rw [hδZ, hE]; exact ENNReal.one_ne_top
  have hU : ∀ k, Probability.MarkedPredictable ℱ (Measure.dirac (0 : ℝ))
      fun ω s e => δU k s ω e := fun _ => markedPredictable_unitWindow ℱ _
  have hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) 1 → δU k s ω e = 0 :=
    fun _ _ _ _ hs => unitWindow_of_notMem hs
  have hUs : ∀ k, Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1
      (fun ω s e => δU k s ω e) ≠ ⊤ := fun _ => by rw [hδU, hEm]; exact ENNReal.one_ne_top
  -- everywhere-càdlàg versions of the two integrals
  obtain ⟨VW, hVWad, -, hVWae, hVWcad, -, -, -⟩ :=
    BSDEJ.Solves.exists_cadlag_vectorIntegral_supBound D.W ℱ hW (δZ 0)
      (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ 0 j))
      (progressivelyMeasurable_of_predictable_of_vanish (hZ 0) (hZv 0))
      (BSDEJ.Solves.sq_int_global_of_vanishing (hZv 0) (hZs 0)) hF0 hnull 1 zero_le_one
  obtain ⟨VN, hVNad, hVNae, hVNr, hVNl⟩ :=
    Poisson.Compensated.exists_everywhere_cadlag_stochasticIntegral D.N ℱ hN
      (fun ω' s e => δU 0 s ω' e)
      ((hU 0).mono (Probability.markedPredictableSigma_le _ _) le_rfl)
      (hU 0).markedProgressivelyMeasurable
      (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv 0) (hUs 0)) hF0 hnull
  rw [hrc] at hVWad hVNad
  set δY : Fin 1 → ℝ → Ω → ℝ := fun _ t ω => VW t ω + VN t ω with hδY
  set δξ : Ω → EuclideanSpace ℝ (Fin 1) := fun ω => WithLp.toLp 2 fun _ => VW 1 ω + VN 1 ω
    with hδξ
  have hξm : Measurable[ℱ 1] δξ :=
    (stronglyMeasurable_iff_forall_coord.mpr fun _ => (hVWad 1).add (hVNad 1)).measurable
  have hVWL : MemLp (VW 1) 2 P := by
    refine MemLp.ae_eq (hVWae 1).symm ?_
    unfold Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
    refine memLp_finsetSum (ι := Fin 1) (μ := P) (p := 2) Finset.univ fun j _ => ?_
    exact (Lp.memLp _).ae_eq (Brownian.Ito.stochasticIntegralBrownian_ae_eq _ _ _ _ _ _ _ 1).symm
  have hVNL : MemLp (VN 1) 2 P :=
    MemLp.ae_eq (hVNae 1).symm (Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hN _ _ _ _ 1)
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, δξ, fun _ _ _ => 0, δY, δZ, δU, hZ, hZv,
    hZs, hU, hUv, hUs, hξm, ?_, fun _ => measurable_const, fun _ => by
      simp [Brownian.Ito.energy], fun _ t _ => (hVWad t).add (hVNad t),
    fun _ ω t _ => (hVWcad ω t).1.add (hVNr ω t), fun _ ω t _ => ?_, fun k t ht => ?_, ?_, ?_⟩
  · exact memLp_iff_forall_coord.mpr fun _ => hVWL.add hVNL
  · obtain ⟨L₁, h₁⟩ := (hVWcad ω t).2
    obtain ⟨L₂, h₂⟩ := hVNl ω t
    exact ⟨L₁ + L₂, h₁.add h₂⟩
  · filter_upwards [hVWae 1, hVWae t, hVNae 1, hVNae t] with ω h1 h2 h3 h4
    simp only [hδY, hδξ, PiLp.toLp_apply, MeasureTheory.integral_zero, add_zero]
    rw [← h1, ← h2, ← h3, ← h4]
    ring
  · rw [hδZ]
    exact hE
  · rw [hδU]
    exact hEm

end Dissertation.Acceptance.A
