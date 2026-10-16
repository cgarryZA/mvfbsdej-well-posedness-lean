/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec5Brownian
import Dissertation.Acceptance.A.Sec2Basics
import Dissertation.Acceptance.A.Sec5

/-!
# Example 5.2 of the well-posedness paper, two further clauses: proofs

## Main statements

* `Dissertation.Acceptance.A.ex_brownian_not_h0` — the martingale `𝔼[Ñ((0, T] × A) | ℱ_t]`, for
  `0 < ν(A) < ∞`, has no representation with `U = 0`, by the uniqueness clause of the
  representation property of §2.
* `Dissertation.Acceptance.A.ex_brownian_rank_gt` — the linear generator with `β₁ = 0`, `β₂ = 1`
  and `G` the diagonal matrix.
* `Dissertation.Acceptance.A.ex_brownian_not_h0_hypotheses`,
  `Dissertation.Acceptance.A.ex_brownian_rank_gt_hypotheses` — the hypotheses can be met.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Enlarged
  Dissertation.WellPosedness.Spec Dissertation.WellPosedness.Existence LevyStochCalc

universe u v w

/-- A σ-finite nonzero measure charges a measurable set of finite measure. -/
theorem exists_measurableSet_pos_lt_top {E : Type*} [MeasurableSpace E] {ν : Measure E}
    [SigmaFinite ν] (hν : ν ≠ 0) : ∃ A, MeasurableSet A ∧ 0 < ν A ∧ ν A < ⊤ := by
  by_contra! h
  refine hν (Measure.measure_univ_eq_zero.mp ?_)
  rw [← iUnion_spanningSets ν]
  refine measure_iUnion_null fun k => ?_
  by_contra h0
  exact (h _ (measurableSet_spanningSets ν k) (pos_iff_ne_zero.mpr h0)).not_gt
    (measure_spanningSets_lt_top ν k)

/-- The marked energy of the indicator of `(0, T] × A` is `ν(A) T`. -/
theorem markedEnergy_window {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E] (ν : Measure E) {A : Set E}
    (hA : MeasurableSet A) (T : ℝ) :
    Poisson.Compensated.markedEnergy P ν T
      (fun (_ : Ω) s e => (Set.Ioc (0 : ℝ) T ×ˢ A).indicator (fun _ => (1 : ℝ)) (s, e))
      = ν A * ENNReal.ofReal T := by
  have h : ∀ s e, (‖(Set.Ioc (0 : ℝ) T ×ˢ A).indicator (fun _ => (1 : ℝ)) (s, e)‖₊ : ℝ≥0∞) ^ 2
      = (Set.Ioc (0 : ℝ) T).indicator (fun _ => A.indicator 1 e) s := by
    intro s e
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) T <;> by_cases he : e ∈ A <;>
      simp [Set.indicator, hs, he]
  simp only [Poisson.Compensated.markedEnergy, h]
  have h2 : ∀ s, ∫⁻ e, (Set.Ioc (0 : ℝ) T).indicator (fun _ => A.indicator 1 e) s ∂ν
      = (Set.Ioc (0 : ℝ) T).indicator (fun _ => ν A) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) T
    · simp [hs, lintegral_indicator_one hA]
    · simp [hs]
  simp only [h2]
  rw [lintegral_indicator measurableSet_Ioc, setLIntegral_const, Measure.restrict_apply
    measurableSet_Ioc, Set.inter_eq_left.mpr Set.Ioc_subset_Icc_self, Real.volume_Ioc, sub_zero]
  simp

/-- Example 5.2, `h ≡ 0` is not a reduction. -/
theorem ex_brownian_not_h0 : PaperSpec.A.ex_brownian_not_h0.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ _ ν _ d P _ D h𝒢₀ hind₀ hd hν T hT
  obtain ⟨A, hA, hA0, hAt⟩ := exists_measurableSet_pos_lt_top hν
  set ℱ := enlJoint 𝒢₀ D h𝒢₀ with hℱ
  have hW := isBrownianFiltration_enlJoint D h𝒢₀ hind₀
  have hN := isPoissonFiltration_enlJoint D h𝒢₀ hind₀
  set φ : ℝ × E → ℝ := (Set.Ioc (0 : ℝ) T ×ˢ A).indicator fun _ => 1 with hφ
  have hU : Probability.MarkedPredictable ℱ ν fun (_ : Ω) s e => φ (s, e) :=
    Probability.markedPredictable_of_measurable_window (T := T) hA hAt.ne
      (measurable_const.indicator (measurableSet_Ioc.prod hA))
      fun _ hp => Set.indicator_of_notMem hp _
  have hφv : ∀ (s : ℝ) (e : E), s ∉ Set.Icc (0 : ℝ) T → φ (s, e) = 0 := fun s e hs =>
    Set.indicator_of_notMem (fun h => hs (Set.Ioc_subset_Icc_self h.1)) _
  have hEm : Poisson.Compensated.markedEnergy P ν T (fun (_ : Ω) s e => φ (s, e))
      = ν A * ENNReal.ofReal T := markedEnergy_window P ν hA T
  have hEm' : Poisson.Compensated.markedEnergy P ν T (fun (_ : Ω) s e => φ (s, e)) ≠ ⊤ := by
    rw [hEm]
    exact ENNReal.mul_ne_top hAt.ne ENNReal.ofReal_ne_top
  have hZ : ∀ j : Fin d, Probability.Predictable ℱ fun (ω : Ω) s =>
      (fun (_ : ℝ) (_ : Ω) (_ : Fin d) => (0 : ℝ)) s ω j := fun _ => stronglyMeasurable_const
  have hZv : ∀ (ω : Ω) s, s ∉ Set.Icc (0 : ℝ) T →
      (fun (_ : ℝ) (_ : Ω) (_ : Fin d) => (0 : ℝ)) s ω = 0 := fun _ _ _ => rfl
  have hE0 : Brownian.Ito.energy P T (fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) = 0 := by
    simp [Brownian.Ito.energy]
  let G : ∀ _ : Fin d, Brownian.Ito.HorizonIntegrand P ℱ T := fun j =>
    ⟨fun _ _ => 0, Brownian.Ito.measurable_uncurry_of_predictable (hZ j),
      progressivelyMeasurable_of_predictable_of_vanish hZ hZv j, fun _ _ _ => rfl,
      by rw [hE0]; exact ENNReal.zero_ne_top⟩
  let K : Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T :=
    ⟨fun _ s e => φ (s, e), hU.mono (Probability.markedPredictableSigma_le _ _) le_rfl,
      hU.markedProgressivelyMeasurable, fun _ s e hs => hφv s e hs, hEm'⟩
  set J := LevyStochCalc.Driver.LevyDriver.jointIntegral hW hN G K with hJdef
  have hrc : ℱ.rightCont = ℱ := MeasureTheory.Filtration.IsRightContinuous.eq
  have hproc : ∀ t ≤ T, P[J | ℱ t] =ᵐ[P]
      LevyStochCalc.Driver.LevyDriver.jointIntegralProcess hW hN G K t := by
    intro t ht
    have h := LevyStochCalc.Driver.LevyDriver.condExp_jointIntegral_rightCont hW hN G K ht
    rwa [hrc] at h
  have h00 : LevyStochCalc.Driver.LevyDriver.jointIntegralProcess hW hN G K 0 =ᵐ[P] 0 := by
    have hb : ∀ i, Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hW i) (G i).toFun
        (G i).measurable_uncurry (G i).progressive (G i).sq_int_global 0 =ᵐ[P] 0 := fun i =>
      Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos (D.W.W i) ℱ (hW i)
        (G i).toFun (G i).measurable_uncurry (G i).progressive (G i).sq_int_global le_rfl
    have hp := Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos (φ := K.toFun) D.N hN
      K.measurable_uncurry K.progressive K.sq_int_global le_rfl
    filter_upwards [ae_all_iff.mpr hb, hp] with ω h1 h2
    simp only [LevyStochCalc.Driver.LevyDriver.jointIntegralProcess,
      LevyStochCalc.Driver.horizonProcess, LevyStochCalc.Driver.markedHorizonProcess,
      Pi.zero_apply]
    rw [h2, Pi.zero_apply, add_zero]
    exact Finset.sum_eq_zero fun i _ => h1 i
  have hrep : PaperSpec.A.RepresentsMart D h𝒢₀ hind₀ T (fun t => P[J | ℱ t])
      (fun _ _ _ => 0) (fun s _ e => φ (s, e)) := by
    refine ⟨hZ, hZv, fun _ => by rw [hE0]; exact ENNReal.zero_ne_top, hU,
      fun _ s e hs => hφv s e hs, hEm', fun t ht => ?_⟩
    filter_upwards [hproc t ht.2, hproc 0 hT.le, h00] with ω h1 h2 h3
    rw [h1, h2, h3, Pi.zero_apply, zero_add]
    rfl
  have hM := martingale_condExp J ℱ P
  have hM2 : ∀ t, MemLp (P[J | ℱ t]) 2 P := fun t =>
    (LevyStochCalc.Driver.LevyDriver.memLp_jointIntegral hW hN G K).condExp (by norm_num)
  refine ⟨fun t => P[J | ℱ t], hM, hM2, ?_⟩
  rintro ⟨Z, hZU⟩
  have h := ((sec2_prp 𝒢₀ ν d P D h𝒢₀ hind₀ hd T hT _ hM hM2).2 Z (fun _ _ _ => 0)
    (fun _ _ _ => 0) (fun s _ e => φ (s, e)) hZU hrep).2
  have hne : Poisson.Compensated.markedEnergy P ν T
      (fun (_ : Ω) s e => (0 : ℝ) - φ (s, e)) ≠ 0 := by
    have e : Poisson.Compensated.markedEnergy P ν T (fun (_ : Ω) s e => (0 : ℝ) - φ (s, e))
        = Poisson.Compensated.markedEnergy P ν T (fun (_ : Ω) s e => φ (s, e)) := by
      simp only [Poisson.Compensated.markedEnergy, zero_sub, nnnorm_neg]
    rw [e, hEm]
    exact mul_ne_zero hA0.ne' (ENNReal.ofReal_pos.mpr hT).ne'
  exact hne h

/-- Example 5.2, the branch `m > n`. -/
theorem ex_brownian_rank_gt : PaperSpec.A.ex_brownian_rank_gt.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ _ d P _ D h𝒢₀ _ n m _ hnm _ T _ ξ₀ hξm hξ
  set G := Dissertation.WellPosedness.diagMatrix m n
  set C : Coeffs (0 : Measure E) n m d := Dissertation.WellPosedness.linearGenerator G 0 1
  have hJ : JointBorel T C :=
    jointBorel_iff.mpr ⟨WellPosedness.coeffBorelW2_linearGenerator T,
      ((GX G).continuous.comp continuous_fst).borel_measurable⟩
  have hL : max (0 * ‖GX G‖) (1 * ‖GX G‖) ≤ ‖GX G‖ := by
    rw [one_mul, zero_mul]
    exact max_le (norm_nonneg _) le_rfl
  have h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T ‖GX G‖ C :=
    ⟨norm_nonneg _, lipInterior_iff_diagonalLipschitzH.mpr (Eventually.of_forall fun t =>
      WellPosedness.diagonalLipschitzHAt_linearGenerator le_rfl zero_le_one hL t),
      lipTerminal_iff_terminalLipschitz.mpr (WellPosedness.terminalLipschitz_linearGenerator le_rfl)⟩
  have hconst : WellPosedness.Constants n m 1 0 1 :=
    ⟨zero_le_one, le_rfl, zero_le_one, by norm_num, by norm_num,
      fun h => (lt_asymm hnm h).elim, fun _ => ⟨one_pos, one_pos⟩⟩
  refine ⟨G, C, ‖GX G‖, 1, 0, 1, hJ,
    ⟨hξm, hξ, originValues_iff_coeffOrigin.mpr (WellPosedness.coeffOrigin_linearGenerator T)⟩, h23,
    Dissertation.WellPosedness.rank_diagMatrix m n, Assumption25.of_monotone hJ h23 hconst
      (Eventually.of_forall fun t => WellPosedness.diagonalMonotoneAt_linearGenerator t)
      WellPosedness.terminalMonotone_linearGenerator, one_pos⟩

/-- **The hypotheses of the representation warning of Example 5.2 can be met.** There is a
probability space carrying a Lévy driver with `d = 1` and the nonzero intensity `ν = δ₀` on `ℝ`,
with `𝒢₀ = ⊥` independent of it. -/
theorem ex_brownian_not_h0_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ))),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P ∧ 0 < (1 : ℕ)
      ∧ Measure.dirac (0 : ℝ) ≠ 0 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, one_pos,
    (Measure.dirac.isProbabilityMeasure (x := (0 : ℝ))).ne_zero⟩

/-- **The hypotheses of the branch `m > n` of Example 5.2 can be met.** There is a probability
space carrying a Lévy driver with `d = 1` and `ν = 0` on `ℝ`, with `𝒢₀ = ⊥` independent of it,
`n = 1 < m = 2` and the initial datum `0`. -/
theorem ex_brownian_rank_gt_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (0 : Measure ℝ)),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P
      ∧ StronglyMeasurable[enlJoint ⊥ D bot_le 0] (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1)))
      ∧ MemLp (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1))) 2 P
      ∧ 0 < (1 : ℕ) ∧ (1 : ℕ) < 2 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (0 : Measure ℝ)
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, stronglyMeasurable_const,
    memLp_const _, one_pos, one_lt_two⟩

end Dissertation.Acceptance.A
