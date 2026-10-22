/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec4BrownianPoisson
import MVFBSDEJ.WellPosedness.BrownianPoisson.EnergyAt
import MVFBSDEJ.WellPosedness.BrownianPoisson.NoSquareMoment
import MVFBSDEJ.Acceptance.Sec2Basics
import MVFBSDEJ.Acceptance.Sec4
import MVFBSDEJ.WellPosedness.BrownianPoisson.PathwiseMartingale

/-!
# Steps of the proof of Lemma 4.1: proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The first clause of
the `M²` paragraph, that for `ν ≠ 0` membership `δU ∈ H²_N` gives the quadratic integrand
`e^s |δU_s(e)|²` no square moment, holds with `δU_s(e) = 1_{(T/2, T]}(s) 1_A(e) c`,
`0 < ν(A) < ∞` and `c = 1_{(0, 1]}(W¹_{T/2}) (W¹_{T/2})^{−1/4}`, for which `𝔼 c² < ∞ = 𝔼 c⁴`.

## Main statements

* `MVFBSDEJ.Acceptance.lem41_M2_no_square_moment` — the first clause.
* `MVFBSDEJ.Acceptance.lem41_jump_times`, `lem41_M2_integrand`, `lem41_M2_zero_mean` — the
  other clauses.
* `MVFBSDEJ.Acceptance.lem41_M2_martingale` — `M²`, read pathwise, is a martingale: the
  integral against the random measure is measurable at time `t` off a null set (truncated
  kernels), and the compensation formula (2.2) for `1_A 1_{(s, t]} e^s |δU|²`, `A ∈ ℱ_s`, gives the
  martingale property (`MVFBSDEJ.WellPosedness.BrownianPoisson.condExp_pathwiseCompensated`).
* `MVFBSDEJ.Acceptance.eq_supE` — the bound at every time and (4.6).
* `MVFBSDEJ.Acceptance.lem41_M2_no_square_moment_hypotheses` — the hypotheses of the first
  clause at `ν = δ₀`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Spec LevyStochCalc

universe u v w

/-- The first clause of the `M²` paragraph: for `ν ≠ 0`, some `δU ∈ H²_N` has a quadratic
integrand without square moment. -/
theorem lem41_M2_no_square_moment : PaperSpec.lem41_M2_no_square_moment.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ _ hν hm hd T hT
  obtain ⟨A, hA, hA0, hAt⟩ : ∃ A : Set E, MeasurableSet A ∧ ν A ≠ 0 ∧ ν A ≠ ⊤ := by
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    apply hν
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets ν]
    refine measure_iUnion_null fun n => ?_
    by_contra hn
    exact hcon _ (measurableSet_spanningSets ν n) hn (measure_spanningSets_lt_top ν n).ne
  have hW : Measurable[enlJoint 𝒢₀ D h𝒢₀ (T / 2)] ((D.W.W ⟨0, hd⟩).W (T / 2)) := by
    have h1 := (Filtration.stronglyAdapted_natural (fun t =>
      ((D.W.W ⟨0, hd⟩).measurable_eval t).stronglyMeasurable) (T / 2)).measurable
    exact h1.mono ((Brownian.Multidim.MultidimBrownianMotion.naturalFiltration_coord_le D.W
      ⟨0, hd⟩ (T / 2)).trans ((D.naturalFiltration_brownian_le (T / 2)).trans
        (filtration_le_enlJoint D h𝒢₀ (T / 2)))) le_rfl
  exact exists_markedPredictable_sq_markedEnergy_eq_top (D.W.W ⟨0, hd⟩) (half_pos hT)
    (half_lt_self hT) hW hA hA0 hAt hm

/-- The second clause of the `M²` paragraph: with `ν(E) = ∞` every `(0, t]` carries infinitely
many jumps, so the jump times are all `0` and do not exhaust `[0, T]`. -/
theorem lem41_jump_times : PaperSpec.lem41_jump_times.{u, v, w} := by
  intro Ω _ P _ E _ ν _ d D hν
  filter_upwards [sec2_infinite_activity P ν d D hν] with ω hω
  have hinf : ∀ t : ℝ, 0 < t → D.N.N ω (Set.Ioc 0 t ×ˢ Set.univ) = ⊤ :=
    fun t ht => hω 0 t le_rfl ht
  have hτ : ∀ k : ℕ,
      (⨅ (t : ℝ) (_ : 0 ≤ t ∧ (k : ℝ≥0∞) ≤ D.N.N ω (Set.Ioc 0 t ×ˢ Set.univ)),
        ENNReal.ofReal t) = 0 := by
    intro k
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) zero_le
    have hε' : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
    rw [zero_add, ← ENNReal.ofReal_coe_nnreal]
    exact iInf₂_le (ε : ℝ) ⟨hε'.le, by rw [hinf ε hε']; exact le_top⟩
  refine ⟨hinf, hτ, fun T hT => ?_⟩
  simp only [hτ, iSup_const]
  exact ENNReal.ofReal_pos.mpr hT

/-- The integrand of the third clause of the `M²` paragraph: `e^s |δU_s(e)|²` is marked
predictable and nonnegative. -/
theorem lem41_M2_integrand : PaperSpec.lem41_M2_integrand.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ hind₀ _ _ T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs
    _ _ _ _ _ _ _ _
  exact ⟨markedPredictable_exp_mul_sum_sq hU hUv, fun ω s e =>
    mul_nonneg (Real.exp_pos s).le (Finset.sum_nonneg fun k _ => sq_nonneg _)⟩

/-- The third clause of the `M²` paragraph: the compensation formula gives
`𝔼[M²_T − M²_t] = 0`. -/
theorem lem41_M2_zero_mean : PaperSpec.lem41_M2_zero_mean.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ hind₀ _ _ T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs
    _ _ _ _ _ _ _ _
  refine ⟨lintegral_exp_mul_sum_sq_le (P := P) hU hUv,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.mpr fun k _ => (hUs k).lt_top),
    fun t ht => ?_⟩
  exact quadratic_compensation (N := D.N) (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) ht.1 hU hUv
    hUs

/-- `M²` of the proof of Lemma 4.1, read pathwise, is a martingale on `[0, T]`. -/
theorem lem41_M2_martingale : PaperSpec.lem41_M2_martingale.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ hind₀ _ _ T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs
    _ _ _ _ _ _ _ _
  have hℱN := isPoissonFiltration_enlJoint D h𝒢₀ hind₀
  set ψ : Ω × ℝ × E → ℝ := fun p => Real.exp p.2.1 * ∑ k, δU k p.2.1 p.1 p.2.2 ^ 2 with hψdef
  have hψ : Measurable[Probability.markedPredictableSigma (enlJoint 𝒢₀ D h𝒢₀) ν] ψ :=
    markedPredictable_exp_mul_sum_sq hU hUv
  have hψ0 : ∀ p, 0 ≤ ψ p := fun p =>
    mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hfin : ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (ψ (ω, s, e)) ∂ν ∂volume ∂P
      < ⊤ := by
    refine lt_of_le_of_lt ((lintegral_mono fun ω => lintegral_mono_set
      Set.Ioc_subset_Icc_self).trans (lintegral_exp_mul_sum_sq_le (P := P) hU hUv)) ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.mpr fun k _ =>
      (hUs k).lt_top)
  refine ⟨fun t ht => ⟨?_, integrable_pathwiseCompensated (N := D.N) hℱN hψ hψ0 hfin ht.2,
    aestronglyMeasurable_pathwiseCompensated (N := D.N) (P := P) hℱN hψ hψ0 t⟩,
    fun s t hs hst htT => condExp_pathwiseCompensated (N := D.N) hℱN hψ hψ0 hfin hs hst htT⟩
  rw [lintegral_N_eq_compensator (N := D.N) hℱN hψ t]
  exact (lintegral_compensator_mono (P := P) (ν := ν) (ψ := ψ) ht.2).trans_lt hfin

/-- The bound at every time and (4.6), with `C₀ = 2 e^T`. -/
theorem eq_supE : PaperSpec.eq_supE.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ hind₀ _ _ T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs
    _ hξ hφm hφs hYa hYr _ heq
  have hξk : ∀ k, MemLp (fun ω => δξ ω k) 2 P := memLp_iff_forall_coord.mp hξ
  refine ⟨fun t ht => brownianPoisson_energy_at_vec_of_measurable (crossWitnessEnl D h𝒢₀ hind₀)
    (hF0_enlJoint D h𝒢₀) (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT
    (ξ := fun k ω => δξ ω k)
    (fun k j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
    (fun k => progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k)) hZv hZs
    (fun k => (hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
    (fun k => (hU k).markedProgressivelyMeasurable) hUv hUs hφm hφs hξk hYa hYr heq ht, ?_⟩
  exact brownianPoisson_supE_vec_of_measurable (crossWitnessEnl D h𝒢₀ hind₀)
    (hF0_enlJoint D h𝒢₀) (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT
    (ξ := fun k ω => δξ ω k)
    (fun k j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
    (fun k => progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k)) hZv hZs
    (fun k => (hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
    (fun k => (hU k).markedProgressivelyMeasurable) hUv hUs hφm hφs hξk hYa hYr heq

/-- **The hypotheses of the first clause of the `M²` paragraph hold.** Over a probability space
carrying a Lévy driver with `d = 1` and `ν = δ₀ ≠ 0` on `ℝ`, `𝒢₀ = ⊥` is independent of the
driver, and `m = 1`, `d = 1` and `T = 1` are positive. -/
theorem lem41_M2_no_square_moment_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ))),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P ∧ Measure.dirac (0 : ℝ) ≠ 0
      ∧ (0 : ℕ) < 1 ∧ (0 : ℕ) < 1 ∧ (0 : ℝ) < 1 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, Measure.dirac_ne_zero, one_pos,
    one_pos, one_pos⟩

end MVFBSDEJ.Acceptance
