/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4BrownianPoisson
import Dissertation.WellPosedness.BrownianPoisson.EnergyAt
import Dissertation.WellPosedness.BrownianPoisson.NoSquareMoment
import Dissertation.Acceptance.A.Sec2Basics
import Dissertation.Acceptance.A.Sec4

/-!
# Steps of the proof of Lemma 4.1: proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The first clause of
the `M²` paragraph, that `δU ∈ H²_N` gives the quadratic integrand `e^s |δU_s(e)|²` no square
moment, is false in a setting with `ν = 0`, where every marked integrand has zero energy; for
`ν ≠ 0` it holds with `δU_s(e) = 1_{(T/2, T]}(s) 1_A(e) c`, `0 < ν(A) < ∞` and
`c = 1_{(0, 1]}(W¹_{T/2}) (W¹_{T/2})^{−1/4}`, for which `𝔼 c² < ∞ = 𝔼 c⁴`.

## Main statements

* `Dissertation.Acceptance.A.lem41_M2_no_square_moment_false` — the first clause read in every
  setting is false.
* `Dissertation.Acceptance.A.lem41_M2_no_square_moment_corr` — the first clause for `ν ≠ 0`.
* `Dissertation.Acceptance.A.lem41_jump_times`, `lem41_M2_zero_mean` — the other two clauses.
* `Dissertation.Acceptance.A.eq_supE` — the bound at every time and (4.6).
* `Dissertation.Acceptance.A.lem41_M2_no_square_moment_corr_hypotheses` — the hypotheses of the
  first clause for `ν ≠ 0` at `ν = δ₀`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Spec LevyStochCalc

universe u v w

/-- The first clause of the `M²` paragraph, read in every setting, is false: with `ν = 0` every
marked integrand has zero energy. -/
theorem lem41_M2_no_square_moment_false :
    ¬ PaperSpec.A.lem41_M2_no_square_moment.{0, 0, w} := by
  intro h
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (0 : Measure ℝ)
  have hind : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨δU, -, -, -, hE⟩ := h ⊥ (0 : Measure ℝ) 1 1 P D bot_le hind one_pos one_pos 1 one_pos
  simp [Poisson.Compensated.markedEnergy] at hE

/-- The first clause of the `M²` paragraph for `ν ≠ 0`. -/
theorem lem41_M2_no_square_moment_corr :
    PaperSpec.A.lem41_M2_no_square_moment_corr.{u, v, w} := by
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

/-- The second clause of the `M²` paragraph: with `ν(E) = ∞` the jump times are all `0`. -/
theorem lem41_jump_times : PaperSpec.A.lem41_jump_times.{u, v, w} := by
  intro Ω _ P _ E _ ν _ d D hν
  filter_upwards [sec2_infinite_activity P ν d D hν] with ω hω k
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_csInf ⟨1, zero_le_one, by rw [hω 0 1 le_rfl one_pos]; exact le_top⟩ fun t ht => ht.1)
  rw [zero_add]
  exact csInf_le ⟨0, fun t ht => ht.1⟩ ⟨hε.le, by rw [hω 0 ε le_rfl hε]; exact le_top⟩

/-- The third clause of the `M²` paragraph: the compensation formula gives
`𝔼[M²_T − M²_t] = 0`. -/
theorem lem41_M2_zero_mean : PaperSpec.A.lem41_M2_zero_mean.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ hind₀ _ _ T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs
    _ _ _ _ _ _ _ _
  refine ⟨lintegral_exp_mul_sum_sq_le (P := P) hU hUv,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.mpr fun k _ => (hUs k).lt_top),
    fun t ht => ?_⟩
  exact quadratic_compensation (N := D.N) (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) ht.1 hU hUv
    hUs

/-- The bound at every time and (4.6), with `C₀ = 2 e^T`. -/
theorem eq_supE : PaperSpec.A.eq_supE.{u, v, w} := by
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

/-- **The hypotheses of the first clause of the `M²` paragraph for `ν ≠ 0` hold.** Over a
probability space carrying a Lévy driver with `d = 1` and `ν = δ₀ ≠ 0` on `ℝ`, `𝒢₀ = ⊥` is
independent of the driver, and `m = 1`, `d = 1` and `T = 1` are positive. -/
theorem lem41_M2_no_square_moment_corr_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ))),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P ∧ Measure.dirac (0 : ℝ) ≠ 0
      ∧ (0 : ℕ) < 1 ∧ (0 : ℕ) < 1 ∧ (0 : ℝ) < 1 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, Measure.dirac_ne_zero, one_pos,
    one_pos, one_pos⟩

end Dissertation.Acceptance.A
