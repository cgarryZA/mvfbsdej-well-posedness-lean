/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4LocalMartingales
import Dissertation.WellPosedness.BrownianPoisson.LocalMartingales
import Dissertation.Acceptance.A.Sec4

/-!
# The local martingales `M^W` and `M¹` of the proof of Lemma 4.1: proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The weight
`w_s = e^s δY_{s−} 1_{(0, T]}(s)` is predictable, bounded by `e^T R` before `δY` leaves the ball of
radius `R`, and satisfies `|w_s|² ≤ e^{2T} sup_{t ≤ T} |δY_t|²`; with `𝔼 sup_{t ≤ T} |δY_t|² < ∞`
from Lemma 4.1, `localBrownian_weight` and `localCompensated_weight` give the local integrals,
their bounds with `c₀ = 9`, and the zero means.

## Main statements

* `Dissertation.Acceptance.A.lem41_MW` — `M^W`.
* `Dissertation.Acceptance.A.lem41_M1` — `M¹`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Martingale Dissertation.WellPosedness.Spec
  Dissertation.WellPosedness.BrownianPoisson LevyStochCalc

universe u v w

/-- **`M^W` in the proof of Lemma 4.1**, with `c₀ = 9`. -/
theorem lem41_MW : PaperSpec.A.lem41_MW.{u, v, w} := by
  refine ⟨9, by norm_num, fun c hc => ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ hind₀ hm hd T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs
    hξm hξ hφm hφs hYa hYr hYl heq
  obtain ⟨CBP, hCBP⟩ := lem_bpbsde.{u, v, w}
  have hS := (hCBP 𝒢₀ ν m d P D h𝒢₀ hind₀ hm hd T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs hξm
    hξ hφm hφs hYa hYr hYl heq).1
  obtain ⟨hwm, hwp, hwb, hwsq⟩ := expLeftLimWeight_props (ℱ := enlJoint 𝒢₀ D h𝒢₀) hT.le
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) hYa hYl
  have key := localBrownian_weight D.W (enlJoint 𝒢₀ D h𝒢₀)
    (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) hT hYa
    (fun i ω t ht => hYr i ω t ht) hS hwm hwp hwb (Real.exp_pos T).le hwsq
    (Z := δZ) (fun k j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
    (fun k j => progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k) j)
    (fun k j => BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k) j) hZv
  rw [expLeftLim_integrand_eq hZv] at key
  have hfin : ENNReal.ofReal (c * Real.exp T)
      * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, esq (fun k => δY k t ω) ∂P) ^ (1 / 2 : ℝ)
      * (∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => δZ k s ω j)) ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hS.ne))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ENNReal.sum_lt_top.2 fun k _ => ENNReal.sum_lt_top.2 fun j _ => (hZs k j).lt_top).ne)
  refine ⟨key.1, fun MW hMW => ⟨?_, hfin, (key.2 MW hMW).2⟩⟩
  have hc9 : 9 * ENNReal.ofReal (Real.exp T) ≤ ENNReal.ofReal (c * Real.exp T) := by
    rw [show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc (Real.exp_pos T).le)
  calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖MW t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 9 * ENNReal.ofReal (Real.exp T)
          * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖δY i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)
          * (∑ k, ∑ j, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖δZ k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            ^ (1 / 2 : ℝ) := (key.2 MW hMW).1
    _ ≤ _ := mul_le_mul' (mul_le_mul' hc9 le_rfl) le_rfl

/-- **`M¹` in the proof of Lemma 4.1**, with `c₀ = 9`. -/
theorem lem41_M1 : PaperSpec.A.lem41_M1.{u, v, w} := by
  refine ⟨9, by norm_num, fun c hc => ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ hind₀ hm hd T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs
    hξm hξ hφm hφs hYa hYr hYl heq
  obtain ⟨CBP, hCBP⟩ := lem_bpbsde.{u, v, w}
  have hS := (hCBP 𝒢₀ ν m d P D h𝒢₀ hind₀ hm hd T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs hξm
    hξ hφm hφs hYa hYr hYl heq).1
  obtain ⟨hwm, hwp, hwb, hwsq⟩ := expLeftLimWeight_props (ℱ := enlJoint 𝒢₀ D h𝒢₀) hT.le
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) hYa hYl
  have key := localCompensated_weight D.N (enlJoint 𝒢₀ D h𝒢₀)
    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) hT hYa
    (fun i ω t ht => hYr i ω t ht) hS hwm hwp hwb (Real.exp_pos T).le hwsq
    (U := δU) (fun k => (hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
    (fun k => (hU k).markedProgressivelyMeasurable)
    (fun k => BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) hUv
  rw [expLeftLim_markedIntegrand_eq hUv] at key
  have hfin : ENNReal.ofReal (c * Real.exp T)
      * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, esq (fun k => δY k t ω) ∂P) ^ (1 / 2 : ℝ)
      * (∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e))
        ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hS.ne))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ENNReal.sum_lt_top.2 fun k _ => (hUs k).lt_top).ne)
  refine ⟨key.1, fun M1 hM1 => ⟨?_, hfin, (key.2 M1 hM1).2⟩⟩
  have hc9 : 9 * ENNReal.ofReal (Real.exp T) ≤ ENNReal.ofReal (c * Real.exp T) := by
    rw [show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc (Real.exp_pos T).le)
  calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M1 t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 9 * ENNReal.ofReal (Real.exp T)
          * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖δY i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)
          * (∑ k, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖δU k s ω e‖₊ : ℝ≥0∞) ^ 2
              ∂ν ∂volume ∂P) ^ (1 / 2 : ℝ) := (key.2 M1 hM1).1
    _ ≤ _ := mul_le_mul' (mul_le_mul' hc9 le_rfl) le_rfl

end Dissertation.Acceptance.A
