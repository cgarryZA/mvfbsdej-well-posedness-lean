/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Martingale.LocalWeight
import Dissertation.WellPosedness.System.LawFlow
import Dissertation.WellPosedness.BrownianPoisson.Compensation
import LevyStochCalc.Probability.MarkedPredictableComp

/-!
# The weight `e^s δY_{s−}` of the local martingales of Lemma 4.1

The integrands `e^s ⟨δY_{s−}, δZ_s ·⟩` and `e^s ⟨δY_{s−}, δU_s(e)⟩` of the local martingales
`M^W` and `M¹` are weighted sums `∑_k w_k δZ_k`, `∑_k w_k δU_k` with the weight
`w_k(s) = e^s δY^k_{s−} 1_{(0, T]}(s)`. The weight is jointly and progressively measurable, at most
`e^T R` at a time before which `|δY| ≤ R`, and `|w_s|² ≤ e^{2T} sup_{t ≤ T} |δY_t|²`, as
`Martingale.localBrownian_weight` and `Martingale.localCompensated_weight` ask.

## Main definitions

* `Dissertation.WellPosedness.BrownianPoisson.expLeftLimWeight` — the weight.

## Main statements

* `Dissertation.WellPosedness.BrownianPoisson.expLeftLimWeight_props` — its properties.
* `Dissertation.WellPosedness.BrownianPoisson.expLeftLim_integrand_eq`,
  `Dissertation.WellPosedness.BrownianPoisson.expLeftLim_markedIntegrand_eq` — the integrands as
  weighted sums.
* `Dissertation.WellPosedness.BrownianPoisson.poisson_sq_chain` — the Cauchy–Schwarz and
  compensation links for the quadratic variation of `M¹`.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Dissertation.WellPosedness.BrownianPoisson

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Martingale LevyStochCalc

section Weight

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ} {m : ℕ}

/-- The weight `e^s δY_{s−}` of `M^W` and `M¹`, cut to `(0, T]`. -/
noncomputable def expLeftLimWeight (Y : Fin m → ℝ → Ω → ℝ) (T : ℝ) (k : Fin m) (s : ℝ)
    (ω : Ω) : ℝ :=
  Real.exp s * (if s ∈ Ioc (0 : ℝ) T then leftLimProc Y k s ω else 0)

/-- The properties of the weight `e^s δY_{s−}` that `localBrownian_weight` asks for. -/
theorem expLeftLimWeight_props (hT : 0 ≤ T) (hℱneg : ∀ r : ℝ, r ≤ 0 → ℱ 0 ≤ ℱ r)
    {Y : Fin m → ℝ → Ω → ℝ} (hYad : ∀ k, ∀ t ∈ Icc (0 : ℝ) T, Measurable[ℱ t] (Y k t))
    (hYl : ∀ k ω, ∀ t ∈ Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l)) :
    (∀ k, Measurable (Function.uncurry fun ω s => expLeftLimWeight Y T k s ω))
    ∧ (∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => expLeftLimWeight Y T k s ω)
    ∧ (∀ (R : ℝ), 0 ≤ R → ∀ k ω s, 0 ≤ s → s ≤ T →
        (∀ u, 0 ≤ u → u < s → ∀ i, |Y i u ω| ≤ R) →
          |expLeftLimWeight Y T k s ω| ≤ Real.exp T * R)
    ∧ ∀ ω, ∀ s ∈ Icc (0 : ℝ) T, ENNReal.ofReal (∑ k, expLeftLimWeight Y T k s ω ^ 2)
        ≤ ENNReal.ofReal (Real.exp T ^ 2)
          * ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2 := by
  have hL := fun k => progressive_leftLim_Ioc (T := T) hℱneg (hYad k) (hYl k)
  have hexpm : Measurable (Function.uncurry fun (_ : Ω) (s : ℝ) => Real.exp s) :=
    Real.measurable_exp.comp measurable_snd
  have hexpp : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (s : ℝ) => Real.exp s :=
    Probability.progressivelyMeasurable_of_rightContinuous (X := fun s (_ : Ω) => Real.exp s)
      (fun _ => measurable_const)
      (fun _ t => Real.continuous_exp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  refine ⟨fun k => hexpm.mul (hL k).1, fun k => hexpp.mul (hL k).2, ?_, ?_⟩
  · intro R hR k ω s hs0 hsT hb
    simp only [expLeftLimWeight]
    split_ifs with hs
    · rw [abs_mul, abs_of_pos (Real.exp_pos s)]
      obtain ⟨l, hl⟩ := hYl k ω s hs
      exact mul_le_mul (Real.exp_le_exp.mpr hsT)
        (abs_leftLim_le hs.1 hl fun u hu hus => hb u hu hus k) (abs_nonneg _)
        (Real.exp_pos T).le
    · simp only [mul_zero, abs_zero]
      positivity
  · intro ω s hs
    by_cases hs' : s ∈ Ioc (0 : ℝ) T
    · simp only [expLeftLimWeight, if_pos hs', mul_pow]
      rw [← Finset.mul_sum, ENNReal.ofReal_mul (by positivity)]
      gcongr
      · exact hs'.2
      · exact ofReal_sum_leftLim_sq_le hs' fun k => hYl k ω s hs'
    · simp only [expLeftLimWeight, if_neg hs', mul_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, Finset.sum_const_zero, ENNReal.ofReal_zero]
      exact bot_le

end Weight

/-- The integrand `e^s ⟨δY_{s−}, δZ_s ·⟩` as the weighted sum `∑_k w_k δZ_k`. -/
theorem expLeftLim_integrand_eq {Ω : Type*} {m d : ℕ} {T : ℝ} {Y : Fin m → ℝ → Ω → ℝ}
    {Z : Fin m → ℝ → Ω → Fin d → ℝ} (hZv : ∀ k ω s, s ∉ Icc (0 : ℝ) T → Z k s ω = 0) :
    (fun s ω j => ∑ k, expLeftLimWeight Y T k s ω * Z k s ω j)
      = fun s ω j => Real.exp s * ∑ k, (if 0 < s then leftLimProc Y k s ω else 0) * Z k s ω j := by
  funext s ω j
  by_cases hs : s ∈ Ioc (0 : ℝ) T
  · simp only [expLeftLimWeight, if_pos hs, if_pos hs.1, Finset.mul_sum, mul_assoc]
  · rcases le_or_gt s 0 with hs0 | hs0
    · simp [expLeftLimWeight, if_neg hs, not_lt.mpr hs0]
    · have hsT : s ∉ Icc (0 : ℝ) T := fun h => hs ⟨hs0, h.2⟩
      simp [expLeftLimWeight, hZv _ ω s hsT]

/-- The marked integrand `e^s ⟨δY_{s−}, δU_s(e)⟩` as the weighted sum `∑_k w_k δU_k`. -/
theorem expLeftLim_markedIntegrand_eq {Ω E : Type*} {m : ℕ} {T : ℝ} {Y : Fin m → ℝ → Ω → ℝ}
    {U : Fin m → ℝ → Ω → E → ℝ} (hUv : ∀ k ω s e, s ∉ Icc (0 : ℝ) T → U k s ω e = 0) :
    (fun ω s e => ∑ k, expLeftLimWeight Y T k s ω * U k s ω e)
      = fun ω s e => Real.exp s * ∑ k, (if 0 < s then leftLimProc Y k s ω else 0) * U k s ω e := by
  funext ω s e
  by_cases hs : s ∈ Ioc (0 : ℝ) T
  · simp only [expLeftLimWeight, if_pos hs, if_pos hs.1, Finset.mul_sum, mul_assoc]
  · rcases le_or_gt s 0 with hs0 | hs0
    · simp [expLeftLimWeight, if_neg hs, not_lt.mpr hs0]
    · have hsT : s ∉ Icc (0 : ℝ) T := fun h => hs ⟨hs0, h.2⟩
      simp [expLeftLimWeight, hUv _ ω s e hsT]

end Dissertation.WellPosedness.BrownianPoisson
