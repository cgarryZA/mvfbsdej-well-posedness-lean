/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec5Dealer
import Dissertation.Acceptance.A.Sec3
import Dissertation.Acceptance.A.Dealer
import Dissertation.WellPosedness.Examples.Dealer.Exposure

/-!
# Example 5.5 of the well-posedness paper: the dealer market, proofs

## Main statements

* `Dissertation.Acceptance.A.ex55Coeffs_eq` — the coefficients of Example 5.5 are
  `dealerExpCoeffs`.
* `Dissertation.Acceptance.A.ex_dealer_coeffs`, `ex_dealer`, `ex_dealer_mono`, `ex_dealer_wp` —
  the coefficients at `ε = 0`, the assumptions, the monotonicity and well-posedness.
* `Dissertation.Acceptance.A.ex_dealer_mean_corr` — the crowding correction is no function of the
  mean when `L²(ν) ≠ 0`.
* `Dissertation.Acceptance.A.ex_dealer_hypotheses` — the hypotheses of `ex_dealer`,
  `ex_dealer_mono` and `ex_dealer_wp` hold on the mark space of the example.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.Law

universe u v w

/-- The coefficients of Example 5.5 are `dealerExpCoeffs`. -/
theorem ex55Coeffs_eq {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (β₁ β₂ : ℝ) (σc : EuclideanSpace ℝ (Fin 1 × Fin 1))
    (hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) (ε : ℝ) :
    PaperSpec.A.ex55Coeffs ν β₁ β₂ σc hc hx ε = dealerExpCoeffs β₁ β₂ σc hc hx ε := by
  simp only [PaperSpec.A.ex55Coeffs, dealerExpCoeffs, dealerCoeffs, Coeffs.perturb, affineCoeffs,
    crowdPert, exposurePert, ex55Crowd_eq, add_zero]
  congr 1
  funext t θ μ
  abel

/-- Example 5.5, the coefficients at `ε = 0` and `h_x = 0`. -/
theorem ex_dealer_coeffs : PaperSpec.A.ex_dealer_coeffs.{v} := by
  intro E _ ν _ _ β₁ β₂ σc hc
  rw [ex55Coeffs_eq, dealerExpCoeffs_zero, dealerCoeffs_zero]

/-- Example 5.5, the assumptions. -/
theorem ex_dealer : PaperSpec.A.ex_dealer.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ _ T _ β₁ β₂ hβ₁ hβ₂ σc hc hx ε hε ξ₀ hξm hξ
  rw [ex55Coeffs_eq]
  obtain ⟨hB, hO, hL, hLT, -, -, -⟩ :=
    dealerExp_assumptions (σc := σc) (hc := hc) (hx := hx) (ℱ := enlJoint 𝒢₀ D h𝒢₀) (P := P) T
      hβ₁ hβ₂ hε
  refine ⟨dealerExpCoeffs_h_origin, jointBorel_iff.mpr ⟨hB, continuous_fst.borel_measurable⟩,
    ⟨hξm, hξ, originValues_iff_coeffOrigin.mpr hO⟩,
    ⟨zero_le_one.trans (le_max_right _ _), lipInterior_iff_diagonalLipschitzH.mpr hL,
      lipTerminal_iff_terminalLipschitz.mpr hLT⟩, rank_one_eq_min, ?_⟩
  rw [Dissertation.WellPosedness.sMin_one]
  norm_num

/-- Example 5.5, monotonicity at every `ε ≥ 0`. -/
theorem ex_dealer_mono : PaperSpec.A.ex_dealer_mono.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc hx ε hε
  obtain ⟨-, hJ, -, h23, -, -⟩ :=
    ex_dealer 𝒢₀ ν P D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc hx ε hε (fun _ => 0)
      stronglyMeasurable_const (memLp_const _)
  rw [ex55Coeffs_eq] at hJ h23 ⊢
  obtain ⟨-, -, -, -, hconst, hM, hMT⟩ :=
    dealerExp_assumptions (σc := σc) (hc := hc) (hx := hx) (ℱ := enlJoint 𝒢₀ D h𝒢₀) (P := P) T
      hβ₁ hβ₂ hε
  refine ⟨fun t p hp p' hp' => ?_, fun δx δu => ?_, fun t p hp p' hp' => ?_,
    Assumption25.of_monotone hJ h23 hconst hM hMT⟩
  · obtain ⟨-, h2, h3⟩ := hp
    obtain ⟨-, h2', h3'⟩ := hp'
    rw [h3, h3']
    exact integral_inner_crowdOp_margU_sub_nonneg h2 h2'
  · rw [real_inner_smul_left]
    ring
  · obtain ⟨-, h2, h3⟩ := hp
    obtain ⟨-, h2', h3'⟩ := hp'
    rw [h3, h3']
    refine le_of_eq_of_le (integral_congr_ae (ae_of_all _ fun ω => ?_))
      (integral_jump_driver_dealerExp_le (β₂ := β₂) (σc := σc) (hc := hc) (hx := hx) hε t h2 h2')
    simp only
    congr 1
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub ((dealerExpCoeffs β₁ β₂ σc hc hx ε).h t (p.1 ω) (lawP2 P p.1))
        ((dealerExpCoeffs β₁ β₂ σc hc hx ε).h t (p'.1 ω) (lawP2 P p'.1)),
      Lp.coeFn_sub (p.1 ω).2.2.2 (p'.1 ω).2.2.2] with e h₁ h₂
    rw [h₁, h₂, Pi.sub_apply, Pi.sub_apply]

/-- Example 5.5, well-posedness at every `ε ≥ 0`. -/
theorem ex_dealer_wp : PaperSpec.A.ex_dealer_wp.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc hx ε hε ξ₀ hξm hξ
  obtain ⟨-, hJ, h22, h23, hG, -⟩ :=
    ex_dealer 𝒢₀ ν P D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc hx ε hε ξ₀ hξm hξ
  obtain ⟨-, -, -, h25⟩ :=
    ex_dealer_mono 𝒢₀ ν P D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc hx ε hε
  exact thm_cwp 𝒢₀ ν 1 1 1 P D h𝒢₀ hind₀ one_pos one_pos one_pos T hT _ 1 β₁ β₂ 1 _ ξ₀ hJ h22
    h23 hG h25

/-- Example 5.5, the crowding correction is no function of the mean when `L²(ν) ≠ 0`. -/
theorem ex_dealer_mean_corr : PaperSpec.A.ex_dealer_mean_corr.{v} := by
  intro E _ ν _ _ hu
  exact (ex_dealer_not_mean_corr ν hu).1

/-- **The hypotheses of Example 5.5 hold on its mark space.** With `c_{±1} = 1/2` and `ϱ = 1`,
the mark measure `ν(dς, dq) = c_ς q^{−2} dq` on `{−1, +1} × (0, 1]` is σ-finite on a countably
generated space and has `ν(E) = ∞`; over a probability space carrying a Lévy driver with `d = 1`
and mark measure `ν`, with `𝒢₀ = ⊥` independent of the driver, the initial datum `0` is strongly
measurable for the time-`0` field of `enlJoint ⊥ D` and square integrable; and
`T = β₁ = β₂ = ε = 1` satisfy `T > 0`, `β₁, β₂ > 0` and `ε ≥ 0`. -/
theorem ex_dealer_hypotheses :
    SigmaFinite (dealerMarks (fun _ => 1 / 2) 1) ∧ MeasurableSpace.CountablyGenerated DealerMark
    ∧ dealerMarks (fun _ => 1 / 2) 1 Set.univ = ⊤
    ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (dealerMarks (fun _ => 1 / 2) 1)),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P
      ∧ StronglyMeasurable[enlJoint ⊥ D bot_le 0] (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1)))
      ∧ MemLp (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1))) 2 P
      ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) ≤ 1 := by
  refine ⟨inferInstance, inferInstance, dealerMarks_univ (fun _ => one_half_pos) zero_le_one, ?_⟩
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 DealerMark (dealerMarks (fun _ => 1 / 2) 1)
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, stronglyMeasurable_const,
    memLp_const _, one_pos, zero_le_one⟩

end Dissertation.Acceptance.A
