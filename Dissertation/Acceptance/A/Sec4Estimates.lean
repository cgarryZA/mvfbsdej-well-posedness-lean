/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4Estimates
import Dissertation.WellPosedness.System.WeakPairDiff
import Dissertation.WellPosedness.Stability.DiffSupEstimates
import Dissertation.WellPosedness.Stability.WeightedWindow

/-!
# Steps 3 and 4 of the proof of Lemma 4.3: proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`. Extended off
`[0, T]`, two solutions of (4.1) in `ℍ_weak` have as difference the difference system of the
implementation (`PaperWeakSolutionForcedInt.exists_pairDiff`, with Lipschitz constants
`K = 10 (2L)²` and `K_T = 4 (2L)²`). Its supremum bounds give (4.23) and (4.27)
(`PairDiff.lintegral_biSup_fwd_le_energy`, `PairDiff.lintegral_biSup_bwd_add_le`), and (4.26)
follows from (4.27) since `sup_t 𝔼|δY_t|² ≤ 𝔼 sup_t |δY_t|²`. The weighted second-moment identity
of the backward coordinates on `Ω × [t, T]` (`LinearBSDEJ.exp_mul_window_eq`), summed over the
coordinates, is (4.24) with equality. The hypotheses are those of Lemma 4.3, an instance of which
is `Dissertation.Acceptance.A.lem_pert_two_data_hypotheses`.

## Main statements

* `Dissertation.Acceptance.A.eq_fwd` — (4.23).
* `Dissertation.Acceptance.A.eq_bwdito` — (4.24).
* `Dissertation.Acceptance.A.eq_wgt` — (4.26).
* `Dissertation.Acceptance.A.eq_bwd` — (4.27).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.WellPosedness.BrownianPoisson
  Dissertation.PaperSpec.A LevyStochCalc

universe u v w

/-- (4.23), with `C = c_X(T, 10 (2L)²)`. -/
theorem eq_fwd : PaperSpec.A.eq_fwd.{u, v, w} := by
  refine ⟨fun T L _ _ _ _ _ => fwdSupConst T (10 * (2 * L) ^ 2), ?_⟩
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ _
  obtain ⟨X₁', X₂', Y₁', Y₂', hXe, hYe, hD⟩ := h₁.exists_pairDiff h₂ hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone
  have hP := (h₁.forcing.sub h₂.forcing).dataSize_ne_top_of_memLp fun i => (hD.fwd i).ξ₀_sq
  have key := hD.lintegral_biSup_fwd_le_energy (crossWitnessEnl D h𝒢₀ hind₀)
    (hF0_enlJoint D h𝒢₀) (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT
    (hlow.le.trans hlam) hlam1 (by positivity) hP
  have hsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁ i t ω - X₂ i t ω)) ∂P
      = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁' i t ω - X₂' i t ω)) ∂P := by
    refine lintegral_congr fun ω => iSup_congr fun t => iSup_congr fun ht => ?_
    simp only [congrFun (hXe _ t ht).1 ω, congrFun (hXe _ t ht).2 ω]
  have heY : ∀ k, Brownian.Ito.energy P T (fun ω s => Y₁' k s ω - Y₂' k s ω)
      = Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω) := fun k =>
    energy_eq_of_eqOn fun t ht => funext fun ω => by
      simp only [congrFun (hYe k t ht).1 ω, congrFun (hYe k t ht).2 ω]
  rw [hsup]
  simpa only [heY] using key

/-- (4.27), with `C = c_Y(T, 10 (2L)², 4 (2L)²)`. -/
theorem eq_bwd : PaperSpec.A.eq_bwd.{u, v, w} := by
  refine ⟨fun T L _ _ _ _ _ => bwdSupConst T (10 * (2 * L) ^ 2) (4 * (2 * L) ^ 2), ?_⟩
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ _
  obtain ⟨X₁', X₂', Y₁', Y₂', hXe, hYe, hD⟩ := h₁.exists_pairDiff h₂ hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone
  have hP := (h₁.forcing.sub h₂.forcing).dataSize_ne_top_of_memLp fun i => (hD.fwd i).ξ₀_sq
  have key := hD.lintegral_biSup_bwd_add_le (crossWitnessEnl D h𝒢₀ hind₀)
    (hF0_enlJoint D h𝒢₀) (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT
    (hlow.le.trans hlam) hlam1 (by positivity) (by positivity) hP
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω)) ∂P
      = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁' k t ω - Y₂' k t ω)) ∂P := by
    refine lintegral_congr fun ω => iSup_congr fun t => iSup_congr fun ht => ?_
    simp only [congrFun (hYe _ t ht).1 ω, congrFun (hYe _ t ht).2 ω]
  have heX : ∀ i, Brownian.Ito.energy P T (fun ω s => X₁' i s ω - X₂' i s ω)
      = Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω) := fun i =>
    energy_eq_of_eqOn fun t ht => funext fun ω => by
      simp only [congrFun (hXe i t ht).1 ω, congrFun (hXe i t ht).2 ω]
  have hXT : ∀ i, X₁' i T = X₁ i T ∧ X₂' i T = X₂ i T := fun i => hXe i T hTm
  rw [hsup]
  simpa only [heX, (hXT _).1, (hXT _).2] using key

/-- (4.26), with the constant of (4.27). -/
theorem eq_wgt : PaperSpec.A.eq_wgt.{u, v, w} := by
  obtain ⟨K, hK⟩ := eq_bwd.{u, v, w}
  refine ⟨K, ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ hq₁ hq₂
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ h₁ h₂ hS
  refine le_trans (add_le_add ?_ le_rfl) (hK 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C
    hJ h23 hG h25 lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂
    qg₁ qg₂ hq₁ hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ h₁ h₂ hS)
  exact iSup₂_le fun t ht => lintegral_mono fun ω =>
    le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => esq (fun k => Y₁ k t ω - Y₂ k t ω)) t ht

/-- (4.24), which holds with equality. -/
theorem eq_bwdito : PaperSpec.A.eq_bwdito.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ _ κ _ t ht
  obtain ⟨X₁', X₂', Y₁', Y₂', -, hYe, hD⟩ := h₁.exists_pairDiff h₂ hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone
  have 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  set μ := P.prod (volume.restrict (Set.Icc t T)) with hμ
  have hsub : Set.Icc t T ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc ht.1 le_rfl
  have hae : ∀ᵐ q ∂μ, q.2 ∈ Set.Icc (0 : ℝ) T :=
    (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)).mono
      fun q hq => hsub hq
  have eY : ∀ k, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω, Y₁' k s ω - Y₂' k s ω = Y₁ k s ω - Y₂ k s ω :=
    fun k s hs ω => by rw [congrFun (hYe k s hs).1 ω, congrFun (hYe k s hs).2 ω]
  have key := fun k => (hD.bwd k).exp_mul_window_eq 𝒲 hT κ ht
  -- the integrability at `t` and at `T`
  have hYt : ∀ k, MemLp (fun ω => Y₁' k t ω - Y₂' k t ω) 2 P := fun k =>
    ((hD.bwd k).linearFSDEJ (ξ₀ := fun ω => Y₁' k 0 ω - Y₂' k 0 ω) EventuallyEq.rfl
      hT.le).memLp_apply ht
  have hξ : ∀ k, MemLp (fun ω => lam * (terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
      + (qg₁ k ω - qg₂ k ω)) 2 P := fun k => (hD.bwd k).ξ_sq
  -- the integrands on `Ω × [t, T]`
  have hG : ∀ k, Integrable (fun q : Ω × ℝ => Real.exp (κ * q.2)
      * (κ * (Y₁' k q.2 q.1 - Y₂' k q.2 q.1) ^ 2 + ∑ j, (Z₁ k q.2 q.1 j - Z₂ k q.2 q.1 j) ^ 2
        + ∫ e, (U₁ k q.2 q.1 e - U₂ k q.2 q.1 e) ^ 2 ∂ν)) μ := fun k => (key k).1
  have hH : ∀ k, Integrable (fun q : Ω × ℝ => Real.exp (κ * q.2)
      * ((Y₁' k q.2 q.1 - Y₂' k q.2 q.1) * (lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k q.1 q.2
        - driverProc P T C X₂ Y₂ Z₂ U₂ k q.1 q.2) + (qf₁ k q.1 q.2 - qf₂ k q.1 q.2)))) μ :=
    fun k => (key k).2.1
  have eG : (fun q : Ω × ℝ => ∑ k, Real.exp (κ * q.2)
      * (κ * (Y₁' k q.2 q.1 - Y₂' k q.2 q.1) ^ 2 + ∑ j, (Z₁ k q.2 q.1 j - Z₂ k q.2 q.1 j) ^ 2
        + ∫ e, (U₁ k q.2 q.1 e - U₂ k q.2 q.1 e) ^ 2 ∂ν))
      =ᵐ[μ] fun p : Ω × ℝ => Real.exp (κ * p.2)
        * (κ * ∑ k, (Y₁ k p.2 p.1 - Y₂ k p.2 p.1) ^ 2
          + ∑ k, ∑ j, (Z₁ k p.2 p.1 j - Z₂ k p.2 p.1 j) ^ 2
          + ∑ k, ∫ e, (U₁ k p.2 p.1 e - U₂ k p.2 p.1 e) ^ 2 ∂ν) := by
    filter_upwards [hae] with q hq
    simp only [eY _ q.2 hq q.1, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  have eH : (fun q : Ω × ℝ => ∑ k, Real.exp (κ * q.2)
      * ((Y₁' k q.2 q.1 - Y₂' k q.2 q.1) * (lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k q.1 q.2
        - driverProc P T C X₂ Y₂ Z₂ U₂ k q.1 q.2) + (qf₁ k q.1 q.2 - qf₂ k q.1 q.2))))
      =ᵐ[μ] fun p : Ω × ℝ => Real.exp (κ * p.2)
        * ∑ k, (Y₁ k p.2 p.1 - Y₂ k p.2 p.1)
          * (lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k p.1 p.2
            - driverProc P T C X₂ Y₂ Z₂ U₂ k p.1 p.2) + (qf₁ k p.1 p.2 - qf₂ k p.1 p.2)) := by
    filter_upwards [hae] with q hq
    simp only [eY _ q.2 hq q.1, Finset.mul_sum]
  have hGs := (integrable_finsetSum _ fun k _ => hG k).congr eG
  have hHs := (integrable_finsetSum _ fun k _ => hH k).congr eH
  refine ⟨integrable_finsetSum _ fun k _ => ((hYt k).ae_eq
      (Eventually.of_forall fun ω => eY k t ht ω)).integrable_sq,
    integrable_finsetSum _ fun k _ => (hξ k).integrable_sq, hGs, hHs, le_of_eq ?_⟩
  -- the identity, summed over the coordinates
  have P1 : ∫ ω, ∑ k, (Y₁ k t ω - Y₂ k t ω) ^ 2 ∂P
      = ∑ k, ∫ ω, (Y₁' k t ω - Y₂' k t ω) ^ 2 ∂P := by
    rw [← integral_finsetSum _ fun k _ => (hYt k).integrable_sq]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [eY _ t ht ω]
  have P2 : ∫ ω, ∫ s in Set.Icc t T, Real.exp (κ * s)
        * (κ * ∑ k, (Y₁ k s ω - Y₂ k s ω) ^ 2 + ∑ k, ∑ j, (Z₁ k s ω j - Z₂ k s ω j) ^ 2
          + ∑ k, ∫ e, (U₁ k s ω e - U₂ k s ω e) ^ 2 ∂ν) ∂volume ∂P
      = ∑ k, ∫ q, Real.exp (κ * q.2)
        * (κ * (Y₁' k q.2 q.1 - Y₂' k q.2 q.1) ^ 2 + ∑ j, (Z₁ k q.2 q.1 j - Z₂ k q.2 q.1 j) ^ 2
          + ∫ e, (U₁ k q.2 q.1 e - U₂ k q.2 q.1 e) ^ 2 ∂ν) ∂μ := by
    rw [← integral_finsetSum _ fun k _ => hG k, integral_congr_ae eG]
    exact (integral_prod _ hGs).symm
  have P3 : ∫ ω, ∑ k, (lam * (terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
        + (qg₁ k ω - qg₂ k ω)) ^ 2 ∂P
      = ∑ k, ∫ ω, (lam * (terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
        + (qg₁ k ω - qg₂ k ω)) ^ 2 ∂P :=
    integral_finsetSum _ fun k _ => (hξ k).integrable_sq
  have P4 : ∫ ω, ∫ s in Set.Icc t T, Real.exp (κ * s) * ∑ k, (Y₁ k s ω - Y₂ k s ω)
        * (lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
          + (qf₁ k ω s - qf₂ k ω s)) ∂volume ∂P
      = ∑ k, ∫ q, Real.exp (κ * q.2)
        * ((Y₁' k q.2 q.1 - Y₂' k q.2 q.1) * (lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k q.1 q.2
          - driverProc P T C X₂ Y₂ Z₂ U₂ k q.1 q.2) + (qf₁ k q.1 q.2 - qf₂ k q.1 q.2))) ∂μ := by
    rw [← integral_finsetSum _ fun k _ => hH k, integral_congr_ae eH]
    exact (integral_prod _ hHs).symm
  rw [P1, P2, P3, P4, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => (key k).2.2

end Dissertation.Acceptance.A
