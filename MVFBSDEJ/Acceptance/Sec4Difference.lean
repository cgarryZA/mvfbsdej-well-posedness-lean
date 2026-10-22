/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec4Difference
import MVFBSDEJ.WellPosedness.System.WeakPairDiff
import MVFBSDEJ.Acceptance.Sec4

/-!
# Steps 1 and 2 of the proof of Lemma 4.3: proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`. Extended off
`[0, T]`, two solutions of (4.1) in `ℍ²` have as difference the difference system of the
implementation (`PaperWeakSolutionForcedInt.exists_pairDiff`), whose equations, `G`-energy
identity, monotonicity and coercivity give (4.15)–(4.22); the jump coefficient at the predictable
tuples agrees with the solutions' representatives almost everywhere
(`PaperWeakSolutionForcedInt.ae_forcedJump_sub_leftLim_eq`). The hypotheses are those of
Lemma 4.3, an instance of which is `MVFBSDEJ.Acceptance.lem_pert_data_forcing_hypotheses`.

## Main statements

* `MVFBSDEJ.Acceptance.eq_dX` — (4.15).
* `MVFBSDEJ.Acceptance.eq_dY` — (4.16).
* `MVFBSDEJ.Acceptance.eq_Gid` — (4.19).
* `MVFBSDEJ.Acceptance.eq_intmono` — (4.20).
* `MVFBSDEJ.Acceptance.eq_termmono` — (4.21).
* `MVFBSDEJ.Acceptance.eq_coerc_insert` — (4.20) and (4.21) inserted into (4.19).
* `MVFBSDEJ.Acceptance.eq_coerc` — (4.22).
* `MVFBSDEJ.Acceptance.eq_coerc_blocks` — each coercive block of (4.22) is at most `𝒦`.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped ENNReal

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.PaperSpec MVFBSDEJ.Law LevyStochCalc
  LevyStochCalc.BSDEJ.Solves

universe u v w

/-- (4.15). -/
theorem eq_dX : PaperSpec.eq_dX.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, hXl₁, hYl₁⟩ ⟨⟨γ₂, h₂⟩, hXl₂, hYl₂⟩ _ i
  obtain ⟨X₁', X₂', Y₁', Y₂', hXe, -, hD⟩ := h₁.exists_pairDiff h₂ hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone
  have hj := h₁.ae_forcedJump_sub_leftLim_eq h₂ hT.le (jointBorel_iff.mp hJ).1.toCoeffBorel
    hXl₁ hYl₁ hXl₂ hYl₂
  have hF := hD.fwd i
  have hq₀ := marked_sq_int_global_of_vanishing hF.γ_vanish hF.γ_sq
  refine ⟨?_, hF.σ_meas, hF.σ_prog, sq_int_global_of_vanishing hF.σ_vanish hF.σ_sq,
    ⟨_, hF.γ_meas, hF.γ_prog, hq₀, ?_⟩, fun H hHm hHp hHq hH t ht => ?_⟩
  · filter_upwards [h₁.b_int i, h₂.b_int i] with ω e₁ e₂
    exact (e₁.sub e₂).congr_fun (fun s _ => by simp only [Pi.sub_apply]; ring) measurableSet_Icc
  · filter_upwards [hj] with q hq
    exact (hq i).symm
  · have hE := markedEnergy_sub_eq_zero_of_ae_eq (φ₂ := fun ω s e =>
      lam * (jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e) + (qh₁ i s ω e - qh₂ i s ω e))
      hHm hF.γ_meas (by
        filter_upwards [hH, hj] with q e₁ e₂
        rw [e₁, e₂ i])
    filter_upwards [hF.eqn t ht, compensatedIntegral_congr_of_markedEnergy (φ₂ := fun ω s e =>
      lam * (jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e) + (qh₁ i s ω e - qh₂ i s ω e)) D.N
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) hHm hHp hHq hF.γ_meas hF.γ_prog hq₀ hE ht.2]
      with ω e₁ e₂
    rw [← congrFun (hXe i t ht).1 ω, ← congrFun (hXe i t ht).2 ω, e₁, e₂]

/-- (4.16). -/
theorem eq_dY : PaperSpec.eq_dY.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ _ k
  obtain ⟨X₁', X₂', Y₁', Y₂', -, hYe, hD⟩ := h₁.exists_pairDiff h₂ hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone
  have hB := hD.bwd k
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  refine ⟨?_, ?_, hB.Z_meas, hB.Z_prog, sq_int_global_of_vanishing hB.Z_vanish hB.Z_sq,
    hB.U_meas, hB.U_prog, marked_sq_int_global_of_vanishing hB.U_vanish hB.U_sq,
    fun t ht => ?_⟩
  · filter_upwards [h₁.f_int k, h₂.f_int k] with ω e₁ e₂
    exact (e₁.sub e₂).congr_fun (fun s _ => by simp only [Pi.sub_apply]; ring) measurableSet_Icc
  · filter_upwards [hB.ae_eq_terminal hT.le] with ω e
    rw [← congrFun (hYe k T hTm).1 ω, ← congrFun (hYe k T hTm).2 ω]
    exact e
  · filter_upwards [hB.eqn t ht] with ω e
    rw [← congrFun (hYe k t ht).1 ω, ← congrFun (hYe k t ht).2 ω]
    exact e

/-- (4.19). -/
theorem eq_Gid : PaperSpec.eq_Gid.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, hXl₁, hYl₁⟩ ⟨⟨γ₂, h₂⟩, hXl₂, hYl₂⟩ _
  obtain ⟨X₁', X₂', Y₁', Y₂', hXe, hYe, hD⟩ := h₁.exists_pairDiff h₂ hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone
  have hj := h₁.ae_forcedJump_sub_leftLim_eq h₂ hT.le (jointBorel_iff.mp hJ).1.toCoeffBorel
    hXl₁ hYl₁ hXl₂ hYl₂
  have 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have h0m : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  set μ₂ := P.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμ₂
  set S : Ω × ℝ → ℝ := fun p =>
    (fun i => lam * (driftProc P T C X₁ Y₁ Z₁ U₁ i p.1 p.2
        - driftProc P T C X₂ Y₂ Z₂ U₂ i p.1 p.2) + (qb₁ i p.1 p.2 - qb₂ i p.1 p.2))
      ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k p.2 p.1 - Y₂ k p.2 p.1)
    + ∑ j, (fun i => lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i p.2 p.1 j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i p.2 p.1 j) + (qσ₁ i p.2 p.1 j - qσ₂ i p.2 p.1 j))
      ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k p.2 p.1 j - Z₂ k p.2 p.1 j)
    + ∫ e, (fun i =>
        lam * (jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
            p.2 p.1 e
          - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
            p.2 p.1 e) + (qh₁ i p.2 p.1 e - qh₂ i p.2 p.1 e))
      ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k p.2 p.1 e - U₂ k p.2 p.1 e) ∂ν
    + (fun k => -(lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k p.1 p.2
        - driverProc P T C X₂ Y₂ Z₂ U₂ k p.1 p.2)) - (qf₁ k p.1 p.2 - qf₂ k p.1 p.2))
      ⬝ᵥ (G *ᵥ fun i => X₁ i p.2 p.1 - X₂ i p.2 p.1) with hS
  have hHi := integrable_gPairing (ν := ν) G hD.memLp_window_drift hD.memLp_window_diffusion
    hD.memLp_window_driver hD.memLp_markedWindow_jump (hD.memLp_window_X 𝒲 hT)
    (hD.memLp_window_Y 𝒲 hT) (hD.memLp_window_Z (T := T)) (hD.memLp_markedWindow_U (T := T))
  have hSR : ∀ᵐ p ∂μ₂, S p = (fun i => lam * (driftProc P T C X₁ Y₁ Z₁ U₁ i p.1 p.2
        - driftProc P T C X₂ Y₂ Z₂ U₂ i p.1 p.2) + (qb₁ i p.1 p.2 - qb₂ i p.1 p.2))
      ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁' k p.2 p.1 - Y₂' k p.2 p.1)
    + ∑ j, (fun i => lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i p.2 p.1 j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i p.2 p.1 j) + (qσ₁ i p.2 p.1 j - qσ₂ i p.2 p.1 j))
      ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k p.2 p.1 j - Z₂ k p.2 p.1 j)
    - (fun k => lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k p.1 p.2
        - driverProc P T C X₂ Y₂ Z₂ U₂ k p.1 p.2) + (qf₁ k p.1 p.2 - qf₂ k p.1 p.2))
      ⬝ᵥ (G *ᵥ fun i => X₁' i p.2 p.1 - X₂' i p.2 p.1)
    + ∫ e, (fun i => lam * (jumpProc T γ₁ i p.2 p.1 e - jumpProc T γ₂ i p.2 p.1 e)
        + (qh₁ i p.2 p.1 e - qh₂ i p.2 p.1 e))
      ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k p.2 p.1 e - U₂ k p.2 p.1 e) ∂ν := by
    filter_upwards [ae_window_mem, ae_ae_of_ae_markedEnergyMeasure hj] with p hp hpj
    have eX : ∀ i, X₁' i p.2 p.1 = X₁ i p.2 p.1 ∧ X₂' i p.2 p.1 = X₂ i p.2 p.1 := fun i =>
      ⟨congrFun (hXe i p.2 hp).1 p.1, congrFun (hXe i p.2 hp).2 p.1⟩
    have eY : ∀ k, Y₁' k p.2 p.1 = Y₁ k p.2 p.1 ∧ Y₂' k p.2 p.1 = Y₂ k p.2 p.1 := fun k =>
      ⟨congrFun (hYe k p.2 hp).1 p.1, congrFun (hYe k p.2 hp).2 p.1⟩
    simp only [hS, (eX _).1, (eX _).2, (eY _).1, (eY _).2]
    rw [integral_dotProduct_congr_ae hpj, neg_sub_dotProduct]
    ring
  have hSi : Integrable S μ₂ := hHi.congr (hSR.mono fun p hp => hp.symm)
  have key := hD.integral_mulVec_dotProduct_eq 𝒲 hT
  have eT : ∀ i, X₁' i T = X₁ i T ∧ X₂' i T = X₂ i T := fun i => hXe i T hTm
  have eYT : ∀ k, Y₁' k T = Y₁ k T ∧ Y₂' k T = Y₂ k T := fun k => hYe k T hTm
  have eY0 : ∀ k, Y₁' k 0 = Y₁ k 0 ∧ Y₂' k 0 = Y₂ k 0 := fun k => hYe k 0 h0m
  simp only [(eT _).1, (eT _).2, (eYT _).1, (eYT _).2, (eY0 _).1, (eY0 _).2] at key
  have mXT : ∀ i, MemLp (fun ω => X₁ i T ω - X₂ i T ω) 2 P := fun i => by
    have h := (hD.fwd i).memLp_terminal hT.le
    simp only [(eT i).1, (eT i).2] at h
    exact h
  have mYT : ∀ k, MemLp (fun ω => Y₁ k T ω - Y₂ k T ω) 2 P := fun k => by
    have h := (hD.bwd k).ξ_sq.ae_eq ((hD.bwd k).ae_eq_terminal hT.le).symm
    simp only [(eYT k).1, (eYT k).2] at h
    exact h
  have mY0 : ∀ k, MemLp (fun ω => Y₁ k 0 ω - Y₂ k 0 ω) 2 P := fun k => by
    have h := (hD.bwd k).memLp_initial hT.le
    simp only [(eY0 k).1, (eY0 k).2] at h
    exact h
  refine ⟨integrable_dotProduct_of_memLp (memLp_mulVec G mXT) mYT,
    integrable_dotProduct_of_memLp (memLp_mulVec G fun i => (hD.fwd i).ξ₀_sq) mY0, hSi, ?_⟩
  calc _ = _ := sub_eq_of_eq_add' key
    _ = ∫ p, S p ∂μ₂ := by
        rw [← integral_prod_symm _ hHi]
        exact integral_congr_ae (hSR.mono fun p hp => hp.symm)
    _ = _ := integral_prod S hSi

/-- (4.20). -/
theorem eq_intmono : PaperSpec.eq_intmono.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ _
  obtain ⟨X₁', Y₁', hX₁, hY₁, hs₁⟩ := h₁.exists_solvesForcedInt hT.le
  obtain ⟨X₂', Y₂', hX₂, hY₂, hs₂⟩ := h₂.exists_solvesForcedInt hT.le
  have hlam0 : 0 ≤ lam := hlow.le.trans hlam
  filter_upwards [h25.interior, hs₁.ae_memLp_tupleAt, hs₂.ae_memLp_tupleAt,
    ae_restrict_mem measurableSet_Icc, h₁.toPaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq hT.le,
    h₂.toPaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq hT.le]
    with t hmono hm₁ hm₂ ht hl₁ hl₂
  have e₁ : tupleAt ν X₁' Y₁' Z₁ U₁ t = tupleAt ν X₁ Y₁ Z₁ U₁ t := tupleAt_eq_of_eqOn hX₁ hY₁ ht
  have e₂ : tupleAt ν X₂' Y₂' Z₂ U₂ t = tupleAt ν X₂ Y₂ Z₂ U₂ t := tupleAt_eq_of_eqOn hX₂ hY₂ ht
  have hs₁' := hs₁.stronglyMeasurable_tupleAt t
  have hs₂' := hs₂.stronglyMeasurable_tupleAt t
  rw [e₁] at hm₁ hs₁'
  rw [e₂] at hm₂ hs₂'
  obtain ⟨hint, hle⟩ := hmono _ (mk_mem_diagonalInputs hs₁' hm₁) _ (mk_mem_diagonalInputs hs₂' hm₂)
  rw [lawP2_congr hl₁, lawP2_congr hl₂]
  have hpair : ∀ᵐ ω ∂P, tupleAt ν (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁ t ω
      = tupleAt ν X₁ Y₁ Z₁ U₁ t ω ∧ tupleAt ν (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂ t ω
      = tupleAt ν X₂ Y₂ Z₂ U₂ t ω := hl₁.and hl₂
  refine ⟨hint.congr ?_, ?_⟩
  · filter_upwards [hpair] with ω hω
    simp only [pairing27, hω.1, hω.2]
    ring
  · calc _ = lam * ∫ ω, pairing27 G C t (tupleAt ν X₁ Y₁ Z₁ U₁ t ω) (tupleAt ν X₂ Y₂ Z₂ U₂ t ω)
            (lawP2 P (tupleAt ν X₁ Y₁ Z₁ U₁ t)) (lawP2 P (tupleAt ν X₂ Y₂ Z₂ U₂ t)) ∂P := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [hpair] with ω hω
          simp only [pairing27, hω.1, hω.2]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hle hlam0
      _ = _ := by ring

/-- (4.21). -/
theorem eq_termmono : PaperSpec.eq_termmono.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ _
  obtain ⟨X₁', X₂', Y₁', Y₂', hXe, hYe, hD⟩ := h₁.exists_pairDiff h₂ hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone
  have hlpos : 0 < lam := hlow.trans_le hlam
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have eX : ∀ i, X₁' i T = X₁ i T ∧ X₂' i T = X₂ i T := fun i => hXe i T hTm
  have eY : ∀ k, Y₁' k T = Y₁ k T ∧ Y₂' k T = Y₂ k T := fun k => hYe k T hTm
  have mXT : ∀ i, MemLp (fun ω => X₁ i T ω - X₂ i T ω) 2 P := fun i => by
    have h := (hD.fwd i).memLp_terminal hT.le
    simp only [(eX i).1, (eX i).2] at h
    exact h
  have mqg : ∀ k, MemLp (fun ω => qg₁ k ω - qg₂ k ω) 2 P := fun k =>
    (h₁.forcing.qg_sq k).sub (h₂.forcing.qg_sq k)
  have mg : ∀ k, MemLp (fun ω => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) 2 P :=
    fun k => (((hD.bwd k).ξ_sq.sub (mqg k)).const_mul lam⁻¹).ae_eq
      (ae_of_all _ fun _ => (eq_inv_mul_add_sub hlpos.ne' _ _).symm)
  have hYT : ∀ᵐ ω ∂P, (fun k => Y₁ k T ω - Y₂ k T ω) = fun k =>
      lam * (terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) + (qg₁ k ω - qg₂ k ω) := by
    filter_upwards [ae_all_iff.mpr fun k => (hD.bwd k).ae_eq_terminal hT.le] with ω hω
    funext k
    rw [← congrFun (eY k).1 ω, ← congrFun (eY k).2 ω]
    exact hω k
  have hgX := integrable_dotProduct_of_memLp (memLp_mulVec G mXT) mg
  have hqgX := integrable_dotProduct_of_memLp (memLp_mulVec G mXT) mqg
  have hTer : ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (fun k => Y₁ k T ω - Y₂ k T ω) ∂P
      = lam * ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω)
          ⬝ᵥ (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) ∂P
        + ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (fun k => qg₁ k ω - qg₂ k ω) ∂P := by
    rw [← integral_const_mul, ← integral_add (hgX.const_mul lam) hqgX]
    refine integral_congr_ae ?_
    filter_upwards [hYT] with ω hω
    rw [hω, dotProduct_comm, dotProduct_mul_add, dotProduct_comm, dotProduct_comm _ (G *ᵥ _)]
  have hmonoT := hD.monoT
  simp only [(eX _).1, (eX _).2] at hmonoT
  have hcomm : ∫ ω, (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
        ⬝ᵥ (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ∂P
      = ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω)
        ⬝ᵥ (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) ∂P :=
    integral_congr_ae (ae_of_all _ fun ω => dotProduct_comm _ _)
  rw [hcomm] at hmonoT
  refine ⟨?_, hgX, hqgX, hTer, ?_⟩
  · refine ((hgX.const_mul lam).add hqgX).congr ?_
    filter_upwards [hYT] with ω hω
    simp only [Pi.add_apply]
    rw [hω]
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  · have h1 := mul_le_mul_of_nonneg_left hmonoT hlpos.le
    have h2 := neg_abs_le (∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω)
      ⬝ᵥ (fun k => qg₁ k ω - qg₂ k ω) ∂P)
    rw [← mul_assoc] at h1
    linarith

/-- (4.20) and (4.21) inserted into (4.19). -/
theorem eq_coerc_insert : PaperSpec.eq_coerc_insert.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ _
  obtain ⟨X₁', X₂', Y₁', Y₂', hXe, hYe, hD⟩ := h₁.exists_pairDiff h₂ hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone
  have 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  have hlpos : 0 < lam := hlow.trans_le hlam
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have h0m : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  set μ₂ := P.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμ₂
  have hP := (h₁.forcing.sub h₂.forcing).dataSize_ne_top_of_memLp fun i => (hD.fwd i).ξ₀_sq
  have eXs : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω i, X₁' i s ω = X₁ i s ω ∧ X₂' i s ω = X₂ i s ω :=
    fun s hs ω i => ⟨congrFun (hXe i s hs).1 ω, congrFun (hXe i s hs).2 ω⟩
  have eYs : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω k, Y₁' k s ω = Y₁ k s ω ∧ Y₂' k s ω = Y₂ k s ω :=
    fun s hs ω k => ⟨congrFun (hYe k s hs).1 ω, congrFun (hYe k s hs).2 ω⟩
  have hset : ∀ F F' : Ω → ℝ → ℝ, (∀ ω, ∀ s ∈ Set.Icc (0 : ℝ) T, F' ω s = F ω s) →
      ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, F' ω s ∂volume ∂P
        = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P := fun F F' h =>
    integral_congr_ae (ae_of_all _ fun ω => setIntegral_congr_fun measurableSet_Icc
      fun s hs => h ω s hs)
  have mXT : ∀ i, MemLp (fun ω => X₁ i T ω - X₂ i T ω) 2 P := fun i => by
    have h := (hD.fwd i).memLp_terminal hT.le
    simp only [(eXs T hTm _ i).1, (eXs T hTm _ i).2] at h
    exact h
  have mY0 : ∀ k, MemLp (fun ω => Y₁ k 0 ω - Y₂ k 0 ω) 2 P := fun k => by
    have h := (hD.bwd k).memLp_initial hT.le
    simp only [(eYs 0 h0m _ k).1, (eYs 0 h0m _ k).2] at h
    exact h
  have mqg : ∀ k, MemLp (fun ω => qg₁ k ω - qg₂ k ω) 2 P := fun k =>
    (h₁.forcing.qg_sq k).sub (h₂.forcing.qg_sq k)
  have mU := hD.memLp_markedWindow_U (T := T)
  -- the blocks
  have eBXT : blockXT P G (fun i t ω => X₁' i t ω - X₂' i t ω) T
      = ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ∂P := by
    simp only [blockXT, (eXs T hTm _ _).1, (eXs T hTm _ _).2]
  have eBX : blockX P G (fun i t ω => X₁' i t ω - X₂' i t ω) T
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)
          ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω) ∂volume ∂P := by
    have hi := hD.integrable_blockX_window 𝒲 hT
    unfold blockX
    rw [← integral_prod_symm _ hi, integral_prod _ hi]
    exact hset _ _ fun ω s hs => by simp only [(eXs s hs ω _).1, (eXs s hs ω _).2]
  have eBY : blockY P ν G (fun k t ω => Y₁' k t ω - Y₂' k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) T
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ((Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
          + ∑ j, (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
          + ∫ e, (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e)
            ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν) ∂volume ∂P := by
    have hi := hD.integrable_blockY_window 𝒲 hT
    unfold blockY
    rw [← integral_prod_symm _ hi, integral_prod _ hi]
    exact hset _ _ fun ω s hs => by simp only [(eYs s hs ω _).1, (eYs s hs ω _).2]
  -- the initial and the terminal pairings
  have eA : ∫ ω, (G *ᵥ fun i => ξ₁ ω i - ξ₂ ω i) ⬝ᵥ (fun k => Y₁' k 0 ω - Y₂' k 0 ω) ∂P
      = ∫ ω, (G *ᵥ fun i => ξ₁ ω i - ξ₂ ω i) ⬝ᵥ (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P := by
    simp only [(eYs 0 h0m _ _).1, (eYs 0 h0m _ _).2]
  have eB : ∫ ω, (fun k => qg₁ k ω - qg₂ k ω) ⬝ᵥ (G *ᵥ fun i => X₁' i T ω - X₂' i T ω) ∂P
      = ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (fun k => qg₁ k ω - qg₂ k ω) ∂P := by
    simp only [(eXs T hTm _ _).1, (eXs T hTm _ _).2]
    exact integral_congr_ae (ae_of_all _ fun ω => dotProduct_comm _ _)
  -- the forcing pairing on the window
  have hpt : ∀ ω, ∀ s ∈ Set.Icc (0 : ℝ) T,
      (fun i => qb₁ i ω s - qb₂ i ω s) ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁' k s ω - Y₂' k s ω)
        + ∑ j, (fun i => qσ₁ i s ω j - qσ₂ i s ω j)
          ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
        - (fun k => qf₁ k ω s - qf₂ k ω s) ⬝ᵥ (G *ᵥ fun i => X₁' i s ω - X₂' i s ω)
        + ∫ e, (fun i => qh₁ i s ω e - qh₂ i s ω e)
          ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν
      = (fun i => qb₁ i ω s - qb₂ i ω s) ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
        + ∑ j, (fun i => qσ₁ i s ω j - qσ₂ i s ω j)
          ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
        + (fun k => -(qf₁ k ω s - qf₂ k ω s)) ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)
        + ∫ e, (fun i => qh₁ i s ω e - qh₂ i s ω e)
          ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν := by
    intro ω s hs
    simp only [(eXs s hs ω _).1, (eXs s hs ω _).2, (eYs s hs ω _).1, (eYs s hs ω _).2]
    rw [show (fun k => -(qf₁ k ω s - qf₂ k ω s)) = -(fun k => qf₁ k ω s - qf₂ k ω s) from rfl,
      neg_dotProduct]
    ring
  have hFi : Integrable (fun p : Ω × ℝ => (fun i => qb₁ i p.1 p.2 - qb₂ i p.1 p.2)
        ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁' k p.2 p.1 - Y₂' k p.2 p.1)
      + ∑ j, (fun i => qσ₁ i p.2 p.1 j - qσ₂ i p.2 p.1 j)
        ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k p.2 p.1 j - Z₂ k p.2 p.1 j)
      - (fun k => qf₁ k p.1 p.2 - qf₂ k p.1 p.2) ⬝ᵥ (G *ᵥ fun i => X₁' i p.2 p.1 - X₂' i p.2 p.1)
      + ∫ e, (fun i => qh₁ i p.2 p.1 e - qh₂ i p.2 p.1 e)
        ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k p.2 p.1 e - U₂ k p.2 p.1 e) ∂ν) μ₂ := by
    have hi := integrable_gPairing (ν := ν) G (hD.memLp_window_qb hP) (hD.memLp_window_qσ hP)
      (hD.memLp_window_qf hP) (hD.memLp_markedWindow_qh hP) (hD.memLp_window_X 𝒲 hT)
      (hD.memLp_window_Y 𝒲 hT) (hD.memLp_window_Z (T := T)) mU
    exact hi
  have eF : ∫ p, ((fun i => qb₁ i p.1 p.2 - qb₂ i p.1 p.2)
        ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁' k p.2 p.1 - Y₂' k p.2 p.1)
      + ∑ j, (fun i => qσ₁ i p.2 p.1 j - qσ₂ i p.2 p.1 j)
        ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k p.2 p.1 j - Z₂ k p.2 p.1 j)
      - (fun k => qf₁ k p.1 p.2 - qf₂ k p.1 p.2) ⬝ᵥ (G *ᵥ fun i => X₁' i p.2 p.1 - X₂' i p.2 p.1)
      + ∫ e, (fun i => qh₁ i p.2 p.1 e - qh₂ i p.2 p.1 e)
        ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k p.2 p.1 e - U₂ k p.2 p.1 e) ∂ν) ∂μ₂
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ((fun i => qb₁ i ω s - qb₂ i ω s)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
          + ∑ j, (fun i => qσ₁ i s ω j - qσ₂ i s ω j)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
          + (fun k => -(qf₁ k ω s - qf₂ k ω s)) ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)
          + ∫ e, (fun i => qh₁ i s ω e - qh₂ i s ω e)
            ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν) ∂volume ∂P := by
    rw [integral_prod _ hFi]
    exact hset _ _ fun ω s hs => hpt ω s hs
  have hins := hD.blocks_le_pairings 𝒲 hT hlpos hP
  rw [eBXT, eBX, eBY, eA, eB, eF] at hins
  refine ⟨integrable_dotProduct_of_memLp (memLp_mulVec G mXT) (memLp_mulVec G mXT),
    integrable_dotProduct_of_memLp (memLp_mulVec G mXT) mqg,
    integrable_dotProduct_of_memLp (memLp_mulVec G fun i => (hD.fwd i).ξ₀_sq) mY0,
    (hD.integrable_blockX_window 𝒲 hT).congr (ae_window_mem.mono fun p hp => by
      simp only [(eXs p.2 hp p.1 _).1, (eXs p.2 hp p.1 _).2]),
    (hD.integrable_blockY_window 𝒲 hT).congr (ae_window_mem.mono fun p hp => by
      simp only [(eYs p.2 hp p.1 _).1, (eYs p.2 hp p.1 _).2]),
    hFi.congr (ae_window_mem.mono fun p hp => hpt p.1 p.2 hp),
    integrable_dotProduct_of_memLp (memLp_mulVec Gᵀ mU) (memLp_mulVec Gᵀ mU),
    integrable_dotProduct_of_memLp (hD.memLp_markedWindow_qh hP) (memLp_mulVec Gᵀ mU), ?_⟩
  linarith

/-- (4.22), with `‖G‖` the operator norm of `GX G`. -/
theorem eq_coerc : PaperSpec.eq_coerc.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ _
  obtain ⟨X₁', X₂', Y₁', Y₂', hXe, hYe, hD⟩ := h₁.exists_pairDiff h₂ hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone
  have 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  have hlpos : 0 < lam := hlow.trans_le hlam
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have h0m : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  set μ₂ := P.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμ₂
  have hP := (h₁.forcing.sub h₂.forcing).dataSize_ne_top_of_memLp fun i => (hD.fwd i).ξ₀_sq
  have eXs : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω i, X₁' i s ω = X₁ i s ω ∧ X₂' i s ω = X₂ i s ω :=
    fun s hs ω i => ⟨congrFun (hXe i s hs).1 ω, congrFun (hXe i s hs).2 ω⟩
  have eYs : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω k, Y₁' k s ω = Y₁ k s ω ∧ Y₂' k s ω = Y₂ k s ω :=
    fun s hs ω k => ⟨congrFun (hYe k s hs).1 ω, congrFun (hYe k s hs).2 ω⟩
  have hset : ∀ F F' : Ω → ℝ → ℝ, (∀ ω, ∀ s ∈ Set.Icc (0 : ℝ) T, F' ω s = F ω s) →
      ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, F' ω s ∂volume ∂P
        = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P := fun F F' h =>
    integral_congr_ae (ae_of_all _ fun ω => setIntegral_congr_fun measurableSet_Icc
      fun s hs => h ω s hs)
  -- the pieces of `N'`
  have mXT : ∀ i, MemLp (fun ω => X₁ i T ω - X₂ i T ω) 2 P := fun i => by
    have h := (hD.fwd i).memLp_terminal hT.le
    simp only [(eXs T hTm _ i).1, (eXs T hTm _ i).2] at h
    exact h
  have mY0 : ∀ k, MemLp (fun ω => Y₁ k 0 ω - Y₂ k 0 ω) 2 P := fun k => by
    have h := (hD.bwd k).memLp_initial hT.le
    simp only [(eYs 0 h0m _ k).1, (eYs 0 h0m _ k).2] at h
    exact h
  have heX : ∀ i, Brownian.Ito.energy P T (fun ω s => X₁' i s ω - X₂' i s ω)
      = Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω) := fun i =>
    energy_eq_of_eqOn fun t ht => funext fun ω => by
      simp only [(eXs t ht ω i).1, (eXs t ht ω i).2]
  have heY : ∀ k, Brownian.Ito.energy P T (fun ω s => Y₁' k s ω - Y₂' k s ω)
      = Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω) := fun k =>
    energy_eq_of_eqOn fun t ht => funext fun ω => by
      simp only [(eYs t ht ω k).1, (eYs t ht ω k).2]
  have n1 := (lintegral_esq_lt_top mXT).ne
  have n2 := (lintegral_esq_lt_top mY0).ne
  have n3 : ∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => by rw [← heX i]; exact ((hD.fwd i).energy_lt_top 𝒲 hT).ne
  have n4 : ∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun k _ => by rw [← heY k]; exact ((hD.bwd k).energy_lt_top 𝒲 hT).ne
  have n5 : ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun k _ => ENNReal.sum_ne_top.mpr fun j _ => (hD.bwd k).Z_sq j
  have n6 : ∑ k, Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => U₁ k s ω e - U₂ k s ω e) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun k _ => (hD.bwd k).U_sq
  -- the blocks
  have eBXT : blockXT P G (fun i t ω => X₁' i t ω - X₂' i t ω) T
      = ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ∂P := by
    simp only [blockXT, (eXs T hTm _ _).1, (eXs T hTm _ _).2]
  have eBX : blockX P G (fun i t ω => X₁' i t ω - X₂' i t ω) T
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)
          ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω) ∂volume ∂P := by
    have hi := hD.integrable_blockX_window 𝒲 hT
    unfold blockX
    rw [← integral_prod_symm _ hi, integral_prod _ hi]
    exact hset _ _ fun ω s hs => by simp only [(eXs s hs ω _).1, (eXs s hs ω _).2]
  have eBY : blockY P ν G (fun k t ω => Y₁' k t ω - Y₂' k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) T
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ((Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
          + ∑ j, (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
          + ∫ e, (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e)
            ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν) ∂volume ∂P := by
    have hi := hD.integrable_blockY_window 𝒲 hT
    unfold blockY
    rw [← integral_prod_symm _ hi, integral_prod _ hi]
    exact hset _ _ fun ω s hs => by simp only [(eYs s hs ω _).1, (eYs s hs ω _).2]
  -- the six pairings
  have eA : ∫ ω, (G *ᵥ fun i => ξ₁ ω i - ξ₂ ω i) ⬝ᵥ (fun k => Y₁' k 0 ω - Y₂' k 0 ω) ∂P
      = ∫ ω, (G *ᵥ fun i => ξ₁ ω i - ξ₂ ω i) ⬝ᵥ (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P := by
    simp only [(eYs 0 h0m _ _).1, (eYs 0 h0m _ _).2]
  have eB : ∫ ω, (fun k => qg₁ k ω - qg₂ k ω) ⬝ᵥ (G *ᵥ fun i => X₁' i T ω - X₂' i T ω) ∂P
      = ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (fun k => qg₁ k ω - qg₂ k ω) ∂P := by
    simp only [(eXs T hTm _ _).1, (eXs T hTm _ _).2]
    exact integral_congr_ae (ae_of_all _ fun ω => dotProduct_comm _ _)
  obtain ⟨hFa, hFb⟩ := hD.integrable_abs_forcing 𝒲 hT hP
  have eF : ∫ p, ((|(fun i => qb₁ i p.1 p.2 - qb₂ i p.1 p.2)
          ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁' k p.2 p.1 - Y₂' k p.2 p.1)|
        + |∑ j, (fun i => qσ₁ i p.2 p.1 j - qσ₂ i p.2 p.1 j)
          ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k p.2 p.1 j - Z₂ k p.2 p.1 j)|)
      + (|∫ e, (fun i => qh₁ i p.2 p.1 e - qh₂ i p.2 p.1 e)
          ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k p.2 p.1 e - U₂ k p.2 p.1 e) ∂ν|
        + |(fun k => qf₁ k p.1 p.2 - qf₂ k p.1 p.2)
          ⬝ᵥ (G *ᵥ fun i => X₁' i p.2 p.1 - X₂' i p.2 p.1)|)) ∂μ₂
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (|(fun i => qb₁ i ω s - qb₂ i ω s)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)|
          + |∑ j, (fun i => qσ₁ i s ω j - qσ₂ i s ω j)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)|) ∂volume ∂P
        + ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (|∫ e, (fun i => qh₁ i s ω e - qh₂ i s ω e)
            ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν|
          + |(fun k => qf₁ k ω s - qf₂ k ω s) ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)|)
            ∂volume ∂P := by
    rw [integral_add hFa hFb, integral_prod _ hFa, integral_prod _ hFb]
    congr 1
    · exact hset _ _ fun ω s hs => by simp only [(eYs s hs ω _).1, (eYs s hs ω _).2]
    · exact hset _ _ fun ω s hs => by simp only [(eXs s hs ω _).1, (eXs s hs ω _).2]
  have hB := hD.blocks_le_abs_pairings 𝒲 hT hlpos hP
  rw [eBXT, eBX, eBY, eA, eB, eF] at hB
  refine ⟨by finiteness, hP, by linarith, fun η hη => ?_⟩
  have hGn := MVFBSDEJ.WellPosedness.System.mulVec_dotProduct_le G
  have hFle := hD.integral_abs_forcing_le 𝒲 hT hP hGn hη
  have hTq := hD.abs_terminal_forcing_le hT hP hGn hη
  have hIni := hD.abs_initial_pairing_le hT hGn hη
  rw [eF] at hFle
  rw [eB] at hTq
  rw [eA] at hIni
  simp only [heX, heY, (eXs T hTm _ _).1, (eXs T hTm _ _).2] at hFle hTq
  simp only [(eYs 0 h0m _ _).1, (eYs 0 h0m _ _).2] at hIni
  rw [toReal_dataSize hP]
  have hN : (∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P
        + ∫⁻ ω, esq (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P
        + (∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)
          + ∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω)
          + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e))).toReal
      = (∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P).toReal
        + (∫⁻ ω, esq (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P).toReal
        + (∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)).toReal
        + (∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω)
          + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e)).toReal := by
    rw [add_assoc (∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)),
      add_assoc (∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness), ← add_assoc]
  rw [hN]
  linarith


/-- **The sentence after (4.22)**: each coercive block, being nonnegative, is at most the sum of
the blocks, hence at most `𝒦`. -/
theorem eq_coerc_blocks : PaperSpec.eq_coerc_blocks.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ hq₁ hq₂
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hS₁ hS₂ hsup η hη
  obtain ⟨-, -, hM, hK⟩ := MVFBSDEJ.Acceptance.eq_coerc 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd
    T hT L α β₁ β₂ G C hJ h23 hG h25 lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁
    qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ hq₁ hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hS₁ hS₂ hsup
  have hl : 0 ≤ lam := (hlow.trans_le hlam).le
  have hdot : ∀ {k : ℕ} (v : Fin k → ℝ), 0 ≤ v ⬝ᵥ v := fun v =>
    Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have h3 : ∀ {a b c M K : ℝ}, 0 ≤ a → 0 ≤ b → 0 ≤ c → a + b + c ≤ M → M ≤ K →
      a ≤ K ∧ b ≤ K ∧ c ≤ K := fun ha hb hc hM hK =>
    ⟨by linarith, by linarith, by linarith⟩
  refine h3 ?_ ?_ ?_ hM (hK η hη)
  · exact mul_nonneg (mul_nonneg hl h25.constants.α_nonneg)
      (integral_nonneg fun ω => hdot _)
  · exact mul_nonneg (mul_nonneg hl h25.constants.β₂_nonneg)
      (integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun s _ => hdot _)
  · refine mul_nonneg (mul_nonneg hl h25.constants.β₁_nonneg)
      (integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun s _ => ?_)
    exact add_nonneg (add_nonneg (hdot _) (Finset.sum_nonneg fun j _ => hdot _))
      (integral_nonneg fun e => hdot _)

end MVFBSDEJ.Acceptance
