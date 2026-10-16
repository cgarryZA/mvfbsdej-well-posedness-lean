/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.JumpLeftEnergy
import Dissertation.WellPosedness.Existence.ZeroEnergy
import Dissertation.WellPosedness.System.PaperSolutionForced

/-!
# A version of a solution with càdlàg paths

A solution `(X, Y, Z, U)` of (1.1) in the sense of `PaperSolution` has right-continuous paths on
`[0, T)` and, almost surely, left limits on `(0, T]`. Over a filtration whose fields contain the
null sets, and when `b, σ, h, f` have the joint measurability (2.3), it has a version all of whose
paths of `X` and `Y` are càdlàg on `[0, T]`: the processes `X, Y`, extended to all times as in
`PaperSolution.exists_solves`, are set to `0` off a measurable set of full measure on which the
paths of `X` and `Y` have left limits. The version is again a solution with the same `Z, U` and
jump representative `γ`, and agrees with `X, Y` at every time of `[0, T]` almost surely.

## Main statements

* `PaperSolution.exists_cadlag_version` — the càdlàg version of a solution.
* `PaperSolutionForced.exists_cadlag_version` — the same for the `λ`-forced system (4.1).
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- Tuples of processes agreeing at a sample point and a time have the same value there. -/
theorem tupleAt_apply_eq_of_eq {X' : Fin n → ℝ → Ω → ℝ} {Y' : Fin m → ℝ → Ω → ℝ} {s : ℝ}
    {ω : Ω} (hx : ∀ i, X' i s ω = X i s ω) (hy : ∀ k, Y' k s ω = Y k s ω) :
    tupleAt ν X' Y' Z U s ω = tupleAt ν X Y Z U s ω := by
  simp only [tupleAt, hx, hy]

/-- **A solution has a version with càdlàg paths.** Let `(X, Y, Z, U)` be a solution of (1.1) in
the sense of `PaperSolution`, with jump representative `γ`, for `T ≥ 0`, coefficients whose
`b, σ, h, f` have the joint measurability (2.3), and a filtration each of whose fields contains the
null sets. Then there are `X', Y'` such that `(X', Y', Z, U)` is a solution with the same `γ`,
every path of `X'` and `Y'` has left limits at every time of `(0, T]`, and almost surely `X' = X`
and `Y' = Y` at every time of `[0, T]`. -/
theorem _root_.Dissertation.WellPosedness.System.PaperSolution.exists_cadlag_version
    (h : PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ) (hT : 0 ≤ T) (hC : CoeffBorel T C)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → ∀ t : ℝ, MeasurableSet[ℱ t] s) :
    ∃ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ),
      PaperSolution D ℱ hℱW hℱN T C ξ₀ X' Y' Z U γ
      ∧ (∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X' i s ω) (𝓝[<] t) (𝓝 l))
      ∧ (∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y' k s ω) (𝓝[<] t) (𝓝 l))
      ∧ ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, (∀ i, X' i t ω = X i t ω) ∧ ∀ k, Y' k t ω = Y k t ω := by
  classical
  obtain ⟨X₁, Y₁, hXe, hYe, hs⟩ := h.exists_solves hT
  -- a measurable set of full measure on which the paths have left limits
  obtain ⟨S, hSae, hSm, hSsub⟩ :=
    ((ae_all_iff.mpr h.X_leftLim).and (ae_all_iff.mpr h.Y_leftLim)).exists_measurable_mem
  have hSae' : ∀ᵐ ω ∂P, ω ∈ S := hSae
  have hSt : ∀ t, MeasurableSet[ℱ t] S := fun t => by
    simpa using (hnull Sᶜ hSm.compl (mem_ae_iff.mp hSae) t).compl
  set X' : Fin n → ℝ → Ω → ℝ := fun i t => S.indicator (X₁ i t) with hX'
  set Y' : Fin m → ℝ → Ω → ℝ := fun k t => S.indicator (Y₁ k t) with hY'
  have hX'eq : ∀ ω ∈ S, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t ω = X i t ω := fun ω hω i t ht => by
    simp only [hX', Set.indicator_of_mem hω, hXe i t ht]
  have hY'eq : ∀ ω ∈ S, ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t ω = Y k t ω := fun ω hω k t ht => by
    simp only [hY', Set.indicator_of_mem hω, hYe k t ht]
  -- the paths of the version
  have hX'r : ∀ i ω t, Tendsto (fun s => X' i s ω) (𝓝[>] t) (𝓝 (X' i t ω)) := fun i ω t => by
    by_cases hω : ω ∈ S
    · simp only [hX', Set.indicator_of_mem hω]
      exact (hs.fwd i).X_rightCont ω t
    · simp only [hX', Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  have hY'r : ∀ k ω t, Tendsto (fun s => Y' k s ω) (𝓝[>] t) (𝓝 (Y' k t ω)) := fun k ω t => by
    by_cases hω : ω ∈ S
    · simp only [hY', Set.indicator_of_mem hω]
      exact (hs.bwd k).Y_rightCont ω t
    · simp only [hY', Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  have hX'l : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
      Tendsto (fun s => X' i s ω) (𝓝[<] t) (𝓝 l) := fun i ω => by
    by_cases hω : ω ∈ S
    · exact exists_tendsto_nhdsLT_of_eqOn (hX'eq ω hω i) ((hSsub ω hω).1 i)
    · intro t _
      refine ⟨0, ?_⟩
      simp only [hX', Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  have hY'l : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
      Tendsto (fun s => Y' k s ω) (𝓝[<] t) (𝓝 l) := fun k ω => by
    by_cases hω : ω ∈ S
    · exact exists_tendsto_nhdsLT_of_eqOn (hY'eq ω hω k) ((hSsub ω hω).2 k)
    · intro t _
      refine ⟨0, ?_⟩
      simp only [hY', Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  -- the version is a progressive tuple, so (2.3) gives the measurability of its coefficients
  have hΘ : ProgTuple ℱ P ν T X' Y' Z U :=
    { X_adapted := fun i t => ((hs.fwd i).X_adapted t).indicator (hSt t)
      X_rightCont := hX'r
      Y_adapted := fun k t => ((hs.bwd k).Y_adapted t).indicator (hSt t)
      Y_rightCont := hY'r
      Z_meas := fun k j => Brownian.Ito.measurable_uncurry_of_predictable (h.Z_pred k j)
      Z_prog := fun k j =>
        progressivelyMeasurable_of_predictable_of_vanish (h.Z_pred k) (h.Z_vanish k) j
      Z_sq := h.Z_sq
      U_meas := fun k => (h.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
      U_prog := fun k => (h.U_pred k).markedProgressivelyMeasurable
      U_sq := h.U_sq }
  have hCE := hC.crossEval hΘ
  -- the tuples, laws and coefficient processes agree on `S`
  have htup : ∀ ω ∈ S, ∀ s ∈ Set.Icc (0 : ℝ) T,
      tupleAt ν X' Y' Z U s ω = tupleAt ν X Y Z U s ω := fun ω hω s hs =>
    tupleAt_apply_eq_of_eq (fun i => hX'eq ω hω i s hs) (fun k => hY'eq ω hω k s hs)
  have hlaw : ∀ s ∈ Set.Icc (0 : ℝ) T,
      lawP2 P (tupleAt ν X' Y' Z U s) = lawP2 P (tupleAt ν X Y Z U s) := fun s hs =>
    lawP2_congr (hSae'.mono fun ω hω => htup ω hω s hs)
  have hb : ∀ ω ∈ S, ∀ i s,
      driftProc P T C X' Y' Z U i ω s = driftProc P T C X Y Z U i ω s := by
    intro ω hω i s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · simp only [driftProc, Set.indicator_of_mem hs, hlaw s hs, htup ω hω s hs]
    · simp only [driftProc, Set.indicator_of_notMem hs]
  have hσ : ∀ ω ∈ S, ∀ i s j,
      diffusionProc P T C X' Y' Z U i s ω j = diffusionProc P T C X Y Z U i s ω j := by
    intro ω hω i s j
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · simp only [diffusionProc, Set.indicator_of_mem hs, hlaw s hs, htup ω hω s hs]
    · simp only [diffusionProc, Set.indicator_of_notMem hs]
  have hf : ∀ ω ∈ S, ∀ k s,
      driverProc P T C X' Y' Z U k ω s = driverProc P T C X Y Z U k ω s := by
    intro ω hω k s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · simp only [driverProc, Set.indicator_of_mem hs, hlaw s hs, htup ω hω s hs]
    · simp only [driverProc, Set.indicator_of_notMem hs]
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hg : ∀ ω ∈ S, ∀ k, terminalVal P T C X' k ω = terminalVal P T C X k ω := by
    have hl : lawP2 P (fun ω' => (WithLp.toLp 2 fun i => X' i T ω' : EuclideanSpace ℝ (Fin n)))
        = lawP2 P (fun ω' => (WithLp.toLp 2 fun i => X i T ω' : EuclideanSpace ℝ (Fin n))) :=
      lawP2_congr (hSae'.mono fun ω hω => by
        have hx : ∀ i, X' i T ω = X i T ω := fun i => hX'eq ω hω i T hTm
        simp only [hx])
    intro ω hω k
    have hx : ∀ i, X' i T ω = X i T ω := fun i => hX'eq ω hω i T hTm
    simp only [terminalVal, hl, hx]
  -- the energies are unchanged
  have hbE : ∀ i, Brownian.Ito.energy P T (driftProc P T C X' Y' Z U i)
      = Brownian.Ito.energy P T (driftProc P T C X Y Z U i) := fun i => by
    unfold Brownian.Ito.energy
    exact lintegral_congr_ae (hSae'.mono fun ω hω => by simp only [hb ω hω i])
  have hσE : ∀ i j, Brownian.Ito.energy P T (fun ω s => diffusionProc P T C X' Y' Z U i s ω j)
      = Brownian.Ito.energy P T (fun ω s => diffusionProc P T C X Y Z U i s ω j) := fun i j => by
    unfold Brownian.Ito.energy
    exact lintegral_congr_ae (hSae'.mono fun ω hω => by simp only [hσ ω hω i])
  have hfE : ∀ k, Brownian.Ito.energy P T (driverProc P T C X' Y' Z U k)
      = Brownian.Ito.energy P T (driverProc P T C X Y Z U k) := fun k => by
    unfold Brownian.Ito.energy
    exact lintegral_congr_ae (hSae'.mono fun ω hω => by simp only [hf ω hω k])
  have hσ0 : ∀ i j, Brownian.Ito.energy P T (fun ω s =>
      diffusionProc P T C X Y Z U i s ω j - diffusionProc P T C X' Y' Z U i s ω j) = 0 :=
    fun i j => by
      unfold Brownian.Ito.energy
      rw [← lintegral_zero]
      exact lintegral_congr_ae (hSae'.mono fun ω hω => by simp [hσ ω hω i])
  -- the predictable tuples and their laws agree on `S`, at every time of `(0, T]`
  have htupL : ∀ ω ∈ S, ∀ s ∈ Set.Ioc (0 : ℝ) T,
      tupleAt ν (leftLimProc X') (leftLimProc Y') Z U s ω
        = tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω := fun ω hω s hs =>
    tupleAt_apply_eq_of_eq
      (fun i => leftLim_eq_of_eqOn (hX'eq ω hω i) ((hSsub ω hω).1 i) hs)
      (fun k => leftLim_eq_of_eqOn (hY'eq ω hω k) ((hSsub ω hω).2 k) hs)
  have hlawL : ∀ s ∈ Set.Ioc (0 : ℝ) T,
      lawP2 P (tupleAt ν (leftLimProc X') (leftLimProc Y') Z U s)
        = lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s) := fun s hs =>
    lawP2_congr (hSae'.mono fun ω hω => htupL ω hω s hs)
  have hIoc : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Ioc (0 : ℝ) T := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := T)).mem_iff]
      with s hs' hsI
    exact hs'.mpr hsI
  refine ⟨X', Y', ?_, hX'l, hY'l, hSae'.mono fun ω hω t ht =>
    ⟨fun i => hX'eq ω hω i t ht, fun k => hY'eq ω hω k t ht⟩⟩
  exact
    { X_adapted := fun i t _ => hΘ.X_adapted i t
      X_rightCont := fun i ω t _ => hX'r i ω t
      X_leftLim := fun i => Eventually.of_forall (hX'l i)
      X_sup := by
        refine (lintegral_congr_ae (hSae'.mono fun ω hω => ?_)).trans_lt h.X_sup
        refine iSup_congr fun t => iSup_congr fun ht => ?_
        have hx : ∀ i, X' i t ω = X i t ω := fun i => hX'eq ω hω i t ht
        simp only [hx]
      Y_adapted := fun k t _ => hΘ.Y_adapted k t
      Y_rightCont := fun k ω t _ => hY'r k ω t
      Y_leftLim := fun k => Eventually.of_forall (hY'l k)
      Y_sup := by
        refine (lintegral_congr_ae (hSae'.mono fun ω hω => ?_)).trans_lt h.Y_sup
        refine iSup_congr fun t => iSup_congr fun ht => ?_
        have hy : ∀ k, Y' k t ω = Y k t ω := fun k => hY'eq ω hω k t ht
        simp only [hy]
      Z_pred := h.Z_pred
      Z_vanish := h.Z_vanish
      Z_sq := h.Z_sq
      U_pred := h.U_pred
      U_vanish := h.U_vanish
      U_sq := h.U_sq
      b_meas := hCE.b_meas
      b_prog := hCE.b_prog
      b_sq := fun i => by rw [hbE i]; exact h.b_sq i
      σ_meas := hCE.σ_meas
      σ_prog := hCE.σ_prog
      σ_sq := fun i j => by rw [hσE i j]; exact h.σ_sq i j
      γ_meas := h.γ_meas
      γ_prog := h.γ_prog
      γ_sq := h.γ_sq
      f_meas := hCE.f_meas
      f_prog := hCE.f_prog
      f_sq := fun k => by rw [hfE k]; exact h.f_sq k
      jump_rep := by
        filter_upwards [h.jump_rep, hIoc] with s hsr hsI
        rw [hlawL s hsI]
        filter_upwards [hsr, hSae'] with ω hω hωS
        rw [htupL ω hωS s hsI]
        exact hω
      fwd := fun i => by
        obtain ⟨M, hM, hMc, hid⟩ := h.fwd i
        refine ⟨M, fun t ht => (hM t ht).trans ?_, hMc, ?_⟩
        · exact multidimStochasticIntegral_congr_of_energy D.W hℱW _ _ _ _ _ _ (hσ0 i) ht.2
        · filter_upwards [hid, hSae'] with ω hω hωS t ht
          have hbω : driftProc P T C X' Y' Z U i ω = driftProc P T C X Y Z U i ω :=
            funext (hb ω hωS i)
          rw [hX'eq ω hωS i t ht, hω t ht, hbω]
      bwd := fun k => by
        obtain ⟨M, hM, hMc, hid⟩ := h.bwd k
        refine ⟨M, hM, hMc, ?_⟩
        filter_upwards [hid, hSae'] with ω hω hωS t ht
        have hfω : driverProc P T C X' Y' Z U k ω = driverProc P T C X Y Z U k ω :=
          funext (hf ω hωS k)
        rw [hY'eq ω hωS k t ht, hω t ht, hg ω hωS k, hfω] }

/-- **A solution of the forced system has a version with càdlàg paths.** Let `(X, Y, Z, U)` solve
the `λ`-forced system (4.1) in the sense of `PaperSolutionForced`, with jump representative `γ`,
for `T ≥ 0`, coefficients whose `b, σ, h, f` have the joint measurability (2.3), and a filtration
each of whose fields contains the null sets. Then there are `X', Y'` such that `(X', Y', Z, U)`
solves it with the same `γ`, every path of `X'` and `Y'` has left limits at every time of
`(0, T]`, and almost surely `X' = X` and `Y' = Y` at every time of `[0, T]`. -/
theorem _root_.Dissertation.WellPosedness.System.PaperSolutionForced.exists_cadlag_version
    {lam : ℝ} {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ}
    {qh : Fin n → ℝ → Ω → E → ℝ} {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
    (h : PaperSolutionForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ) (hT : 0 ≤ T)
    (hC : CoeffBorel T C)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → ∀ t : ℝ, MeasurableSet[ℱ t] s) :
    ∃ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ),
      PaperSolutionForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X' Y' Z U γ
      ∧ (∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X' i s ω) (𝓝[<] t) (𝓝 l))
      ∧ (∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y' k s ω) (𝓝[<] t) (𝓝 l))
      ∧ ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, (∀ i, X' i t ω = X i t ω) ∧ ∀ k, Y' k t ω = Y k t ω := by
  classical
  obtain ⟨X₁, hXe, hXa, hXr⟩ := exists_adapted_rightCont_extension hT h.X_adapted h.X_rightCont
  obtain ⟨Y₁, hYe, hYa, hYr⟩ := exists_adapted_rightCont_extension hT h.Y_adapted h.Y_rightCont
  obtain ⟨S, hSae, hSm, hSsub⟩ :=
    ((ae_all_iff.mpr h.X_leftLim).and (ae_all_iff.mpr h.Y_leftLim)).exists_measurable_mem
  have hSae' : ∀ᵐ ω ∂P, ω ∈ S := hSae
  have hSt : ∀ t, MeasurableSet[ℱ t] S := fun t => by
    simpa using (hnull Sᶜ hSm.compl (mem_ae_iff.mp hSae) t).compl
  set X' : Fin n → ℝ → Ω → ℝ := fun i t => S.indicator (X₁ i t) with hX'
  set Y' : Fin m → ℝ → Ω → ℝ := fun k t => S.indicator (Y₁ k t) with hY'
  have hX'eq : ∀ ω ∈ S, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t ω = X i t ω := fun ω hω i t ht => by
    simp only [hX', Set.indicator_of_mem hω, hXe i t ht]
  have hY'eq : ∀ ω ∈ S, ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t ω = Y k t ω := fun ω hω k t ht => by
    simp only [hY', Set.indicator_of_mem hω, hYe k t ht]
  have hX'r : ∀ i ω t, Tendsto (fun s => X' i s ω) (𝓝[>] t) (𝓝 (X' i t ω)) := fun i ω t => by
    by_cases hω : ω ∈ S
    · simp only [hX', Set.indicator_of_mem hω]
      exact hXr i ω t
    · simp only [hX', Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  have hY'r : ∀ k ω t, Tendsto (fun s => Y' k s ω) (𝓝[>] t) (𝓝 (Y' k t ω)) := fun k ω t => by
    by_cases hω : ω ∈ S
    · simp only [hY', Set.indicator_of_mem hω]
      exact hYr k ω t
    · simp only [hY', Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  have hX'l : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
      Tendsto (fun s => X' i s ω) (𝓝[<] t) (𝓝 l) := fun i ω => by
    by_cases hω : ω ∈ S
    · exact exists_tendsto_nhdsLT_of_eqOn (hX'eq ω hω i) ((hSsub ω hω).1 i)
    · intro t _
      refine ⟨0, ?_⟩
      simp only [hX', Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  have hY'l : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
      Tendsto (fun s => Y' k s ω) (𝓝[<] t) (𝓝 l) := fun k ω => by
    by_cases hω : ω ∈ S
    · exact exists_tendsto_nhdsLT_of_eqOn (hY'eq ω hω k) ((hSsub ω hω).2 k)
    · intro t _
      refine ⟨0, ?_⟩
      simp only [hY', Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  have hΘ : ProgTuple ℱ P ν T X' Y' Z U :=
    { X_adapted := fun i t => (hXa i t).indicator (hSt t)
      X_rightCont := hX'r
      Y_adapted := fun k t => (hYa k t).indicator (hSt t)
      Y_rightCont := hY'r
      Z_meas := fun k j => Brownian.Ito.measurable_uncurry_of_predictable (h.Z_pred k j)
      Z_prog := fun k j =>
        progressivelyMeasurable_of_predictable_of_vanish (h.Z_pred k) (h.Z_vanish k) j
      Z_sq := h.Z_sq
      U_meas := fun k => (h.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
      U_prog := fun k => (h.U_pred k).markedProgressivelyMeasurable
      U_sq := h.U_sq }
  have hCE := hC.crossEval hΘ
  have htup : ∀ ω ∈ S, ∀ s ∈ Set.Icc (0 : ℝ) T,
      tupleAt ν X' Y' Z U s ω = tupleAt ν X Y Z U s ω := fun ω hω s hs =>
    tupleAt_apply_eq_of_eq (fun i => hX'eq ω hω i s hs) (fun k => hY'eq ω hω k s hs)
  have hlaw : ∀ s ∈ Set.Icc (0 : ℝ) T,
      lawP2 P (tupleAt ν X' Y' Z U s) = lawP2 P (tupleAt ν X Y Z U s) := fun s hs =>
    lawP2_congr (hSae'.mono fun ω hω => htup ω hω s hs)
  have hb : ∀ ω ∈ S, ∀ i s,
      driftProc P T C X' Y' Z U i ω s = driftProc P T C X Y Z U i ω s := by
    intro ω hω i s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · simp only [driftProc, Set.indicator_of_mem hs, hlaw s hs, htup ω hω s hs]
    · simp only [driftProc, Set.indicator_of_notMem hs]
  have hσ : ∀ ω ∈ S, ∀ i s j,
      diffusionProc P T C X' Y' Z U i s ω j = diffusionProc P T C X Y Z U i s ω j := by
    intro ω hω i s j
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · simp only [diffusionProc, Set.indicator_of_mem hs, hlaw s hs, htup ω hω s hs]
    · simp only [diffusionProc, Set.indicator_of_notMem hs]
  have hf : ∀ ω ∈ S, ∀ k s,
      driverProc P T C X' Y' Z U k ω s = driverProc P T C X Y Z U k ω s := by
    intro ω hω k s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · simp only [driverProc, Set.indicator_of_mem hs, hlaw s hs, htup ω hω s hs]
    · simp only [driverProc, Set.indicator_of_notMem hs]
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hg : ∀ ω ∈ S, ∀ k, terminalVal P T C X' k ω = terminalVal P T C X k ω := by
    have hl : lawP2 P (fun ω' => (WithLp.toLp 2 fun i => X' i T ω' : EuclideanSpace ℝ (Fin n)))
        = lawP2 P (fun ω' => (WithLp.toLp 2 fun i => X i T ω' : EuclideanSpace ℝ (Fin n))) :=
      lawP2_congr (hSae'.mono fun ω hω => by
        have hx : ∀ i, X' i T ω = X i T ω := fun i => hX'eq ω hω i T hTm
        simp only [hx])
    intro ω hω k
    have hx : ∀ i, X' i T ω = X i T ω := fun i => hX'eq ω hω i T hTm
    simp only [terminalVal, hl, hx]
  have hbE : ∀ i, Brownian.Ito.energy P T (fun ω s => lam * driftProc P T C X' Y' Z U i ω s
      + qb i ω s) = Brownian.Ito.energy P T (fun ω s => lam * driftProc P T C X Y Z U i ω s
      + qb i ω s) := fun i => by
    unfold Brownian.Ito.energy
    exact lintegral_congr_ae (hSae'.mono fun ω hω => by simp only [hb ω hω i])
  have hσE : ∀ i j, Brownian.Ito.energy P T (fun ω s =>
      lam * diffusionProc P T C X' Y' Z U i s ω j + qσ i s ω j)
      = Brownian.Ito.energy P T (fun ω s =>
      lam * diffusionProc P T C X Y Z U i s ω j + qσ i s ω j) := fun i j => by
    unfold Brownian.Ito.energy
    exact lintegral_congr_ae (hSae'.mono fun ω hω => by simp only [hσ ω hω i])
  have hfE : ∀ k, Brownian.Ito.energy P T (fun ω s => lam * driverProc P T C X' Y' Z U k ω s
      + qf k ω s) = Brownian.Ito.energy P T (fun ω s => lam * driverProc P T C X Y Z U k ω s
      + qf k ω s) := fun k => by
    unfold Brownian.Ito.energy
    exact lintegral_congr_ae (hSae'.mono fun ω hω => by simp only [hf ω hω k])
  have hσ0 : ∀ i j, Brownian.Ito.energy P T (fun ω s =>
      (lam * diffusionProc P T C X Y Z U i s ω j + qσ i s ω j)
        - (lam * diffusionProc P T C X' Y' Z U i s ω j + qσ i s ω j)) = 0 :=
    fun i j => by
      unfold Brownian.Ito.energy
      rw [← lintegral_zero]
      exact lintegral_congr_ae (hSae'.mono fun ω hω => by simp [hσ ω hω i])
  have htupL : ∀ ω ∈ S, ∀ s ∈ Set.Ioc (0 : ℝ) T,
      tupleAt ν (leftLimProc X') (leftLimProc Y') Z U s ω
        = tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω := fun ω hω s hs =>
    tupleAt_apply_eq_of_eq
      (fun i => leftLim_eq_of_eqOn (hX'eq ω hω i) ((hSsub ω hω).1 i) hs)
      (fun k => leftLim_eq_of_eqOn (hY'eq ω hω k) ((hSsub ω hω).2 k) hs)
  have hlawL : ∀ s ∈ Set.Ioc (0 : ℝ) T,
      lawP2 P (tupleAt ν (leftLimProc X') (leftLimProc Y') Z U s)
        = lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s) := fun s hs =>
    lawP2_congr (hSae'.mono fun ω hω => htupL ω hω s hs)
  have hIoc : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Ioc (0 : ℝ) T := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := T)).mem_iff]
      with s hs' hsI
    exact hs'.mpr hsI
  have hmul : Continuous fun x : ℝ => lam * x := continuous_const.mul continuous_id
  refine ⟨X', Y', ?_, hX'l, hY'l, hSae'.mono fun ω hω t ht =>
    ⟨fun i => hX'eq ω hω i t ht, fun k => hY'eq ω hω k t ht⟩⟩
  exact
    { forcing := h.forcing
      X_adapted := fun i t _ => hΘ.X_adapted i t
      X_rightCont := fun i ω t _ => hX'r i ω t
      X_leftLim := fun i => Eventually.of_forall (hX'l i)
      X_sup := by
        refine (lintegral_congr_ae (hSae'.mono fun ω hω => ?_)).trans_lt h.X_sup
        refine iSup_congr fun t => iSup_congr fun ht => ?_
        have hx : ∀ i, X' i t ω = X i t ω := fun i => hX'eq ω hω i t ht
        simp only [hx]
      Y_adapted := fun k t _ => hΘ.Y_adapted k t
      Y_rightCont := fun k ω t _ => hY'r k ω t
      Y_leftLim := fun k => Eventually.of_forall (hY'l k)
      Y_sup := by
        refine (lintegral_congr_ae (hSae'.mono fun ω hω => ?_)).trans_lt h.Y_sup
        refine iSup_congr fun t => iSup_congr fun ht => ?_
        have hy : ∀ k, Y' k t ω = Y k t ω := fun k => hY'eq ω hω k t ht
        simp only [hy]
      Z_pred := h.Z_pred
      Z_vanish := h.Z_vanish
      Z_sq := h.Z_sq
      U_pred := h.U_pred
      U_vanish := h.U_vanish
      U_sq := h.U_sq
      b_meas := fun i => ((hCE.b_meas i).const_mul lam).add (h.forcing.qb_meas i)
      b_prog := fun i => (hmul.comp_progressivelyMeasurable (mul_zero lam) (hCE.b_prog i)).add
        (h.forcing.qb_prog i)
      b_sq := fun i => by rw [hbE i]; exact h.b_sq i
      σ_meas := fun i j => ((hCE.σ_meas i j).const_mul lam).add (h.forcing.qσ_meas i j)
      σ_prog := fun i j =>
        (hmul.comp_progressivelyMeasurable (mul_zero lam) (hCE.σ_prog i j)).add
          (h.forcing.qσ_prog i j)
      σ_sq := fun i j => by rw [hσE i j]; exact h.σ_sq i j
      γ_meas := h.γ_meas
      γ_prog := h.γ_prog
      γ_sq := h.γ_sq
      f_meas := fun k => ((hCE.f_meas k).const_mul lam).add (h.forcing.qf_meas k)
      f_prog := fun k => (hmul.comp_progressivelyMeasurable (mul_zero lam) (hCE.f_prog k)).add
        (h.forcing.qf_prog k)
      f_sq := fun k => by rw [hfE k]; exact h.f_sq k
      jump_rep := by
        filter_upwards [h.jump_rep, hIoc] with s hsr hsI
        rw [hlawL s hsI]
        filter_upwards [hsr, hSae'] with ω hω hωS
        rw [htupL ω hωS s hsI]
        exact hω
      fwd := fun i => by
        obtain ⟨M, hM, hMc, hid⟩ := h.fwd i
        refine ⟨M, fun t ht => (hM t ht).trans ?_, hMc, ?_⟩
        · exact multidimStochasticIntegral_congr_of_energy D.W hℱW _ _ _ _ _ _ (hσ0 i) ht.2
        · filter_upwards [hid, hSae'] with ω hω hωS t ht
          have hbω : driftProc P T C X' Y' Z U i ω = driftProc P T C X Y Z U i ω :=
            funext (hb ω hωS i)
          rw [hX'eq ω hωS i t ht, hω t ht, hbω]
      bwd := fun k => by
        obtain ⟨M, hM, hMc, hid⟩ := h.bwd k
        refine ⟨M, hM, hMc, ?_⟩
        filter_upwards [hid, hSae'] with ω hω hωS t ht
        have hfω : driverProc P T C X' Y' Z U k ω = driverProc P T C X Y Z U k ω :=
          funext (hf ω hωS k)
        rw [hY'eq ω hωS k t ht, hω t ht, hg ω hωS k, hfω] }

end Dissertation.WellPosedness.Existence
