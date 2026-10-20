/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.PaperSolutionForced
import MVFBSDEJ.WellPosedness.System.PaperSolutionSolves

/-!
# Solutions of (4.1) in the sense of the paper and the predicate `SolvesForced`

`PaperSolutionForced` states the well-posedness paper's definition of a solution of the
`λ`-forced system (4.1), and `SolvesForced` is the form of (4.1) on which the proofs of Lemmas
4.2–4.4 run. They differ as `PaperSolution` and `Solves` do
(`MVFBSDEJ.WellPosedness.System.PaperSolutionSolves`), and the passage between them is the
same, with the forced integrands `λ ψ + q^ψ` in place of the coefficient processes `ψ` and the
terminal value `λ g(X_T, Law X_T) + q^g_T` in place of `g(X_T, Law X_T)`.

* A solution in the sense of the paper, extended off `[0, T]` (`0` before `0`, frozen after
  `T`), is a solution of `SolvesForced` with the same `Z`, `U`, `γ`
  (`PaperSolutionForced.exists_solvesForced`): the forced integrands only see `[0, T]`, the
  representative `γ` of `h` at `(Θ⁻_s, μ⁻_s)` represents `h` at `(Θ_s, μ_s)` since
  `Θ⁻_s = Θ_s` almost surely at almost every time, and `ξ₀` and the terminal value are square
  integrable by the `S²` bounds.
* A solution of `SolvesForced` with predictable `(Z, U)` is a solution in the sense of the paper
  (`SolvesForced.paperSolutionForced`), over a filtration on which Lemma 4.1 gives the `S²`
  bounds; every solution has predictable versions of `(Z, U)` with which it is again a solution,
  under (2.5) along every progressive tuple, `CoeffRegular`
  (`SolvesForced.exists_paperSolutionForced`).

## Main statements

* `PaperSolutionForced.toPaperWeakTuple` — the tuple of a solution lies in `ℍ²_weak`.
* `PaperSolutionForced.memLp_initial`, `PaperSolutionForced.memLp_terminal` — `ξ₀` and
  `λ g(X_T, Law X_T) + q^g_T` are square integrable.
* `PaperSolutionForced.ae_ae_tupleAt_leftLimProc_eq`, `PaperSolutionForced.jump_rep_tupleAt` —
  `Θ⁻_s = Θ_s` almost surely at almost every time, so `γ` represents `h(s, Θ_s, ·, μ_s)`.
* `PaperSolutionForced.exists_solvesForced` — a solution in the sense of the paper, extended off
  `[0, T]`, is a solution of `SolvesForced`.
* `SolvesForced.paperSolutionForced` — a solution of `SolvesForced` with predictable integrands
  is a solution in the sense of the paper.
* `SolvesForced.exists_paperSolutionForced` — a solution of `SolvesForced` is one in the sense of
  the paper after passing to predictable versions of `(Z, U)`.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Existence LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T lam : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}

/-! ### Solutions in the sense of the paper as solutions of `SolvesForced` -/

namespace PaperSolutionForced

variable (h : PaperSolutionForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ)
include h

/-- **The tuple of a solution lies in `ℍ²_weak`**: the `S²` bounds on `X` and `Y` give finite
energy on `[0, T]`. -/
theorem toPaperWeakTuple : PaperWeakTuple ℱ P ν T X Y Z U where
  X_adapted := h.X_adapted
  X_rightCont := h.X_rightCont
  X_leftLim := h.X_leftLim
  X_sq := energy_ne_top_of_lintegral_biSup_esq_lt_top h.X_sup
  Y_adapted := h.Y_adapted
  Y_rightCont := h.Y_rightCont
  Y_leftLim := h.Y_leftLim
  Y_sq := energy_ne_top_of_lintegral_biSup_esq_lt_top h.Y_sup
  Z_pred := h.Z_pred
  Z_vanish := h.Z_vanish
  Z_sq := h.Z_sq
  U_pred := h.U_pred
  U_vanish := h.U_vanish
  U_sq := h.U_sq

variable (hT : 0 ≤ T)
include hT

/-- **The initial datum of a solution is square integrable**: `ξ₀ = X_0` almost surely, and
`X_0` is square integrable by the `S²` bound. -/
theorem memLp_initial (i : Fin n) : MemLp (ξ₀ i) 2 P := by
  obtain ⟨M, hMae, -, hid⟩ := h.fwd i
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hX0 : MemLp (X i 0) 2 P := memLp_of_lintegral_biSup_esq_lt_top h.X_sup h0 i
    ((h.X_adapted i 0 h0).mono (ℱ.le 0) le_rfl).aestronglyMeasurable
  refine hX0.ae_eq ?_
  filter_upwards [hid, hMae 0 h0,
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W ℱ hℱW _
      (h.σ_meas i) (h.σ_prog i)
      (sq_int_global_of_vanishing (forcedDiffusion_of_notMem h.forcing.qσ_vanish lam i)
        (h.σ_sq i)) le_rfl,
    Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos
      (φ := fun ω s e => lam * jumpProc T γ i s ω e + qh i s ω e) D.N hℱN (h.γ_meas i)
      (h.γ_prog i)
      (marked_sq_int_global_of_vanishing (forcedJump_of_notMem h.forcing.qh_vanish lam i)
        (h.γ_sq i)) le_rfl] with ω hω hM hW hN
  simp only [Pi.zero_apply] at hW hN
  rw [hω 0 h0, hM, hW, hN, Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
    integral_zero_measure]
  ring

/-- **The terminal value of a solution is square integrable**:
`λ g(X_T, Law X_T) + q^g_T = Y_T` almost surely, and `Y_T` is square integrable by the `S²`
bound. -/
theorem memLp_terminal (k : Fin m) :
    MemLp (fun ω => lam * terminalVal P T C X k ω + qg k ω) 2 P := by
  obtain ⟨M, -, -, hid⟩ := h.bwd k
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hYT : MemLp (Y k T) 2 P := memLp_of_lintegral_biSup_esq_lt_top h.Y_sup hTm k
    ((h.Y_adapted k T hTm).mono (ℱ.le T) le_rfl).aestronglyMeasurable
  refine hYT.ae_eq ?_
  filter_upwards [hid] with ω hω
  rw [hω T hTm, Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
    integral_zero_measure]
  ring

/-- **The predictable tuple of a solution is its tuple at almost every time**: for almost every
`s ∈ [0, T]`, `Θ⁻_s = (X_{s−}, Y_{s−}, Z_s, U_s)` equals `Θ_s` almost surely. -/
theorem ae_ae_tupleAt_leftLimProc_eq :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s =ᵐ[P] tupleAt ν X Y Z U s :=
  h.toPaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq hT

/-- **The jump coefficient at the tuple**: for a solution of (4.1) in the sense of the paper, `γ`
also represents `e ↦ h(s, Θ_s(ω), e, μ_s)` in `L²(ν)` for almost every `s ∈ [0, T]` and almost
every `ω`. -/
theorem jump_rep_tupleAt :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
        =ᵐ[ν] C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)) := by
  filter_upwards [h.jump_rep, h.ae_ae_tupleAt_leftLimProc_eq hT] with s hs heq
  filter_upwards [hs, heq] with ω hω hωeq
  rw [← hωeq, ← lawP2_congr heq]
  exact hω

/-- **A solution of (4.1) in the sense of the paper solves `SolvesForced`.** For `T ≥ 0`, there
are `X'`, `Y'` equal to `X`, `Y` at every time of `[0, T]` — adapted with right-continuous paths,
`0` before `0` and frozen after `T` — such that `(X', Y', Z, U)` solves the `λ`-forced system
(4.1) in the sense of `SolvesForced`, with the same forcing and the same `γ`. -/
theorem exists_solvesForced :
    ∃ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ),
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X i t)
      ∧ (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y k t)
      ∧ SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X' Y' Z U γ := by
  obtain ⟨X', hXe, hXa, hXr⟩ := exists_adapted_rightCont_extension hT h.X_adapted h.X_rightCont
  obtain ⟨Y', hYe, hYa, hYr⟩ := exists_adapted_rightCont_extension hT h.Y_adapted h.Y_rightCont
  have hdrift := driftProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hdiff := diffusionProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hdriver := driverProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hterm := terminalVal_eq_of_eq (P := P) (C := C) fun i => hXe i T ⟨hT, le_rfl⟩
  refine ⟨X', Y', hXe, hYe, ⟨h.forcing, ?_, fun i => ?_, fun k => ?_⟩⟩
  · filter_upwards [h.jump_rep_tupleAt hT, ae_restrict_mem measurableSet_Icc] with s hs hsI
    rw [tupleAt_eq_of_eqOn hXe hYe hsI]
    exact hs
  · rw [hdrift, hdiff]
    obtain ⟨M, hMae, -, hid⟩ := h.fwd i
    exact
      { σ_meas := h.σ_meas i
        σ_prog := h.σ_prog i
        σ_vanish := forcedDiffusion_of_notMem h.forcing.qσ_vanish lam i
        σ_sq := h.σ_sq i
        γ_meas := h.γ_meas i
        γ_prog := h.γ_prog i
        γ_vanish := forcedJump_of_notMem h.forcing.qh_vanish lam i
        γ_sq := h.γ_sq i
        b_meas := h.b_meas i
        b_prog := h.b_prog i
        b_vanish := fun ω s hs => by
          rw [driftProc_of_notMem hs, h.forcing.qb_vanish i ω s hs, mul_zero, add_zero]
        b_sq := h.b_sq i
        ξ₀_sq := h.memLp_initial hT i
        X_adapted := hXa i
        X_rightCont := hXr i
        eqn := fun t ht => by
          filter_upwards [hid, hMae t ht] with ω h1 h2
          rw [congrFun (hXe i t ht) ω, h1 t ht, h2] }
  · rw [hterm, hdriver]
    obtain ⟨M, hMae, -, hid⟩ := h.bwd k
    exact
      { Z_meas := fun j => Brownian.Ito.measurable_uncurry_of_predictable (h.Z_pred k j)
        Z_prog := progressivelyMeasurable_of_predictable_of_vanish (h.Z_pred k) (h.Z_vanish k)
        Z_vanish := h.Z_vanish k
        Z_sq := h.Z_sq k
        U_meas := (h.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
        U_prog := (h.U_pred k).markedProgressivelyMeasurable
        U_vanish := h.U_vanish k
        U_sq := h.U_sq k
        φ_meas := h.f_meas k
        φ_prog := h.f_prog k
        φ_vanish := fun ω s hs => by
          rw [driverProc_of_notMem hs, h.forcing.qf_vanish k ω s hs, mul_zero, add_zero]
        φ_sq := h.f_sq k
        ξ_sq := h.memLp_terminal hT k
        Y_adapted := hYa k
        Y_rightCont := hYr k
        eqn := fun t ht => by
          filter_upwards [hid, hMae t ht, hMae T ⟨hT, le_rfl⟩] with ω h1 h2 h3
          rw [congrFun (hYe k t ht) ω, h1 t ht, h2, h3] }

end PaperSolutionForced

/-! ### Solutions of `SolvesForced` as solutions in the sense of the paper -/

/-- **A solution of `SolvesForced` with predictable integrands is a solution in the sense of the
paper.** Over a filtration whose null sets lie in its time-`0` field, whose right-continuation is
constant before `0` and which admits a cross witness, for `T > 0`, a solution `(X, Y, Z, U)` of
the `λ`-forced system (4.1) in the sense of `SolvesForced` with `Z` predictable and `U` marked
predictable, coordinatewise, is a solution of (4.1) in the sense of the paper, with the same
forcing and the same `γ`. -/
theorem SolvesForced.paperSolutionForced
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ)
    (hZ : ∀ k j, Probability.Predictable ℱ fun ω s => Z k s ω j)
    (hU : ∀ k, Probability.MarkedPredictable ℱ ν fun ω s e => U k s ω e)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    PaperSolutionForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ where
  forcing := h.forcing
  X_adapted i t _ := (h.fwd i).X_adapted t
  X_rightCont i ω t _ := (h.fwd i).X_rightCont ω t
  X_leftLim i := (h.fwd i).ae_leftLim hT.le
  X_sup := h.lintegral_biSup_X_lt_top 𝒲 hℱ0 hnull hT
  Y_adapted k t _ := (h.bwd k).Y_adapted t
  Y_rightCont k ω t _ := (h.bwd k).Y_rightCont ω t
  Y_leftLim k := (h.bwd k).ae_leftLim hT.le
  Y_sup := h.lintegral_biSup_Y_lt_top 𝒲 hℱ0 hnull hT
  Z_pred := hZ
  Z_vanish k := (h.bwd k).Z_vanish
  Z_sq k := (h.bwd k).Z_sq
  U_pred := hU
  U_vanish k := (h.bwd k).U_vanish
  U_sq k := (h.bwd k).U_sq
  b_meas i := (h.fwd i).b_meas
  b_prog i := (h.fwd i).b_prog
  b_sq i := (h.fwd i).b_sq
  σ_meas i := (h.fwd i).σ_meas
  σ_prog i := (h.fwd i).σ_prog
  σ_sq i := (h.fwd i).σ_sq
  γ_meas i := (h.fwd i).γ_meas
  γ_prog i := (h.fwd i).γ_prog
  γ_sq i := (h.fwd i).γ_sq
  f_meas k := (h.bwd k).φ_meas
  f_prog k := (h.bwd k).φ_prog
  f_sq k := (h.bwd k).φ_sq
  jump_rep := h.jump_rep_left hT.le
  fwd i := by
    have hi := h.fwd i
    obtain ⟨M, -, hMae, hMcad⟩ := exists_ae_cadlag_brownianIntegral D.W ℱ hℱW _ hi.σ_meas
      hi.σ_prog (sq_int_global_of_vanishing hi.σ_vanish hi.σ_sq)
    exact ⟨M, fun t _ => hMae t, hMcad.mono fun _ hω => ⟨fun t _ => (hω t).1, fun t _ => (hω t).2⟩,
      hi.ae_forall_eq hT.le (fun t _ => hMae t) (hMcad.mono fun _ hω t => (hω t).1)⟩
  bwd k := by
    have hk := h.bwd k
    obtain ⟨M, -, hMae, hMcad⟩ := exists_ae_cadlag_brownianIntegral D.W ℱ hℱW _ hk.Z_meas
      hk.Z_prog (sq_int_global_of_vanishing hk.Z_vanish hk.Z_sq)
    exact ⟨M, fun t _ => hMae t, hMcad.mono fun _ hω => ⟨fun t _ => (hω t).1, fun t _ => (hω t).2⟩,
      hk.ae_forall_eq hT.le (fun t _ => hMae t) (hMcad.mono fun _ hω t => (hω t).1)⟩

/-- **Every solution of `SolvesForced` is a solution in the sense of the paper, up to versions of
`(Z, U)`.** Over a filtration whose null sets lie in its time-`0` field, whose right-continuation
is constant before `0` and which admits a cross witness, for coefficients with (2.5) along every
progressive tuple and `T > 0`, a solution `(X, Y, Z, U)` of the `λ`-forced system (4.1) in the
sense of `SolvesForced` has `Z'` and `U'` with `Z = Z'` `dP ⊗ ds`-almost everywhere on
`Ω × [0, T]` and `U = U'` `dP ⊗ ds ⊗ ν`-almost everywhere on `Ω × [0, T] × E`, coordinatewise,
such that `(X, Y, Z', U')` solves (4.1) in the sense of the paper, with the same forcing and the
same `γ`. -/
theorem SolvesForced.exists_paperSolutionForced
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ)
    (hC : CoeffRegular ℱ P T C) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∃ (Z' : Fin m → ℝ → Ω → Fin d → ℝ) (U' : Fin m → ℝ → Ω → E → ℝ),
      (∀ k j, ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T), Z k p.2 p.1 j = Z' k p.2 p.1 j)
      ∧ (∀ k, ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
          U k q.2.1 q.1 q.2.2 = U' k q.2.1 q.1 q.2.2)
      ∧ PaperSolutionForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z' U' γ := by
  obtain ⟨Z', U', hZpred, hUpred, hZae, hUae, h'⟩ := h.exists_predictable hC hT
  exact ⟨Z', U', hZae, hUae, h'.paperSolutionForced hZpred hUpred 𝒲 hℱ0 hnull hT⟩

end MVFBSDEJ.WellPosedness.System
