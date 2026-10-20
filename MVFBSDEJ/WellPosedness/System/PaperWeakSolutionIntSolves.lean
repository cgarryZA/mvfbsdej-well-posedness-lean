/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.PaperWeakSolutionInt
import MVFBSDEJ.WellPosedness.System.SolvesInt

/-!
# Solutions of `PaperWeakSolutionInt` as solutions of `SolvesInt`

`PaperWeakSolutionInt` states the solution notion of Theorem 3.3 of the well-posedness paper in
the encoding of `PaperSolution`, and `SolvesInt` is the form of (1.1) in `ℍ²_weak` on which the
uniqueness proof runs. They differ as `PaperSolution` and `Solves` do, in all but the
integrability of the data (`MVFBSDEJ.WellPosedness.System.PaperSolutionSolves`):

* `SolvesInt` asks every path of `X` and `Y` to be right-continuous at every time, and each
  process to be adapted at every time; the extension of `X` and `Y` by `0` before `0` and by
  `X_T`, `Y_T` after `T` has these properties (`exists_adapted_rightCont_extension`), with the
  same coefficient processes, finite energy on `[0, T]` and value at `T`;
* `SolvesInt` asks the identities almost surely at each time with the canonical Brownian
  integral, which a càdlàg version agrees with almost surely at each time;
* `SolvesInt` evaluates the jump coefficient at `(Θ_s, μ_s)`, and `Θ⁻_s = Θ_s` almost surely for
  almost every `s` along a tuple of `ℍ²_weak`
  (`PaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq`);
* `SolvesInt` takes `Z` and `U` progressively measurable, and a predictable integrand vanishing
  off `[0, T]` is progressively measurable.

Both notions ask the drift and driver processes along the solution only to have almost surely
integrable paths on `[0, T]`, and neither asks `ξ₀` or `g(X_T, Law X_T)` to be square
integrable; both ask `X_T` to be. So no condition on the coefficients enters the passage
(`PaperWeakSolutionInt.exists_solvesInt`).

## Main statements

* `SolvesInt.of_linear` — a solution of `SolvesInt` from its unforced linear equations.
* `PaperWeakSolutionInt.jump_rep_tupleAt` — `γ` represents `h(s, Θ_s, ·, μ_s)`.
* `PaperWeakSolutionInt.exists_solvesInt` — a solution of `PaperWeakSolutionInt`, extended off
  `[0, T]`, is a solution of `SolvesInt`.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ} {C : Coeffs ν n m d}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {ξ₀ : Fin n → Ω → ℝ}

/-- **A solution of (1.1) in `ℍ²_weak` from its unforced equations**: a representative of the
jump coefficient, the forward equations of `LinearFSDEJInt` from `ξ₀`, the backward equations of
`LinearBSDEJInt` with terminal value `g(X_T, Law X_T)`, finite energy of `X` and `Y` on `[0, T]`
and a square-integrable `X_T`. -/
theorem SolvesInt.of_linear
    (hrep : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
        =ᵐ[ν] C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)))
    (hfwd : ∀ i, LinearFSDEJInt D ℱ hℱW hℱN T (ξ₀ i) (driftProc P T C X Y Z U i) (X i)
      (diffusionProc P T C X Y Z U i) (jumpProc T γ i))
    (hbwd : ∀ k, LinearBSDEJInt D ℱ hℱW hℱN T (terminalVal P T C X k)
      (driverProc P T C X Y Z U k) (Y k) (Z k) (U k))
    (hX : ∀ i, Brownian.Ito.energy P T (fun ω s => X i s ω) ≠ ⊤)
    (hY : ∀ k, Brownian.Ito.energy P T (fun ω s => Y k s ω) ≠ ⊤)
    (hXT : ∀ i, MemLp (X i T) 2 P) :
    SolvesInt D ℱ hℱW hℱN T C ξ₀ X Y Z U γ where
  forcing := Forcing.zero
  jump_rep := hrep
  fwd i := by simpa only [one_mul, Pi.zero_apply, add_zero] using hfwd i
  bwd k := by simpa only [one_mul, Pi.zero_apply, add_zero] using hbwd k
  X_sq := hX
  Y_sq := hY
  XT_sq := hXT

namespace PaperWeakSolutionInt

variable (h : PaperWeakSolutionInt D ℱ hℱW hℱN T C ξ₀ X Y Z U γ) (hT : 0 ≤ T)
include h hT

/-- **The jump coefficient at the tuple**: for a solution of `PaperWeakSolutionInt`, `γ` also
represents `e ↦ h(s, Θ_s(ω), e, μ_s)` in `L²(ν)` for almost every `s ∈ [0, T]` and almost every
`ω`. -/
theorem jump_rep_tupleAt :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
        =ᵐ[ν] C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)) := by
  filter_upwards [h.jump_rep, h.toPaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq hT] with s hs heq
  filter_upwards [hs, heq] with ω hω hωeq
  rw [← hωeq, ← lawP2_congr heq]
  exact hω

/-- **A solution of `PaperWeakSolutionInt` solves `SolvesInt`.** For `T ≥ 0`, there are `X'`,
`Y'` equal to `X`, `Y` at every time of `[0, T]` — adapted with right-continuous paths, `0` before
`0` and frozen after `T` — such that `(X', Y', Z, U)` solves the system (1.1) in the sense of
`SolvesInt`, with the same `γ`. -/
theorem exists_solvesInt :
    ∃ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ),
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X i t)
      ∧ (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y k t)
      ∧ SolvesInt D ℱ hℱW hℱN T C ξ₀ X' Y' Z U γ := by
  obtain ⟨X', hXe, hXa, hXr⟩ := exists_adapted_rightCont_extension hT h.X_adapted h.X_rightCont
  obtain ⟨Y', hYe, hYa, hYr⟩ := exists_adapted_rightCont_extension hT h.Y_adapted h.Y_rightCont
  have hdrift := driftProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hdiff := diffusionProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hdriver := driverProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hterm := terminalVal_eq_of_eq (P := P) (C := C) fun i => hXe i T hTm
  refine ⟨X', Y', hXe, hYe, SolvesInt.of_linear ?_ (fun i => ?_) (fun k => ?_)
    (fun i => ?_) (fun k => ?_) (fun i => ?_)⟩
  · filter_upwards [h.jump_rep_tupleAt hT, ae_restrict_mem measurableSet_Icc] with s hs hsI
    rw [tupleAt_eq_of_eqOn hXe hYe hsI]
    exact hs
  · rw [hdrift, hdiff]
    obtain ⟨M, hMae, -, hid⟩ := h.fwd i
    exact
      { σ_meas := h.σ_meas i
        σ_prog := h.σ_prog i
        σ_vanish := fun ω s hs => diffusionProc_of_notMem hs i ω
        σ_sq := h.σ_sq i
        γ_meas := h.γ_meas i
        γ_prog := h.γ_prog i
        γ_vanish := fun ω s e hs => jumpProc_of_notMem hs i ω e
        γ_sq := h.γ_sq i
        b_meas := h.b_meas i
        b_prog := h.b_prog i
        b_vanish := fun ω s hs => driftProc_of_notMem hs i ω
        b_int := h.b_int i
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
        φ_vanish := fun ω s hs => driverProc_of_notMem hs k ω
        φ_int := h.f_int k
        Y_adapted := hYa k
        Y_rightCont := hYr k
        eqn := fun t ht => by
          filter_upwards [hid, hMae t ht, hMae T hTm] with ω h1 h2 h3
          rw [congrFun (hYe k t ht) ω, h1 t ht, h2, h3] }
  · rw [energy_eq_of_eqOn (hXe i)]
    exact h.X_sq i
  · rw [energy_eq_of_eqOn (hYe k)]
    exact h.Y_sq k
  · rw [hXe i T hTm]
    exact h.XT_sq i

end PaperWeakSolutionInt

end MVFBSDEJ.WellPosedness.System
