/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.PaperWeakSolutionForcedInt
import Dissertation.WellPosedness.System.SolvesInt

/-!
# Solutions of `PaperWeakSolutionForcedInt` as solutions of `SolvesForcedInt`

`PaperWeakSolutionForcedInt` states the class of Lemma 4.3 of the well-posedness paper in the
encoding of `PaperSolutionForced`, and `SolvesForcedInt` is the form of the `λ`-forced system
(4.1) in `ℍ²` on which the proof of Lemma 4.3 runs. They differ as `PaperWeakSolutionInt`
and `SolvesInt` do (`Dissertation.WellPosedness.System.PaperWeakSolutionIntSolves`), with the
forced integrands `λ ψ + q^ψ` in place of the coefficient processes `ψ` and the terminal value
`λ g(X_T, Law X_T) + q^g_T` in place of `g(X_T, Law X_T)`:

* `SolvesForcedInt` asks every path of `X` and `Y` to be right-continuous at every time, and each
  process to be adapted at every time; the extension of `X` and `Y` by `0` before `0` and by
  `X_T`, `Y_T` after `T` has these properties (`exists_adapted_rightCont_extension`), with the
  same forced integrands, finite energy on `[0, T]` and value at `T`;
* `SolvesForcedInt` asks the identities almost surely at each time with the canonical Brownian
  integral, which a càdlàg version agrees with almost surely at each time;
* `SolvesForcedInt` evaluates the jump coefficient at `(Θ_s, μ_s)`, and `Θ⁻_s = Θ_s` almost
  surely for almost every `s` along a tuple of `ℍ²`
  (`PaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq`);
* `SolvesForcedInt` takes `Z` and `U` progressively measurable, and a predictable integrand
  vanishing off `[0, T]` is progressively measurable.

Both notions ask the forced drift and driver only to have almost surely integrable paths on
`[0, T]`, neither asks `ξ₀` or the terminal value to be square integrable, and both ask `X_T` to
be. So no condition on the coefficients enters the passage
(`PaperWeakSolutionForcedInt.exists_solvesForcedInt`).

## Main statements

* `PaperWeakSolutionForcedInt.jump_rep_tupleAt` — `γ` represents `h(s, Θ_s, ·, μ_s)`.
* `PaperWeakSolutionForcedInt.exists_solvesForcedInt` — a solution of
  `PaperWeakSolutionForcedInt`, extended off `[0, T]`, is a solution of `SolvesForcedInt`.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  LevyStochCalc.BSDEJ.Solves LevyStochCalc

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

namespace PaperWeakSolutionForcedInt

variable (h : PaperWeakSolutionForcedInt D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ)
  (hT : 0 ≤ T)
include h hT

/-- **The jump coefficient at the tuple**: for a solution of `PaperWeakSolutionForcedInt`, `γ`
also represents `e ↦ h(s, Θ_s(ω), e, μ_s)` in `L²(ν)` for almost every `s ∈ [0, T]` and almost
every `ω`. -/
theorem jump_rep_tupleAt :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
        =ᵐ[ν] C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)) := by
  filter_upwards [h.jump_rep, h.toPaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq hT] with s hs heq
  filter_upwards [hs, heq] with ω hω hωeq
  rw [← hωeq, ← lawP2_congr heq]
  exact hω

/-- **A solution of `PaperWeakSolutionForcedInt` solves `SolvesForcedInt`.** For `T ≥ 0`, there
are `X'`, `Y'` equal to `X`, `Y` at every time of `[0, T]` — adapted with right-continuous paths,
`0` before `0` and frozen after `T` — such that `(X', Y', Z, U)` solves the `λ`-forced system
(4.1) in the sense of `SolvesForcedInt`, with the same forcing and the same `γ`. -/
theorem exists_solvesForcedInt :
    ∃ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ),
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X i t)
      ∧ (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y k t)
      ∧ SolvesForcedInt D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X' Y' Z U γ := by
  obtain ⟨X', hXe, hXa, hXr⟩ := exists_adapted_rightCont_extension hT h.X_adapted h.X_rightCont
  obtain ⟨Y', hYe, hYa, hYr⟩ := exists_adapted_rightCont_extension hT h.Y_adapted h.Y_rightCont
  have hdrift := driftProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hdiff := diffusionProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hdriver := driverProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hterm := terminalVal_eq_of_eq (P := P) (C := C) fun i => hXe i T hTm
  refine ⟨X', Y', hXe, hYe,
    ⟨h.forcing, ?_, fun i => ?_, fun k => ?_, fun i => ?_, fun k => ?_, fun i => ?_⟩⟩
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
        φ_vanish := fun ω s hs => by
          rw [driverProc_of_notMem hs, h.forcing.qf_vanish k ω s hs, mul_zero, add_zero]
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

end PaperWeakSolutionForcedInt

end Dissertation.WellPosedness.System
