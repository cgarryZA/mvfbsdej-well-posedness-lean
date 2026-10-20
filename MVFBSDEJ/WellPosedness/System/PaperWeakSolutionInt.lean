/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.PaperWeakS2

/-!
# Solutions of (1.1) in `ℍ²_weak` with pathwise drift and driver integrals

Theorem 3.3 of the well-posedness paper concerns two tuples `Θ¹, Θ² ∈ ℍ²_weak` satisfying (1.1),
under Assumptions 2.3–2.5 only. Without Assumption 2.2 the drift `b(s, Θ_s, μ_s)` and the driver
`f(s, Θ_s, μ_s)` along such a tuple need not have finite energy on `[0, T]`: they enter (1.1)
only through the Lebesgue integrals `∫_0^t b ds` and `∫_t^T f ds`, which need almost every path
to be integrable on `[0, T]`. The diffusion `σ(s, Θ_s, μ_s)` and the jump coefficient
`h(s, Θ⁻_s, ·, μ⁻_s)` enter through the `L²` stochastic integrals, so they keep finite energy on
`[0, T]`. The terminal condition `g(X_T, Law X_T)` presupposes `Law X_T ∈ P₂(ℝⁿ)`, that is,
`X_T` square integrable. Without Assumption 2.2 the initial datum `ξ₀` need not be square
integrable.

`PaperAdmissibleInt` is `PaperAdmissible` with the finite energy of the drift and driver
processes on `[0, T]` replaced by the integrability of almost every path on `[0, T]`.
`PaperWeakSolutionInt` is `PaperWeakSolution` with `PaperAdmissibleInt` in place of
`PaperAdmissible`, together with the square integrability of `X_T`: the tuple lies in `ℍ²_weak`,
the integrals of (1.1) along it exist, `γ` represents `h(s, Θ⁻_s, ·, μ⁻_s)`, and both identities
of (1.1) hold at every `t ∈ [0, T]` on one set of full measure.

## Main definitions

* `PaperAdmissibleInt` — the integrals of (1.1) along `(X, Y, Z, U)` exist, the drift and the
  driver along almost every path.
* `PaperWeakSolutionInt` — `(X, Y, Z, U)` is a solution of (1.1) in `ℍ²_weak` with pathwise
  drift and driver integrals.
* `PaperWeakSolutionIntAug` — the same over the augmented joint filtration `augJoint D`.

## Main statements

* `PaperAdmissible.toInt` — drift and driver processes of finite energy have almost surely
  integrable paths.
* `PaperWeakSolution.toIntOfMemLp` — a solution in `ℍ²_weak` with `X_T` square integrable is a
  solution of `PaperWeakSolutionInt`.
* `PaperSolution.toWeakInt` — a solution in `ℍ²` is a solution of `PaperWeakSolutionInt`.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-- **The integrals of (1.1) along `Θ = (X, Y, Z, U)` exist, with pathwise drift and driver
integrals**, with `γ` a representative of the jump coefficient at the predictable tuple: the
drift and driver processes of `C` along `Θ` are jointly and progressively measurable and almost
every path of each is integrable on `[0, T]`, the diffusion process along `Θ` is jointly and
progressively measurable with finite energy on `[0, T]`, the jump integrand `γ` cut to `[0, T]`
is jointly and marked progressively measurable with finite marked energy on `[0, T]`, and `γ`
represents `e ↦ h(s, Θ⁻_s(ω), e, μ⁻_s)` in `L²(ν)` at almost every time of `[0, T]`, almost
surely. -/
structure PaperAdmissibleInt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℝ) (C : Coeffs ν n m d) (X : Fin n → ℝ → Ω → ℝ)
    (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop where
  /-- The drift process is jointly measurable. -/
  b_meas : ∀ i, Measurable (Function.uncurry (driftProc P T C X Y Z U i))
  /-- The drift process is progressively measurable. -/
  b_prog : ∀ i, Probability.ProgressivelyMeasurable ℱ (driftProc P T C X Y Z U i)
  /-- Almost every path of the drift process is integrable on the horizon. -/
  b_int : ∀ i, ∀ᵐ ω ∂P, IntegrableOn (driftProc P T C X Y Z U i ω) (Set.Icc (0 : ℝ) T)
  /-- The diffusion process is jointly measurable. -/
  σ_meas : ∀ i j,
    Measurable (Function.uncurry fun ω s => diffusionProc P T C X Y Z U i s ω j)
  /-- The diffusion process is progressively measurable. -/
  σ_prog : ∀ i j,
    Probability.ProgressivelyMeasurable ℱ fun ω s => diffusionProc P T C X Y Z U i s ω j
  /-- The diffusion process has finite energy on the horizon. -/
  σ_sq : ∀ i j,
    Brownian.Ito.energy P T (fun ω s => diffusionProc P T C X Y Z U i s ω j) ≠ ⊤
  /-- The jump integrand is jointly measurable in the sample point, the time and the mark. -/
  γ_meas : ∀ i, Measurable fun p : Ω × ℝ × E => jumpProc T γ i p.2.1 p.1 p.2.2
  /-- The jump integrand is marked progressively measurable. -/
  γ_prog : ∀ i,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => jumpProc T γ i s ω e
  /-- The jump integrand has finite marked energy on the horizon. -/
  γ_sq : ∀ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => jumpProc T γ i s ω e) ≠ ⊤
  /-- The driver process is jointly measurable. -/
  f_meas : ∀ k, Measurable (Function.uncurry (driverProc P T C X Y Z U k))
  /-- The driver process is progressively measurable. -/
  f_prog : ∀ k, Probability.ProgressivelyMeasurable ℱ (driverProc P T C X Y Z U k)
  /-- Almost every path of the driver process is integrable on the horizon. -/
  f_int : ∀ k, ∀ᵐ ω ∂P, IntegrableOn (driverProc P T C X Y Z U k ω) (Set.Icc (0 : ℝ) T)
  /-- `γ` represents the jump coefficient at the predictable tuple in `L²(ν)`, at almost every
  time of the horizon, almost surely. -/
  jump_rep : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
    (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
      =ᵐ[ν] C.h s (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
        (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s))

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`(X, Y, Z, U)` is a solution of (1.1) in `ℍ²_weak` with pathwise drift and driver
integrals**, with coefficients `C` and initial datum `ξ₀`, over the filtration `ℱ` carrying the
driver `D`, and with `γ` a representative of the jump coefficient: `X` and `Y` are adapted on
`[0, T]` with right-continuous paths on `[0, T)`, left limits on `(0, T]` almost surely and finite
energy on `[0, T]`; `Z` and `U` are predictable with finite energy and vanish off `[0, T]`; the
drift and driver processes along `Θ` are jointly and progressively measurable with almost surely
integrable paths on `[0, T]`, and the diffusion process along `Θ` and the jump integrand `γ` meet
the conditions for the `L²` stochastic integrals of (1.1) to exist; `γ` represents
`h(s, Θ⁻_s, ·, μ⁻_s)` in `L²(ν)` at almost every time, almost surely; `X_T` is square
integrable; and both identities of (1.1) hold at every `t ∈ [0, T]` on one set of full measure,
with càdlàg versions of the Brownian integrals. -/
structure PaperWeakSolutionInt (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ) (T : ℝ) (C : Coeffs ν n m d)
    (ξ₀ : Fin n → Ω → ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop
    extends PaperWeakTuple ℱ P ν T X Y Z U, PaperAdmissibleInt ℱ P T C X Y Z U γ where
  /-- Each coordinate of `X_T` is square integrable. -/
  XT_sq : ∀ i, MemLp (X i T) 2 P
  /-- The forward identity at every time of the horizon on one set of full measure, with a
  càdlàg version `M` of the Brownian integral. -/
  fwd : ∀ i, ∃ M : ℝ → Ω → ℝ,
    (∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P]
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW
        (diffusionProc P T C X Y Z U i) (σ_meas i) (σ_prog i)
        (sq_int_global_of_vanishing (fun ω s hs => diffusionProc_of_notMem hs i ω) (σ_sq i)) t)
    ∧ (∀ᵐ ω ∂P, (∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)))
      ∧ ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L))
    ∧ ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      X i t ω = ξ₀ i ω + (∫ s in Set.Icc (0 : ℝ) t, driftProc P T C X Y Z U i ω s) + M t ω
        + Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
            (fun ω' s e => jumpProc T γ i s ω' e) (γ_meas i) (γ_prog i)
            (marked_sq_int_global_of_vanishing (fun ω s e hs => jumpProc_of_notMem hs i ω e)
              (γ_sq i)) t ω
  /-- The backward identity at every time of the horizon on one set of full measure, with a
  càdlàg version `M` of the Brownian integral. -/
  bwd : ∀ k, ∃ M : ℝ → Ω → ℝ,
    (∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P]
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW (Z k)
        (fun j => Brownian.Ito.measurable_uncurry_of_predictable (Z_pred k j))
        (progressivelyMeasurable_of_predictable_of_vanish (Z_pred k) (Z_vanish k))
        (sq_int_global_of_vanishing (Z_vanish k) (Z_sq k)) t)
    ∧ (∀ᵐ ω ∂P, (∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)))
      ∧ ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L))
    ∧ ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Y k t ω = terminalVal P T C X k ω + (∫ s in Set.Icc t T, driverProc P T C X Y Z U k ω s)
        - (M T ω - M t ω)
        - (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U k s ω' e)
              ((U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl)
              (U_pred k).markedProgressivelyMeasurable
              (marked_sq_int_global_of_vanishing (U_vanish k) (U_sq k)) T ω
            - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U k s ω' e)
              ((U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl)
              (U_pred k).markedProgressivelyMeasurable
              (marked_sq_int_global_of_vanishing (U_vanish k) (U_sq k)) t ω)

/-- `(X, Y, Z, U)` is a solution of (1.1) in `ℍ²_weak` with pathwise drift and driver integrals
over the augmented joint filtration `augJoint D` of the driver. -/
abbrev PaperWeakSolutionIntAug (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (T : ℝ)
    (C : Coeffs ν n m d) (ξ₀ : Fin n → Ω → ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop :=
  PaperWeakSolutionInt D (augJoint D) D.isBrownianFiltration_aug D.isPoissonFiltration_aug T C
    ξ₀ X Y Z U γ

variable {T : ℝ} {C : Coeffs ν n m d} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {ξ₀ : Fin n → Ω → ℝ}

/-- **Drift and driver processes of finite energy have almost surely integrable paths**: if the
integrals of (1.1) along `Θ` exist in the sense of `PaperAdmissible`, they exist in the sense of
`PaperAdmissibleInt`, with the same `γ`. -/
theorem PaperAdmissible.toInt (h : PaperAdmissible ℱ P T C X Y Z U γ) :
    PaperAdmissibleInt ℱ P T C X Y Z U γ where
  b_meas := h.b_meas
  b_prog := h.b_prog
  b_int i := ae_mem_integrablePaths (h.b_meas i) (h.b_sq i)
  σ_meas := h.σ_meas
  σ_prog := h.σ_prog
  σ_sq := h.σ_sq
  γ_meas := h.γ_meas
  γ_prog := h.γ_prog
  γ_sq := h.γ_sq
  f_meas := h.f_meas
  f_prog := h.f_prog
  f_int k := ae_mem_integrablePaths (h.f_meas k) (h.f_sq k)
  jump_rep := h.jump_rep

/-- **A solution in `ℍ²_weak` with `X_T` square integrable is a solution of
`PaperWeakSolutionInt`**, with the same `γ`. -/
theorem PaperWeakSolution.toIntOfMemLp (h : PaperWeakSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ)
    (hXT : ∀ i, MemLp (X i T) 2 P) : PaperWeakSolutionInt D ℱ hℱW hℱN T C ξ₀ X Y Z U γ where
  toPaperWeakTuple := h.toPaperWeakTuple
  toPaperAdmissibleInt := h.toPaperAdmissible.toInt
  XT_sq := hXT
  fwd := h.fwd
  bwd := h.bwd

/-- **A solution in `ℍ²` is a solution of `PaperWeakSolutionInt`**, for `T ≥ 0`, with the same
`γ`: the `S²` bound on `X` makes `X_T` square integrable. -/
theorem PaperSolution.toWeakInt (h : PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ) (hT : 0 ≤ T) :
    PaperWeakSolutionInt D ℱ hℱW hℱN T C ξ₀ X Y Z U γ :=
  h.toWeak.toIntOfMemLp fun i => memLp_of_lintegral_biSup_esq_lt_top h.X_sup ⟨hT, le_rfl⟩ i
    ((h.X_adapted i T ⟨hT, le_rfl⟩).mono (ℱ.le T) le_rfl).aestronglyMeasurable

end MVFBSDEJ.WellPosedness.System
