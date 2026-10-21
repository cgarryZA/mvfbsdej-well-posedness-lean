/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.PaperSolutionForcedOne
import Dissertation.WellPosedness.System.PaperSolutionForcedSolves
import Dissertation.WellPosedness.System.PaperWeakSolutionInt

/-!
# Solutions of the `λ`-forced system (4.1) in `ℍ²` with pathwise drift and driver integrals

Lemma 4.3 compares, under Assumptions 2.3–2.5 only, two solutions of the `λ`-forced system (4.1)
whose `X` and `Y` are càdlàg adapted with `𝔼 ∫_0^T (|X_t|² + |Y_t|²) dt < ∞`, whose `X_T` is square
integrable and whose `Z`, `U` lie in `H²_W`, `H²_N`. As for (1.1) in `PaperWeakSolutionInt`, without
Assumption 2.2 the forced drift `λ b(s, Θ_s, μ_s) + q^b_s` and the forced driver
`λ f(s, Θ_s, μ_s) + q^f_s` need not have finite energy on `[0, T]`: they enter (4.1) only through
Lebesgue integrals, which need almost every path to be integrable on `[0, T]`. The forced diffusion
and jump integrands enter through the `L²` stochastic integrals and keep finite energy, and neither
the initial datum nor the terminal value `λ g(X_T, Law X_T) + q^g_T` need be square integrable.

`PaperWeakSolutionForcedInt` is `PaperSolutionForced` with three changes: the `S²` bounds on `X`
and `Y` are replaced by finite energy on `[0, T]`, so that the tuple lies in `ℍ²`
(`PaperWeakTuple`); the finite energy of the forced drift and driver is replaced by the
integrability of almost every path on `[0, T]`; and `X_T` is square integrable. The forcing, the
forced integrands `λ ψ + q^ψ`, the representative `γ` of `h(s, Θ⁻_s, ·, μ⁻_s)` and the two
identities of (4.1) are those of `PaperSolutionForced`. At `λ = 1` and `q = 0` it is
`PaperWeakSolutionInt` (`paperWeakSolutionForcedInt_one_zero_iff`).

## Main definitions

* `PaperWeakSolutionForcedInt` — `(X, Y, Z, U)` solves the `λ`-forced system (4.1) in `ℍ²`
  with pathwise drift and driver integrals.

## Main statements

* `paperWeakSolutionForcedInt_one_zero_iff` — at `λ = 1` with zero forcing,
  `PaperWeakSolutionForcedInt` is `PaperWeakSolutionInt`.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`(X, Y, Z, U)` solves the `λ`-forced system (4.1) in `ℍ²` with pathwise drift and
driver integrals**, with coefficients `C`, initial datum `ξ₀` and forcing
`q = (q^b, q^σ, q^h, q^f, q^g)`, over the filtration `ℱ` carrying the driver `D`, and with `γ` a
representative of the jump coefficient: `X` and `Y` are adapted on `[0, T]` with
right-continuous paths on `[0, T)`, left limits on `(0, T]` almost surely and finite energy on
`[0, T]`; `Z` and `U` are predictable with finite energy and vanish off `[0, T]`; `q` is a
forcing; the forced drift and driver integrands `λ b(s, Θ_s, μ_s) + q^b_s`,
`λ f(s, Θ_s, μ_s) + q^f_s` are jointly and progressively measurable with almost surely
integrable paths on `[0, T]`, and the forced diffusion integrand `λ σ(s, Θ_s, μ_s) + q^σ_s` and
jump integrand `λ γ + q^h`, `γ` cut to `[0, T]`, meet the conditions for the `L²` stochastic
integrals of (4.1) to exist; `γ` represents `h(s, Θ⁻_s, ·, μ⁻_s)` in `L²(ν)` at almost every
time, almost surely; `X_T` is square integrable; and both identities of (4.1) hold at every
`t ∈ [0, T]` on one set of full measure, with càdlàg versions of the Brownian integrals. -/
structure PaperWeakSolutionForcedInt (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ) (T lam : ℝ) (C : Coeffs ν n m d)
    (ξ₀ : Fin n → Ω → ℝ)
    (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
    (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ)
    (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop
    extends PaperWeakTuple ℱ P ν T X Y Z U where
  /-- `q` is a square-integrable forcing. -/
  forcing : Forcing ℱ P ν T qb qσ qh qf qg
  /-- The forced drift integrand is jointly measurable. -/
  b_meas : ∀ i, Measurable (Function.uncurry fun ω s =>
    lam * driftProc P T C X Y Z U i ω s + qb i ω s)
  /-- The forced drift integrand is progressively measurable. -/
  b_prog : ∀ i, Probability.ProgressivelyMeasurable ℱ fun ω s =>
    lam * driftProc P T C X Y Z U i ω s + qb i ω s
  /-- Almost every path of the forced drift integrand is integrable on the horizon. -/
  b_int : ∀ i, ∀ᵐ ω ∂P, IntegrableOn (fun s =>
    lam * driftProc P T C X Y Z U i ω s + qb i ω s) (Set.Icc (0 : ℝ) T)
  /-- The forced diffusion integrand is jointly measurable. -/
  σ_meas : ∀ i j, Measurable (Function.uncurry fun ω s =>
    lam * diffusionProc P T C X Y Z U i s ω j + qσ i s ω j)
  /-- The forced diffusion integrand is progressively measurable. -/
  σ_prog : ∀ i j, Probability.ProgressivelyMeasurable ℱ fun ω s =>
    lam * diffusionProc P T C X Y Z U i s ω j + qσ i s ω j
  /-- The forced diffusion integrand has finite energy on the horizon. -/
  σ_sq : ∀ i j, Brownian.Ito.energy P T (fun ω s =>
    lam * diffusionProc P T C X Y Z U i s ω j + qσ i s ω j) ≠ ⊤
  /-- The forced jump integrand is jointly measurable in the sample point, the time and the
  mark. -/
  γ_meas : ∀ i, Measurable fun p : Ω × ℝ × E =>
    lam * jumpProc T γ i p.2.1 p.1 p.2.2 + qh i p.2.1 p.1 p.2.2
  /-- The forced jump integrand is marked progressively measurable. -/
  γ_prog : ∀ i, Probability.MarkedProgressivelyMeasurable ℱ fun ω s e =>
    lam * jumpProc T γ i s ω e + qh i s ω e
  /-- The forced jump integrand has finite marked energy on the horizon. -/
  γ_sq : ∀ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
    lam * jumpProc T γ i s ω e + qh i s ω e) ≠ ⊤
  /-- The forced driver integrand is jointly measurable. -/
  f_meas : ∀ k, Measurable (Function.uncurry fun ω s =>
    lam * driverProc P T C X Y Z U k ω s + qf k ω s)
  /-- The forced driver integrand is progressively measurable. -/
  f_prog : ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s =>
    lam * driverProc P T C X Y Z U k ω s + qf k ω s
  /-- Almost every path of the forced driver integrand is integrable on the horizon. -/
  f_int : ∀ k, ∀ᵐ ω ∂P, IntegrableOn (fun s =>
    lam * driverProc P T C X Y Z U k ω s + qf k ω s) (Set.Icc (0 : ℝ) T)
  /-- `γ` represents the jump coefficient at the predictable tuple in `L²(ν)`, at almost every
  time of the horizon, almost surely. -/
  jump_rep : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
    (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
      =ᵐ[ν] C.h s (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
        (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s))
  /-- Each coordinate of `X_T` is square integrable. -/
  XT_sq : ∀ i, MemLp (X i T) 2 P
  /-- The forward identity at every time of the horizon on one set of full measure, with a
  càdlàg version `M` of the Brownian integral. -/
  fwd : ∀ i, ∃ M : ℝ → Ω → ℝ,
    (∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P]
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW
        (fun s ω j => lam * diffusionProc P T C X Y Z U i s ω j + qσ i s ω j) (σ_meas i)
        (σ_prog i)
        (sq_int_global_of_vanishing (forcedDiffusion_of_notMem forcing.qσ_vanish lam i)
          (σ_sq i)) t)
    ∧ (∀ᵐ ω ∂P, (∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)))
      ∧ ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L))
    ∧ ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      X i t ω = ξ₀ i ω
        + (∫ s in Set.Icc (0 : ℝ) t, lam * driftProc P T C X Y Z U i ω s + qb i ω s) + M t ω
        + Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
            (fun ω' s e => lam * jumpProc T γ i s ω' e + qh i s ω' e) (γ_meas i) (γ_prog i)
            (marked_sq_int_global_of_vanishing (forcedJump_of_notMem forcing.qh_vanish lam i)
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
      Y k t ω = lam * terminalVal P T C X k ω + qg k ω
          + (∫ s in Set.Icc t T, lam * driverProc P T C X Y Z U k ω s + qf k ω s)
        - (M T ω - M t ω)
        - (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U k s ω' e)
              ((U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl)
              (U_pred k).markedProgressivelyMeasurable
              (marked_sq_int_global_of_vanishing (U_vanish k) (U_sq k)) T ω
            - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U k s ω' e)
              ((U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl)
              (U_pred k).markedProgressivelyMeasurable
              (marked_sq_int_global_of_vanishing (U_vanish k) (U_sq k)) t ω)

variable {T lam : ℝ} {C : Coeffs ν n m d} {ξ₀ : Fin n → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}

/-- **The forced system at `λ = 1` with zero forcing is (1.1), in `ℍ²` with pathwise drift
and driver integrals**: `(X, Y, Z, U)` solves the `λ`-forced system (4.1) at `λ = 1` with
forcing `q = 0` in the sense of `PaperWeakSolutionForcedInt` if and only if it solves the system
(1.1) in the sense of `PaperWeakSolutionInt`, with the same `γ`. -/
theorem paperWeakSolutionForcedInt_one_zero_iff :
    PaperWeakSolutionForcedInt D ℱ hℱW hℱN T 1 C ξ₀ 0 0 0 0 0 X Y Z U γ
      ↔ PaperWeakSolutionInt D ℱ hℱW hℱN T C ξ₀ X Y Z U γ := by
  have eσ : ∀ i, (fun s ω j => 1 * diffusionProc P T C X Y Z U i s ω j
      + (0 : Fin n → ℝ → Ω → Fin d → ℝ) i s ω j) = diffusionProc P T C X Y Z U i := fun i => by
    funext s ω j
    simp
  have eγ : ∀ i, (fun ω' s e => 1 * jumpProc T γ i s ω' e + (0 : Fin n → ℝ → Ω → E → ℝ) i s ω' e)
      = fun ω' s e => jumpProc T γ i s ω' e := fun i => by
    funext ω' s e
    simp
  constructor
  · intro h
    exact
      { toPaperWeakTuple := h.toPaperWeakTuple
        b_meas := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.b_meas i
        b_prog := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.b_prog i
        b_int := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.b_int i
        σ_meas := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.σ_meas i
        σ_prog := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.σ_prog i
        σ_sq := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.σ_sq i
        γ_meas := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.γ_meas i
        γ_prog := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.γ_prog i
        γ_sq := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.γ_sq i
        f_meas := fun k => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.f_meas k
        f_prog := fun k => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.f_prog k
        f_int := fun k => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.f_int k
        jump_rep := h.jump_rep
        XT_sq := h.XT_sq
        fwd := fun i => by
          obtain ⟨M, hMae, hMc, hid⟩ := h.fwd i
          refine ⟨M, fun t ht => (hMae t ht).trans (EventuallyEq.of_eq (congrFun
            (multidimStochasticIntegral_eq_of_integrand_eq D.W ℱ hℱW (eσ i) _ _ _ _ _ _) t)),
            hMc, ?_⟩
          filter_upwards [hid] with ω hω t ht
          rw [hω t ht]
          congr 1
          · simp only [one_mul, Pi.zero_apply, add_zero]
          · exact congrFun (congrFun
              (compensatedIntegral_eq_of_integrand_eq D.N ℱ hℱN (eγ i) _ _ _ _ _ _) t) ω
        bwd := fun k => by
          obtain ⟨M, hMae, hMc, hid⟩ := h.bwd k
          refine ⟨M, hMae, hMc, ?_⟩
          filter_upwards [hid] with ω hω t ht
          rw [hω t ht]
          simp only [one_mul, Pi.zero_apply, add_zero] }
  · intro h
    exact
      { toPaperWeakTuple := h.toPaperWeakTuple
        forcing := Forcing.zero
        b_meas := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.b_meas i
        b_prog := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.b_prog i
        b_int := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.b_int i
        σ_meas := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.σ_meas i
        σ_prog := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.σ_prog i
        σ_sq := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.σ_sq i
        γ_meas := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.γ_meas i
        γ_prog := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.γ_prog i
        γ_sq := fun i => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.γ_sq i
        f_meas := fun k => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.f_meas k
        f_prog := fun k => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.f_prog k
        f_int := fun k => by simpa only [one_mul, Pi.zero_apply, add_zero] using h.f_int k
        jump_rep := h.jump_rep
        XT_sq := h.XT_sq
        fwd := fun i => by
          obtain ⟨M, hMae, hMc, hid⟩ := h.fwd i
          refine ⟨M, fun t ht => (hMae t ht).trans (EventuallyEq.of_eq (congrFun
            (multidimStochasticIntegral_eq_of_integrand_eq D.W ℱ hℱW (eσ i).symm _ _ _ _ _ _)
              t)), hMc, ?_⟩
          filter_upwards [hid] with ω hω t ht
          rw [hω t ht]
          congr 1
          · simp only [one_mul, Pi.zero_apply, add_zero]
          · exact congrFun (congrFun
              (compensatedIntegral_eq_of_integrand_eq D.N ℱ hℱN (eγ i).symm _ _ _ _ _ _) t) ω
        bwd := fun k => by
          obtain ⟨M, hMae, hMc, hid⟩ := h.bwd k
          refine ⟨M, hMae, hMc, ?_⟩
          filter_upwards [hid] with ω hω t ht
          rw [hω t ht]
          simp only [one_mul, Pi.zero_apply, add_zero] }

end Dissertation.WellPosedness.System
