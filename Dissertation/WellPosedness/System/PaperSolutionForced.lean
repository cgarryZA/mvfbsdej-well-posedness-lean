/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.PaperSolution

/-!
# The solution notion of the paper for the `λ`-forced system (4.1)

For `λ ∈ [0, 1]`, an initial datum `ξ₀` and a forcing `q = (q^b, q^σ, q^h, q^f, q^g_T)`, a
solution of the `λ`-forced system (4.1) is a tuple `Θ = (X, Y, Z, U) ∈ ℍ²` such that, with
`μ_s = Law(Θ_s)` and `μ⁻_s = Law(Θ⁻_s)`,

`X_t = ξ₀ + ∫_0^t (λ b(s, Θ_s, μ_s) + q^b_s) ds + ∫_0^t (λ σ(s, Θ_s, μ_s) + q^σ_s) dW_s
  + ∫_0^t ∫_E (λ h(s, Θ⁻_s, e, μ⁻_s) + q^h_s(e)) Ñ(ds, de)`,

`Y_t = λ g(X_T, Law X_T) + q^g_T + ∫_t^T (λ f(s, Θ_s, μ_s) + q^f_s) ds − ∫_t^T Z_s dW_s
  − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`,

and (4.1) is *well posed at `λ`*, `WP(λ)`, if it has a unique solution in `ℍ²` for every forcing.
At `λ = 1`, `q = 0` it is the system (1.1).

`PaperSolutionForced` states this definition in the encoding of `PaperSolution`, whose fields it
shares, with the following changes.

* **The forcing.** `q` is a forcing in the sense of `Forcing` (field `forcing`), as in
  `SolvesForced`: its components are jointly and progressively measurable (marked progressively
  measurable, for `q^h`, which the paper takes predictable), vanish off `[0, T]` and are square
  integrable, and `q^g_T` is `ℱ_T`-measurable.
* **The integrands.** The conditions under which the integrals of (4.1) exist are asked of the
  forced integrands `λ b(s, Θ_s, μ_s) + q^b_s`, `λ σ(s, Θ_s, μ_s) + q^σ_s`,
  `λ f(s, Θ_s, μ_s) + q^f_s` and `λ γ_s + q^h_s`, `γ` cut to `[0, T]`, as the linear equations
  of `SolvesForced` ask them (fields `b_meas`, …, `f_sq`). The paper writes the coefficient and
  the forcing integrals separately; for square-integrable integrands the two forms agree by
  linearity of the integrals. At `λ = 0` these conditions do not involve the coefficient
  processes.
* **The identities.** The terminal value is `λ g(X_T, Law X_T) + q^g_T`, and the Brownian
  integrals are those of the forced integrands, with càdlàg versions as in `PaperSolution`.

The jump coefficient is evaluated at the predictable tuple `(Θ⁻_s, μ⁻_s)` through the
representative `γ` (`jump_rep`), as in `PaperSolution`. The relation to `SolvesForced` is in
`Dissertation.WellPosedness.System.PaperSolutionForcedSolves`, and the case `λ = 1`, `q = 0` in
`Dissertation.WellPosedness.System.PaperSolutionForcedOne`.

## Main definitions

* `PaperSolutionForced` — `(X, Y, Z, U)` solves the `λ`-forced system (4.1) in `ℍ²` with forced
  integrands of finite energy.

## Main statements

* `forcedDiffusion_of_notMem`, `forcedJump_of_notMem` — the forced integrands vanish off
  `[0, T]`.
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

/-! ### The forced integrands off the horizon -/

section Vanish

variable {T : ℝ} {C : Coeffs ν n m d} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}
  {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}

/-- Off the horizon the forced diffusion integrand `λ σ(s, Θ_s, μ_s) + q^σ_s` vanishes, for `q^σ`
vanishing off `[0, T]`. -/
theorem forcedDiffusion_of_notMem (hq : ∀ i ω s, s ∉ Set.Icc (0 : ℝ) T → qσ i s ω = 0)
    (lam : ℝ) (i : Fin n) (ω : Ω) (s : ℝ) (hs : s ∉ Set.Icc (0 : ℝ) T) :
    (fun j => lam * diffusionProc P T C X Y Z U i s ω j + qσ i s ω j) = 0 := by
  funext j
  rw [diffusionProc_of_notMem hs, hq i ω s hs]
  simp

omit [MeasurableSpace Ω] [MeasurableSpace E] [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] in
/-- Off the horizon the forced jump integrand `λ γ_s(e) + q^h_s(e)`, `γ` cut to `[0, T]`,
vanishes, for `q^h` vanishing off `[0, T]`. -/
theorem forcedJump_of_notMem (hq : ∀ i ω s e, s ∉ Set.Icc (0 : ℝ) T → qh i s ω e = 0)
    (lam : ℝ) (i : Fin n) (ω : Ω) (s : ℝ) (e : E) (hs : s ∉ Set.Icc (0 : ℝ) T) :
    lam * jumpProc T γ i s ω e + qh i s ω e = 0 := by
  rw [jumpProc_of_notMem hs, hq i ω s e hs, mul_zero, add_zero]

end Vanish

/-! ### The solution predicate -/

/-- **`(X, Y, Z, U)` solves the `λ`-forced system (4.1) in `ℍ²` with forced integrands of finite
energy**, with
coefficients `C`, initial datum `ξ₀` and forcing `q = (q^b, q^σ, q^h, q^f, q^g)`, over the
filtration `ℱ` carrying the driver `D`, and with `γ` a representative of the jump coefficient:
`q` is a forcing; `X` and `Y` are adapted on `[0, T]` with right-continuous paths on `[0, T)`,
left limits on `(0, T]` almost surely and finite `𝔼 sup_{t ≤ T} |·|²`; `Z` and `U` are
predictable with finite energy and vanish off `[0, T]`; the forced integrands
`λ ψ(s, Θ_s, μ_s) + q^ψ_s`, `ψ ∈ {b, σ, f}`, and `λ γ + q^h`, `γ` cut to `[0, T]`, meet the
conditions for the integrals of (4.1) to exist; `γ` represents `h(s, Θ⁻_s, ·, μ⁻_s)` in `L²(ν)`
at almost every time, almost surely; and both identities of (4.1) hold at every `t ∈ [0, T]` on
one set of full measure, with càdlàg versions of the Brownian integrals. -/
structure PaperSolutionForced (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ) (T lam : ℝ) (C : Coeffs ν n m d)
    (ξ₀ : Fin n → Ω → ℝ)
    (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
    (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ)
    (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop where
  /-- `q` is a square-integrable forcing. -/
  forcing : Forcing ℱ P ν T qb qσ qh qf qg
  /-- Each coordinate of `X` is adapted on the horizon. -/
  X_adapted : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (X i t)
  /-- Every path of each coordinate of `X` is right-continuous on `[0, T)`. -/
  X_rightCont : ∀ i ω, ∀ t ∈ Set.Ico (0 : ℝ) T,
    Tendsto (fun s => X i s ω) (𝓝[>] t) (𝓝 (X i t ω))
  /-- Almost every path of each coordinate of `X` has left limits on `(0, T]`. -/
  X_leftLim : ∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioc (0 : ℝ) T,
    ∃ L : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 L)
  /-- `𝔼 sup_{t ≤ T} |X_t|² < ∞`. -/
  X_sup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P < ⊤
  /-- Each coordinate of `Y` is adapted on the horizon. -/
  Y_adapted : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (Y k t)
  /-- Every path of each coordinate of `Y` is right-continuous on `[0, T)`. -/
  Y_rightCont : ∀ k ω, ∀ t ∈ Set.Ico (0 : ℝ) T,
    Tendsto (fun s => Y k s ω) (𝓝[>] t) (𝓝 (Y k t ω))
  /-- Almost every path of each coordinate of `Y` has left limits on `(0, T]`. -/
  Y_leftLim : ∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioc (0 : ℝ) T,
    ∃ L : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 L)
  /-- `𝔼 sup_{t ≤ T} |Y_t|² < ∞`. -/
  Y_sup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y k t ω)) ∂P < ⊤
  /-- Each coordinate of `Z` is predictable. -/
  Z_pred : ∀ k j, Probability.Predictable ℱ fun ω s => Z k s ω j
  /-- `Z` vanishes off the horizon. -/
  Z_vanish : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) T → Z k s ω = 0
  /-- Each coordinate of `Z` has finite energy on the horizon. -/
  Z_sq : ∀ k j, Brownian.Ito.energy P T (fun ω s => Z k s ω j) ≠ ⊤
  /-- Each coordinate of `U` is marked predictable. -/
  U_pred : ∀ k, Probability.MarkedPredictable ℱ ν fun ω s e => U k s ω e
  /-- `U` vanishes off the horizon. -/
  U_vanish : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → U k s ω e = 0
  /-- Each coordinate of `U` has finite marked energy on the horizon. -/
  U_sq : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) ≠ ⊤
  /-- The forced drift integrand is jointly measurable. -/
  b_meas : ∀ i, Measurable (Function.uncurry fun ω s =>
    lam * driftProc P T C X Y Z U i ω s + qb i ω s)
  /-- The forced drift integrand is progressively measurable. -/
  b_prog : ∀ i, Probability.ProgressivelyMeasurable ℱ fun ω s =>
    lam * driftProc P T C X Y Z U i ω s + qb i ω s
  /-- The forced drift integrand has finite energy on the horizon. -/
  b_sq : ∀ i, Brownian.Ito.energy P T (fun ω s =>
    lam * driftProc P T C X Y Z U i ω s + qb i ω s) ≠ ⊤
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
  /-- The forced driver integrand has finite energy on the horizon. -/
  f_sq : ∀ k, Brownian.Ito.energy P T (fun ω s =>
    lam * driverProc P T C X Y Z U k ω s + qf k ω s) ≠ ⊤
  /-- `γ` represents the jump coefficient at the predictable tuple in `L²(ν)`, at almost every
  time of the horizon, almost surely. -/
  jump_rep : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
    (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
      =ᵐ[ν] C.h s (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
        (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s))
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

end Dissertation.WellPosedness.System
