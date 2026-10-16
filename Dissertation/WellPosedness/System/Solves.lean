/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.ForwardEq
import Dissertation.WellPosedness.System.Coefficients
import Dissertation.WellPosedness.System.ULiftMeasurable

/-!
# The solution predicate of the `λ`-forced system (4.1)

For `λ ∈ [0, 1]`, an initial datum `ξ₀` and a forcing `q = (q^b, q^σ, q^h, q^f, q^g_T)`, the
`λ`-scaled forced system (4.1) of the well-posedness paper reads, with `Θ_s = (X_s, Y_s, Z_s, U_s)`
and `μ_s = Law(Θ_s)`,

`X_t = ξ₀ + ∫_0^t (λ b(s, Θ_s, μ_s) + q^b_s) ds + ∫_0^t (λ σ(s, Θ_s, μ_s) + q^σ_s) dW_s
  + ∫_0^t ∫_E (λ h(s, Θ_s, e, μ_s) + q^h_s(e)) Ñ(ds, de)`,

`Y_t = λ g(X_T, Law X_T) + q^g_T + ∫_t^T (λ f(s, Θ_s, μ_s) + q^f_s) ds − ∫_t^T Z_s dW_s
  − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`,

and at `λ = 1`, `q = 0` it is the system (1.1). `SolvesForced` states it over a filtration `ℱ`
carrying the driver `D`: the forward equation as `n` scalar linear forward equations
`LinearFSDEJ` and the backward one as `m` scalar linear backward equations `LinearBSDEJ`, whose
integrands are the coefficient processes `driftProc`, `diffusionProc`, `jumpProc`, `driverProc`
and `terminalVal`, evaluated along the tuple `tupleAt ν X Y Z U s ω` of the coordinate processes
and its law `lawP2 P (tupleAt ν X Y Z U s)` at each time. `Solves` is the case `λ = 1`, `q = 0`.

The paper's objects take the following forms.

* The unknowns are coordinate families. Each equation holds almost surely at each time, and every
  path of `X` and `Y` is right-continuous; left limits are not required. `Z` and `U` are
  progressively measurable and marked progressively measurable, not predictable.
* The jump coefficient is evaluated at `(Θ_s, μ_s)`, not at `(Θ_{s−}, μ⁻_s)`: the two agree for
  `dt ⊗ dP`-almost every `(s, ω)`, and the `L²` stochastic integral does not tell them apart. The
  integrand of the Poisson integral is a function `γ` of `(i, s, ω, e)` that represents
  `e ↦ h(s, Θ_s(ω), e, μ_s)` in `L²(ν)` for almost every `s ∈ [0, T]` and almost every `ω`,
  as in (2.4).
* `μ_s` is `Law(Θ_s)` at every time.
* The coefficient processes vanish off `[0, T]`, and so do the forcings (`Forcing`).

Two conditions of `SolvesForced` go beyond the hypotheses of the paper.

* **Square integrability of the coefficient processes.** For `λ ≠ 0` the two equations require
  `b(s, Θ_s, μ_s)`, `σ(s, Θ_s, μ_s)`, `h(s, Θ_s, ·, μ_s)` and `f(s, Θ_s, μ_s)` to have finite
  energy on `[0, T]`, and `g(X_T, Law X_T)` to be square integrable, since the integrals are the
  `L²` ones. Under Assumptions 2.2–2.3 this follows from (4.2)–(4.3). Without Assumption 2.2, as
  in Theorem 3.3, it asks `b` and `f` along the solution to be square integrable in time rather
  than integrable. The equations also ask `ξ₀` to be square integrable; for a solution in `ℍ²`
  this follows from the forward equation at almost every time, as the square integrability of
  the terminal value follows from the backward one.
* **Measurability of the coefficient processes**, (2.5). For `λ ≠ 0` they are jointly and
  progressively measurable (for `h`, its representative `γ` is). The paper derives this from
  Lemma A.1 and the Borel measurability of the coefficients; for coefficients jointly measurable
  with the evaluation σ-algebra on `P₂(H)`, `CoeffBorel`, it holds along every progressive tuple
  at every time and for the exact law (`CoeffBorel.crossEval`).

The `L²(ν)` channel needs no condition of its own: `U` is marked progressively measurable, so for
every time `s` the class `uLift` of `ω ↦ U_s(ω, ·) ∈ L²(ν; ℝᵐ)` is strongly `ℱ_s`-measurable
(`stronglyMeasurable_uLift_of_markedProgressive`). Hence the tuple `Θ_s` is strongly
`ℱ_s`-measurable, so that `(Θ_s, μ_s)` is a diagonal input wherever `Θ_s` is square integrable.

## Main definitions

* `driftProc`, `diffusionProc`, `jumpProc`, `driverProc`, `terminalVal` — the coefficient
  processes along a tuple of coordinate processes.
* `SolvesForced` — `(X, Y, Z, U)` solves the `λ`-forced system (4.1).
* `Solves` — `(X, Y, Z, U)` solves the system (1.1).

## Main statements

* `SolvesForced.stronglyMeasurable_tupleAt` — the tuple is strongly `ℱ_s`-measurable.
* `Solves.linearFSDEJ`, `Solves.linearBSDEJ`, `Solves.of_linear` — `Solves` in the unforced
  form of (1.1).
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-! ### The coefficient processes -/

section Processes

variable (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (C : Coeffs ν n m d)
  (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
  (U : Fin m → ℝ → Ω → E → ℝ)

/-- The drift process: coordinate `i` of `b(s, Θ_s(ω), μ_s)`, with `Θ_s` the tuple of the
coordinate processes and `μ_s` its law, for `s ∈ [0, T]`, and `0` off `[0, T]`. -/
noncomputable def driftProc (i : Fin n) (ω : Ω) (s : ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) T).indicator
    (fun s => C.b s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)) i) s

/-- The diffusion process: entry `(i, j)` of `σ(s, Θ_s(ω), μ_s)` for `s ∈ [0, T]`, and `0` off
`[0, T]`. -/
noncomputable def diffusionProc (i : Fin n) (s : ℝ) (ω : Ω) (j : Fin d) : ℝ :=
  (Set.Icc (0 : ℝ) T).indicator
    (fun s => C.σ s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)) (i, j)) s

/-- The driver process: coordinate `k` of `f(s, Θ_s(ω), μ_s)` for `s ∈ [0, T]`, and `0` off
`[0, T]`. -/
noncomputable def driverProc (k : Fin m) (ω : Ω) (s : ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) T).indicator
    (fun s => C.f s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)) k) s

/-- The terminal value: coordinate `k` of `g(X_T(ω), Law X_T)`. -/
noncomputable def terminalVal (k : Fin m) (ω : Ω) : ℝ :=
  C.g (WithLp.toLp 2 fun i => X i T ω) (lawP2 P fun ω' => WithLp.toLp 2 fun i => X i T ω') k

end Processes

/-- The jump process: a representative `γ` of the jump coefficient, for `s ∈ [0, T]`, and `0`
off `[0, T]`. -/
noncomputable def jumpProc (T : ℝ) (γ : Fin n → ℝ → Ω → E → ℝ) (i : Fin n) (s : ℝ) (ω : Ω)
    (e : E) : ℝ :=
  (Set.Icc (0 : ℝ) T).indicator (fun s => γ i s ω e) s

/-! ### Measurability of the tuple -/

section Measurability

variable {Ω' : Type*} {mΩ : MeasurableSpace Ω'}

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The tuple of the coordinate processes at time `s` is strongly measurable when its
coordinates are measurable and the `L²(ν)` class of its jump channel is strongly measurable. -/
theorem stronglyMeasurable_tupleAt_of {X : Fin n → ℝ → Ω' → ℝ} {Y : Fin m → ℝ → Ω' → ℝ}
    {Z : Fin m → ℝ → Ω' → Fin d → ℝ} {U : Fin m → ℝ → Ω' → E → ℝ} {s : ℝ}
    (hX : ∀ i, Measurable (X i s)) (hY : ∀ k, Measurable (Y k s))
    (hZ : ∀ k j, StronglyMeasurable fun ω => Z k s ω j)
    (hU : StronglyMeasurable fun ω => uLift ν fun e k => U k s ω e) :
    StronglyMeasurable (tupleAt ν X Y Z U s) := by
  have hX' : StronglyMeasurable fun ω =>
      (WithLp.toLp 2 fun i => X i s ω : EuclideanSpace ℝ (Fin n)) :=
    ((WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.mpr hX)).stronglyMeasurable
  have hY' : StronglyMeasurable fun ω =>
      (WithLp.toLp 2 fun k => Y k s ω : EuclideanSpace ℝ (Fin m)) :=
    ((WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.mpr hY)).stronglyMeasurable
  have hZ' : StronglyMeasurable fun ω =>
      (WithLp.toLp 2 fun p : Fin m × Fin d => Z p.1 s ω p.2 : EuclideanSpace ℝ (Fin m × Fin d)) :=
    ((WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr fun p : Fin m × Fin d =>
      (hZ p.1 p.2).measurable)).stronglyMeasurable
  exact hX'.prodMk (hY'.prodMk (hZ'.prodMk hU))

end Measurability

/-! ### The solution predicate -/

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`(X, Y, Z, U)` solves the `λ`-forced system (4.1)** with coefficients `C`, initial datum
`ξ₀` and forcing `q = (q^b, q^σ, q^h, q^f, q^g)` over the filtration `ℱ` carrying the driver `D`,
with `γ` a representative of the jump coefficient along the solution: `q` is a forcing, `γ`
represents `h(s, Θ_s(ω), ·, μ_s)` in `L²(ν)` for almost every `s ∈ [0, T]` and almost every `ω`,
each coordinate of `X` solves the linear forward equation from `ξ₀` with drift `λ b + q^b`,
diffusion `λ σ + q^σ` and jump integrand `λ γ + q^h`, and each coordinate of `(Y, Z, U)` solves
the linear backward equation with terminal value `λ g(X_T, Law X_T) + q^g` and drift `λ f + q^f`,
the coefficients evaluated along `(Θ_s, μ_s)`. -/
structure SolvesForced (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
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
  /-- `γ` represents the jump coefficient along the solution in `L²(ν)`, at almost every time of
  the horizon, almost surely. -/
  jump_rep : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
    (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
      =ᵐ[ν] C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))
  /-- The forward equation, coordinatewise. -/
  fwd : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (ξ₀ i)
    (fun ω s => lam * driftProc P T C X Y Z U i ω s + qb i ω s) (X i)
    (fun s ω j => lam * diffusionProc P T C X Y Z U i s ω j + qσ i s ω j)
    (fun s ω e => lam * jumpProc T γ i s ω e + qh i s ω e)
  /-- The backward equation, coordinatewise. -/
  bwd : ∀ k, LinearBSDEJ D ℱ hℱW hℱN T (fun ω => lam * terminalVal P T C X k ω + qg k ω)
    (fun ω s => lam * driverProc P T C X Y Z U k ω s + qf k ω s) (Y k) (Z k) (U k)

/-- **`(X, Y, Z, U)` solves the system (1.1)**: the `λ`-forced system at `λ = 1` with zero
forcing. -/
abbrev Solves (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ) (T : ℝ) (C : Coeffs ν n m d)
    (ξ₀ : Fin n → Ω → ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop :=
  SolvesForced D ℱ hℱW hℱN T 1 C ξ₀ 0 0 0 0 0 X Y Z U γ

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- **The tuple of a solution is strongly `ℱ_s`-measurable** at each time. -/
theorem SolvesForced.stronglyMeasurable_tupleAt
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ) (s : ℝ) :
    StronglyMeasurable[ℱ s] (tupleAt ν X Y Z U s) :=
  stronglyMeasurable_tupleAt_of (mΩ := ℱ s) (fun i => (h.fwd i).X_adapted s)
    (fun k => (h.bwd k).Y_adapted s)
    (fun k j => ((h.bwd k).Z_prog j).stronglyMeasurable_eval s)
    (stronglyMeasurable_uLift_of_markedProgressive (fun k => (h.bwd k).U_prog) s)

/-- A solution of (1.1) solves, coordinatewise, the linear forward equation from `ξ₀` with the
coefficient processes as integrands. -/
theorem Solves.linearFSDEJ (h : Solves D ℱ hℱW hℱN T C ξ₀ X Y Z U γ) (i : Fin n) :
    LinearFSDEJ D ℱ hℱW hℱN T (ξ₀ i) (driftProc P T C X Y Z U i) (X i)
      (diffusionProc P T C X Y Z U i) (jumpProc T γ i) := by
  simpa only [one_mul, Pi.zero_apply, add_zero] using h.fwd i

/-- A solution of (1.1) solves, coordinatewise, the linear backward equation with terminal value
`g(X_T, Law X_T)` and the driver process as drift. -/
theorem Solves.linearBSDEJ (h : Solves D ℱ hℱW hℱN T C ξ₀ X Y Z U γ) (k : Fin m) :
    LinearBSDEJ D ℱ hℱW hℱN T (terminalVal P T C X k) (driverProc P T C X Y Z U k) (Y k) (Z k)
      (U k) := by
  simpa only [one_mul, Pi.zero_apply, add_zero] using h.bwd k

/-- **A solution of (1.1) from its unforced equations**: a representative of the jump
coefficient, the forward equations from `ξ₀` and the backward equations with terminal value
`g(X_T, Law X_T)`. -/
theorem Solves.of_linear
    (hrep : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
        =ᵐ[ν] C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s)))
    (hfwd : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (ξ₀ i) (driftProc P T C X Y Z U i) (X i)
      (diffusionProc P T C X Y Z U i) (jumpProc T γ i))
    (hbwd : ∀ k, LinearBSDEJ D ℱ hℱW hℱN T (terminalVal P T C X k)
      (driverProc P T C X Y Z U k) (Y k) (Z k) (U k)) :
    Solves D ℱ hℱW hℱN T C ξ₀ X Y Z U γ where
  forcing := Forcing.zero
  jump_rep := hrep
  fwd i := by simpa only [one_mul, Pi.zero_apply, add_zero] using hfwd i
  bwd k := by simpa only [one_mul, Pi.zero_apply, add_zero] using hbwd k

end Dissertation.WellPosedness.System
