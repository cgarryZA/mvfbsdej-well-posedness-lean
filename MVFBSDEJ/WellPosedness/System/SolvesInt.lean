/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.IntegrableDrift
import MVFBSDEJ.WellPosedness.Stability.WindowIntegrable
import MVFBSDEJ.WellPosedness.System.ChannelCoords
import MVFBSDEJ.WellPosedness.System.SolvesMemLp

/-!
# Solutions of the system (1.1) in the class `ℍ²_weak`

Theorem 3.3 of the well-posedness paper concerns tuples `Θ = (X, Y, Z, U)` in `ℍ²_weak`, the class
of progressive tuples with

`𝔼 ∫_0^T (|X_t|² + |Y_t|² + |Z_t|²_F + ‖U_t‖²_{L²(ν)}) dt < ∞`,

satisfying (1.1), under Assumptions 2.3–2.5 only. Without Assumption 2.2 the coefficient processes
along such a tuple are the sum of the origin values `ψ(s, 0, δ₀)`, which need not be square
integrable in time, and a part in `L²(dt ⊗ dP)`. The drift `b` and the driver `f` along `Θ` enter
(1.1) only through pathwise Lebesgue integrals, which need almost every path to be integrable on
`[0, T]`. The diffusion `σ` and the jump coefficient `h` along `Θ` enter through the `L²`
stochastic integrals, so they have finite energy on `[0, T]`, and the terminal condition
`g(X_T, Law X_T)` presupposes `Law X_T ∈ P₂(ℝⁿ)`, that is `X_T ∈ L²`.

`SolvesForcedInt` records the `λ`-forced system (4.1) in this class: the forward equations as
`LinearFSDEJInt` and the backward ones as `LinearBSDEJInt` — the drift and the driver along the
solution with almost surely integrable paths, and no integrability condition on the initial datum
or on the terminal value — together with the finite energies of `X` and `Y` on `[0, T]` and the
square integrability of `X_T`. `SolvesInt` is the case `λ = 1`, `q = 0`. Neither carries a
condition on the origin values of the coefficients, nor a square integrability condition on `ξ₀`,
on `b` or `f` along the solution, or on `g(X_T, Law X_T)`.

As for `SolvesForced`, the coefficient processes are jointly and progressively measurable, (2.5),
and the jump coefficient enters through a representative `γ`. Along a solution of
`SolvesForcedInt` the tuple is square integrable at almost every time of `[0, T]`, and for
`λ ≠ 0` the coefficient processes are measurable one by one and the terminal value
`g(X_T, Law X_T)` is almost everywhere strongly measurable.

## Main definitions

* `SolvesForcedInt` — `(X, Y, Z, U)` solves the `λ`-forced system (4.1) in `ℍ²_weak`.
* `SolvesInt` — `(X, Y, Z, U)` solves the system (1.1) in `ℍ²_weak`.

## Main statements

* `SolvesForcedInt.stronglyMeasurable_tupleAt` — the tuple is strongly `ℱ_s`-measurable.
* `SolvesForcedInt.ae_memLp_tupleAt` — the tuple is square integrable at almost every time.
* `SolvesForcedInt.ae_ae_memLp_jump` — the jump channel is square integrable in the mark.
* `SolvesForcedInt.measurable_driftProc` and its companions — measurability of the coefficient
  processes for `λ ≠ 0`.
* `SolvesForcedInt.aestronglyMeasurable_terminalVal` — for `λ ≠ 0` the terminal value is almost
  everywhere strongly measurable.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`(X, Y, Z, U)` solves the `λ`-forced system (4.1) in `ℍ²_weak`** with coefficients `C`,
initial datum `ξ₀` and forcing `q = (q^b, q^σ, q^h, q^f, q^g)` over the filtration `ℱ` carrying the
driver
`D`, with `γ` a representative of the jump coefficient along the solution: `q` is a forcing, `γ`
represents `h(s, Θ_s(ω), ·, μ_s)` in `L²(ν)` for almost every `s ∈ [0, T]` and almost every `ω`,
each coordinate of `X` solves the linear forward equation of `LinearFSDEJInt` from `ξ₀` with drift
`λ b + q^b`, diffusion `λ σ + q^σ` and jump integrand `λ γ + q^h`, each coordinate of `(Y, Z, U)`
solves the linear backward equation of `LinearBSDEJInt` with terminal value
`λ g(X_T, Law X_T) + q^g` and drift `λ f + q^f`, the coefficients evaluated along `(Θ_s, μ_s)`,
the coordinates of `X` and `Y` have finite energy on `[0, T]`, and `X_T` is square integrable. -/
structure SolvesForcedInt (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
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
  fwd : ∀ i, LinearFSDEJInt D ℱ hℱW hℱN T (ξ₀ i)
    (fun ω s => lam * driftProc P T C X Y Z U i ω s + qb i ω s) (X i)
    (fun s ω j => lam * diffusionProc P T C X Y Z U i s ω j + qσ i s ω j)
    (fun s ω e => lam * jumpProc T γ i s ω e + qh i s ω e)
  /-- The backward equation, coordinatewise. -/
  bwd : ∀ k, LinearBSDEJInt D ℱ hℱW hℱN T (fun ω => lam * terminalVal P T C X k ω + qg k ω)
    (fun ω s => lam * driverProc P T C X Y Z U k ω s + qf k ω s) (Y k) (Z k) (U k)
  /-- Each coordinate of `X` has finite energy on the horizon. -/
  X_sq : ∀ i, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => X i s ω) ≠ ⊤
  /-- Each coordinate of `Y` has finite energy on the horizon. -/
  Y_sq : ∀ k, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Y k s ω) ≠ ⊤
  /-- Each coordinate of `X_T` is square integrable. -/
  XT_sq : ∀ i, MemLp (X i T) 2 P

/-- **`(X, Y, Z, U)` solves the system (1.1) in `ℍ²_weak`**: the `λ`-forced system of
`SolvesForcedInt` at `λ = 1` with zero forcing. -/
abbrev SolvesInt (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ) (T : ℝ) (C : Coeffs ν n m d)
    (ξ₀ : Fin n → Ω → ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop :=
  SolvesForcedInt D ℱ hℱW hℱN T 1 C ξ₀ 0 0 0 0 0 X Y Z U γ

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

namespace SolvesForcedInt

variable (h : SolvesForcedInt D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ)
include h

/-! ### The tuple -/

/-- **The tuple of a solution is strongly `ℱ_s`-measurable** at each time. -/
theorem stronglyMeasurable_tupleAt (s : ℝ) : StronglyMeasurable[ℱ s] (tupleAt ν X Y Z U s) :=
  stronglyMeasurable_tupleAt_of (mΩ := ℱ s) (fun i => (h.fwd i).X_adapted s)
    (fun k => (h.bwd k).Y_adapted s)
    (fun k j => ((h.bwd k).Z_prog j).stronglyMeasurable_eval s)
    (stronglyMeasurable_uLift_of_markedProgressive (fun k => (h.bwd k).U_prog) s)

/-- Each coordinate of `X` is jointly measurable in the sample point and time. -/
theorem measurable_X (i : Fin n) : Measurable (Function.uncurry fun ω s => X i s ω) :=
  (h.fwd i).measurable_uncurry.comp measurable_swap

/-- Each coordinate of `Y` is jointly measurable in the sample point and time. -/
theorem measurable_Y (k : Fin m) : Measurable (Function.uncurry fun ω s => Y k s ω) :=
  (h.bwd k).measurable_uncurry.comp measurable_swap

/-- **The jump channel of a solution is square integrable in the mark**: at almost every time of
`[0, T]`, almost surely, each `e ↦ U_{k,s}(ω, e)` lies in `L²(ν)`. -/
theorem ae_ae_memLp_jump :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, ∀ k,
      MemLp (fun e => U k s ω e) 2 ν := by
  filter_upwards [ae_all_iff.mpr fun k =>
    ae_ae_memLp_of_markedEnergy_ne_top (h.bwd k).U_meas (h.bwd k).U_sq] with s hs
  exact ae_all_iff.mpr hs

/-- **The tuple of a solution is square integrable at almost every time** of `[0, T]`. -/
theorem ae_memLp_tupleAt :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (tupleAt ν X Y Z U s) 2 P :=
  MVFBSDEJ.WellPosedness.System.ae_memLp_tupleAt
    (fun s _ => ((h.stronglyMeasurable_tupleAt s).mono (ℱ.le s)).aestronglyMeasurable)
    h.measurable_X h.measurable_Y (fun k j => (h.bwd k).Z_meas j) (fun k => (h.bwd k).U_meas)
    h.X_sq h.Y_sq (fun k j => (h.bwd k).Z_sq j) (fun k => (h.bwd k).U_sq)

/-! ### The coefficient processes -/

/-- For `λ ≠ 0`, the drift process along a solution is jointly measurable. -/
theorem measurable_driftProc (hlam : lam ≠ 0) (i : Fin n) :
    Measurable (Function.uncurry (driftProc P T C X Y Z U i)) := by
  have e : Function.uncurry (driftProc P T C X Y Z U i) = fun p : Ω × ℝ =>
      lam⁻¹ * ((lam * driftProc P T C X Y Z U i p.1 p.2 + qb i p.1 p.2) - qb i p.1 p.2) := by
    funext p
    exact eq_inv_mul_add_sub hlam _ _
  rw [e]
  exact ((h.fwd i).b_meas.sub (h.forcing.qb_meas i)).const_mul _

/-- For `λ ≠ 0`, the diffusion process along a solution is jointly measurable in each
coordinate. -/
theorem measurable_diffusionProc (hlam : lam ≠ 0) (i : Fin n) (j : Fin d) :
    Measurable (Function.uncurry fun ω s => diffusionProc P T C X Y Z U i s ω j) := by
  have e : (Function.uncurry fun ω s => diffusionProc P T C X Y Z U i s ω j)
      = fun p : Ω × ℝ => lam⁻¹ * ((lam * diffusionProc P T C X Y Z U i p.2 p.1 j
        + qσ i p.2 p.1 j) - qσ i p.2 p.1 j) := by
    funext p
    exact eq_inv_mul_add_sub hlam _ _
  rw [e]
  exact (((h.fwd i).σ_meas j).sub (h.forcing.qσ_meas i j)).const_mul _

/-- For `λ ≠ 0`, the jump process along a solution is jointly measurable in the sample point, the
time and the mark. -/
theorem measurable_jumpProc (hlam : lam ≠ 0) (i : Fin n) :
    Measurable fun p : Ω × ℝ × E => jumpProc T γ i p.2.1 p.1 p.2.2 := by
  have e : (fun p : Ω × ℝ × E => jumpProc T γ i p.2.1 p.1 p.2.2) = fun p : Ω × ℝ × E =>
      lam⁻¹ * ((lam * jumpProc T γ i p.2.1 p.1 p.2.2 + qh i p.2.1 p.1 p.2.2)
        - qh i p.2.1 p.1 p.2.2) := by
    funext p
    exact eq_inv_mul_add_sub hlam _ _
  rw [e]
  exact ((h.fwd i).γ_meas.sub (h.forcing.qh_meas i)).const_mul _

/-- For `λ ≠ 0`, the driver process along a solution is jointly measurable. -/
theorem measurable_driverProc (hlam : lam ≠ 0) (k : Fin m) :
    Measurable (Function.uncurry (driverProc P T C X Y Z U k)) := by
  have e : Function.uncurry (driverProc P T C X Y Z U k) = fun p : Ω × ℝ =>
      lam⁻¹ * ((lam * driverProc P T C X Y Z U k p.1 p.2 + qf k p.1 p.2) - qf k p.1 p.2) := by
    funext p
    exact eq_inv_mul_add_sub hlam _ _
  rw [e]
  exact ((h.bwd k).φ_meas.sub (h.forcing.qf_meas k)).const_mul _

/-- For `λ ≠ 0` and `T ≥ 0`, the terminal value `g(X_T, Law X_T)` along a solution is almost
everywhere strongly measurable: by the backward equation at `T` it is `λ⁻¹ (Y_T − q^g_T)` almost
surely. -/
theorem aestronglyMeasurable_terminalVal (hlam : lam ≠ 0) (hT : 0 ≤ T) (k : Fin m) :
    AEStronglyMeasurable (terminalVal P T C X k) P := by
  have h1 : AEStronglyMeasurable (fun ω => lam * terminalVal P T C X k ω + qg k ω) P :=
    (((h.bwd k).Y_adapted T).mono (ℱ.le T) le_rfl).aestronglyMeasurable.congr
      ((h.bwd k).ae_eq_terminal hT)
  have e : terminalVal P T C X k
      = fun ω => lam⁻¹ * ((lam * terminalVal P T C X k ω + qg k ω) - qg k ω) := by
    funext ω
    exact eq_inv_mul_add_sub hlam _ _
  rw [e]
  exact (h1.sub (h.forcing.qg_sq k).aestronglyMeasurable).const_mul _

end SolvesForcedInt

end MVFBSDEJ.WellPosedness.System
