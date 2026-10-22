/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.BrownianPoisson.ItoLevy

/-!
# The linear forward equation with jumps

The forward difference equation (4.15) of the well-posedness paper is, coordinatewise, the linear
forward equation

`X_t = ξ₀ + ∫_0^t b_s ds + ∫_0^t σ_s dW_s + ∫_0^t ∫_E γ_s(e) Ñ(ds, de)`,   `t ∈ [0, T]`,

with given integrands `b`, `σ`, `γ`. This file records it as one predicate, `LinearFSDEJ`, over a
filtration `ℱ` for which every coordinate of the Brownian motion `W` of a Lévy driver is a
Brownian motion and its Poisson random measure `N` is a Poisson random measure, with the same
conventions as the linear backward equation `LinearBSDEJ`: the integrands are progressive, of
finite energy on `[0, T]` and vanish off it, the initial value is square integrable, `X` is
adapted with right-continuous paths, and the equation holds almost surely at each time.

Subtracting the equation at `t` from the equation at `T` writes it backward from `X_T`:

`X_t = X_T + ∫_t^T (−b_s) ds − ∫_t^T σ_s dW_s − ∫_t^T ∫_E γ_s(e) Ñ(ds, de)`,

so a solution of the forward equation is a solution of the linear backward equation with terminal
value `X_T` and drift `−b` whose initial value is `ξ₀` almost surely, and conversely.

## Main definitions

* `LinearFSDEJ` — `X` solves the linear forward equation with initial value `ξ₀`, drift `b`,
  diffusion vector `σ` and jump integrand `γ` over `ℱ`.

## Main statements

* `LinearFSDEJ.linearBSDEJ`, `LinearFSDEJ.initial_ae_eq` — a solution of the forward equation
  solves the backward equation from `X_T` and starts at `ξ₀`.
* `LinearBSDEJ.linearFSDEJ` — the converse.
* `LinearFSDEJ.isItoLevyProcess_clampT` — frozen at the horizon, a solution is an Itô–Lévy
  process with drift `b`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- `X` solves the linear forward equation with jumps

`X_t = ξ₀ + ∫_0^t b_s ds + ∫_0^t σ_s dW_s + ∫_0^t ∫_E γ_s(e) Ñ(ds, de)`

driven by `D` over the filtration `ℱ`, almost surely at each `t ∈ [0, T]`, with the two
stochastic integrals the canonical ones for `ℱ`; `b`, `σ` and `γ` are progressive, of finite
energy on `[0, T]` and vanish off it, `ξ₀` is square integrable, and `X` is adapted with
right-continuous paths. -/
structure LinearFSDEJ (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ)
    (T : ℝ) (ξ₀ : Ω → ℝ) (b : Ω → ℝ → ℝ)
    (X : ℝ → Ω → ℝ) (σ : ℝ → Ω → (Fin d → ℝ)) (γ : ℝ → Ω → E → ℝ) : Prop where
  /-- Each coordinate of `σ` is jointly measurable. -/
  σ_meas : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ s ω j)
  /-- Each coordinate of `σ` is progressively measurable. -/
  σ_prog : ∀ j : Fin d, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => σ s ω j
  /-- `σ` vanishes off the horizon. -/
  σ_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → σ s ω = 0
  /-- Each coordinate of `σ` has finite energy on the horizon. -/
  σ_sq : ∀ j : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => σ s ω j) ≠ ⊤
  /-- `γ` is jointly measurable in the sample point, the time and the mark. -/
  γ_meas : Measurable fun p : Ω × ℝ × E => γ p.2.1 p.1 p.2.2
  /-- `γ` is marked progressively measurable. -/
  γ_prog : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => γ s ω e
  /-- `γ` vanishes off the horizon. -/
  γ_vanish : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → γ s ω e = 0
  /-- `γ` has finite marked energy on the horizon. -/
  γ_sq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => γ s ω e) ≠ ⊤
  /-- The drift is jointly measurable. -/
  b_meas : Measurable (Function.uncurry b)
  /-- The drift is progressively measurable. -/
  b_prog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ b
  /-- The drift vanishes off the horizon. -/
  b_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0
  /-- The drift has finite energy on the horizon. -/
  b_sq : LevyStochCalc.Brownian.Ito.energy P T b ≠ ⊤
  /-- The initial value is square integrable. -/
  ξ₀_sq : MemLp ξ₀ 2 P
  /-- `X` is adapted. -/
  X_adapted : MeasureTheory.Adapted ℱ X
  /-- Every path of `X` is right-continuous. -/
  X_rightCont : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
  /-- The forward equation, almost surely at each time of the horizon. -/
  eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
    X t ω = ξ₀ ω + (∫ s in Set.Icc (0 : ℝ) t, b ω s)
      + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW σ
          σ_meas σ_prog (sq_int_global_of_vanishing σ_vanish σ_sq) t ω
      + LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
          (fun ω' s e => γ s ω' e) γ_meas γ_prog (marked_sq_int_global_of_vanishing γ_vanish γ_sq)
          t ω

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {T : ℝ} {ξ₀ ξ : Ω → ℝ} {b φ : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ} {σ : ℝ → Ω → (Fin d → ℝ)}
  {γ : ℝ → Ω → E → ℝ}

namespace LinearFSDEJ

/-- A solution of the linear forward equation starts at its initial value, almost surely. -/
theorem initial_ae_eq (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) (hT : 0 ≤ T) :
    X 0 =ᵐ[P] ξ₀ := by
  filter_upwards [h.eqn 0 ⟨le_rfl, hT⟩,
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W ℱ hℱW σ
      h.σ_meas h.σ_prog (sq_int_global_of_vanishing h.σ_vanish h.σ_sq) le_rfl,
    Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos (φ := fun ω s e => γ s ω e) D.N
      hℱN h.γ_meas h.γ_prog (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) le_rfl]
    with ω h0 hW hN
  simp only [Pi.zero_apply] at hW hN
  rw [h0, hW, hN, Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
    integral_zero_measure]
  ring

/-- The value of a solution of the linear forward equation at the horizon is square
integrable. -/
theorem memLp_terminal (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) (hT : 0 ≤ T) :
    MemLp (X T) 2 P := by
  have hA : MemLp (fun ω => ∫ s in Set.Icc (0 : ℝ) T, b ω s) 2 P :=
    Ito.SecondMoment.memLp_two_setIntegral h.b_meas hT h.b_sq.lt_top
  have hB : MemLp (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW σ
      h.σ_meas h.σ_prog (sq_int_global_of_vanishing h.σ_vanish h.σ_sq) T) 2 P :=
    memLp_finsetSum Finset.univ fun i _ =>
      Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W i) ℱ (hℱW i) (fun ω s => σ s ω i)
        (h.σ_meas i) (h.σ_prog i) (sq_int_global_of_vanishing h.σ_vanish h.σ_sq i) T
  have hN : MemLp (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
      (fun ω' s e => γ s ω' e) h.γ_meas h.γ_prog
      (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) T) 2 P :=
    Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN _ h.γ_meas h.γ_prog
      (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) T
  refine (((h.ξ₀_sq.add hA).add hB).add hN).ae_eq ?_
  filter_upwards [h.eqn T ⟨hT, le_rfl⟩] with ω hω
  rw [hω]
  rfl

/-- **A solution of the linear forward equation solves the linear backward equation** with
terminal value `X_T` and drift `−b`. -/
theorem linearBSDEJ (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) (hT : 0 ≤ T) :
    LinearBSDEJ D ℱ hℱW hℱN T (X T) (fun ω s => -b ω s) X σ γ where
  Z_meas := h.σ_meas
  Z_prog := h.σ_prog
  Z_vanish := h.σ_vanish
  Z_sq := h.σ_sq
  U_meas := h.γ_meas
  U_prog := h.γ_prog
  U_vanish := h.γ_vanish
  U_sq := h.γ_sq
  φ_meas := h.b_meas.neg
  φ_prog := continuous_neg.comp_progressivelyMeasurable neg_zero h.b_prog
  φ_vanish ω s hs := by rw [h.b_vanish ω s hs, neg_zero]
  φ_sq := by
    simpa only [Brownian.Ito.energy, nnnorm_neg] using h.b_sq
  ξ_sq := h.memLp_terminal hT
  Y_adapted := h.X_adapted
  Y_rightCont := h.X_rightCont
  eqn t ht := by
    filter_upwards [h.eqn t ht, h.eqn T ⟨ht.1.trans ht.2, le_rfl⟩,
      driftLeg_ae_eq h.b_meas h.b_sq T, driftLeg_ae_eq h.b_meas h.b_sq t,
      driftLeg_sub_ae h.b_meas h.b_sq ht.1 ht.2] with ω h1 h2 h3 h4 h5
    rw [integral_neg]
    linarith

end LinearFSDEJ

/-- **A solution of the linear backward equation with drift `φ` starting at `ξ₀` solves the
linear forward equation** with initial value `ξ₀` and drift `−φ`. -/
theorem _root_.MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.linearFSDEJ
    (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ X σ γ) (h0 : X 0 =ᵐ[P] ξ₀) (hT : 0 ≤ T) :
    LinearFSDEJ D ℱ hℱW hℱN T ξ₀ (fun ω s => -φ ω s) X σ γ where
  σ_meas := h.Z_meas
  σ_prog := h.Z_prog
  σ_vanish := h.Z_vanish
  σ_sq := h.Z_sq
  γ_meas := h.U_meas
  γ_prog := h.U_prog
  γ_vanish := h.U_vanish
  γ_sq := h.U_sq
  b_meas := h.φ_meas.neg
  b_prog := continuous_neg.comp_progressivelyMeasurable neg_zero h.φ_prog
  b_vanish ω s hs := by rw [h.φ_vanish ω s hs, neg_zero]
  b_sq := by
    simpa only [Brownian.Ito.energy, nnnorm_neg] using h.φ_sq
  ξ₀_sq := (h.memLp_initial hT).ae_eq h0
  X_adapted := h.Y_adapted
  X_rightCont := h.Y_rightCont
  eqn t ht := by
    filter_upwards [h.eqn t ht, h.eqn 0 ⟨le_rfl, hT⟩, h0,
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W ℱ hℱW σ
        h.Z_meas h.Z_prog (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) le_rfl,
      Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos (φ := fun ω s e => γ s ω e) D.N
        hℱN h.U_meas h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) le_rfl,
      driftLeg_ae_eq h.φ_meas h.φ_sq T, driftLeg_ae_eq h.φ_meas h.φ_sq t,
      driftLeg_sub_ae h.φ_meas h.φ_sq ht.1 ht.2] with ω h1 h2 h3 h4 h5 h6 h7 h8
    simp only [Pi.zero_apply] at h4 h5
    rw [integral_neg]
    linarith

namespace LinearFSDEJ

/-- **The frozen solution of the linear forward equation is an Itô–Lévy process**, with initial
value `X_0`, drift `b`, diffusion vector `σ` and jump integrand `γ`. -/
theorem isItoLevyProcess_clampT (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) (hT : 0 < T) :
    Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN (clampT T X) (X 0)
      (fun s ω => b ω s) σ (fun ω s e => γ s ω e) := by
  simpa only [neg_neg] using (h.linearBSDEJ hT.le).isItoLevyProcess_clampT hT

end LinearFSDEJ

end MVFBSDEJ.WellPosedness.Stability
