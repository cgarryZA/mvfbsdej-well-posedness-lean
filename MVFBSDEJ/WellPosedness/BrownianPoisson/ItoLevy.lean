/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.BrownianPoisson.Hypotheses

/-!
# The linear backward equation as a forward Itô–Lévy decomposition

Subtracting the linear backward equation (4.4) at `t` from the same equation at `0` gives the
forward decomposition `Y_t = Y_0 − ∫_0^t φ_s ds + ∫_0^t Z_s dW_s + ∫_0^t ∫_E U_s(e) Ñ(ds, de)`.
Frozen at the horizon, `t ↦ Y (min t T)` is therefore an Itô–Lévy process with initial value
`Y_0`, drift `−φ`, diffusion vector `Z` and jump integrand `U`. The initial value is square
integrable and measurable at time `0`, and the terminal value is `ξ` almost surely.

## Main statements

* `LinearBSDEJ.isItoLevyProcess_clampT` — the frozen solution is an Itô–Lévy process.
* `LinearBSDEJ.ae_eq_terminal` — `Y_T = ξ` almost surely.
* `LinearBSDEJ.memLp_initial` — `Y_0` is square integrable.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.BrownianPoisson

open LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {T : ℝ} {ξ : Ω → ℝ} {φ : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
  {U : ℝ → Ω → E → ℝ}

namespace LinearBSDEJ

/-- A solution of the linear backward equation is jointly measurable in time and sample
point. -/
theorem measurable_uncurry (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) :
    Measurable (Function.uncurry Y) :=
  Probability.measurable_uncurry_of_rightContinuous h.Y_adapted h.Y_rightCont

/-- The initial value of a solution of the linear backward equation is measurable at time
`0`. -/
theorem stronglyMeasurable_initial (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) :
    StronglyMeasurable[ℱ 0] (Y 0) :=
  (h.Y_adapted 0).stronglyMeasurable

/-- The multidimensional Itô integral of a square-integrable progressive integrand is square
integrable at every time. -/
theorem memLp_brownianIntegral (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (t : ℝ) :
    MemLp (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z h.Z_meas
      h.Z_prog (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) t) 2 P :=
  memLp_finsetSum Finset.univ fun i _ =>
    Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W i) ℱ (hℱW i) (fun ω s => Z s ω i)
      (h.Z_meas i) (h.Z_prog i) (sq_int_global_of_vanishing h.Z_vanish h.Z_sq i) t

/-- The value of a solution of the linear backward equation at the horizon is its terminal value,
almost surely. -/
theorem ae_eq_terminal (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (hT : 0 ≤ T) :
    Y T =ᵐ[P] ξ := by
  filter_upwards [h.eqn T ⟨hT, le_rfl⟩] with ω hω
  rw [hω, integral_Icc_eq_integral_Ioc, Set.Ioc_self, setIntegral_empty]
  ring

/-- The initial value of a solution of the linear backward equation is square integrable. -/
theorem memLp_initial (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (hT : 0 ≤ T) :
    MemLp (Y 0) 2 P := by
  have hA : MemLp (fun ω => ∫ s in Set.Icc (0 : ℝ) T, φ ω s) 2 P :=
    Ito.SecondMoment.memLp_two_setIntegral h.φ_meas hT h.φ_sq.lt_top
  have hN : ∀ t, MemLp (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
      (fun ω' s e => U s ω' e) h.U_meas h.U_prog
      (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) t) 2 P := fun t =>
    Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN _ h.U_meas h.U_prog
      (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) t
  refine ((((h.ξ_sq.add hA).sub ((h.memLp_brownianIntegral T).sub
    (h.memLp_brownianIntegral 0))).sub ((hN T).sub (hN 0)))).ae_eq ?_
  filter_upwards [h.eqn 0 ⟨le_rfl, hT⟩] with ω hω
  rw [hω]
  rfl

/-- **The frozen solution of the linear backward equation is an Itô–Lévy process**, with initial
value `Y_0`, drift `−φ`, diffusion vector `Z` and jump integrand `U`. -/
theorem isItoLevyProcess_clampT (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (hT : 0 < T) :
    Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN (clampT T Y) (Y 0)
      (fun s ω => -φ ω s) Z (fun ω s e => U s ω e) where
  measurable_path := measurable_uncurry_clampT h.measurable_uncurry
  σ_meas := h.Z_meas
  σ_prog := h.Z_prog
  σ_sq := sq_int_global_of_vanishing h.Z_vanish h.Z_sq
  γ_meas := h.U_meas
  γ_prog := h.U_prog
  γ_sq := marked_sq_int_global_of_vanishing h.U_vanish h.U_sq
  decomposition := by
    refine clampT_decomposition_of_eqn (ξ := ξ) hT h.φ_meas h.φ_sq h.φ_vanish h.eqn ?_ ?_ ?_ ?_
    · exact Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W ℱ
        hℱW Z h.Z_meas h.Z_prog (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) le_rfl
    · exact Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos
        (φ := fun ω s e => U s ω e) D.N hℱN h.U_meas h.U_prog
        (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) le_rfl
    · exact fun t hTt =>
        Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_eq_of_vanish D.W ℱ hℱW
          h.Z_meas h.Z_prog (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) hT hTt h.Z_vanish
    · exact fun t hTt =>
        Poisson.Compensated.stochasticIntegral_ae_eq_of_vanish (φ := fun ω s e => U s ω e) D.N
          hℱN h.U_meas h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) hT hTt
          h.U_vanish

end LinearBSDEJ

end MVFBSDEJ.WellPosedness.BrownianPoisson
