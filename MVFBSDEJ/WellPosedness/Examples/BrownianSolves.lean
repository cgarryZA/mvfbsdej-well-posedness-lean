/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Examples.Brownian
import MVFBSDEJ.WellPosedness.Existence.CoeffBorelW2
import MVFBSDEJ.WellPosedness.Existence.OriginBound
import MVFBSDEJ.WellPosedness.System.DiagonalLipschitzH
import MVFBSDEJ.WellPosedness.System.Solves

/-!
# Example 5.2: the linear Brownian equations at zero intensity

Over a filtration for which each coordinate of a `d`-dimensional Brownian motion `W` is a Brownian
motion, `LinearFSDE` and `LinearBSDE` are the coordinatewise linear forward and backward Brownian
equations

`X_t = ξ₀ + ∫_0^t b_s ds + ∫_0^t σ_s dW_s`,

`Y_t = ξ + ∫_t^T φ_s ds − ∫_t^T Z_s dW_s`,

with the Brownian integrals the canonical ones: the linear equations with jumps `LinearFSDEJ`,
`LinearBSDEJ` without their jump terms.

At the zero intensity `ν = 0` the Poisson random measure of a Lévy driver carries no
compensated integral: every marked integrand has zero marked energy, so by the Itô–Lévy isometry
its compensated integral vanishes almost surely at each time. Hence, for a Lévy driver of zero
intensity, a solution of a linear Brownian equation driven by its Brownian motion solves the
linear equation with jumps with the zero jump integrand.

## Main definitions

* `LinearFSDE`, `LinearBSDE` — the linear forward and backward Brownian equations.

## Main statements

* `markedEnergy_nu_zero` — at `ν = 0` every marked integrand has zero marked energy.
* `stochasticIntegral_nu_zero` — at `ν = 0` the compensated integral vanishes almost surely.
* `LinearFSDE.linearFSDEJ`, `LinearBSDE.linearBSDEJ` — at `ν = 0` a solution of a linear
  Brownian equation solves the linear equation with jumps with the zero jump integrand.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped ENNReal NNReal

namespace MVFBSDEJ.WellPosedness.System

open LevyStochCalc LevyStochCalc.BSDEJ.Solves MVFBSDEJ.WellPosedness.BrownianPoisson
  MVFBSDEJ.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n m d : ℕ}

/-! ### The compensated integral at zero intensity -/

section Zero

variable {E : Type v} [MeasurableSpace E]

omit [IsProbabilityMeasure P] in
/-- At `ν = 0` every marked integrand has zero marked energy. -/
theorem markedEnergy_nu_zero (T : ℝ) (φ : Ω → ℝ → E → ℝ) :
    Poisson.Compensated.markedEnergy P (0 : Measure E) T φ = 0 := by
  simp [Poisson.Compensated.markedEnergy]

/-- **At `ν = 0` the compensated integral vanishes**: for a Poisson random measure of zero
intensity, `∫_0^t ∫_E φ_s(e) Ñ(ds, de) = 0` almost surely at every time `t`. -/
theorem stochasticIntegral_nu_zero (N : Poisson.PoissonRandomMeasure.{u, v, w} P (0 : Measure E))
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : Poisson.IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ) (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (h_prog : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂(0 : Measure E) ∂volume ∂P < ⊤) (t : ℝ) :
    Poisson.Compensated.stochasticIntegral N ℱ hℱ φ h_meas h_prog h_sq t =ᵐ[P] 0 := by
  rcases le_or_gt t 0 with ht | ht
  · exact (Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ φ h_meas h_prog h_sq
      t).trans (Poisson.Compensated.process_ae_zero_of_nonpos N ℱ hℱ φ h_meas h_prog h_sq ht)
  · have hiso := Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱ φ h_meas h_prog h_sq t ht
    simp only [lintegral_zero_measure, lintegral_const, zero_mul] at hiso
    have hm : Measurable (Poisson.Compensated.stochasticIntegral N ℱ hℱ φ h_meas h_prog h_sq t) :=
      (Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱ φ h_meas h_prog h_sq t).mono
        (ℱ.rightCont.le t) le_rfl
    filter_upwards [(lintegral_eq_zero_iff (hm.nnnorm.coe_nnreal_ennreal.pow_const 2)).mp hiso]
      with ω hω
    simpa using hω

end Zero

/-! ### The Brownian linear equations -/

section Linear

variable (W : Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, Brownian.IsBrownianFiltration (W.W j) ℱ)

/-- `X` solves the linear forward Brownian equation

`X_t = ξ₀ + ∫_0^t b_s ds + ∫_0^t σ_s dW_s`

over the filtration `ℱ`, almost surely at each `t ∈ [0, T]`, with the Brownian integral the
canonical one for `ℱ`; `b` and `σ` are progressive, of finite energy on `[0, T]` and vanish off
it, `ξ₀` is square integrable, and `X` is adapted with right-continuous paths. -/
structure LinearFSDE (T : ℝ) (ξ₀ : Ω → ℝ) (b : Ω → ℝ → ℝ) (X : ℝ → Ω → ℝ)
    (σ : ℝ → Ω → (Fin d → ℝ)) : Prop where
  /-- Each coordinate of `σ` is jointly measurable. -/
  σ_meas : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ s ω j)
  /-- Each coordinate of `σ` is progressively measurable. -/
  σ_prog : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => σ s ω j
  /-- `σ` vanishes off the horizon. -/
  σ_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → σ s ω = 0
  /-- Each coordinate of `σ` has finite energy on the horizon. -/
  σ_sq : ∀ j : Fin d, Brownian.Ito.energy P T (fun ω s => σ s ω j) ≠ ⊤
  /-- The drift is jointly measurable. -/
  b_meas : Measurable (Function.uncurry b)
  /-- The drift is progressively measurable. -/
  b_prog : Probability.ProgressivelyMeasurable ℱ b
  /-- The drift vanishes off the horizon. -/
  b_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0
  /-- The drift has finite energy on the horizon. -/
  b_sq : Brownian.Ito.energy P T b ≠ ⊤
  /-- The initial value is square integrable. -/
  ξ₀_sq : MemLp ξ₀ 2 P
  /-- `X` is adapted. -/
  X_adapted : MeasureTheory.Adapted ℱ X
  /-- Every path of `X` is right-continuous. -/
  X_rightCont : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
  /-- The forward equation, almost surely at each time of the horizon. -/
  eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
    X t ω = ξ₀ ω + (∫ s in Set.Icc (0 : ℝ) t, b ω s)
      + Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW σ σ_meas σ_prog
          (sq_int_global_of_vanishing σ_vanish σ_sq) t ω

/-- `(Y, Z)` solves the linear backward Brownian equation

`Y_t = ξ + ∫_t^T φ_s ds − ∫_t^T Z_s dW_s`

over the filtration `ℱ`, almost surely at each `t ∈ [0, T]`, with the Brownian integral the
canonical one for `ℱ`; `Z` and `φ` are progressive, of finite energy on `[0, T]` and vanish off
it, `ξ` is square integrable, and `Y` is adapted with right-continuous paths. -/
structure LinearBSDE (T : ℝ) (ξ : Ω → ℝ) (φ : Ω → ℝ → ℝ) (Y : ℝ → Ω → ℝ)
    (Z : ℝ → Ω → (Fin d → ℝ)) : Prop where
  /-- Each coordinate of `Z` is jointly measurable. -/
  Z_meas : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i)
  /-- Each coordinate of `Z` is progressively measurable. -/
  Z_prog : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i
  /-- `Z` vanishes off the horizon. -/
  Z_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0
  /-- Each coordinate of `Z` has finite energy on the horizon. -/
  Z_sq : ∀ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤
  /-- The drift is jointly measurable. -/
  φ_meas : Measurable (Function.uncurry φ)
  /-- The drift is progressively measurable. -/
  φ_prog : Probability.ProgressivelyMeasurable ℱ φ
  /-- The drift vanishes off the horizon. -/
  φ_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ ω s = 0
  /-- The drift has finite energy on the horizon. -/
  φ_sq : Brownian.Ito.energy P T φ ≠ ⊤
  /-- The terminal value is square integrable. -/
  ξ_sq : MemLp ξ 2 P
  /-- `Y` is adapted. -/
  Y_adapted : MeasureTheory.Adapted ℱ Y
  /-- Every path of `Y` is right-continuous. -/
  Y_rightCont : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω))
  /-- The backward equation, almost surely at each time of the horizon. -/
  eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
    Y t ω = ξ ω + (∫ s in Set.Icc t T, φ ω s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW Z Z_meas Z_prog
            (sq_int_global_of_vanishing Z_vanish Z_sq) T ω
          - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW Z Z_meas Z_prog
            (sq_int_global_of_vanishing Z_vanish Z_sq) t ω)

end Linear

section Equations

variable {E : Type v} [MeasurableSpace E]
  {D : Driver.LevyDriver.{u, v, w} P d (0 : Measure E)} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {ξ₀ ξ : Ω → ℝ} {b φ : Ω → ℝ → ℝ}
  {X Y : ℝ → Ω → ℝ} {σ Z : ℝ → Ω → (Fin d → ℝ)} {γ U : ℝ → Ω → E → ℝ}

/-- **At `ν = 0` a solution of the linear forward Brownian equation solves the equation with
jumps** with the zero jump integrand. -/
theorem LinearFSDE.linearFSDEJ (h : LinearFSDE D.W ℱ hℱW T ξ₀ b X σ) :
    LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ (fun _ _ _ => 0) where
  σ_meas := h.σ_meas
  σ_prog := h.σ_prog
  σ_vanish := h.σ_vanish
  σ_sq := h.σ_sq
  γ_meas := measurable_const
  γ_prog := Poisson.Compensated.markedProgressivelyMeasurable_zero ℱ
  γ_vanish _ _ _ _ := rfl
  γ_sq := by rw [markedEnergy_nu_zero]; exact ENNReal.zero_ne_top
  b_meas := h.b_meas
  b_prog := h.b_prog
  b_vanish := h.b_vanish
  b_sq := h.b_sq
  ξ₀_sq := h.ξ₀_sq
  X_adapted := h.X_adapted
  X_rightCont := h.X_rightCont
  eqn t ht := by
    filter_upwards [h.eqn t ht, stochasticIntegral_nu_zero D.N ℱ hℱN (fun _ _ _ => 0)
      measurable_const (Poisson.Compensated.markedProgressivelyMeasurable_zero ℱ)
      (marked_sq_int_global_of_vanishing (U := fun _ _ _ => 0) (T := T) (fun _ _ _ _ => rfl)
        (by rw [markedEnergy_nu_zero]; exact ENNReal.zero_ne_top)) t] with ω h1 h2
    rw [h1, h2, Pi.zero_apply, add_zero]

/-- **At `ν = 0` a solution of the linear backward Brownian equation solves the equation with
jumps** with the zero jump integrand. -/
theorem LinearBSDE.linearBSDEJ (h : LinearBSDE D.W ℱ hℱW T ξ φ Y Z) :
    LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z (fun _ _ _ => 0) where
  Z_meas := h.Z_meas
  Z_prog := h.Z_prog
  Z_vanish := h.Z_vanish
  Z_sq := h.Z_sq
  U_meas := measurable_const
  U_prog := Poisson.Compensated.markedProgressivelyMeasurable_zero ℱ
  U_vanish _ _ _ _ := rfl
  U_sq := by rw [markedEnergy_nu_zero]; exact ENNReal.zero_ne_top
  φ_meas := h.φ_meas
  φ_prog := h.φ_prog
  φ_vanish := h.φ_vanish
  φ_sq := h.φ_sq
  ξ_sq := h.ξ_sq
  Y_adapted := h.Y_adapted
  Y_rightCont := h.Y_rightCont
  eqn t ht := by
    have hN := stochasticIntegral_nu_zero D.N ℱ hℱN (fun _ _ _ => 0) measurable_const
      (Poisson.Compensated.markedProgressivelyMeasurable_zero ℱ)
      (marked_sq_int_global_of_vanishing (U := fun _ _ _ => 0) (T := T) (fun _ _ _ _ => rfl)
        (by rw [markedEnergy_nu_zero]; exact ENNReal.zero_ne_top))
    filter_upwards [h.eqn t ht, hN T, hN t] with ω h1 h2 h3
    rw [h1, h2, h3, Pi.zero_apply, sub_self, sub_zero]

end Equations

end MVFBSDEJ.WellPosedness.System
