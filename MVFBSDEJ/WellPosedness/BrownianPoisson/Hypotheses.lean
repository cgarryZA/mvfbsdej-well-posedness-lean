/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.ExistenceUniqueness

/-!
# The linear backward equation with jumps of the Brownian–Poisson estimate

Lemma 4.1 of the well-posedness paper bounds a solution `(δY, δZ, δU)` of the linear backward
equation with jumps

`δY_t = δξ + ∫_t^T φ_s ds − ∫_t^T δZ_s dW_s − ∫_t^T ∫_E δU_s(e) Ñ(ds, de)`   (4.4)

in terms of its terminal value `δξ` and its drift `φ`. This file records (4.4) and the
integrability of its data as one predicate, `LinearBSDEJ`, over a filtration `ℱ` for which every
coordinate of the Brownian motion `W` of a Lévy driver is a Brownian motion and its Poisson random
measure `N` is a Poisson random measure. The two stochastic integrals are the canonical ones of
that filtration.

The predicate takes the following forms of the paper's hypotheses.

* The drift `φ` is jointly measurable, of finite energy on `[0, T]` and **progressively
  measurable**; the paper asks only `φ ∈ L²(Ω × [0, T])`.
* Equation (4.4) holds **for each `t ∈ [0, T]` almost surely**, the exceptional set depending on
  `t`; the canonical stochastic integrals are defined only up to a null set at each time.
* The integrands `δZ`, `δU` and the drift `φ` vanish off `[0, T]`, and `δZ`, `δU` are
  progressively measurable (respectively marked progressively measurable) with finite energy on
  `[0, T]`.
* `δY` is adapted and every one of its paths is right-continuous; left limits are not required.
* `δξ` is square integrable; its measurability at the horizon is not required.

The equation is scalar; the `ℝᵐ`-valued equation is a family of `m` scalar ones.

## Main definitions

* `LinearBSDEJ` — `(Y, Z, U)` solves (4.4) with terminal value `ξ` and drift `φ` over `ℱ`.
* `LinearBSDEJAug` — the same over the augmented joint filtration `augJoint D` of the driver.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.BrownianPoisson

open LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- `(Y, Z, U)` solves the linear backward equation with jumps

`Y_t = ξ + ∫_t^T φ_s ds − ∫_t^T Z_s dW_s − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`

driven by `D` over the filtration `ℱ`, almost surely at each `t ∈ [0, T]`, with the two
stochastic integrals the canonical ones for `ℱ`; `Z`, `U` and `φ` are progressive, of finite
energy on `[0, T]` and vanish off it, `ξ` is square integrable, and `Y` is adapted with
right-continuous paths. -/
structure LinearBSDEJ (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ)
    (T : ℝ) (ξ : Ω → ℝ) (φ : Ω → ℝ → ℝ)
    (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) : Prop where
  /-- Each coordinate of `Z` is jointly measurable. -/
  Z_meas : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i)
  /-- Each coordinate of `Z` is progressively measurable. -/
  Z_prog : ∀ i : Fin d, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i
  /-- `Z` vanishes off the horizon. -/
  Z_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0
  /-- Each coordinate of `Z` has finite energy on the horizon. -/
  Z_sq : ∀ i : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤
  /-- `U` is jointly measurable in the sample point, the time and the mark. -/
  U_meas : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2
  /-- `U` is marked progressively measurable. -/
  U_prog : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U s ω e
  /-- `U` vanishes off the horizon. -/
  U_vanish : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0
  /-- `U` has finite marked energy on the horizon. -/
  U_sq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤
  /-- The drift is jointly measurable. -/
  φ_meas : Measurable (Function.uncurry φ)
  /-- The drift is progressively measurable. -/
  φ_prog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ φ
  /-- The drift vanishes off the horizon. -/
  φ_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ ω s = 0
  /-- The drift has finite energy on the horizon. -/
  φ_sq : LevyStochCalc.Brownian.Ito.energy P T φ ≠ ⊤
  /-- The terminal value is square integrable. -/
  ξ_sq : MemLp ξ 2 P
  /-- `Y` is adapted. -/
  Y_adapted : MeasureTheory.Adapted ℱ Y
  /-- Every path of `Y` is right-continuous. -/
  Y_rightCont : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω))
  /-- The backward equation, almost surely at each time of the horizon. -/
  eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
    Y t ω = ξ ω + (∫ s in Set.Icc t T, φ ω s)
      - (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z
            Z_meas Z_prog (sq_int_global_of_vanishing Z_vanish Z_sq) T ω
          - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z
            Z_meas Z_prog (sq_int_global_of_vanishing Z_vanish Z_sq) t ω)
      - (LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
            (fun ω' s e => U s ω' e) U_meas U_prog (marked_sq_int_global_of_vanishing U_vanish U_sq)
            T ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
            (fun ω' s e => U s ω' e) U_meas U_prog (marked_sq_int_global_of_vanishing U_vanish U_sq)
            t ω)

/-- `(Y, Z, U)` solves the linear backward equation with jumps over the augmented joint
filtration `augJoint D` of the driver, with its canonical stochastic integrals. -/
abbrev LinearBSDEJAug (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (T : ℝ) (ξ : Ω → ℝ) (φ : Ω → ℝ → ℝ)
    (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) : Prop :=
  LinearBSDEJ D (augJoint D) D.isBrownianFiltration_aug D.isPoissonFiltration_aug T ξ φ Y Z U

end MVFBSDEJ.WellPosedness.BrownianPoisson
