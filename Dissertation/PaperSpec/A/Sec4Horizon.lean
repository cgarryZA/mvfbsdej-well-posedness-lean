/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Setting
import Mathlib.Topology.Connected.Separation

/-!
# The horizon remark of §4 of the well-posedness paper

Statement numbers refer to the well-posedness paper at `1f67672`, in the standing setting of §2.
The introduction to §4 observes that the continuation is in the coupling strength, not the
horizon: shortening the horizon does not make the frozen-coefficient map of Lemma 4.2
contractive, since the `(z, u)`-dependence of `σ, h` enters the contraction constant with no
`T`-factor.

## Main definitions

* `Dissertation.PaperSpec.A.BrownianFrozenStep` — the frozen step (4.7)–(4.8) at `λ = 1`, for a
  scalar Brownian driver without jumps.
* `Dissertation.PaperSpec.A.sec4_horizon_not_contractive` — on every horizon, a system of
  Example 5.1(i) whose frozen map does not decrease the distance of a trial from `0`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.WellPosedness.BrownianPoisson LevyStochCalc

universe u w

/-- The frozen step (4.7)–(4.8) of Lemma 4.2 at `λ = 1`, without forcing and from the initial
datum `0`, for `n = m = d = 1` and no jumps (`E` a point, `ν = 0`), over the filtration of §2:
the trial `Θ = (X, Y, Z, U)` is sent to `Θ̄ = (X̄, Ȳ, Z̄, Ū)` when
`X̄_t = ∫_0^t b(s, Θ_s, μ_s) ds + ∫_0^t σ(s, Θ_s, μ_s) dW_s` and
`Ȳ_t = g(X̄_T, Law(X̄_T)) + ∫_t^T f(s, Θ_s, μ_s) ds − ∫_t^T Z̄_s dW_s − ∫_t^T Ū_s Ñ(ds, de)`
almost surely for every `t ∈ [0, T]`, with `μ_s = Law(Θ_s)`. -/
def BrownianFrozenStep {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (0 : Measure Unit)) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T : ℝ) (C : Coeffs (0 : Measure Unit) 1 1 1)
    (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
    (U : Fin 1 → ℝ → Ω → Unit → ℝ) (X' : Fin 1 → ℝ → Ω → ℝ) (Y' : Fin 1 → ℝ → Ω → ℝ)
    (Z' : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U' : Fin 1 → ℝ → Ω → Unit → ℝ) : Prop :=
  (∀ i, LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T 0 (driftProc P T C X Y Z U i) (X' i)
      (diffusionProc P T C X Y Z U i) 0)
  ∧ ∀ k, LinearBSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (terminalVal P T C X' k)
      (driverProc P T C X Y Z U k) (Y' k) (Z' k) (U' k)

/-- §4, the horizon: shortening the horizon does not make the frozen-coefficient map
contractive. For every `T > 0`, `β₁ ≥ 1` and `β₂ > 0`, over the filtration of §2 of a scalar
Brownian driver without jumps, the system of Example 5.1(i) with `σ_c = 0`, `h_c = 0`
(`b = −β₁ y`, `σ = −β₁ z`, `h = −β₁ u`, `f = β₂ x`, `g = x`) satisfies (2.3) and
Assumptions 2.2–2.5 with `ξ₀ = 0`, `G = 1`, `α = 1`, constants that do not depend on `T`; the
frozen step of Lemma 4.2 at `λ = 1` sends `0` to `0` and sends the trial `Θ = (0, 0, 1, 0)` of
`𝕊` to `Θ̄ = (−β₁ W, −β₁ W, −β₁, 0)` in `𝕊`, so that
`0 < ‖Θ − 0‖_𝕊 ≤ ‖Θ̄ − 0‖_𝕊`. -/
def sec4_horizon_not_contractive : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (0 : Measure Unit))
    (h𝒢₀ : 𝒢₀ ≤ mΩ) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T β₁ β₂ : ℝ),
    0 < T → 1 ≤ β₁ → 0 < β₂ →
    JointBorel T (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1) β₁ β₂ 0 0)
    ∧ Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T
        (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1) β₁ β₂ 0 0) 0
    ∧ Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T (β₁ + β₂)
        (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1) β₁ β₂ 0 0)
    ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
    ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 β₁ β₂
        (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1) β₁ β₂ 0 0)
    ∧ BrownianFrozenStep 𝒢₀ D h𝒢₀ hind₀ T
        (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1) β₁ β₂ 0 0) 0 0 0 0 0 0 0 0
    ∧ ∃ (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (X' : Fin 1 → ℝ → Ω → ℝ) (Y' : Fin 1 → ℝ → Ω → ℝ)
        (Z' : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U' : Fin 1 → ℝ → Ω → Unit → ℝ),
        PaperWeakTuple (n := 1) (enlJoint 𝒢₀ D h𝒢₀) P (0 : Measure Unit) T 0 0 Z 0
        ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, Z 0 t ω 0 = 1)
        ∧ PaperWeakTuple (enlJoint 𝒢₀ D h𝒢₀) P (0 : Measure Unit) T X' Y' Z' U'
        ∧ BrownianFrozenStep 𝒢₀ D h𝒢₀ hind₀ T
            (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1) β₁ β₂ 0 0) 0 0 Z 0
            X' Y' Z' U'
        ∧ (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X' 0 t ω = -β₁ * (D.W.W 0).W t ω
            ∧ Y' 0 t ω = -β₁ * (D.W.W 0).W t ω)
        ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ω, Z' 0 t ω 0 = -β₁ ∧ U' 0 t ω () = 0)
        ∧ 0 < supSize (n := 1) P (0 : Measure Unit) T 0 0 Z 0
        ∧ supSize (n := 1) P (0 : Measure Unit) T 0 0 Z 0
          ≤ supSize P (0 : Measure Unit) T X' Y' Z' U'
        ∧ supSize P (0 : Measure Unit) T X' Y' Z' U' ≠ ⊤

end Dissertation.PaperSpec.A
