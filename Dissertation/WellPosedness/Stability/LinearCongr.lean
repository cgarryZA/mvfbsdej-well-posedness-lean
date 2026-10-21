/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.Predictable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Dissertation.WellPosedness.Stability.Sub
import LevyStochCalc.Brownian.ItoCellIsometry
import LevyStochCalc.Ito.CompensatedCellIsometry
import Dissertation.WellPosedness.Existence.ForwardZero
import Dissertation.WellPosedness.System.ChannelCoords

/-!
# Linear equations with deterministic integrands and equal data

A deterministic measurable process `(ω, s) ↦ g(s)` is predictable, the predictable σ-algebra
containing the sets `(r, ∞) × Ω`. A solution of the linear forward equation is one for any equal
data.

## Main statements

* `predictable_of_measurable_time` — deterministic integrands are predictable.
* `LinearFSDEJ.of_eq` — the linear forward equation for equal data.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System LevyStochCalc Dissertation.WellPosedness

/-! ### Deterministic integrands -/

section Deterministic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {E : Type*} [MeasurableSpace E] {ν : Measure E}
  {T : ℝ}

/-- A deterministic measurable process is predictable: the predictable σ-algebra contains the
sets `(r, ∞) × Ω`. -/
theorem predictable_of_measurable_time {ℱ : Filtration ℝ mΩ} {g : ℝ → ℝ} (hg : Measurable g) :
    Probability.Predictable ℱ fun (_ : Ω) s => g s := by
  letI : MeasurableSpace (ℝ × Ω) := Probability.predictableSigma ℱ
  have hfst : Measurable (Prod.fst : ℝ × Ω → ℝ) := measurable_of_Ioi fun x => by
    have hset : (Prod.fst : ℝ × Ω → ℝ) ⁻¹' Set.Ioi x = Set.Ioi x ×ˢ Set.univ := by
      ext p
      simp
    rw [hset]
    exact Probability.measurableSet_predictableSigma_Ioi_prod (@MeasurableSet.univ Ω (ℱ x))
  exact (hg.comp hfst).stronglyMeasurable

end Deterministic

/-! ### The forward equation -/

universe u v w

section Forward

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] {n d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T β₁ β₂ : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}

/-- A solution of the linear forward equation is one for equal data. -/
theorem _root_.Dissertation.WellPosedness.Stability.LinearFSDEJ.of_eq {ξ₀ ξ₀' : Ω → ℝ}
    {b b' : Ω → ℝ → ℝ} {X X' : ℝ → Ω → ℝ} {σ σ' : ℝ → Ω → (Fin d → ℝ)} {γ γ' : ℝ → Ω → E → ℝ}
    (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) (hξ : ξ₀ = ξ₀') (hb : b = b') (hX : X = X')
    (hσ : σ = σ') (hγ : γ = γ') : LinearFSDEJ D ℱ hℱW hℱN T ξ₀' b' X' σ' γ' := by
  subst hξ hb hX hσ hγ
  exact h

end Forward

end Dissertation.WellPosedness.Existence
