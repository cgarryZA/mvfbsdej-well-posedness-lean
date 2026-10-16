/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.Energy
import Dissertation.WellPosedness.BrownianPoisson.SupBound

/-!
# The Brownian–Poisson `L²` estimate

Lemma 4.1 of the well-posedness paper: a solution `(Y, Z, U)` of the linear backward equation
with jumps (4.4) with terminal value `ξ` and drift `φ` satisfies

`𝔼 sup_{t ≤ T} |Y_t|² + 𝔼 ∫_0^T (|Z_s|² + ‖U_s‖²_{L²(ν)}) ds
  ≤ (13 e^T + 3T) (𝔼|ξ|² + 𝔼 ∫_0^T |φ_s|² ds)`,

and in particular `Y ∈ S²(0, T)`. The time-zero energy bound gives
`𝔼|Y_0|² + 𝔼 ∫_0^T (|Z_s|² + ‖U_s‖²) ds ≤ e^T (𝔼|ξ|² + 𝔼 ∫_0^T |φ_s|² ds)`, the `S²` bound gives
`𝔼 sup |Y|² ≤ 3 𝔼|Y_0|² + 3T 𝔼 ∫_0^T |φ_s|² ds + 12 𝔼 ∫_0^T (|Z_s|² + ‖U_s‖²) ds`, and adding
the two yields the constant `13 e^T + 3T`.

The estimate holds over any filtration carrying the driver whose null sets lie in its time-`0`
field, whose right-continuation is constant before `0`, and which admits a cross witness.

## Main statements

* `LinearBSDEJ.brownianPoisson_estimate` — the estimate over a general filtration.
* `LinearBSDEJ.lintegral_biSup_sq_lt_top` — `Y ∈ S²(0, T)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.BrownianPoisson

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

/-- **The Brownian–Poisson `L²` estimate** (Lemma 4.1 of the well-posedness paper). A solution of
the linear backward equation with jumps over a filtration carrying the driver satisfies

`𝔼 sup_{t ≤ T} |Y_t|² + 𝔼 ∫_0^T |Z_s|² ds + 𝔼 ∫_0^T ∫_E U_s(e)² ν(de) ds
  ≤ (13 e^T + 3T) (𝔼|ξ|² + 𝔼 ∫_0^T φ_s² ds)`. -/
theorem brownianPoisson_estimate (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
        + (∑ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i))
        + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e)
      ≤ ENNReal.ofReal (13 * Real.exp T + 3 * T)
        * (∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P + Brownian.Ito.energy P T φ) := by
  have hE := lintegral_sq_initial_add_energy_le (h.isItoLevyProcess_clampT hT) 𝒲
    h.stronglyMeasurable_initial (h.memLp_initial hT.le) h.φ_meas h.φ_prog h.φ_vanish h.φ_sq hT
  have hXT : ∫⁻ ω, (‖clampT T Y T ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [h.ae_eq_terminal hT.le] with ω hω
    rw [clampT_apply, min_self, hω]
  rw [hXT, add_assoc] at hE
  have hS := h.lintegral_biSup_sq_le 𝒲 hℱ0 hnull hT
  rw [add_assoc]
  generalize ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P = S at hS ⊢
  generalize ∫⁻ ω, (‖Y 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = a at hS hE
  generalize (∑ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i))
    + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) = b at hS hE ⊢
  generalize ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P = x at hE ⊢
  generalize Brownian.Ito.energy P T φ = f at hS hE ⊢
  have h3 : 3 * a ≤ 13 * a := mul_le_mul_left (by norm_num) a
  calc S + b ≤ 3 * a + 3 * (ENNReal.ofReal T * f) + 12 * b + b := add_le_add hS le_rfl
    _ = 3 * a + 13 * b + 3 * (ENNReal.ofReal T * f) := by ring
    _ ≤ 13 * a + 13 * b + 3 * (ENNReal.ofReal T * f) := by gcongr
    _ = 13 * (a + b) + 3 * (ENNReal.ofReal T * f) := by ring
    _ ≤ 13 * (ENNReal.ofReal (Real.exp T) * (x + f)) + 3 * (ENNReal.ofReal T * (x + f)) := by
      gcongr
      exact le_add_self
    _ = ENNReal.ofReal (13 * Real.exp T + 3 * T) * (x + f) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
      ring

/-- A solution of the linear backward equation with square-integrable data lies in `S²(0, T)`:
its squared running supremum over `[0, T]` has finite expectation. -/
theorem lintegral_biSup_sq_lt_top (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
  refine lt_of_le_of_lt (le_trans le_self_add le_self_add)
    ((h.brownianPoisson_estimate 𝒲 hℱ0 hnull hT).trans_lt ?_)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr
    ⟨LevyStochCalc.Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two h.ξ_sq, h.φ_sq.lt_top⟩)

end LinearBSDEJ

end Dissertation.WellPosedness.BrownianPoisson
