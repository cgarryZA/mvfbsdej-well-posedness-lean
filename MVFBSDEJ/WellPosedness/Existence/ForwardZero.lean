/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.ForwardEq
import MVFBSDEJ.WellPosedness.System.Coefficients
import LevyStochCalc.BSDEJ.CadlagLegs
import LevyStochCalc.BSDEJ.DriftLeg

/-!
# The forward equation of the `λ = 0` system

At `λ = 0` the forward equation of the `λ`-system (4.1) does not involve the unknown: it is the
linear forward equation with jumps

`X_t = ξ₀ + ∫_0^t b_s ds + ∫_0^t σ_s dW_s + ∫_0^t ∫_E γ_s(e) Ñ(ds, de)`,   `t ∈ [0, T]`,

with given integrands `b = q^b`, `σ = q^σ`, `γ = q^h`, and its solution is the right-hand side.
To meet the path regularity of `LinearFSDEJ`, the drift integral is taken to be the drift leg
`driftLeg b T`, which has continuous paths, and each stochastic integral is replaced by its
version that is right-continuous with left limits at every sample point. Those versions are
adapted to the right-continuation `ℱ₊` of the filtration; for a right-continuous filtration
whose right-continuation is constant before `0` and whose time-`0` field contains the null sets
the sum is adapted to `ℱ` itself, given an `ℱ_0`-measurable initial value.

## Main statements

* `exists_linearFSDEJ` — the linear forward equation has a solution for given integrands and
  initial value.
* `Forcing.exists_linearFSDEJ` — each coordinate of the forward equation of the `λ = 0` system
  with the forcing `q^b, q^σ, q^h` has a solution.
-/

open MeasureTheory Filter Topology

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.Stability MVFBSDEJ.WellPosedness.System
  LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

/-- **The linear forward equation has a solution** over a right-continuous filtration whose
right-continuation is constant before `0` and whose time-`0` field contains the null sets: for a
square-integrable `ℱ_0`-measurable initial value `ξ₀` and jointly measurable integrands `b`,
`σ`, `γ` that are progressive (for `γ`, marked progressive), of finite energy on `[0, T]` and
vanish off it. -/
theorem exists_linearFSDEJ [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 ≤ T)
    {ξ₀ : Ω → ℝ} (hξ : MemLp ξ₀ 2 P) (hξm : Measurable[ℱ 0] ξ₀) {b : Ω → ℝ → ℝ}
    (hbm : Measurable (Function.uncurry b)) (hbp : Probability.ProgressivelyMeasurable ℱ b)
    (hbv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0) (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    {σ : ℝ → Ω → (Fin d → ℝ)} (hσm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ s ω j))
    (hσp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => σ s ω j)
    (hσv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → σ s ω = 0)
    (hσq : ∀ j : Fin d, Brownian.Ito.energy P T (fun ω s => σ s ω j) ≠ ⊤)
    {γ : ℝ → Ω → E → ℝ} (hγm : Measurable fun p : Ω × ℝ × E => γ p.2.1 p.1 p.2.2)
    (hγp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => γ s ω e)
    (hγv : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → γ s ω e = 0)
    (hγq : Poisson.Compensated.markedEnergy P ν T (fun ω s e => γ s ω e) ≠ ⊤) :
    ∃ X : ℝ → Ω → ℝ, LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ := by
  obtain ⟨MW, hWa, -, hWe, hWc, -⟩ := exists_cadlag_vectorIntegral_supBound D.W ℱ hℱW σ hσm hσp
    (sq_int_global_of_vanishing hσv hσq) hℱ0 hnull T hT
  obtain ⟨MN, hNa, -, hNe, hNc, -⟩ := exists_cadlag_compensatedIntegral_supBound D.N ℱ hℱN
    (fun ω s e => γ s ω e) hγm hγp (marked_sq_int_global_of_vanishing hγv hγq) hℱ0 hnull T hT
  have hξt : ∀ t, Measurable[ℱ t] ξ₀ := fun t => by
    rcases le_total 0 t with ht | ht
    · exact hξm.mono (ℱ.mono ht) le_rfl
    · exact hξm.mono ((ℱ.le_rightCont 0).trans
        ((hℱ0 t ht).trans (Filtration.IsRightContinuous.RC t))) le_rfl
  exact ⟨fun t ω => ξ₀ ω + driftLeg b T t ω + MW t ω + MN t ω,
    { σ_meas := hσm
      σ_prog := hσp
      σ_vanish := hσv
      σ_sq := hσq
      γ_meas := hγm
      γ_prog := hγp
      γ_vanish := hγv
      γ_sq := hγq
      b_meas := hbm
      b_prog := hbp
      b_vanish := hbv
      b_sq := hbq
      ξ₀_sq := hξ
      X_adapted := fun t => (((hξt t).add (adapted_driftLeg hbm hbp hbq hnull t)).add
        ((hWa t).mono (Filtration.IsRightContinuous.RC t) le_rfl)).add
        ((hNa t).mono (Filtration.IsRightContinuous.RC t) le_rfl)
      X_rightCont := fun ω t => ((tendsto_const_nhds.add (((continuous_driftLeg hbv ω).tendsto
        t).mono_left nhdsWithin_le_nhds)).add (hWc ω t).1).add (hNc ω t).1
      eqn := fun t _ => by
        filter_upwards [driftLeg_ae_eq hbm hbq t, hWe t, hNe t] with ω h1 h2 h3
        rw [h1, h2, h3] }⟩

/-- **The forward equations of the `λ = 0` system have a solution**: for a forcing
`q = (q^b, q^σ, q^h, q^f, q^g_T)` and square-integrable `ℱ_0`-measurable initial values `ξ₀`,
over a right-continuous filtration whose right-continuation is constant before `0` and whose
time-`0` field contains the null sets, each coordinate `i` of the linear forward equation from
`ξ₀_i` with drift `q^b_i`, diffusion vector `q^σ_i` and jump integrand `q^h_i` has a solution. -/
theorem _root_.MVFBSDEJ.WellPosedness.System.Forcing.exists_linearFSDEJ {n m : ℕ}
    [ℱ.IsRightContinuous] {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ}
    {qh : Fin n → ℝ → Ω → E → ℝ} {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
    (hF : Forcing ℱ P ν T qb qσ qh qf qg)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 ≤ T)
    {ξ₀ : Fin n → Ω → ℝ} (hξ : ∀ i, MemLp (ξ₀ i) 2 P) (hξm : ∀ i, Measurable[ℱ 0] (ξ₀ i)) :
    ∃ X : Fin n → ℝ → Ω → ℝ,
      ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (ξ₀ i) (qb i) (X i) (qσ i) (qh i) := by
  choose X hX using fun i => Existence.exists_linearFSDEJ (D := D) (hℱW := hℱW) (hℱN := hℱN)
    hℱ0 hnull hT (hξ i) (hξm i) (hF.qb_meas i) (hF.qb_prog i) (hF.qb_vanish i) (hF.qb_sq i)
    (hF.qσ_meas i) (hF.qσ_prog i) (hF.qσ_vanish i) (hF.qσ_sq i) (hF.qh_meas i) (hF.qh_prog i)
    (hF.qh_vanish i) (hF.qh_sq i)
  exact ⟨X, hX⟩

end MVFBSDEJ.WellPosedness.Existence
