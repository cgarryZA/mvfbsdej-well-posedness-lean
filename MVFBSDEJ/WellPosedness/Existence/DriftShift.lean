/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Existence.TerminalRep
import MVFBSDEJ.WellPosedness.System.Coefficients

/-!
# The linear backward equation with a random drift

The backward equation of the `λ`-system (4.1) at `λ = 0` is, coordinatewise, the linear backward
equation with jumps (4.4) with terminal value `q^g_T` and random drift `q^f`. It is solved by
representing `Ξ = ξ + ∫_0^T φ_s ds` with drift `0`,

`Ξ = Y'_t + ∫_t^T Z_s dW_s + ∫_t^T ∫_E U_s(e) Ñ(ds, de)`,

and shifting by the running integral of the drift: `Y_t = Y'_t − ∫_0^t φ_s ds` gives

`Y_t = ξ + ∫_t^T φ_s ds − ∫_t^T Z_s dW_s − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`.

The running integral is the drift leg `driftLeg φ T`, whose paths are continuous and which is
adapted as soon as the time-`0` field of the filtration contains the null sets. Over a filtration
with the terminal representation property the linear backward equation therefore has a solution
for every square-integrable `ℱ_T`-measurable terminal value and every progressive drift of finite
energy that vanishes off `[0, T]`.

## Main statements

* `LinearBSDEJ.driftShift` — the shift of a representation of `ξ + ∫_0^T φ_s ds` with drift `0`
  solves the equation with terminal value `ξ` and drift `φ`.
* `HasTerminalRep.exists_linearBSDEJ` — existence for a terminal value and a drift.
* `HasTerminalRep.exists_linearBSDEJ_forcing` — existence, coordinatewise, for the terminal and
  driver components of a forcing.
-/

open MeasureTheory Filter Topology

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.System
  LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {ξ : Ω → ℝ}
  {φ : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}

/-- **Shifting a representation by the drift leg.** If `(Y, Z, U)` solves the linear backward
equation with drift `0` and terminal value `ξ + ∫_0^T φ_s ds`, then
`(Y − ∫_0^· φ_s ds, Z, U)` solves it with drift `φ` and terminal value `ξ`, for a jointly
measurable, progressive drift `φ` of finite energy on `[0, T]` that vanishes off it, over a
filtration whose time-`0` field contains the null sets. -/
theorem _root_.MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.driftShift
    (h : LinearBSDEJ D ℱ hℱW hℱN T (fun ω => ξ ω + ∫ s in Set.Icc (0 : ℝ) T, φ ω s)
      (fun _ _ => 0) Y Z U)
    (hφm : Measurable (Function.uncurry φ)) (hφp : Probability.ProgressivelyMeasurable ℱ φ)
    (hφv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ ω s = 0)
    (hφq : Brownian.Ito.energy P T φ ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 ≤ T) :
    LinearBSDEJ D ℱ hℱW hℱN T ξ φ (fun t ω => Y t ω - driftLeg φ T t ω) Z U where
  Z_meas := h.Z_meas
  Z_prog := h.Z_prog
  Z_vanish := h.Z_vanish
  Z_sq := h.Z_sq
  U_meas := h.U_meas
  U_prog := h.U_prog
  U_vanish := h.U_vanish
  U_sq := h.U_sq
  φ_meas := hφm
  φ_prog := hφp
  φ_vanish := hφv
  φ_sq := hφq
  ξ_sq := by
    convert h.ξ_sq.sub (Ito.SecondMoment.memLp_two_setIntegral hφm hT hφq.lt_top) using 1
    funext ω
    simp
  Y_adapted := fun t => (h.Y_adapted t).sub (adapted_driftLeg hφm hφp hφq hnull t)
  Y_rightCont := fun ω t =>
    (h.Y_rightCont ω t).sub (((continuous_driftLeg hφv ω).tendsto t).mono_left
      nhdsWithin_le_nhds)
  eqn t ht := by
    filter_upwards [h.eqn t ht, driftLeg_ae_eq hφm hφq t, driftLeg_ae_eq hφm hφq T,
      driftLeg_sub_ae hφm hφq ht.1 ht.2] with ω h1 h2 h3 h4
    simp only [integral_zero, add_zero] at h1
    linarith

/-- **The linear backward equation with a drift has a solution** over a filtration with the
terminal representation property whose time-`0` field contains the null sets: for every
square-integrable `ξ` that is almost everywhere strongly `ℱ_T`-measurable and every jointly
measurable, progressive drift `φ` of finite energy on `[0, T]` that vanishes off it. -/
theorem HasTerminalRep.exists_linearBSDEJ (hrep : HasTerminalRep D ℱ hℱW hℱN T)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 ≤ T)
    (hξ : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[ℱ T] ξ P)
    (hφm : Measurable (Function.uncurry φ)) (hφp : Probability.ProgressivelyMeasurable ℱ φ)
    (hφv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ ω s = 0)
    (hφq : Brownian.Ito.energy P T φ ≠ ⊤) :
    ∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ),
      LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U := by
  have hIm : StronglyMeasurable[ℱ T] fun ω => ∫ s in Set.Icc (0 : ℝ) T, φ ω s :=
    hφp.stronglyMeasurable_setIntegral measurableSet_Icc Set.Icc_subset_Iic_self volume
  obtain ⟨Y, Z, U, h⟩ := hrep (fun ω => ξ ω + ∫ s in Set.Icc (0 : ℝ) T, φ ω s)
    (hξ.add (Ito.SecondMoment.memLp_two_setIntegral hφm hT hφq.lt_top))
    (hξm.add hIm.aestronglyMeasurable)
  exact ⟨_, Z, U, h.driftShift hφm hφp hφv hφq hnull hT⟩

/-- **The backward equations of the `λ = 0` system have a solution**: for a forcing
`q = (q^b, q^σ, q^h, q^f, q^g_T)` over a filtration with the terminal representation property
whose time-`0` field contains the null sets, each coordinate `k` of the linear backward equation
with terminal value `q^g_{T,k}` and drift `q^f_k` has a solution. -/
theorem HasTerminalRep.exists_linearBSDEJ_forcing {n m : ℕ} {qb : Fin n → Ω → ℝ → ℝ}
    {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ} {qf : Fin m → Ω → ℝ → ℝ}
    {qg : Fin m → Ω → ℝ} (hrep : HasTerminalRep D ℱ hℱW hℱN T)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 ≤ T)
    (hF : Forcing ℱ P ν T qb qσ qh qf qg) :
    ∃ (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ),
      ∀ k, LinearBSDEJ D ℱ hℱW hℱN T (qg k) (qf k) (Y k) (Z k) (U k) := by
  choose Y Z U h using fun k => hrep.exists_linearBSDEJ hnull hT (hF.qg_sq k)
    (hF.qg_meas k).aestronglyMeasurable (hF.qf_meas k) (hF.qf_prog k) (hF.qf_vanish k)
    (hF.qf_sq k)
  exact ⟨Y, Z, U, h⟩

end MVFBSDEJ.WellPosedness.Existence
