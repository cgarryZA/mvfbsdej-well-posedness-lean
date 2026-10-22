/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.PaperWeakSolutionIntSolves

/-!
# Solutions of `SolvesInt` as solutions of `PaperWeakSolutionInt`

A solution of `SolvesInt` with predictable integrands is a solution of `PaperWeakSolutionInt`
(`SolvesInt.paperWeakSolutionInt`), the converse of `PaperWeakSolutionInt.exists_solvesInt`. The
passage is that of `Solves.paperSolution`, with two changes.

* **No `S²` bounds.** `PaperWeakSolutionInt` asks `X` and `Y` for finite energy on `[0, T]` and
  `X_T` for square integrability, which `SolvesInt` carries as they are; so no condition on the
  filtration enters.
* **Pathwise drift integrals.** The drift and the driver of the linear equations of `SolvesInt` have
  almost surely integrable paths, not finite energy. The drift leg `t ↦ ∫_0^t b_s ds` is continuous
  along every such path, and the identities of `LinearFSDEJInt` and `LinearBSDEJInt` hold at every
  time of `[0, T]` on one set of full measure with any version of the Brownian integral with almost
  surely right-continuous paths (`LinearFSDEJInt.ae_forall_eq`, `LinearBSDEJInt.ae_forall_eq`), as
  for `LinearFSDEJ` and `MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ`. With a càdlàg
  version this gives left limits on `(0, T]` (`LinearFSDEJInt.ae_leftLim`,
  `LinearBSDEJInt.ae_leftLim`).

The representative `γ` of `h(s, Θ_s, ·, μ_s)` represents `h(s, Θ⁻_s, ·, μ⁻_s)`, since
`Θ⁻_s = Θ_s` almost surely at almost every time along a tuple of `ℍ²`
(`PaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq`).

## Main statements

* `LinearFSDEJInt.ae_forall_eq`, `LinearBSDEJInt.ae_forall_eq` — the forward and backward
  identities at all times of `[0, T]` on one set of full measure.
* `LinearFSDEJInt.ae_leftLim`, `LinearBSDEJInt.ae_leftLim` — a solution has left limits at every
  time of `(0, T]`, almost surely.
* `SolvesInt.linearFSDEJInt`, `SolvesInt.linearBSDEJInt` — the unforced linear equations of a
  solution of `SolvesInt`.
* `SolvesInt.paperWeakSolutionInt` — a solution of `SolvesInt` with predictable integrands is a
  solution of `PaperWeakSolutionInt`.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

/-! ### The linear equations on one set of full measure -/

section Forward

variable {ξ₀ : Ω → ℝ} {b : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ} {σ : ℝ → Ω → (Fin d → ℝ)}
  {γ : ℝ → Ω → E → ℝ}

/-- **The forward identity on one set of full measure, for an integrable drift.** For a solution
of the linear forward equation of `LinearFSDEJInt` and a version `M` of its Brownian integral
with almost surely right-continuous paths, on a single set of full measure

`X_t = ξ₀ + ∫_{[0, t]} b_s ds + M_t + ∫_0^t ∫_E γ_s(e) Ñ(ds, de)`

at every `t ∈ [0, T]`. -/
theorem _root_.MVFBSDEJ.WellPosedness.Stability.LinearFSDEJInt.ae_forall_eq
    (h : LinearFSDEJInt D ℱ hℱW hℱN T ξ₀ b X σ γ) (hT : 0 ≤ T) {M : ℝ → Ω → ℝ}
    (hMae : ∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P]
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW σ h.σ_meas h.σ_prog
        (sq_int_global_of_vanishing h.σ_vanish h.σ_sq) t)
    (hMrc : ∀ᵐ ω ∂P, ∀ t : ℝ, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      X t ω = ξ₀ ω + (∫ s in Set.Icc (0 : ℝ) t, b ω s) + M t ω
        + Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => γ s ω' e) h.γ_meas
          h.γ_prog (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) t ω := by
  set N := Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => γ s ω' e) h.γ_meas
    h.γ_prog (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) with hN
  have hBrc : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Tendsto (fun s => ξ₀ ω + driftLeg b T s ω + M s ω + N s ω) (𝓝[>] t)
        (𝓝 (ξ₀ ω + driftLeg b T t ω + M t ω + N t ω)) := by
    filter_upwards [hMrc, Poisson.Compensated.stochasticIntegral_cadlag D.N ℱ hℱN _ h.γ_meas
      h.γ_prog (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq)] with ω hM hNc t
    exact ((tendsto_const_nhds.add (((continuous_driftLeg h.b_vanish ω).tendsto t).mono_left
      nhdsWithin_le_nhds)).add (hM t)).add (hNc t).1
  have hkey := ae_forall_Icc_eq_of_ae_rightContinuous (A := X)
    (B := fun t ω => ξ₀ ω + driftLeg b T t ω + M t ω + N t ω) hT
    (fun t ht => by
      filter_upwards [h.eqn t ht, h.b_int, hMae t ht] with ω h1 h2 h3
      rw [h1, driftLeg_of_mem h2 t, h3])
    (ae_of_all _ h.X_rightCont) hBrc
  filter_upwards [hkey, h.b_int] with ω hω hωb t ht
  rw [hω t ht, driftLeg_of_mem hωb t]

/-- **A solution of the linear forward equation with an integrable drift has left limits on
`(0, T]`**, almost surely: along almost every path, `s ↦ X_s` has a left limit at every
`t ∈ (0, T]`. -/
theorem _root_.MVFBSDEJ.WellPosedness.Stability.LinearFSDEJInt.ae_leftLim
    (h : LinearFSDEJInt D ℱ hℱW hℱN T ξ₀ b X σ γ) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 L) := by
  obtain ⟨M, -, hMae, hMcad⟩ := exists_ae_cadlag_brownianIntegral D.W ℱ hℱW σ h.σ_meas h.σ_prog
    (sq_int_global_of_vanishing h.σ_vanish h.σ_sq)
  have hid := h.ae_forall_eq hT (fun t _ => hMae t) (hMcad.mono fun _ hω t => (hω t).1)
  filter_upwards [hid, hMcad, Poisson.Compensated.stochasticIntegral_cadlag D.N ℱ hℱN _ h.γ_meas
    h.γ_prog (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq), h.b_int]
    with ω hω hM hNc hωb t ht
  obtain ⟨LM, hLM⟩ := (hM t).2
  obtain ⟨LN, hLN⟩ := (hNc t).2
  refine ⟨ξ₀ ω + driftLeg b T t ω + LM + LN, ?_⟩
  refine (((tendsto_const_nhds.add (((continuous_driftLeg h.b_vanish ω).tendsto t).mono_left
    nhdsWithin_le_nhds)).add hLM).add hLN).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ht.1] with s hs
  rw [hω s ⟨hs.1.le, hs.2.le.trans ht.2⟩, driftLeg_of_mem hωb s]

end Forward

section Backward

variable {ξ : Ω → ℝ} {φ : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
  {U : ℝ → Ω → E → ℝ}

/-- **The backward identity on one set of full measure, for an integrable drift.** For a
solution of the linear backward equation of `LinearBSDEJInt` and a version `M` of its Brownian
integral with almost surely right-continuous paths, on a single set of full measure

`Y_t = ξ + ∫_{[t, T]} φ_s ds − (M_T − M_t) − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`

at every `t ∈ [0, T]`. -/
theorem _root_.MVFBSDEJ.WellPosedness.Stability.LinearBSDEJInt.ae_forall_eq
    (h : LinearBSDEJInt D ℱ hℱW hℱN T ξ φ Y Z U) (hT : 0 ≤ T) {M : ℝ → Ω → ℝ}
    (hMae : ∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P]
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z h.Z_meas h.Z_prog
        (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) t)
    (hMrc : ∀ᵐ ω ∂P, ∀ t : ℝ, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Y t ω = ξ ω + (∫ s in Set.Icc t T, φ ω s) - (M T ω - M t ω)
        - (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) h.U_meas
            h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) T ω
          - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) h.U_meas
            h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) t ω) := by
  set N := Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) h.U_meas
    h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) with hN
  have hBrc : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Tendsto (fun s => ξ ω + (driftLeg φ T T ω - driftLeg φ T s ω) - (M T ω - M s ω)
          - (N T ω - N s ω)) (𝓝[>] t)
        (𝓝 (ξ ω + (driftLeg φ T T ω - driftLeg φ T t ω) - (M T ω - M t ω)
          - (N T ω - N t ω))) := by
    filter_upwards [hMrc, Poisson.Compensated.stochasticIntegral_cadlag D.N ℱ hℱN _ h.U_meas
      h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq)] with ω hM hNc t
    exact ((tendsto_const_nhds.add (tendsto_const_nhds.sub
      (((continuous_driftLeg h.φ_vanish ω).tendsto t).mono_left nhdsWithin_le_nhds))).sub
      (tendsto_const_nhds.sub (hM t))).sub (tendsto_const_nhds.sub (hNc t).1)
  have hkey := ae_forall_Icc_eq_of_ae_rightContinuous (A := Y)
    (B := fun t ω => ξ ω + (driftLeg φ T T ω - driftLeg φ T t ω) - (M T ω - M t ω)
      - (N T ω - N t ω)) hT
    (fun t ht => by
      filter_upwards [h.eqn t ht, hMae t ht, hMae T ⟨hT, le_rfl⟩, h.φ_int] with ω h1 h2 h3 h4
      rw [h1, h2, h3, setIntegral_Icc_eq_driftLeg_sub h4 ht])
    (ae_of_all _ h.Y_rightCont) hBrc
  filter_upwards [hkey, h.φ_int] with ω hω hωφ t ht
  rw [hω t ht, setIntegral_Icc_eq_driftLeg_sub hωφ ht]

/-- **A solution of the linear backward equation with an integrable drift has left limits on
`(0, T]`**, almost surely: along almost every path, `s ↦ Y_s` has a left limit at every
`t ∈ (0, T]`. -/
theorem _root_.MVFBSDEJ.WellPosedness.Stability.LinearBSDEJInt.ae_leftLim
    (h : LinearBSDEJInt D ℱ hℱW hℱN T ξ φ Y Z U) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 L) := by
  obtain ⟨M, -, hMae, hMcad⟩ := exists_ae_cadlag_brownianIntegral D.W ℱ hℱW Z h.Z_meas h.Z_prog
    (sq_int_global_of_vanishing h.Z_vanish h.Z_sq)
  have hid := h.ae_forall_eq hT (fun t _ => hMae t) (hMcad.mono fun _ hω t => (hω t).1)
  set N := Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) h.U_meas
    h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) with hN
  filter_upwards [hid, hMcad, Poisson.Compensated.stochasticIntegral_cadlag D.N ℱ hℱN _ h.U_meas
    h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq), h.φ_int]
    with ω hω hM hNc hωφ t ht
  obtain ⟨LM, hLM⟩ := (hM t).2
  obtain ⟨LN, hLN⟩ := (hNc t).2
  refine ⟨ξ ω + (driftLeg φ T T ω - driftLeg φ T t ω) - (M T ω - LM) - (N T ω - LN), ?_⟩
  refine (((tendsto_const_nhds.add (tendsto_const_nhds.sub
    (((continuous_driftLeg h.φ_vanish ω).tendsto t).mono_left nhdsWithin_le_nhds))).sub
    (tendsto_const_nhds.sub hLM)).sub (tendsto_const_nhds.sub hLN)).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ht.1] with s hs
  have hsI : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le.trans ht.2⟩
  rw [hω s hsI, setIntegral_Icc_eq_driftLeg_sub hωφ hsI]

end Backward

/-! ### Solutions of `SolvesInt` as solutions of `PaperWeakSolutionInt` -/

variable [MeasurableSpace.CountablyGenerated E] {n m : ℕ} {C : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

namespace SolvesInt

variable (h : SolvesInt D ℱ hℱW hℱN T C ξ₀ X Y Z U γ)
include h

/-- **The forward equations of a solution of `SolvesInt`**: each coordinate of `X` solves the
linear forward equation of `LinearFSDEJInt` from `ξ₀` with the drift, diffusion and jump
processes along the solution. -/
theorem linearFSDEJInt (i : Fin n) :
    LinearFSDEJInt D ℱ hℱW hℱN T (ξ₀ i) (driftProc P T C X Y Z U i) (X i)
      (diffusionProc P T C X Y Z U i) (jumpProc T γ i) := by
  simpa only [one_mul, Pi.zero_apply, add_zero] using h.fwd i

/-- **The backward equations of a solution of `SolvesInt`**: each coordinate of `(Y, Z, U)`
solves the linear backward equation of `LinearBSDEJInt` with terminal value `g(X_T, Law X_T)`
and the driver process along the solution. -/
theorem linearBSDEJInt (k : Fin m) :
    LinearBSDEJInt D ℱ hℱW hℱN T (terminalVal P T C X k) (driverProc P T C X Y Z U k) (Y k)
      (Z k) (U k) := by
  simpa only [one_mul, Pi.zero_apply, add_zero] using h.bwd k

/-- **A solution of `SolvesInt` with predictable integrands is a solution of
`PaperWeakSolutionInt`.** For `T ≥ 0`, a solution `(X, Y, Z, U)` of (1.1) in the sense of
`SolvesInt` with `Z` predictable and `U` marked predictable, coordinatewise, is a solution of
(1.1) in `ℍ²` with pathwise drift and driver integrals in the sense of
`PaperWeakSolutionInt`, with the same `γ`, over any filtration. -/
theorem paperWeakSolutionInt (hZ : ∀ k j, Probability.Predictable ℱ fun ω s => Z k s ω j)
    (hU : ∀ k, Probability.MarkedPredictable ℱ ν fun ω s e => U k s ω e) (hT : 0 ≤ T) :
    PaperWeakSolutionInt D ℱ hℱW hℱN T C ξ₀ X Y Z U γ :=
  have hw : PaperWeakTuple ℱ P ν T X Y Z U :=
    { X_adapted := fun i t _ => (h.linearFSDEJInt i).X_adapted t
      X_rightCont := fun i ω t _ => (h.linearFSDEJInt i).X_rightCont ω t
      X_leftLim := fun i => (h.linearFSDEJInt i).ae_leftLim hT
      X_sq := h.X_sq
      Y_adapted := fun k t _ => (h.linearBSDEJInt k).Y_adapted t
      Y_rightCont := fun k ω t _ => (h.linearBSDEJInt k).Y_rightCont ω t
      Y_leftLim := fun k => (h.linearBSDEJInt k).ae_leftLim hT
      Y_sq := h.Y_sq
      Z_pred := hZ
      Z_vanish := fun k => (h.linearBSDEJInt k).Z_vanish
      Z_sq := fun k => (h.linearBSDEJInt k).Z_sq
      U_pred := hU
      U_vanish := fun k => (h.linearBSDEJInt k).U_vanish
      U_sq := fun k => (h.linearBSDEJInt k).U_sq }
  { toPaperWeakTuple := hw
    b_meas := fun i => (h.linearFSDEJInt i).b_meas
    b_prog := fun i => (h.linearFSDEJInt i).b_prog
    b_int := fun i => (h.linearFSDEJInt i).b_int
    σ_meas := fun i => (h.linearFSDEJInt i).σ_meas
    σ_prog := fun i => (h.linearFSDEJInt i).σ_prog
    σ_sq := fun i => (h.linearFSDEJInt i).σ_sq
    γ_meas := fun i => (h.linearFSDEJInt i).γ_meas
    γ_prog := fun i => (h.linearFSDEJInt i).γ_prog
    γ_sq := fun i => (h.linearFSDEJInt i).γ_sq
    f_meas := fun k => (h.linearBSDEJInt k).φ_meas
    f_prog := fun k => (h.linearBSDEJInt k).φ_prog
    f_int := fun k => (h.linearBSDEJInt k).φ_int
    jump_rep := by
      filter_upwards [h.jump_rep, hw.ae_ae_tupleAt_leftLimProc_eq hT] with s hs heq
      filter_upwards [hs, heq] with ω hω hωeq
      rw [hωeq, lawP2_congr heq]
      exact hω
    XT_sq := h.XT_sq
    fwd := fun i => by
      have hi := h.linearFSDEJInt i
      obtain ⟨M, -, hMae, hMcad⟩ := exists_ae_cadlag_brownianIntegral D.W ℱ hℱW _ hi.σ_meas
        hi.σ_prog (sq_int_global_of_vanishing hi.σ_vanish hi.σ_sq)
      exact ⟨M, fun t _ => hMae t,
        hMcad.mono fun _ hω => ⟨fun t _ => (hω t).1, fun t _ => (hω t).2⟩,
        hi.ae_forall_eq hT (fun t _ => hMae t) (hMcad.mono fun _ hω t => (hω t).1)⟩
    bwd := fun k => by
      have hk := h.linearBSDEJInt k
      obtain ⟨M, -, hMae, hMcad⟩ := exists_ae_cadlag_brownianIntegral D.W ℱ hℱW _ hk.Z_meas
        hk.Z_prog (sq_int_global_of_vanishing hk.Z_vanish hk.Z_sq)
      exact ⟨M, fun t _ => hMae t,
        hMcad.mono fun _ hω => ⟨fun t _ => (hω t).1, fun t _ => (hω t).2⟩,
        hk.ae_forall_eq hT (fun t _ => hMae t) (hMcad.mono fun _ hω t => (hω t).1)⟩ }

end SolvesInt

end MVFBSDEJ.WellPosedness.System
