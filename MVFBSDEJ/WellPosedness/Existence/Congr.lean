/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Existence.ZeroEnergy
import MVFBSDEJ.WellPosedness.System.Solves

/-!
# Changing the forcing by zero energy

The solution predicates of the linear equations with jumps see their integrands only through the
drift integral and the two stochastic integrals, and these do not change when an integrand is
changed by a process of zero energy on the horizon `[0, T]`. Hence a solution of the linear
forward equation `LinearFSDEJ` remains a solution when its drift, diffusion vector and jump
integrand are changed by zero energy, a solution of the linear backward equation `LinearBSDEJ`
remains one when its drift is changed by zero energy and its terminal value almost surely, and a
solution of the `λ`-forced system (4.1) remains one when its forcing is replaced by another
forcing whose difference from it has zero energy and zero terminal second moment — in
particular, when the data size of the difference of the two forcings vanishes.

In the continuation argument this identifies a solution driven by the limit of the forcings with a
solution driven by the forcing that solution generates.

## Main statements

* `LinearFSDEJ.congr` — the forward equation.
* `LinearBSDEJ.congr` — the backward equation.
* `SolvesForced.congr` — the `λ`-forced system, for a forcing changed by zero energy.
* `SolvesForced.congr_of_dataSize` — the same, for a forcing difference of zero data size.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.System LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

/-! ### The linear equations -/

section Linear

variable {ξ₀ ξ ξ' : Ω → ℝ} {b b' φ φ' : Ω → ℝ → ℝ} {X Y : ℝ → Ω → ℝ}
  {σ σ' Z : ℝ → Ω → (Fin d → ℝ)} {γ γ' U : ℝ → Ω → E → ℝ}

/-- **The linear forward equation is unchanged by a change of integrands of zero energy**: if
`X` solves it from `ξ₀` with drift `b`, diffusion vector `σ` and jump integrand `γ`, then it
solves it with `b'`, `σ'`, `γ'`, for jointly measurable, progressive integrands vanishing off
`[0, T]` such that `b − b'`, each coordinate of `σ − σ'` and `γ − γ'` have zero energy on
`[0, T]`. -/
theorem _root_.MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ.congr
    (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ)
    (hbm : Measurable (Function.uncurry b')) (hbp : Probability.ProgressivelyMeasurable ℱ b')
    (hbv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b' ω s = 0)
    (hσm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ' s ω j))
    (hσp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => σ' s ω j)
    (hσv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → σ' s ω = 0)
    (hγm : Measurable fun p : Ω × ℝ × E => γ' p.2.1 p.1 p.2.2)
    (hγp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => γ' s ω e)
    (hγv : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → γ' s ω e = 0)
    (hb : Brownian.Ito.energy P T (fun ω s => b ω s - b' ω s) = 0)
    (hσ : ∀ j : Fin d, Brownian.Ito.energy P T (fun ω s => σ s ω j - σ' s ω j) = 0)
    (hγ : Poisson.Compensated.markedEnergy P ν T (fun ω s e => γ s ω e - γ' s ω e) = 0) :
    LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b' X σ' γ' := by
  have hbq : Brownian.Ito.energy P T b' ≠ ⊤ := by
    rw [energy_eq_of_energy_sub_eq_zero h.b_meas hbm hb]
    exact h.b_sq
  have hσq : ∀ j : Fin d, Brownian.Ito.energy P T (fun ω s => σ' s ω j) ≠ ⊤ := fun j => by
    rw [energy_eq_of_energy_sub_eq_zero (H₁ := fun ω s => σ s ω j) (h.σ_meas j) (hσm j) (hσ j)]
    exact h.σ_sq j
  have hγq : Poisson.Compensated.markedEnergy P ν T (fun ω s e => γ' s ω e) ≠ ⊤ := by
    rw [markedEnergy_eq_of_markedEnergy_sub_eq_zero (φ₁ := fun ω s e => γ s ω e) h.γ_meas hγm
      hγ]
    exact h.γ_sq
  refine
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
      ξ₀_sq := h.ξ₀_sq
      X_adapted := h.X_adapted
      X_rightCont := h.X_rightCont
      eqn := fun t ht => ?_ }
  filter_upwards [h.eqn t ht,
    ae_setIntegral_congr_of_energy h.b_meas hbm hb (Set.Icc_subset_Icc le_rfl ht.2),
    multidimStochasticIntegral_congr_of_energy D.W hℱW h.σ_meas h.σ_prog
      (sq_int_global_of_vanishing h.σ_vanish h.σ_sq) hσm hσp
      (sq_int_global_of_vanishing hσv hσq) hσ ht.2,
    compensatedIntegral_congr_of_markedEnergy D.N hℱN (φ₁ := fun ω s e => γ s ω e)
      (φ₂ := fun ω s e => γ' s ω e) h.γ_meas h.γ_prog
      (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) hγm hγp
      (marked_sq_int_global_of_vanishing hγv hγq) hγ ht.2] with ω e1 e2 e3 e4
  rw [e1, e2, e3, e4]

/-- **The linear backward equation is unchanged by a change of data of zero size**: if
`(Y, Z, U)` solves it with terminal value `ξ` and drift `φ`, then it solves it with a terminal
value `ξ'` equal to `ξ` almost surely and a jointly measurable, progressive drift `φ'` vanishing
off `[0, T]` such that `φ − φ'` has zero energy on `[0, T]`. -/
theorem _root_.MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.congr
    (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (hξ : ξ =ᵐ[P] ξ')
    (hφm : Measurable (Function.uncurry φ')) (hφp : Probability.ProgressivelyMeasurable ℱ φ')
    (hφv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ' ω s = 0)
    (hφ : Brownian.Ito.energy P T (fun ω s => φ ω s - φ' ω s) = 0) :
    LinearBSDEJ D ℱ hℱW hℱN T ξ' φ' Y Z U where
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
  φ_sq := by
    rw [energy_eq_of_energy_sub_eq_zero h.φ_meas hφm hφ]
    exact h.φ_sq
  ξ_sq := h.ξ_sq.ae_eq hξ
  Y_adapted := h.Y_adapted
  Y_rightCont := h.Y_rightCont
  eqn t ht := by
    filter_upwards [h.eqn t ht, hξ,
      ae_setIntegral_congr_of_energy h.φ_meas hφm hφ (Set.Icc_subset_Icc ht.1 le_rfl)]
      with ω e1 e2 e3
    rw [e1, e2, e3]

end Linear

/-! ### Regularity of a changed integrand -/

section Regularity

/-- `A + q'` is jointly measurable when `A + q`, `q` and `q'` are. -/
theorem measurable_add_of_add {A q q' : Ω → ℝ → ℝ}
    (h : Measurable (Function.uncurry fun ω s => A ω s + q ω s))
    (hq : Measurable (Function.uncurry q)) (hq' : Measurable (Function.uncurry q')) :
    Measurable (Function.uncurry fun ω s => A ω s + q' ω s) := by
  have e : (Function.uncurry fun ω s => A ω s + q' ω s)
      = fun p => (Function.uncurry (fun ω s => A ω s + q ω s) p - Function.uncurry q p)
        + Function.uncurry q' p := by
    funext ⟨ω, s⟩
    simp
  rw [e]
  exact (h.sub hq).add hq'

/-- `A + q'` is progressively measurable when `A + q`, `q` and `q'` are. -/
theorem progressivelyMeasurable_add_of_add {A q q' : Ω → ℝ → ℝ}
    (h : Probability.ProgressivelyMeasurable ℱ fun ω s => A ω s + q ω s)
    (hq : Probability.ProgressivelyMeasurable ℱ q)
    (hq' : Probability.ProgressivelyMeasurable ℱ q') :
    Probability.ProgressivelyMeasurable ℱ fun ω s => A ω s + q' ω s := by
  have e : (fun ω s => A ω s + q' ω s) = fun ω s => (A ω s + q ω s - q ω s) + q' ω s := by
    funext ω s
    ring
  rw [e]
  exact (h.sub hq).add hq'

/-- The marked integrand `A + q'` is jointly measurable when `A + q`, `q` and `q'` are. -/
theorem measurable_marked_add_of_add {A q q' : ℝ → Ω → E → ℝ}
    (h : Measurable fun p : Ω × ℝ × E => A p.2.1 p.1 p.2.2 + q p.2.1 p.1 p.2.2)
    (hq : Measurable fun p : Ω × ℝ × E => q p.2.1 p.1 p.2.2)
    (hq' : Measurable fun p : Ω × ℝ × E => q' p.2.1 p.1 p.2.2) :
    Measurable fun p : Ω × ℝ × E => A p.2.1 p.1 p.2.2 + q' p.2.1 p.1 p.2.2 := by
  have e : (fun p : Ω × ℝ × E => A p.2.1 p.1 p.2.2 + q' p.2.1 p.1 p.2.2)
      = fun p => (A p.2.1 p.1 p.2.2 + q p.2.1 p.1 p.2.2 - q p.2.1 p.1 p.2.2)
        + q' p.2.1 p.1 p.2.2 := by
    funext p
    ring
  rw [e]
  exact (h.sub hq).add hq'

/-- The marked integrand `A + q'` is marked progressively measurable when `A + q`, `q` and `q'`
are. -/
theorem markedProgressivelyMeasurable_add_of_add {A q q' : ℝ → Ω → E → ℝ}
    (h : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => A s ω e + q s ω e)
    (hq : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => q s ω e)
    (hq' : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => q' s ω e) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => A s ω e + q' s ω e := by
  have e : (fun ω s e => A s ω e + q' s ω e)
      = fun ω s e => (A s ω e + q s ω e + -1 * q s ω e) + q' s ω e := by
    funext ω s e
    ring
  rw [e]
  exact Poisson.Compensated.markedProgressivelyMeasurable_add
    (Poisson.Compensated.markedProgressivelyMeasurable_add h
      (Poisson.Compensated.markedProgressivelyMeasurable_const_mul hq (-1))) hq'

end Regularity

/-! ### The `λ`-forced system -/

section System

variable [MeasurableSpace.CountablyGenerated E] {n m : ℕ} {lam : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ} {qb qb' : Fin n → Ω → ℝ → ℝ} {qσ qσ' : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh qh' : Fin n → ℝ → Ω → E → ℝ} {qf qf' : Fin m → Ω → ℝ → ℝ} {qg qg' : Fin m → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- **The `λ`-forced system is unchanged by a change of forcing of zero energy**: a solution with
forcing `q` solves the system with any forcing `q'` such that `q^b − q'^b`, `q^σ − q'^σ`,
`q^h − q'^h` and `q^f − q'^f` have zero energy on `[0, T]`, coordinatewise, and `q^g_T = q'^g_T`
almost surely. -/
theorem _root_.MVFBSDEJ.WellPosedness.System.SolvesForced.congr
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ)
    (hF : Forcing ℱ P ν T qb' qσ' qh' qf' qg')
    (hb : ∀ i, Brownian.Ito.energy P T (fun ω s => qb i ω s - qb' i ω s) = 0)
    (hσ : ∀ i j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j - qσ' i s ω j) = 0)
    (hh : ∀ i,
      Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e - qh' i s ω e) = 0)
    (hf : ∀ k, Brownian.Ito.energy P T (fun ω s => qf k ω s - qf' k ω s) = 0)
    (hg : ∀ k, qg k =ᵐ[P] qg' k) :
    SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb' qσ' qh' qf' qg' X Y Z U γ where
  forcing := hF
  jump_rep := h.jump_rep
  fwd i := (h.fwd i).congr
    (measurable_add_of_add (h.fwd i).b_meas (h.forcing.qb_meas i) (hF.qb_meas i))
    (progressivelyMeasurable_add_of_add (h.fwd i).b_prog (h.forcing.qb_prog i) (hF.qb_prog i))
    (fun ω s hs => by simp [driftProc, Set.indicator_of_notMem hs, hF.qb_vanish i ω s hs])
    (fun j => measurable_add_of_add ((h.fwd i).σ_meas j) (h.forcing.qσ_meas i j)
      (hF.qσ_meas i j))
    (fun j => progressivelyMeasurable_add_of_add ((h.fwd i).σ_prog j) (h.forcing.qσ_prog i j)
      (hF.qσ_prog i j))
    (fun ω s hs => by
      funext j
      simp [diffusionProc, Set.indicator_of_notMem hs, hF.qσ_vanish i ω s hs])
    (measurable_marked_add_of_add (A := fun s ω e => lam * jumpProc T γ i s ω e)
      (h.fwd i).γ_meas (h.forcing.qh_meas i) (hF.qh_meas i))
    (markedProgressivelyMeasurable_add_of_add (h.fwd i).γ_prog (h.forcing.qh_prog i)
      (hF.qh_prog i))
    (fun ω s e hs => by simp [jumpProc, Set.indicator_of_notMem hs, hF.qh_vanish i ω s e hs])
    (by simpa only [add_sub_add_left_eq_sub] using hb i)
    (fun j => by simpa only [add_sub_add_left_eq_sub] using hσ i j)
    (by simpa only [add_sub_add_left_eq_sub] using hh i)
  bwd k := (h.bwd k).congr
    (by filter_upwards [hg k] with ω hω; rw [hω])
    (measurable_add_of_add (h.bwd k).φ_meas (h.forcing.qf_meas k) (hF.qf_meas k))
    (progressivelyMeasurable_add_of_add (h.bwd k).φ_prog (h.forcing.qf_prog k) (hF.qf_prog k))
    (fun ω s hs => by simp [driverProc, Set.indicator_of_notMem hs, hF.qf_vanish k ω s hs])
    (by simpa only [add_sub_add_left_eq_sub] using hf k)

/-- **The `λ`-forced system is unchanged by a change of forcing of zero data size**: a solution
with forcing `q` solves the system with any forcing `q'` for which the data size of `q − q'`,
with any initial difference, vanishes. -/
theorem _root_.MVFBSDEJ.WellPosedness.System.SolvesForced.congr_of_dataSize
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ)
    (hF : Forcing ℱ P ν T qb' qσ' qh' qf' qg') {δξ : Fin n → Ω → ℝ}
    (h0 : dataSize P ν T δξ (fun i ω s => qb i ω s - qb' i ω s)
      (fun i s ω j => qσ i s ω j - qσ' i s ω j) (fun i s ω e => qh i s ω e - qh' i s ω e)
      (fun k ω s => qf k ω s - qf' k ω s) (fun k ω => qg k ω - qg' k ω) = 0) :
    SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb' qσ' qh' qf' qg' X Y Z U γ := by
  unfold dataSize at h0
  simp only [add_eq_zero, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies] at h0
  obtain ⟨⟨⟨⟨⟨-, hg⟩, hb⟩, hσ⟩, hh⟩, hf⟩ := h0
  exact h.congr hF hb hσ hh hf (ae_eq_of_lintegral_esq_sub_eq_zero
    (fun k => ((h.forcing.qg_meas k).mono (ℱ.le T)).measurable.aemeasurable)
    (fun k => ((hF.qg_meas k).mono (ℱ.le T)).measurable.aemeasurable) hg)

end System

end MVFBSDEJ.WellPosedness.Existence
