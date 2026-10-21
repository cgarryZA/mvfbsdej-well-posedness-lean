/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.JumpLeftEnergy
import MVFBSDEJ.WellPosedness.System.WeakTupleProg

/-!
# The linear equations of the frozen step

In the proof of Lemma 4.2 of the well-posedness paper the trial tuple `Θ` is frozen inside the
coefficients, and the step `Θ ↦ Θ̄` solves, coordinatewise, a linear forward equation (4.7) and a
linear backward equation (4.8). This file collects the facts about these linear equations that
the step uses.

* Along a tuple at which the integrals of (1.1) exist (`PaperAdmissible`), the coefficient
  processes and the jump representative, with a zero terminal component, form a forcing.
* A solution of either linear equation set to `0` off a set of full measure that lies in every
  field of the filtration is again a solution; this gives versions with càdlàg paths.
* The integrands `Z`, `U` of a solution of the linear backward equation have predictable versions
  with which it is again a solution.
* Two solutions of the linear forward equation with the same initial value, drift and diffusion,
  and jump integrands agreeing almost everywhere, are indistinguishable on `[0, T]`; two
  representatives of the same jump coefficient give such integrands.
* Two solutions of the linear backward equation with the same drift and almost surely equal
  terminal values are indistinguishable on `[0, T]`, and their integrands differ by zero energy.

## Main statements

* `setLIntegral_lintegral_add_lt_top` — a finite time integral of expectations plus a finite
  deterministic one.
* `PaperAdmissible.forcing` — the coefficient processes along an admissible tuple are a forcing.
* `LinearFSDEJ.indicator`, `LinearBSDEJ.indicator` — the solution off a null set.
* `LinearBSDEJ.exists_predictable` — predictable versions of `Z` and `U`.
* `ae_forcedJump_eq_of_rep` — two representatives give the same forced jump integrand.
* `LinearFSDEJ.ae_forall_Icc_eq` — uniqueness for the linear forward equation.
* `LinearBSDEJ.eq_of_ae_eq_terminal` — uniqueness for the linear backward equation.
* `PaperWeakTuple.setLIntegral_lintegral_channels_lt_top` — the time integral of the expected
  squared channels of a tuple of `ℍ²` with finite running suprema is finite.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Existence LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

/-! ### Time integrals with a deterministic summand -/

/-- If `∫_S 𝔼 f_t dt < ∞` and `c` is almost everywhere measurable on `S` with `∫_S c_t dt < ∞`,
then `∫_S 𝔼 (f_t + c_t) dt < ∞`. -/
theorem setLIntegral_lintegral_add_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : Set ℝ} {f : ℝ → Ω → ℝ≥0∞} {c : ℝ → ℝ≥0∞}
    (hf : ∫⁻ t in S, ∫⁻ ω, f t ω ∂P < ⊤) (hc : AEMeasurable c (volume.restrict S))
    (hc' : ∫⁻ t in S, c t < ⊤) :
    ∫⁻ t in S, ∫⁻ ω, (f t ω + c t) ∂P < ⊤ := by
  have e : ∀ t, ∫⁻ ω, (f t ω + c t) ∂P = ∫⁻ ω, f t ω ∂P + c t := fun t => by
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  simp_rw [e]
  rw [lintegral_add_right' _ hc]
  exact ENNReal.add_lt_top.mpr ⟨hf, hc'⟩

/-! ### The coefficient forcing -/

section Coeff

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  {C : Coeffs ν n m d} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- **The coefficient processes along an admissible tuple form a forcing**: for a tuple at which
the integrals of (1.1) exist with jump representative `γ`, the drift, diffusion, jump and driver
processes `(b(s, Θ_s, μ_s), σ(s, Θ_s, μ_s), γ, f(s, Θ_s, μ_s))`, with terminal component `0`. -/
theorem PaperAdmissible.forcing (h : PaperAdmissible ℱ P T C X Y Z U γ) :
    Forcing ℱ P ν T (driftProc P T C X Y Z U) (diffusionProc P T C X Y Z U) (jumpProc T γ)
      (driverProc P T C X Y Z U) 0 where
  qb_meas := h.b_meas
  qb_prog := h.b_prog
  qb_vanish i ω _ hs := driftProc_of_notMem hs i ω
  qb_sq := h.b_sq
  qσ_meas := h.σ_meas
  qσ_prog := h.σ_prog
  qσ_vanish i ω _ hs := diffusionProc_of_notMem hs i ω
  qσ_sq := h.σ_sq
  qh_meas := h.γ_meas
  qh_prog := h.γ_prog
  qh_vanish i ω _ e hs := jumpProc_of_notMem hs i ω e
  qh_sq := h.γ_sq
  qf_meas := h.f_meas
  qf_prog := h.f_prog
  qf_vanish k ω _ hs := driverProc_of_notMem hs k ω
  qf_sq := h.f_sq
  qg_meas _ := stronglyMeasurable_const
  qg_sq _ := MemLp.zero

omit [MeasurableSpace.CountablyGenerated E] in
/-- **Two representatives of one jump coefficient give one forced jump integrand.** If `γ¹`
and `γ²` both represent, at almost every time of `[0, T]` and almost surely, the same random
element `F_s(ω)` of `L²(ν; ℝⁿ)`, then `λ γ¹_i + q^h_i` and `λ γ²_i + q^h_i`, cut to `[0, T]`, agree
almost everywhere for the marked energy measure, provided the set where they agree is
measurable. -/
theorem ae_forcedJump_eq_of_rep {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ}
    {F : ℝ → Ω → E → EuclideanSpace ℝ (Fin n)} (lam : ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
    (i : Fin n)
    (h₁ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (WithLp.toLp 2 fun i => γ₁ i s ω e : EuclideanSpace ℝ (Fin n))) =ᵐ[ν] F s ω)
    (h₂ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (WithLp.toLp 2 fun i => γ₂ i s ω e : EuclideanSpace ℝ (Fin n))) =ᵐ[ν] F s ω)
    (hm : MeasurableSet {q : Ω × ℝ × E | lam * jumpProc T γ₁ i q.2.1 q.1 q.2.2
      + qh i q.2.1 q.1 q.2.2 = lam * jumpProc T γ₂ i q.2.1 q.1 q.2.2 + qh i q.2.1 q.1 q.2.2}) :
    ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
      lam * jumpProc T γ₁ i q.2.1 q.1 q.2.2 + qh i q.2.1 q.1 q.2.2
        = lam * jumpProc T γ₂ i q.2.1 q.1 q.2.2 + qh i q.2.1 q.1 q.2.2 := by
  refine ae_markedEnergyMeasure_of_ae_ae_ae hm ?_
  filter_upwards [h₁, h₂, ae_restrict_mem measurableSet_Icc] with s e₁ e₂ hs
  filter_upwards [e₁, e₂] with ω f₁ f₂
  filter_upwards [f₁, f₂] with e a b
  have c := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) (a.trans b.symm)
  simp only at c
  simp only [jumpProc, Set.indicator_of_mem hs, c]

end Coeff

/-! ### Versions of solutions of the linear equations -/

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

section Forward

variable {ξ₀ : Ω → ℝ} {b : Ω → ℝ → ℝ} {X X₁ X₂ : ℝ → Ω → ℝ} {σ : ℝ → Ω → (Fin d → ℝ)}
  {γ γ₁ γ₂ : ℝ → Ω → E → ℝ}

/-- A solution of the linear forward equation set to `0` off a set `S` of full measure lying in
every field of the filtration is again a solution. -/
theorem _root_.MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ.indicator
    (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) {S : Set Ω}
    (hSt : ∀ t, MeasurableSet[ℱ t] S) (hS : ∀ᵐ ω ∂P, ω ∈ S) :
    LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b (fun t => S.indicator (X t)) σ γ :=
  { h with
    X_adapted := fun t => (h.X_adapted t).indicator (hSt t)
    X_rightCont := fun ω t => by
      by_cases hω : ω ∈ S
      · simp only [Set.indicator_of_mem hω]
        exact h.X_rightCont ω t
      · simp only [Set.indicator_of_notMem hω]
        exact tendsto_const_nhds
    eqn := fun t ht => by
      filter_upwards [h.eqn t ht, hS] with ω h1 hω
      simp only [Set.indicator_of_mem hω]
      exact h1 }

/-- **Uniqueness for the linear forward equation.** Two solutions with the same initial value,
drift and diffusion, whose jump integrands agree almost everywhere for the marked energy measure
on `[0, T]`, agree at every time of `[0, T]` on one set of full measure. -/
theorem _root_.MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ.ae_forall_Icc_eq
    (h₁ : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X₁ σ γ₁) (h₂ : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X₂ σ γ₂)
    (hγ : ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
      γ₁ q.2.1 q.1 q.2.2 = γ₂ q.2.1 q.1 q.2.2) (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ t ω = X₂ t ω := by
  have h0 : Poisson.Compensated.markedEnergy P ν T (fun ω s e => γ₁ s ω e - γ₂ s ω e) = 0 :=
    markedEnergy_sub_eq_zero_of_ae_eq (φ₁ := fun ω s e => γ₁ s ω e)
      (φ₂ := fun ω s e => γ₂ s ω e) h₁.γ_meas h₂.γ_meas hγ
  refine ae_forall_Icc_eq_of_rightContinuous hT (fun t ht => ?_) h₁.X_rightCont h₂.X_rightCont
  filter_upwards [h₁.eqn t ht, h₂.eqn t ht,
    compensatedIntegral_congr_of_markedEnergy D.N hℱN (φ₁ := fun ω s e => γ₁ s ω e)
      (φ₂ := fun ω s e => γ₂ s ω e) h₁.γ_meas h₁.γ_prog
      (marked_sq_int_global_of_vanishing h₁.γ_vanish h₁.γ_sq) h₂.γ_meas h₂.γ_prog
      (marked_sq_int_global_of_vanishing h₂.γ_vanish h₂.γ_sq) h0 ht.2] with ω e₁ e₂ e₃
  rw [e₁, e₂, e₃]

end Forward

section Backward

variable {ξ ξ₁ ξ₂ : Ω → ℝ} {φ : Ω → ℝ → ℝ} {Y Y₁ Y₂ : ℝ → Ω → ℝ}
  {Z Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U U₁ U₂ : ℝ → Ω → E → ℝ}

/-- A solution of the linear backward equation whose `Y` is set to `0` off a set `S` of full
measure lying in every field of the filtration is again a solution. -/
theorem _root_.MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.indicator
    (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) {S : Set Ω}
    (hSt : ∀ t, MeasurableSet[ℱ t] S) (hS : ∀ᵐ ω ∂P, ω ∈ S) :
    LinearBSDEJ D ℱ hℱW hℱN T ξ φ (fun t => S.indicator (Y t)) Z U :=
  { h with
    Y_adapted := fun t => (h.Y_adapted t).indicator (hSt t)
    Y_rightCont := fun ω t => by
      by_cases hω : ω ∈ S
      · simp only [Set.indicator_of_mem hω]
        exact h.Y_rightCont ω t
      · simp only [Set.indicator_of_notMem hω]
        exact tendsto_const_nhds
    eqn := fun t ht => by
      filter_upwards [h.eqn t ht, hS] with ω h1 hω
      simp only [Set.indicator_of_mem hω]
      exact h1 }

/-- **Predictable versions of the integrands of a solution of the linear backward equation.**
For `T > 0` there are `Z'`, coordinatewise predictable, and `U'`, marked predictable, such that
`(Y, Z', U')` is again a solution. -/
theorem _root_.MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.exists_predictable
    (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (hT : 0 < T) :
    ∃ (Z' : ℝ → Ω → (Fin d → ℝ)) (U' : ℝ → Ω → E → ℝ),
      (∀ j, Probability.Predictable ℱ fun ω s => Z' s ω j)
      ∧ Probability.MarkedPredictable ℱ ν (fun ω s e => U' s ω e)
      ∧ LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z' U' := by
  choose K hKpred hKae using fun j : Fin d =>
    Probability.exists_predictable_ae_eq ℱ (h.Z_meas j) (h.Z_prog j) hT (h.Z_sq j)
  obtain ⟨ψ, hψpred, hψae⟩ :=
    Probability.exists_markedPredictable_ae_eq D.N h.U_meas h.U_prog hT h.U_sq
  set Z' : ℝ → Ω → Fin d → ℝ :=
    fun s ω j => (Set.Ioc (0 : ℝ) T).indicator (fun _ => K j ω s) s with hZ'
  set U' : ℝ → Ω → E → ℝ :=
    fun s ω e => (Set.Ioc (0 : ℝ) T).indicator (fun _ => ψ ω s e) s with hU'
  have hZpred : ∀ j, Probability.Predictable ℱ fun ω s => Z' s ω j := fun j =>
    Brownian.Ito.predictable_indicator_Ioc (hKpred j) hT.le
  have hUpred : Probability.MarkedPredictable ℱ ν fun ω s e => U' s ω e :=
    Poisson.Compensated.markedPredictable_indicator_Ioc hψpred T
  have hZae : ∀ j, ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T), Z p.2 p.1 j = Z' p.2 p.1 j :=
    fun j => by
      filter_upwards [hKae j, Brownian.Ito.ae_mem_Ioc_energyMeasure (P := P) hT.le]
        with p hp hIoc
      exact hp.trans (Set.indicator_of_mem hIoc fun _ => K j p.1 p.2).symm
  have hUae : ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
      U q.2.1 q.1 q.2.2 = U' q.2.1 q.1 q.2.2 := by
    filter_upwards [hψae,
      Poisson.Compensated.ae_mem_Ioc_markedEnergyMeasure (P := P) (ν := ν) hT.le] with q hq hIoc
    exact hq.trans (Set.indicator_of_mem hIoc fun _ => ψ q.1 q.2.1 q.2.2).symm
  have hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z' s ω j) := fun j =>
    Brownian.Ito.measurable_uncurry_of_predictable (hZpred j)
  have hUm : Measurable fun p : Ω × ℝ × E => U' p.2.1 p.1 p.2.2 :=
    hUpred.mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  refine ⟨Z', U', hZpred, hUpred, h.congr_integrands h.φ_meas h.φ_prog h.φ_vanish hZm
    (fun j => progressivelyMeasurable_indicator_Ioc (hKpred j) hT.le)
    (fun ω s hs => funext fun j => Set.indicator_of_notMem (fun hs' => hs ⟨hs'.1.le, hs'.2⟩) _)
    hUm hUpred.markedProgressivelyMeasurable
    (fun ω s e hs => Set.indicator_of_notMem (fun hs' => hs ⟨hs'.1.le, hs'.2⟩) _)
    (energy_sub_eq_zero_of_ae_eq h.φ_meas h.φ_meas (ae_of_all _ fun _ => rfl))
    (fun j => energy_sub_eq_zero_of_ae_eq (h.Z_meas j) (hZm j) (hZae j))
    (markedEnergy_sub_eq_zero_of_ae_eq (φ₁ := fun ω s e => U s ω e)
      (φ₂ := fun ω s e => U' s ω e) h.U_meas hUm hUae)⟩

/-- **Uniqueness for the linear backward equation.** Two solutions with the same drift and almost
surely equal terminal values, over a filtration carrying the driver, agree at every time of
`[0, T]` on one set of full measure, and the differences of their integrands have zero energy on
`[0, T]`. -/
theorem _root_.MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.eq_of_ae_eq_terminal
    (h₁ : LinearBSDEJ D ℱ hℱW hℱN T ξ₁ φ Y₁ Z₁ U₁) (h₂ : LinearBSDEJ D ℱ hℱW hℱN T ξ₂ φ Y₂ Z₂ U₂)
    (hξ : ξ₁ =ᵐ[P] ξ₂) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ t ω = Y₂ t ω)
      ∧ (∀ j, Brownian.Ito.energy P T (fun ω s => Z₁ s ω j - Z₂ s ω j) = 0)
      ∧ Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ s ω e - U₂ s ω e) = 0 := by
  have hD := (h₁.sub h₂).brownianPoisson_estimate 𝒲 hℱ0 hnull hT
  beta_reduce at hD
  have hξ0 : ∫⁻ ω, (‖ξ₁ ω - ξ₂ ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := by
    rw [lintegral_congr_ae (g := fun _ => 0) (hξ.mono fun ω hω => by simp [hω])]
    simp
  have hφ0 : Brownian.Ito.energy P T (fun ω s => φ ω s - φ ω s) = 0 := by
    simp [Brownian.Ito.energy]
  rw [hξ0, hφ0, add_zero, mul_zero, nonpos_iff_eq_zero] at hD
  obtain ⟨hSZ, hU⟩ := add_eq_zero.mp hD
  obtain ⟨hS, hZ⟩ := add_eq_zero.mp hSZ
  refine ⟨?_, fun j => (Finset.sum_eq_zero_iff.mp hZ) j (Finset.mem_univ j), hU⟩
  have hm := measurable_biSup_sq_of_rightContinuous hT.le (M := fun t ω => Y₁ t ω - Y₂ t ω)
    (fun t => ((h₁.Y_adapted t).mono (ℱ.le t) le_rfl).sub ((h₂.Y_adapted t).mono (ℱ.le t) le_rfl))
    (fun ω t => (h₁.Y_rightCont ω t).sub (h₂.Y_rightCont ω t))
  filter_upwards [(lintegral_eq_zero_iff hm).mp hS] with ω hω t ht
  have hle := le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) =>
    (‖Y₁ t ω - Y₂ t ω‖₊ : ℝ≥0∞) ^ 2) t ht
  rw [show (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y₁ t ω - Y₂ t ω‖₊ : ℝ≥0∞) ^ 2) = 0 from hω,
    nonpos_iff_eq_zero] at hle
  have h0 : Y₁ t ω - Y₂ t ω = 0 := by simpa using hle
  exact sub_eq_zero.mp h0

end Backward

/-! ### Tuples of `ℍ²` with finite running suprema -/

variable [MeasurableSpace.CountablyGenerated E] {n m : ℕ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ}

omit [MeasurableSpace.CountablyGenerated E] in
/-- **The expected squared channels of a tuple of `ℍ²` have finite time integral** when the
running suprema of `X` and `Y` have finite expectation:
`∫_0^T 𝔼(|X_s|² + |Y_s|² + |Z_s|²_F + ‖U_s‖²_{L²(ν)}) ds < ∞`. -/
theorem PaperWeakTuple.setLIntegral_lintegral_channels_lt_top
    (hΘ : PaperWeakTuple ℱ P ν T X Y Z U) (hT : 0 ≤ T)
    (hX : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P < ⊤)
    (hY : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y k t ω)) ∂P < ⊤) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, (‖(tupleAt ν X Y Z U s ω).1‖ₑ ^ 2
      + ‖(tupleAt ν X Y Z U s ω).2.1‖ₑ ^ 2 + ‖(tupleAt ν X Y Z U s ω).2.2.1‖ₑ ^ 2
      + ‖(tupleAt ν X Y Z U s ω).2.2.2‖ₑ ^ 2) ∂P < ⊤ := by
  obtain ⟨X', Y', hXe, hYe, hP, -, -⟩ := hΘ.exists_progTuple hT
  have hsup : ∀ {ι : Type} [Fintype ι] {x x' : ι → ℝ → Ω → ℝ},
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, x' i t = x i t) →
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x' i t ω)) ∂P
        = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂P := by
    intro ι _ x x' h
    refine lintegral_congr fun ω => iSup_congr fun t => iSup_congr fun ht => ?_
    simp only [fun i => congrFun (h i t ht) ω]
  calc _ = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω,
          ENNReal.ofReal (channelSq (tupleAt ν X' Y' Z U s ω)) ∂P :=
        setLIntegral_congr_fun measurableSet_Icc fun s hs => lintegral_congr fun ω => by
          rw [tupleAt_eq_of_eqOn hXe hYe hs, ofReal_channelSq]
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, (esq (fun i => X' i s ω) + esq (fun k => Y' k s ω)
          + ∑ k, esq (Z k s ω) + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P :=
        lintegral_mono fun s => lintegral_mono fun ω => ofReal_channelSq_tupleAt_le s ω
    _ ≤ _ := setLIntegral_lintegral_coords_le hP.measurable_X hP.measurable_Y hP.Z_meas hP.U_meas
    _ < ⊤ := by
        rw [hsup hXe, hsup hYe]
        refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
          ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hX,
            ENNReal.mul_lt_top ENNReal.ofReal_lt_top hY⟩, ENNReal.add_lt_top.mpr
          ⟨ENNReal.sum_lt_top.mpr fun k _ => ENNReal.sum_lt_top.mpr fun j _ =>
            (hΘ.Z_sq k j).lt_top, ENNReal.sum_lt_top.mpr fun k _ => (hΘ.U_sq k).lt_top⟩⟩

end MVFBSDEJ.WellPosedness.System
