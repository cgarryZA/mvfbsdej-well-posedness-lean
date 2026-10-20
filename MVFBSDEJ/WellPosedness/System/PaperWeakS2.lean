/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.PaperSolutionSolves

/-!
# Remark 3.2: a solution in `ℍ²_weak` lies in `ℍ²`

Remark 3.2 of the well-posedness paper: a tuple `Θ = (X, Y, Z, U) ∈ ℍ²_weak` satisfying (1.1),
whose `X` and `Y` are only asked `𝔼 ∫_0^T |·|² dt < ∞`, lies in `ℍ²`:
`𝔼 sup_{t ≤ T} |X_t|² < ∞` and `𝔼 sup_{t ≤ T} |Y_t|² < ∞`. For `T > 0` the argument runs as
follows.

* **The data are square integrable.** Since `𝔼 ∫_0^T |X_t|² dt < ∞`, `X_t` is square integrable
  at almost every `t ∈ [0, T]` (`ae_forall_memLp_of_energy_ne_top`), in particular at some `t`,
  and the forward identity at `t`,
  `ξ₀ = X_t − ∫_0^t b(s, Θ_s, μ_s) ds − ∫_0^t σ(s, Θ_s, μ_s) dW_s − ∫_0^t ∫_E γ_s(e) Ñ(ds, de)`,
  writes `ξ₀` as a sum of square-integrable terms: the drift integral by the Cauchy–Schwarz
  inequality, the two stochastic integrals by the isometry. The backward identity at a time `t`
  at which `Y_t` is square integrable does the same for `g(X_T, Law X_T)`
  (`PaperWeakSolution.memLp_initial`, `PaperWeakSolution.memLp_terminal`). The coefficients
  enter only through the conditions of `PaperWeakSolution` under which the integrals of (1.1)
  exist, the measurability and finite energy of the coefficient processes along `Θ`, which the
  paper derives from (2.5) and Assumptions 2.2–2.3 (`PaperWeakTuple.exists_paperAdmissible`);
  the paper assumes `ξ₀` square integrable, and derives the square integrability of
  `g(X_T, Law X_T)` from the `S²` bound on `X` and Assumption 2.3.
* **The `S²` bounds.** Then `Θ`, extended off `[0, T]`, solves `Solves`
  (`PaperWeakSolution.exists_solves`): each coordinate of `X` solves a linear forward equation
  and each coordinate of `(Y, Z, U)` a linear backward equation with square-integrable data, and
  Lemma 4.1 bounds `𝔼 sup_{t ≤ T} |X_t|²` and `𝔼 sup_{t ≤ T} |Y_t|²`
  (`SolvesForced.lintegral_biSup_X_lt_top`, `SolvesForced.lintegral_biSup_Y_lt_top`), over a
  filtration whose null sets lie in its time-`0` field, whose right-continuation is constant
  before `0` and which admits a cross witness.

## Main statements

* `ae_forall_memLp_of_energy_ne_top` — a process of finite energy on `[0, T]` is square
  integrable at almost every time of `[0, T]`.
* `PaperWeakSolution.memLp_initial`, `PaperWeakSolution.memLp_terminal` — for a solution in
  `ℍ²_weak`, `ξ₀` and `g(X_T, Law X_T)` are square integrable.
* `PaperWeakSolution.exists_solves` — a solution in `ℍ²_weak`, extended off `[0, T]`, is a
  solution of `Solves`.
* `PaperWeakSolution.toPaperSolution` — Remark 3.2: a solution in `ℍ²_weak` is a solution in
  `ℍ²`.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

/-! ### Square integrability at almost every time -/

/-- **A process of finite energy on `[0, T]` is square integrable at almost every time**: if each
coordinate of `x` is adapted at every time of `[0, T]`, has right-continuous paths on `[0, T)` and
finite energy on `[0, T]`, then at almost every `t ∈ [0, T]` every coordinate `x_{i,t}` is square
integrable. -/
theorem ae_forall_memLp_of_energy_ne_top {ι : Type*} [Countable ι]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [SFinite P] {T : ℝ}
    {x : ι → ℝ → Ω → ℝ} (hT : 0 ≤ T)
    (hadapt : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (x i t))
    (hrc : ∀ i ω, ∀ t ∈ Set.Ico (0 : ℝ) T,
      Tendsto (fun s => x i s ω) (𝓝[>] t) (𝓝 (x i t ω)))
    (he : ∀ i, Brownian.Ito.energy P T (fun ω s => x i s ω) ≠ ⊤) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i, MemLp (x i t) 2 P := by
  obtain ⟨x', hxe, hxa, hxr⟩ := exists_adapted_rightCont_extension hT hadapt hrc
  have hm : ∀ i, Measurable (Function.uncurry fun ω s => x' i s ω) := fun i =>
    (Probability.measurable_uncurry_of_rightContinuous (hxa i) (hxr i)).comp measurable_swap
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_all_iff.mpr fun i =>
    ae_lintegral_lt_top (φ := fun ω s => (‖x' i s ω‖₊ : ℝ≥0∞) ^ 2)
      ((hm i).nnnorm.coe_nnreal_ennreal.pow_const 2)
      (by rw [← Brownian.Ito.energy, energy_eq_of_eqOn (hxe i)]; exact he i)] with t ht hfin i
  rw [← hxe i t ht]
  exact Brownian.Ito.memLp_two_of_lintegral_sq_lt_top
    ((hxa i t).mono (ℱ.le t) le_rfl).aestronglyMeasurable (hfin i)

/-- **A property holding at almost every time of `[0, T]` holds at some time of `[0, T]`**, for
`T > 0`. -/
theorem exists_mem_Icc_of_ae {T : ℝ} (hT : 0 < T) {p : ℝ → Prop}
    (h : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), p t) :
    ∃ t ∈ Set.Icc (0 : ℝ) T, p t := by
  have hne : volume.restrict (Set.Icc (0 : ℝ) T) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc, sub_zero, ENNReal.ofReal_eq_zero, not_le]
    exact hT
  haveI := ae_neBot.mpr hne
  obtain ⟨t, hp, ht⟩ := (h.and (ae_restrict_mem measurableSet_Icc)).exists
  exact ⟨t, ht, hp⟩

/-! ### The data of a solution in `ℍ²_weak` -/

variable {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ} {C : Coeffs ν n m d}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {ξ₀ : Fin n → Ω → ℝ}

/-- The multidimensional Itô integral of a square-integrable progressive integrand is square
integrable at every time. -/
theorem memLp_multidimStochasticIntegral (σ : ℝ → Ω → Fin d → ℝ)
    (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ s ω j))
    (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => σ s ω j)
    (hq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ) :
    MemLp (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW σ hm hp hq t)
      2 P :=
  memLp_finsetSum Finset.univ fun j _ =>
    Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W j) ℱ (hℱW j) (fun ω s => σ s ω j)
      (hm j) (hp j) (hq j) t

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] [IsProbabilityMeasure P] in
/-- **Cauchy–Schwarz for the drift integral over `[0, t]`**: for a jointly measurable process of
finite energy on `[0, T]` and `t ∈ [0, T]`, `ω ↦ ∫_0^t φ_s(ω) ds` is square integrable. -/
theorem memLp_setIntegral_Icc_zero {φ : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry φ))
    (hq : Brownian.Ito.energy P T φ ≠ ⊤) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    MemLp (fun ω => ∫ s in Set.Icc (0 : ℝ) t, φ ω s) 2 P :=
  Ito.SecondMoment.memLp_two_setIntegral hm ht.1 ((lintegral_mono fun _ =>
    lintegral_mono_set (Set.Icc_subset_Icc le_rfl ht.2)).trans_lt hq.lt_top)

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] [IsProbabilityMeasure P] in
/-- **Cauchy–Schwarz for the drift integral over `[t, T]`**: for a jointly measurable process of
finite energy on `[0, T]` and `t ∈ [0, T]`, `ω ↦ ∫_t^T φ_s(ω) ds` is square integrable. -/
theorem memLp_setIntegral_Icc_horizon {φ : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry φ))
    (hq : Brownian.Ito.energy P T φ ≠ ⊤) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    MemLp (fun ω => ∫ s in Set.Icc t T, φ ω s) 2 P := by
  refine ((memLp_setIntegral_Icc_zero hm hq ⟨ht.1.trans ht.2, le_rfl⟩).sub
    (memLp_setIntegral_Icc_zero hm hq ht)).ae_eq ?_
  filter_upwards [driftLeg_sub_ae hm hq ht.1 ht.2, driftLeg_ae_eq hm hq T, driftLeg_ae_eq hm hq t]
    with ω h1 h2 h3
  simp only [Pi.sub_apply]
  rw [← h2, ← h3, h1]
  ring

namespace PaperWeakSolution

variable (h : PaperWeakSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ) (hT : 0 < T)
include h hT

/-- **The initial datum of a solution in `ℍ²_weak` is square integrable**, for `T > 0`: at some
`t ∈ [0, T]` every coordinate of `X_t` is square integrable, and the forward identity at `t`
writes `ξ₀` as `X_t` minus square-integrable integrals. -/
theorem memLp_initial (i : Fin n) : MemLp (ξ₀ i) 2 P := by
  obtain ⟨t, ht, hXt⟩ := exists_mem_Icc_of_ae hT
    (ae_forall_memLp_of_energy_ne_top hT.le h.X_adapted h.X_rightCont h.X_sq)
  obtain ⟨M, hMae, -, hid⟩ := h.fwd i
  have hM : MemLp (M t) 2 P := (memLp_multidimStochasticIntegral _ _ _ _ t).ae_eq (hMae t ht).symm
  have hN := Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN
    (fun ω' s e => jumpProc T γ i s ω' e) (h.γ_meas i) (h.γ_prog i)
    (marked_sq_int_global_of_vanishing (fun ω s e hs => jumpProc_of_notMem hs i ω e) (h.γ_sq i))
    t
  refine ((((hXt i).sub (memLp_setIntegral_Icc_zero (h.b_meas i) (h.b_sq i) ht)).sub hM).sub
    hN).ae_eq ?_
  filter_upwards [hid] with ω hω
  simp only [Pi.sub_apply]
  rw [hω t ht]
  ring

/-- **The terminal value of a solution in `ℍ²_weak` is square integrable**, for `T > 0`: at some
`t ∈ [0, T]` every coordinate of `Y_t` is square integrable, and the backward identity at `t`
writes `g(X_T, Law X_T)` as `Y_t` plus square-integrable integrals. -/
theorem memLp_terminal (k : Fin m) : MemLp (terminalVal P T C X k) 2 P := by
  obtain ⟨t, ht, hYt⟩ := exists_mem_Icc_of_ae hT
    (ae_forall_memLp_of_energy_ne_top hT.le h.Y_adapted h.Y_rightCont h.Y_sq)
  obtain ⟨M, hMae, -, hid⟩ := h.bwd k
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hM : ∀ s ∈ Set.Icc (0 : ℝ) T, MemLp (M s) 2 P := fun s hs =>
    (memLp_multidimStochasticIntegral _ _ _ _ s).ae_eq (hMae s hs).symm
  have hN := fun s => Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN
    (fun ω' s e => U k s ω' e)
    ((h.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl)
    (h.U_pred k).markedProgressivelyMeasurable
    (marked_sq_int_global_of_vanishing (h.U_vanish k) (h.U_sq k)) s
  refine (((((hYt k).sub (memLp_setIntegral_Icc_horizon (h.f_meas k) (h.f_sq k) ht)).add
    ((hM T hTm).sub (hM t ht))).add ((hN T).sub (hN t)))).ae_eq ?_
  filter_upwards [hid] with ω hω
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [hω t ht]
  ring

/-- **A solution in `ℍ²_weak` solves `Solves`.** For `T > 0`, there are `X'`, `Y'` equal to
`X`, `Y` at every time of `[0, T]` — adapted with right-continuous paths, `0` before `0` and
frozen after `T` — such that `(X', Y', Z, U)` solves the system (1.1) in the sense of `Solves`,
with the same `γ`. -/
theorem exists_solves :
    ∃ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ),
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X i t)
      ∧ (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y k t)
      ∧ Solves D ℱ hℱW hℱN T C ξ₀ X' Y' Z U γ :=
  h.exists_solves_of_memLp hT.le (h.memLp_initial hT) (h.memLp_terminal hT)

end PaperWeakSolution

/-! ### Remark 3.2 -/

/-- **Remark 3.2: a solution in `ℍ²_weak` is a solution in `ℍ²`.** Over a filtration whose null
sets lie in its time-`0` field, whose right-continuation is constant before `0` and which admits
a cross witness, for `T > 0`, a solution `(X, Y, Z, U)` of (1.1) in `ℍ²_weak` satisfies
`𝔼 sup_{t ≤ T} |X_t|² < ∞` and `𝔼 sup_{t ≤ T} |Y_t|² < ∞`, so it is a solution of (1.1) in the
sense of the paper, with the same `γ`. -/
theorem PaperWeakSolution.toPaperSolution (h : PaperWeakSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ := by
  obtain ⟨X', Y', hXe, hYe, hs⟩ := h.exists_solves hT
  refine h.paperSolution ((lintegral_mono fun ω => iSup₂_mono fun t ht => le_of_eq ?_).trans_lt
    (SolvesForced.lintegral_biSup_X_lt_top hs 𝒲 hℱ0 hnull hT))
    ((lintegral_mono fun ω => iSup₂_mono fun t ht => le_of_eq ?_).trans_lt
      (SolvesForced.lintegral_biSup_Y_lt_top hs 𝒲 hℱ0 hnull hT))
  · simp only [hXe _ t ht]
  · simp only [hYe _ t ht]

end MVFBSDEJ.WellPosedness.System
