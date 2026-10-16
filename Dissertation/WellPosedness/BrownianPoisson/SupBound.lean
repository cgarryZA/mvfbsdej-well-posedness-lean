/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.LegIsometry
import Dissertation.WellPosedness.BrownianPoisson.Decomposition

/-!
# The `S²` bound of a solution of the linear backward equation

On one set of full measure a solution of the linear backward equation (4.4) is
`Y_t = Y_0 − A_t + M_t` for every `t ∈ [0, T]`, with `A` the primitive of the drift and `M` the
càdlàg martingale sum of the two stochastic legs. Hence
`sup_{t ≤ T} |Y_t|² ≤ 3 |Y_0|² + 3 sup_{t ≤ T} |A_t|² + 3 sup_{t ≤ T} |M_t|²`. Cauchy–Schwarz
bounds the drift term by `T ∫_0^T φ_s² ds`, and Doob's `L²` maximal inequality together with
the joint isometry bounds the martingale term by `4 (𝔼 ∫_0^T |Z_s|² ds + 𝔼 ∫_0^T ∫_E U_s² dν ds)`:

`𝔼 sup_{t ≤ T} |Y_t|² ≤ 3 𝔼|Y_0|² + 3 T 𝔼 ∫_0^T φ_s² ds
  + 12 (𝔼 ∫_0^T |Z_s|² ds + 𝔼 ∫_0^T ∫_E U_s(e)² ν(de) ds)`.

## Main statements

* `sq_nnnorm_add_add_le` — `|a + b + c|² ≤ 3 (|a|² + |b|² + |c|²)` in `ℝ≥0∞`.
* `lintegral_biSup_sq_driftLeg_le` — the drift primitive's `S²` bound.
* `LinearBSDEJ.lintegral_biSup_sq_le` — the `S²` bound of a solution.
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

/-- The square of a sum of three reals is at most three times the sum of their squares, in
`ℝ≥0∞`. -/
theorem sq_nnnorm_add_add_le (a b c : ℝ) :
    (‖a + b + c‖₊ : ℝ≥0∞) ^ 2
      ≤ 3 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖b‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖c‖₊ : ℝ≥0∞) ^ 2 := by
  have hnn : ‖a + b + c‖₊ ^ 2 ≤ 3 * ‖a‖₊ ^ 2 + 3 * ‖b‖₊ ^ 2 + 3 * ‖c‖₊ ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  calc (‖a + b + c‖₊ : ℝ≥0∞) ^ 2 = ((‖a + b + c‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((3 * ‖a‖₊ ^ 2 + 3 * ‖b‖₊ ^ 2 + 3 * ‖c‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.coe_le_coe.mpr hnn
    _ = 3 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖b‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖c‖₊ : ℝ≥0∞) ^ 2 := by
        push_cast; ring

omit [IsProbabilityMeasure P] in
/-- The squared running supremum over `[0, T]` of the primitive of a drift is at most `T` times
the energy of the drift on `[0, T]`, in expectation. -/
theorem lintegral_biSup_sq_driftLeg_le {b : Ω → ℝ → ℝ} (hbm : Measurable (Function.uncurry b))
    (T : ℝ) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
      ≤ ENNReal.ofReal T * Brownian.Ito.energy P T b := by
  have key : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2)
      ≤ ENNReal.ofReal T * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    by_cases hω : ω ∈ integrablePaths b T
    · have hslice : Measurable (b ω) := hbm.comp (measurable_const.prodMk measurable_id)
      calc (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2)
          = ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖∫ s in Set.Icc (0 : ℝ) t, b ω s‖₊ : ℝ≥0∞) ^ 2 := by
            simp_rw [driftLeg_of_mem hω]
        _ ≤ (∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ∂volume) ^ 2 :=
            BSDEJ.SupBound.biSup_sq_setIntegral_le b T ω
        _ ≤ ENNReal.ofReal T * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
            BSDEJ.SupBound.sq_lintegral_le_ofReal_mul_lintegral_sq T
              hslice.aestronglyMeasurable.enorm
    · simp [driftLeg_of_notMem hω]
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal T
          * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P := lintegral_mono key
    _ = ENNReal.ofReal T * Brownian.Ito.energy P T b :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

namespace LinearBSDEJ

/-- **The `S²` bound.** A solution of the linear backward equation satisfies

`𝔼 sup_{t ≤ T} |Y_t|² ≤ 3 𝔼|Y_0|² + 3 T 𝔼 ∫_0^T φ_s² ds
  + 12 (𝔼 ∫_0^T |Z_s|² ds + 𝔼 ∫_0^T ∫_E U_s(e)² ν(de) ds)`. -/
theorem lintegral_biSup_sq_le (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
      ≤ 3 * ∫⁻ ω, (‖Y 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        + 3 * (ENNReal.ofReal T * Brownian.Ito.energy P T φ)
        + 12 * ((∑ j : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω j))
          + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e)) := by
  obtain ⟨M, hMme, hMae, hMrc, hMmart, hMiso⟩ := h.exists_cadlag_legSum 𝒲 hℱ0 hnull hT
  have hdec := h.ae_forall_eq_decomposition hT hMae hMrc
  have hY0 : Measurable fun ω => (‖Y 0 ω‖₊ : ℝ≥0∞) ^ 2 :=
    ((h.measurable_uncurry.comp (measurable_const.prodMk measurable_id)).nnnorm
      |>.coe_nnreal_ennreal).pow_const 2
  have hAm : Measurable fun ω =>
      ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg φ T t ω‖₊ : ℝ≥0∞) ^ 2 :=
    measurable_biSup_sq_of_rightContinuous hT.le
      (fun t => (measurable_uncurry_driftLeg h.φ_meas).comp
        (measurable_const.prodMk measurable_id))
      fun ω t => ((continuous_driftLeg h.φ_vanish ω).tendsto t).mono_left nhdsWithin_le_nhds
  have hMm : Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2 :=
    measurable_biSup_sq_of_rightContinuous hT.le
      (fun t => hMme.comp (measurable_const.prodMk measurable_id)) hMrc
  have hpt : ∀ᵐ ω ∂P, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2)
      ≤ 3 * (‖Y 0 ω‖₊ : ℝ≥0∞) ^ 2
        + 3 * (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg φ T t ω‖₊ : ℝ≥0∞) ^ 2)
        + 3 * (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2) := by
    filter_upwards [hdec] with ω hω
    refine iSup₂_le fun t ht => ?_
    rw [hω t ht, sub_eq_add_neg]
    refine (sq_nnnorm_add_add_le _ _ _).trans ?_
    rw [nnnorm_neg]
    gcongr
    · exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) =>
        (‖driftLeg φ T t ω‖₊ : ℝ≥0∞) ^ 2) t ht
    · exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => (‖M t ω‖₊ : ℝ≥0∞) ^ 2) t ht
  have hDoob := BSDEJ.SupBound.lintegral_biSup_sq_le_of_martingale hMmart hT.le
    (Eventually.of_forall fun ω => hMrc ω)
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
      ≤ ∫⁻ ω, (3 * (‖Y 0 ω‖₊ : ℝ≥0∞) ^ 2
        + 3 * (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg φ T t ω‖₊ : ℝ≥0∞) ^ 2)
        + 3 * (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2)) ∂P := lintegral_mono_ae hpt
    _ = 3 * ∫⁻ ω, (‖Y 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        + 3 * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg φ T t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
        + 3 * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
      have h12 : Measurable fun ω => 3 * (‖Y 0 ω‖₊ : ℝ≥0∞) ^ 2
          + 3 * (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg φ T t ω‖₊ : ℝ≥0∞) ^ 2) :=
        (hY0.const_mul 3).add (hAm.const_mul 3)
      rw [lintegral_add_left h12, lintegral_add_left (hY0.const_mul 3), lintegral_const_mul _ hY0,
        lintegral_const_mul _ hAm, lintegral_const_mul _ hMm]
    _ ≤ 3 * ∫⁻ ω, (‖Y 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        + 3 * (ENNReal.ofReal T * Brownian.Ito.energy P T φ)
        + 3 * (4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P) := by
      gcongr
      exact lintegral_biSup_sq_driftLeg_le h.φ_meas T
    _ = 3 * ∫⁻ ω, (‖Y 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        + 3 * (ENNReal.ofReal T * Brownian.Ito.energy P T φ)
        + 12 * ((∑ j : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω j))
          + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e)) := by
      rw [hMiso]
      ring

end LinearBSDEJ

end Dissertation.WellPosedness.BrownianPoisson
