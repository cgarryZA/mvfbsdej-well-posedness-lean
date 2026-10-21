/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.MarkCoding.PullMarks
import MVFBSDEJ.WellPosedness.MarkCoding.Exhaustion
import LevyStochCalc.Poisson.PredictableIntegrand
import LevyStochCalc.Poisson.CompensatedCongr
import LevyStochCalc.Ito.JumpSplittingAllTimes

/-!
# The compensated integral of a pulled-back integrand

Let `N` be a Poisson random measure for a filtration `ℱ`, let `φ : E → F` be measurable with
`ν.map φ` σ-finite, and let `ψ` be an admissible integrand on the image marks. The compensated
integral against `N` of `ψ` read through `φ` is, at every time, almost surely the compensated
integral of `ψ` against the image `(id × φ)_* N`:

`∫_0^T ∫_E ψ(s, φ e) Ñ(ds, de) = ∫_0^T ∫_F ψ(s, f) (id × φ)_* Ñ(ds, df)`.

For a predictable `ψ` carried by a mark window of finite intensity both integrals are pathwise
differences of a set integral against the random measure and one against the intensity, and
these agree by the change of variables along `id × φ`. A predictable `ψ` vanishing off `(0, T]`
is the limit in mean of its cuts to a spanning sequence of `ν.map φ`, and the pulled-back cuts
are the cuts of the pulled-back integrand to the preimages, which cover `E`. A general `ψ` has a
predictable version cut to `(0, T]`, and its pull-back is a version of the pulled-back integrand
since the energy measure of `ν` is carried to that of `ν.map φ`.

## Main statements

* `stochasticIntegral_pullMarks` — the identity at each time, almost surely.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace MVFBSDEJ.WellPosedness.MarkCoding

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

universe u v v' w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {F : Type v'} [MeasurableSpace F] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E}
  [SigmaFinite ν] {φ : E → F}
  (N : PoissonRandomMeasure.{u, v, w} P ν) (hφ : Measurable φ) [SigmaFinite (ν.map φ)]
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)

/-- For a marked predictable integrand on the image marks carried by a mark window of finite
image intensity, the compensated integral against `N` of the pulled-back integrand is almost
surely the compensated integral against the image of `N`. -/
theorem stochasticIntegral_pullMarks_window {ψ : Ω → ℝ → F → ℝ}
    (hψm : Measurable fun p : Ω × ℝ × F => ψ p.1 p.2.1 p.2.2)
    (hψp : MarkedProgressivelyMeasurable ℱ ψ)
    (hψq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂(ν.map φ) ∂volume ∂P < ⊤)
    (hψpred : MarkedPredictable ℱ (ν.map φ) ψ)
    {A : Set F} (hA : MeasurableSet A) (hAν : ν.map φ A ≠ ⊤)
    (hsupp : ∀ ω s e, e ∉ A → ψ ω s e = 0) {T : ℝ} (hT : 0 < T) :
    stochasticIntegral N ℱ hℱ (pullMarks φ ψ) (measurable_pullMarks hφ hψm)
        (markedProgressivelyMeasurable_pullMarks hφ hψp) (sq_int_pullMarks hφ hψm hψq) T
      =ᵐ[P] stochasticIntegral (PoissonRandomMeasure.mapMarks N hφ) ℱ
        (isPoissonFiltration_mapMarks hℱ hφ) ψ hψm hψp hψq T := by
  have hAν' : ν (φ ⁻¹' A) ≠ ⊤ := by rwa [Measure.map_apply hφ hA] at hAν
  have hL := stochasticIntegral_ae_eq_pathwise N ℱ hℱ (pullMarks φ ψ)
    (measurable_pullMarks hφ hψm) (markedProgressivelyMeasurable_pullMarks hφ hψp)
    (sq_int_pullMarks hφ hψm hψq) (hφ hA) (markedPredictable_pullMarks hφ hψpred) hAν'
    (fun ω s e he => hsupp ω s (φ e) he) hT
  have hR := stochasticIntegral_ae_eq_pathwise (PoissonRandomMeasure.mapMarks N hφ) ℱ
    (isPoissonFiltration_mapMarks hℱ hφ) ψ hψm hψp hψq hA hψpred hAν hsupp hT
  refine hL.trans (EventuallyEq.trans (Eventually.of_forall fun ω => ?_) hR.symm)
  have hf : Measurable fun q : ℝ × F => ψ ω q.1 q.2 :=
    hψm.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  have hwin : MeasurableSet (Set.Ioc (0 : ℝ) T ×ˢ A) := measurableSet_Ioc.prod hA
  change _ = (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, ψ ω q.1 q.2 ∂((N.N ω).map (markMap φ)))
      - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, ψ ω q.1 q.2 ∂(referenceIntensity (ν.map φ))
  rw [referenceIntensity_map hφ, setIntegral_map_markMap hφ hf hwin,
    setIntegral_map_markMap hφ hf hwin]
  rfl

/-- For a marked predictable integrand on the image marks vanishing off `(0, T]`, the
compensated integral at `T > 0` against `N` of the pulled-back integrand is almost surely the
compensated integral against the image of `N`. -/
theorem stochasticIntegral_pullMarks_of_predictable {ψ : Ω → ℝ → F → ℝ}
    (hψm : Measurable fun p : Ω × ℝ × F => ψ p.1 p.2.1 p.2.2)
    (hψp : MarkedProgressivelyMeasurable ℱ ψ)
    (hψq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂(ν.map φ) ∂volume ∂P < ⊤)
    (hψpred : MarkedPredictable ℱ (ν.map φ) ψ) {T : ℝ} (hT : 0 < T)
    (hvan : ∀ ω s e, s ∉ Set.Ioc (0 : ℝ) T → ψ ω s e = 0) :
    stochasticIntegral N ℱ hℱ (pullMarks φ ψ) (measurable_pullMarks hφ hψm)
        (markedProgressivelyMeasurable_pullMarks hφ hψp) (sq_int_pullMarks hφ hψm hψq) T
      =ᵐ[P] stochasticIntegral (PoissonRandomMeasure.mapMarks N hφ) ℱ
        (isPoissonFiltration_mapMarks hℱ hφ) ψ hψm hψp hψq T := by
  set S : ℕ → Set F := spanningSets (ν.map φ) with hSdef
  have hS : ∀ k, MeasurableSet (S k) := measurableSet_spanningSets _
  have hSν : ∀ k, ν.map φ (S k) ≠ ⊤ := fun k => (measure_spanningSets_lt_top _ k).ne
  have hkm : ∀ k, Measurable fun p : Ω × ℝ × F => markCut (S k) ψ p.1 p.2.1 p.2.2 :=
    fun k => measurable_markCut hψm (hS k)
  have hkp : ∀ k, MarkedProgressivelyMeasurable ℱ (markCut (S k) ψ) :=
    fun k => hψp.indicator_mark (hS k)
  have hkq : ∀ k, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖markCut (S k) ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂(ν.map φ) ∂volume ∂P < ⊤ :=
    fun k T' hT' => sq_markCut hψq (S k) T' hT'
  have hkpred : ∀ k, MarkedPredictable ℱ (ν.map φ) (markCut (S k) ψ) := by
    intro k
    have hrw : (fun p : Ω × ℝ × F => markCut (S k) ψ p.1 p.2.1 p.2.2)
        = ((Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T ×ˢ S k)).indicator
          fun p : Ω × ℝ × F => ψ p.1 p.2.1 p.2.2 := by
      funext p
      by_cases hs : p.2.1 ∈ Set.Ioc (0 : ℝ) T
      · by_cases he : p.2.2 ∈ S k
        · simp [markCut, hs, he]
        · simp [markCut, he]
      · by_cases he : p.2.2 ∈ S k
        · simp [markCut, hs, he, hvan p.1 p.2.1 p.2.2 hs]
        · simp [markCut, he]
    change Measurable[markedPredictableSigma ℱ (ν.map φ)]
      fun p : Ω × ℝ × F => markCut (S k) ψ p.1 p.2.1 p.2.2
    rw [hrw]
    exact hψpred.indicator (measurableSet_univ_prod_window_self ℱ T (hS k) (hSν k))
  have hwin : ∀ k, stochasticIntegral N ℱ hℱ (pullMarks φ (markCut (S k) ψ))
        (measurable_pullMarks hφ (hkm k)) (markedProgressivelyMeasurable_pullMarks hφ (hkp k))
        (sq_int_pullMarks hφ (hkm k) (hkq k)) T
      =ᵐ[P] stochasticIntegral (PoissonRandomMeasure.mapMarks N hφ) ℱ
        (isPoissonFiltration_mapMarks hℱ hφ) (markCut (S k) ψ) (hkm k) (hkp k) (hkq k) T :=
    fun k => stochasticIntegral_pullMarks_window N hφ ℱ hℱ (hkm k) (hkp k) (hkq k) (hkpred k)
      (hS k) (hSν k) (fun ω s e he => by simp [markCut, he]) hT
  have hcoverF : ⋃ k, S k = Set.univ := iUnion_spanningSets _
  have hcoverE : ⋃ k, φ ⁻¹' S k = Set.univ := by
    rw [← Set.preimage_iUnion, hcoverF, Set.preimage_univ]
  have hR := tendsto_lintegral_sub_markCut (PoissonRandomMeasure.mapMarks N hφ) ℱ
    (isPoissonFiltration_mapMarks hℱ hφ) ψ hψm hψp hψq S hS (monotone_spanningSets _) hcoverF hT
  have hL := tendsto_lintegral_sub_markCut N ℱ hℱ (pullMarks φ ψ) (measurable_pullMarks hφ hψm)
    (markedProgressivelyMeasurable_pullMarks hφ hψp) (sq_int_pullMarks hφ hψm hψq)
    (fun k => φ ⁻¹' S k) (fun k => hφ (hS k))
    (fun a b hab => Set.preimage_mono (monotone_spanningSets _ hab)) hcoverE hT
  have hLk : ∀ k, stochasticIntegral N ℱ hℱ (pullMarks φ (markCut (S k) ψ))
        (measurable_pullMarks hφ (hkm k)) (markedProgressivelyMeasurable_pullMarks hφ (hkp k))
        (sq_int_pullMarks hφ (hkm k) (hkq k)) T
      = stochasticIntegral N ℱ hℱ (markCut (φ ⁻¹' S k) (pullMarks φ ψ))
        (measurable_markCut (measurable_pullMarks hφ hψm) (hφ (hS k)))
        ((markedProgressivelyMeasurable_pullMarks hφ hψp).indicator_mark (hφ (hS k)))
        (fun T' hT' => sq_markCut (sq_int_pullMarks hφ hψm hψq) (φ ⁻¹' S k) T' hT') T :=
    fun k => stochasticIntegral_congr_fun (markCut_pullMarks (S k) ψ).symm _ _ _ _ _ _ T
  refine ae_eq_of_tendsto_lintegral_enorm
    (X := fun k => stochasticIntegral N ℱ hℱ (pullMarks φ (markCut (S k) ψ))
        (measurable_pullMarks hφ (hkm k)) (markedProgressivelyMeasurable_pullMarks hφ (hkp k))
        (sq_int_pullMarks hφ (hkm k) (hkq k)) T)
    (stochasticIntegral_memLp N ℱ hℱ _ _ _ _ T).aestronglyMeasurable
    (stochasticIntegral_memLp _ ℱ (isPoissonFiltration_mapMarks hℱ hφ) _ _ _ _ T).1
    (fun k => (stochasticIntegral_memLp N ℱ hℱ _ _ _ _ T).aestronglyMeasurable) ?_ ?_
  · simp only [hLk]
    exact hL
  · refine hR.congr fun k => lintegral_congr_ae ?_
    filter_upwards [hwin k] with ω hω
    rw [hω, enorm_sub_rev]

/-- **The compensated integral of a pulled-back integrand.** For an admissible integrand `ψ` on
the image marks, at every time `T` the compensated integral against `N` of `ψ` read through `φ`
is almost surely the compensated integral of `ψ` against the image of `N` under `id × φ`. -/
theorem stochasticIntegral_pullMarks {ψ : Ω → ℝ → F → ℝ}
    (hψm : Measurable fun p : Ω × ℝ × F => ψ p.1 p.2.1 p.2.2)
    (hψp : MarkedProgressivelyMeasurable ℱ ψ)
    (hψq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂(ν.map φ) ∂volume ∂P < ⊤) (T : ℝ) :
    stochasticIntegral N ℱ hℱ (pullMarks φ ψ) (measurable_pullMarks hφ hψm)
        (markedProgressivelyMeasurable_pullMarks hφ hψp) (sq_int_pullMarks hφ hψm hψq) T
      =ᵐ[P] stochasticIntegral (PoissonRandomMeasure.mapMarks N hφ) ℱ
        (isPoissonFiltration_mapMarks hℱ hφ) ψ hψm hψp hψq T := by
  have hℱ' := isPoissonFiltration_mapMarks hℱ hφ
  rcases le_or_gt T 0 with hT | hT
  · refine ((stochasticIntegral_ae_eq_process N ℱ hℱ _ _ _ _ T).trans
      (process_ae_zero_of_nonpos N ℱ hℱ _ _ _ _ hT)).trans ?_
    exact ((stochasticIntegral_ae_eq_process _ ℱ hℱ' _ _ _ _ T).trans
      (process_ae_zero_of_nonpos _ ℱ hℱ' _ _ _ _ hT)).symm
  obtain ⟨ψ₀, hψ₀pred, hψ₀ae⟩ :=
    exists_markedPredictable_ae_eq (PoissonRandomMeasure.mapMarks N hφ) hψm hψp hT
      (hψq T hT).ne
  set ψ' : Ω → ℝ → F → ℝ :=
    fun ω s e => (Set.Ioc (0 : ℝ) T).indicator (fun _ => ψ₀ ω s e) s with hψ'def
  have hψ'pred : MarkedPredictable ℱ (ν.map φ) ψ' := markedPredictable_indicator_Ioc hψ₀pred T
  have hψ'm : Measurable fun p : Ω × ℝ × F => ψ' p.1 p.2.1 p.2.2 :=
    hψ'pred.mono (markedPredictableSigma_le ℱ _) le_rfl
  have hψ'p : MarkedProgressivelyMeasurable ℱ ψ' := hψ'pred.markedProgressivelyMeasurable
  have hψ'ae : (fun p : Ω × ℝ × F => ψ p.1 p.2.1 p.2.2)
      =ᵐ[markedEnergyMeasure P (ν.map φ) T] fun p : Ω × ℝ × F => ψ' p.1 p.2.1 p.2.2 := by
    refine hψ₀ae.trans ?_
    filter_upwards [ae_mem_Ioc_markedEnergyMeasure (P := P) (ν := ν.map φ) hT.le] with p hp
    exact (Set.indicator_of_mem hp fun _ => ψ₀ p.1 p.2.1 p.2.2).symm
  have hψ'fin : markedEnergy P (ν.map φ) T ψ' ≠ ⊤ := by
    rw [markedEnergy_eq_eLpNorm_sq hψ'm T, ← eLpNorm_congr_ae hψ'ae,
      ← markedEnergy_eq_eLpNorm_sq hψm T]
    exact (hψq T hT).ne
  have hvan : ∀ ω s e, s ∉ Set.Ioc (0 : ℝ) T → ψ' ω s e = 0 := fun ω s e hs =>
    Set.indicator_of_notMem hs _
  have hψ'q := MarkedHorizonIntegrand.sq_int_global
    (⟨ψ', hψ'm, hψ'p, fun ω s e hs => hvan ω s e fun h => hs ⟨h.1.le, h.2⟩, hψ'fin⟩ :
      MarkedHorizonIntegrand P (ν.map φ) ℱ T)
  have hpullae : (fun p : Ω × ℝ × E => pullMarks φ ψ p.1 p.2.1 p.2.2)
      =ᵐ[markedEnergyMeasure P ν T] fun p : Ω × ℝ × E => pullMarks φ ψ' p.1 p.2.1 p.2.2 := by
    rw [← markedEnergyMeasure_map (P := P) hφ T] at hψ'ae
    exact ae_of_ae_map (measurable_fullMap hφ).aemeasurable hψ'ae
  have h1 := stochasticIntegral_congr_ae N hℱ (pullMarks φ ψ) (pullMarks φ ψ')
    (measurable_pullMarks hφ hψm) (measurable_pullMarks hφ hψ'm)
    (markedProgressivelyMeasurable_pullMarks hφ hψp)
    (markedProgressivelyMeasurable_pullMarks hφ hψ'p) (sq_int_pullMarks hφ hψm hψq)
    (sq_int_pullMarks hφ hψ'm hψ'q) hT hpullae
  have h2 := stochasticIntegral_pullMarks_of_predictable N hφ ℱ hℱ hψ'm hψ'p hψ'q hψ'pred hT
    hvan
  have h3 := stochasticIntegral_congr_ae (PoissonRandomMeasure.mapMarks N hφ) hℱ' ψ ψ' hψm hψ'm
    hψp hψ'p hψq hψ'q hT hψ'ae
  exact h1.trans (h2.trans h3.symm)

end MVFBSDEJ.WellPosedness.MarkCoding
