/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.Compensator

/-!
# The compensation formula and the mean of a compensated integral

For a Poisson random measure `N` with intensity `dt ⊗ ν(de)`, `ν` σ-finite, carried by a
filtration `ℱ`, and a function `ψ` measurable for the marked predictable σ-algebra of `ℱ`:

* if `ψ ≥ 0`, `𝔼 ∫_{(0, T] × E} ψ dN = 𝔼 ∫_0^T ∫_E ψ ν(de) ds` in `[0, ∞]`, (2.1) of the
  well-posedness paper; the library proves it on `(0, T] × A` for `ν(A) < ∞`, and monotone
  convergence along an exhaustion of `E` by sets of finite measure extends it to `E`;
* if `𝔼 ∫_0^T ∫_E |ψ| ν(de) ds < ∞`, the pathwise compensated integral
  `∫_{(0, T] × E} ψ dN − ∫_0^T ∫_E ψ ν(de) ds` has mean zero, (2.2), by (2.1) for the positive and
  negative parts of `ψ`.

## Main statements

* `aemeasurable_and_lintegral_compensation` — (2.1).
* `integrable_and_integral_compensated_eq_zero`, `integral_compensated_eq_zero` — (2.2).
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.BrownianPoisson

open LevyStochCalc

universe u' v' w'

variable {Ω : Type u'} [MeasurableSpace Ω] {E : Type v'} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {N : Poisson.PoissonRandomMeasure.{u', v', w'} P ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **The compensation formula (2.1).** For a filtration carrying the Poisson random measure `N`
and a nonnegative function `ψ` measurable for the marked predictable σ-algebra, the mean lower
integral of `ψ` against `N` on `(0, T] × E` equals its mean iterated integral against
`ds ⊗ ν(de)` on `(0, T] × E`; both inner integrals are almost everywhere measurable in the sample
point. -/
theorem aemeasurable_and_lintegral_compensation (hℱN : Poisson.IsPoissonFiltration N ℱ) (T : ℝ)
    {ψ : Ω × ℝ × E → ℝ≥0∞} (hψ : Measurable[Probability.markedPredictableSigma ℱ ν] ψ) :
    AEMeasurable (fun ω => ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ, ψ (ω, p) ∂(N.N ω)) P
      ∧ AEMeasurable (fun ω => ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ψ (ω, s, e) ∂ν) P
      ∧ ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ, ψ (ω, p) ∂(N.N ω) ∂P
        = ∫⁻ ω, (∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ψ (ω, s, e) ∂ν) ∂P := by
  set A := spanningSets ν
  have hAm : ∀ k, MeasurableSet (A k) := measurableSet_spanningSets ν
  have hAν : ∀ k, ν (A k) ≠ ⊤ := fun k => (measure_spanningSets_lt_top ν k).ne
  have hAmono : Monotone A := monotone_spanningSets ν
  have hU : (⋃ k, Set.Ioc (0 : ℝ) T ×ˢ A k) = Set.Ioc (0 : ℝ) T ×ˢ Set.univ := by
    rw [← Set.prod_iUnion, iUnion_spanningSets]
  have hdir : Directed (· ⊆ ·) fun k => Set.Ioc (0 : ℝ) T ×ˢ A k :=
    (hAmono.directed_le).mono_comp _ fun _ _ h => Set.prod_mono le_rfl h
  have hwin := fun k => Poisson.aemeasurable_and_lintegral_lintegral_slice_eq N hℱN (hAm k)
    (hAν k) T hψ
  have hmono : ∀ (μ : Measure (ℝ × E)) (ω : Ω),
      Monotone fun k => ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A k, ψ (ω, p) ∂μ :=
    fun μ ω _ _ h => lintegral_mono_set (Set.prod_mono le_rfl (hAmono h))
  have hL : (fun ω => ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ, ψ (ω, p) ∂(N.N ω))
      = fun ω => ⨆ k, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A k, ψ (ω, p) ∂(N.N ω) := funext fun ω => by
    rw [← hU, setLIntegral_iUnion_of_directed _ hdir]
  have hR : (fun ω => ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ψ (ω, s, e) ∂ν)
      = fun ω => ⨆ k, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A k, ψ (ω, p)
          ∂(Poisson.referenceIntensity ν) := funext fun ω => by
    have hψω : Measurable fun p : ℝ × E => ψ (ω, p) :=
      (hψ.mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl).comp measurable_prodMk_left
    rw [← setLIntegral_iUnion_of_directed _ hdir, hU, Poisson.referenceIntensity,
      ← Measure.prod_restrict, Measure.restrict_restrict measurableSet_Ioc,
      Set.inter_eq_left.mpr (fun (x : ℝ) (hx : x ∈ Set.Ioc 0 T) => Set.mem_Ici.mpr hx.1.le),
      Measure.restrict_univ, lintegral_prod _ hψω.aemeasurable]
  rw [hL, hR]
  refine ⟨AEMeasurable.iSup fun k => (hwin k).1, AEMeasurable.iSup fun k =>
    (hwin k).2.1.aemeasurable, ?_⟩
  rw [lintegral_iSup' (fun k => (hwin k).1) (Eventually.of_forall fun ω => hmono _ ω),
    lintegral_iSup' (fun k => (hwin k).2.1.aemeasurable)
      (Eventually.of_forall fun ω => hmono _ ω)]
  exact iSup_congr fun k => (hwin k).2.2

/-- The extended norm of a real number is the sum of its positive and negative parts. -/
theorem enorm_eq_ofReal_add_ofReal_neg (x : ℝ) :
    ‖x‖ₑ = ENNReal.ofReal x + ENNReal.ofReal (-x) := by
  rcases le_total 0 x with hx | hx
  · rw [ENNReal.ofReal_of_nonpos (show -x ≤ 0 by linarith), add_zero, Real.enorm_eq_ofReal hx]
  · rw [ENNReal.ofReal_of_nonpos hx, zero_add, ← Real.enorm_eq_ofReal (show 0 ≤ -x by linarith),
      enorm_neg]

/-- The integral of a measurable real function of finite lower integral of the norm is the
difference of the lower integrals of its positive and negative parts. -/
theorem integral_eq_toReal_sub_toReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Measurable f) (hfin : ∫⁻ a, ‖f a‖ₑ ∂μ ≠ ⊤) :
    ∫ a, f a ∂μ = (∫⁻ a, ENNReal.ofReal (f a) ∂μ).toReal
      - (∫⁻ a, ENNReal.ofReal (-f a) ∂μ).toReal :=
  integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    ⟨hf.aestronglyMeasurable, lt_top_iff_ne_top.mpr hfin⟩

/-- For a filtration carrying `N` and a real function `ψ` measurable for the marked predictable
σ-algebra with `𝔼 ∫_0^T ∫_E |ψ| ν(de) ds < ∞`, the pathwise compensated integral
`∫_{(0, T] × E} ψ dN − ∫_0^T ∫_E ψ ν(de) ds` is integrable and has mean zero. -/
theorem integrable_and_integral_compensated_eq_zero (hℱN : Poisson.IsPoissonFiltration N ℱ)
    (T : ℝ) {ψ : Ω × ℝ × E → ℝ} (hψ : Measurable[Probability.markedPredictableSigma ℱ ν] ψ)
    (hfin : ∫⁻ ω, (∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ‖ψ (ω, s, e)‖ₑ ∂ν) ∂P < ⊤) :
    Integrable (fun ω => (∫ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ, ψ (ω, p) ∂(N.N ω))
      - ∫ s in Set.Ioc (0 : ℝ) T, ∫ e, ψ (ω, s, e) ∂ν) P
    ∧ ∫ ω, ((∫ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ, ψ (ω, p) ∂(N.N ω))
      - ∫ s in Set.Ioc (0 : ℝ) T, ∫ e, ψ (ω, s, e) ∂ν) ∂P = 0 := by
  set R : Set (ℝ × E) := Set.Ioc (0 : ℝ) T ×ˢ Set.univ with hR
  set lam : Measure (ℝ × E) := (volume.restrict (Set.Ioc (0 : ℝ) T)).prod ν with hlam
  have hψm : Measurable ψ := hψ.mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hsl : ∀ ω, Measurable fun p : ℝ × E => ψ (ω, p) := fun ω => hψm.comp measurable_prodMk_left
  have hslp : ∀ ω, Measurable fun p : ℝ × E => ENNReal.ofReal (ψ (ω, p)) := fun ω =>
    ENNReal.measurable_ofReal.comp (hsl ω)
  have hslm : ∀ ω, Measurable fun p : ℝ × E => ENNReal.ofReal (-ψ (ω, p)) := fun ω =>
    ENNReal.measurable_ofReal.comp (hsl ω).neg
  have hp := aemeasurable_and_lintegral_compensation (N := N) hℱN T
    (ψ := fun x => ENNReal.ofReal (ψ x)) (ENNReal.measurable_ofReal.comp hψ)
  have hm := aemeasurable_and_lintegral_compensation (N := N) hℱN T
    (ψ := fun x => ENNReal.ofReal (-ψ x)) (ENNReal.measurable_ofReal.comp hψ.neg)
  have hItp : ∀ ω, ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (ψ (ω, s, e)) ∂ν
      = ∫⁻ p, ENNReal.ofReal (ψ (ω, p)) ∂lam := fun ω =>
    (lintegral_prod _ (hslp ω).aemeasurable).symm
  have hItm : ∀ ω, ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (-ψ (ω, s, e)) ∂ν
      = ∫⁻ p, ENNReal.ofReal (-ψ (ω, p)) ∂lam := fun ω =>
    (lintegral_prod _ (hslm ω).aemeasurable).symm
  have hIta : ∀ ω, ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ‖ψ (ω, s, e)‖ₑ ∂ν
      = ∫⁻ p, ‖ψ (ω, p)‖ₑ ∂lam := fun ω =>
    (lintegral_prod _ (hsl ω).enorm.aemeasurable).symm
  have hsplit : ∀ (μ : Measure (ℝ × E)) ω, ∫⁻ p, ‖ψ (ω, p)‖ₑ ∂μ
      = ∫⁻ p, ENNReal.ofReal (ψ (ω, p)) ∂μ + ∫⁻ p, ENNReal.ofReal (-ψ (ω, p)) ∂μ := by
    intro μ ω
    have h := lintegral_add_left (μ := μ) (hslp ω) fun p => ENNReal.ofReal (-ψ (ω, p))
    rw [← h]
    exact lintegral_congr fun p => enorm_eq_ofReal_add_ofReal_neg _
  have hfinp : ∫⁻ ω, (∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (ψ (ω, s, e)) ∂ν) ∂P
      ≠ ⊤ := ne_top_of_le_ne_top hfin.ne (lintegral_mono fun ω => by
        rw [hItp, hIta, hsplit]; exact le_self_add)
  have hfinm : ∫⁻ ω, (∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (-ψ (ω, s, e)) ∂ν) ∂P
      ≠ ⊤ := ne_top_of_le_ne_top hfin.ne (lintegral_mono fun ω => by
        rw [hItm, hIta, hsplit]; exact le_add_self)
  have hfinNp : ∫⁻ ω, ∫⁻ p in R, ENNReal.ofReal (ψ (ω, p)) ∂(N.N ω) ∂P ≠ ⊤ := hp.2.2 ▸ hfinp
  have hfinNm : ∫⁻ ω, ∫⁻ p in R, ENNReal.ofReal (-ψ (ω, p)) ∂(N.N ω) ∂P ≠ ⊤ := hm.2.2 ▸ hfinm
  have hae : ∀ᵐ ω ∂P, ((∫ p in R, ψ (ω, p) ∂(N.N ω))
        - ∫ s in Set.Ioc (0 : ℝ) T, ∫ e, ψ (ω, s, e) ∂ν)
      = ((∫⁻ p in R, ENNReal.ofReal (ψ (ω, p)) ∂(N.N ω)).toReal
          - (∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (ψ (ω, s, e)) ∂ν).toReal)
        - ((∫⁻ p in R, ENNReal.ofReal (-ψ (ω, p)) ∂(N.N ω)).toReal
          - (∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (-ψ (ω, s, e)) ∂ν).toReal) := by
    filter_upwards [ae_lt_top' hp.1 hfinNp, ae_lt_top' hm.1 hfinNm, ae_lt_top' hp.2.1 hfinp,
      ae_lt_top' hm.2.1 hfinm] with ω h1 h2 h3 h4
    have hN : ∫⁻ p in R, ‖ψ (ω, p)‖ₑ ∂(N.N ω) ≠ ⊤ := by
      rw [hsplit]
      exact ENNReal.add_ne_top.mpr ⟨h1.ne, h2.ne⟩
    have hν : ∫⁻ p, ‖ψ (ω, p)‖ₑ ∂lam ≠ ⊤ := by
      rw [hsplit, ← hItp, ← hItm]
      exact ENNReal.add_ne_top.mpr ⟨h3.ne, h4.ne⟩
    have hint : Integrable (fun p => ψ (ω, p)) lam :=
      ⟨(hsl ω).aestronglyMeasurable, lt_top_iff_ne_top.mpr hν⟩
    have e1 := integral_eq_toReal_sub_toReal (μ := (N.N ω).restrict R) (hsl ω) hN
    have e2 := integral_prod _ hint
    have e3 := integral_eq_toReal_sub_toReal (μ := lam) (hsl ω) hν
    rw [e1, ← e2, e3, hItp, hItm]
    ring
  have i1 := integrable_toReal_of_lintegral_ne_top hp.1 hfinNp
  have i2 := integrable_toReal_of_lintegral_ne_top hp.2.1 hfinp
  have i3 := integrable_toReal_of_lintegral_ne_top hm.1 hfinNm
  have i4 := integrable_toReal_of_lintegral_ne_top hm.2.1 hfinm
  have t1 := integral_toReal hp.1 (ae_lt_top' hp.1 hfinNp)
  have t2 := integral_toReal hp.2.1 (ae_lt_top' hp.2.1 hfinp)
  have t3 := integral_toReal hm.1 (ae_lt_top' hm.1 hfinNm)
  have t4 := integral_toReal hm.2.1 (ae_lt_top' hm.2.1 hfinm)
  refine ⟨((i1.sub i2).sub (i3.sub i4)).congr (hae.mono fun ω h => h.symm), ?_⟩
  rw [integral_congr_ae hae, integral_sub, integral_sub, integral_sub, t1, t2, t3, t4, hp.2.2,
    hm.2.2]
  · ring
  all_goals first | exact i1 | exact i2 | exact i3 | exact i4 | exact i1.sub i2 | exact i3.sub i4

/-- **The compensated integral has mean zero (2.2).** For a filtration carrying `N` and a real
function `ψ` measurable for the marked predictable σ-algebra with
`𝔼 ∫_0^T ∫_E |ψ| ν(de) ds < ∞`, the pathwise compensated integral
`∫_{(0, T] × E} ψ dN − ∫_0^T ∫_E ψ ν(de) ds` has mean zero. -/
theorem integral_compensated_eq_zero (hℱN : Poisson.IsPoissonFiltration N ℱ) (T : ℝ)
    {ψ : Ω × ℝ × E → ℝ} (hψ : Measurable[Probability.markedPredictableSigma ℱ ν] ψ)
    (hfin : ∫⁻ ω, (∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ‖ψ (ω, s, e)‖ₑ ∂ν) ∂P < ⊤) :
    ∫ ω, ((∫ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ, ψ (ω, p) ∂(N.N ω))
      - ∫ s in Set.Ioc (0 : ℝ) T, ∫ e, ψ (ω, s, e) ∂ν) ∂P = 0 :=
  (integrable_and_integral_compensated_eq_zero hℱN T hψ hfin).2

end MVFBSDEJ.WellPosedness.BrownianPoisson
