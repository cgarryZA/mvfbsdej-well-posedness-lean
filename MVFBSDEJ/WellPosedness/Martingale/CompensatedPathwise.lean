/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.BrownianPoisson.Compensation
import MVFBSDEJ.WellPosedness.Martingale.LocalIntegral
import LevyStochCalc.Ito.JumpCoefficientPredictableCriteria

/-!
# The compensated integral of an integrable predictable integrand is pathwise

For a marked predictable integrand `ψ` of finite energy, vanishing at the nonpositive times, with
`𝔼 ∫_0^t ∫_E |ψ_s(e)| ν(de) ds < ∞`, the compensated integral at `t > 0` is almost surely

`∫_0^t ∫_E ψ dÑ = ∫_{(0, t] × E} ψ dN − ∫_0^t ∫_E ψ ν(de) ds`.

The library gives this on windows `(0, t] × E_k` of finite mark measure. On the windows the
integrals converge in `L²` by the isometry, and the pathwise forms converge in `L¹` by the
compensation formula and dominated convergence, so the two limits agree.

## Main statements

* `MVFBSDEJ.WellPosedness.Martingale.lintegral_count_eq_lintegral_ref` — the compensation
  formula (2.1) with the reference intensity.
* `MVFBSDEJ.WellPosedness.Martingale.stochasticIntegral_ae_eq_pathwise_of_integrable` — the
  pathwise form.
-/

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal Topology

namespace MVFBSDEJ.WellPosedness.Martingale

open LevyStochCalc LevyStochCalc.Probability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **The compensation formula (2.1) against the reference intensity.** For a nonnegative marked
predictable `Ψ`, the integral against `N` over `(0, T] × E` is almost everywhere measurable and
has the mean of the integral against the reference intensity. -/
theorem lintegral_count_eq_lintegral_ref (hℱ : Poisson.IsPoissonFiltration N ℱ) (T : ℝ)
    {Ψ : Ω × ℝ × E → ℝ≥0∞} (hΨ : Measurable[markedPredictableSigma ℱ ν] Ψ) :
    AEMeasurable (fun ω => ∫⁻ q in Ioc (0 : ℝ) T ×ˢ (univ : Set E), Ψ (ω, q) ∂(N.N ω)) P
      ∧ ∫⁻ ω, ∫⁻ q in Ioc (0 : ℝ) T ×ˢ (univ : Set E), Ψ (ω, q) ∂(N.N ω) ∂P
        = ∫⁻ ω, ∫⁻ q in Ioc (0 : ℝ) T ×ˢ (univ : Set E), Ψ (ω, q)
            ∂(Poisson.referenceIntensity ν) ∂P := by
  obtain ⟨h1, -, h3⟩ := BrownianPoisson.aemeasurable_and_lintegral_compensation (N := N) hℱ T hΨ
  have hΨm : Measurable Ψ := hΨ.mono (markedPredictableSigma_le ℱ ν) le_rfl
  refine ⟨h1, h3.trans (lintegral_congr fun ω => ?_)⟩
  rw [Poisson.lintegral_referenceIntensity_window (f := fun q : ℝ × E => Ψ (ω, q))
    (hΨm.comp measurable_prodMk_left) univ T]
  simp only [Measure.restrict_univ]

variable (hℱ : Poisson.IsPoissonFiltration N ℱ)

/-- **The `L²` compensated integral of an integrable predictable integrand is pathwise.** For a
marked predictable `ψ` of finite energy, vanishing at the nonpositive times, with
`𝔼 ∫_{(0, t] × E} |ψ| d(ds ν) < ∞` and `t > 0`, almost surely
`∫_0^t ∫_E ψ dÑ = ∫_{(0, t] × E} ψ dN − ∫_{(0, t] × E} ψ d(ds ν)`. -/
theorem stochasticIntegral_ae_eq_pathwise_of_integrable {ψ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hp : MarkedProgressivelyMeasurable ℱ ψ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hpred : MarkedPredictable ℱ ν ψ) (h0 : ∀ ω s e, s ≤ 0 → ψ ω s e = 0) {t : ℝ} (ht : 0 < t)
    (hL1 : ∫⁻ ω, ∫⁻ q in Ioc (0 : ℝ) t ×ˢ (univ : Set E), ‖ψ ω q.1 q.2‖ₑ
      ∂(Poisson.referenceIntensity ν) ∂P ≠ ⊤) :
    Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hm hp hq t =ᵐ[P] fun ω =>
      (∫ q in Ioc (0 : ℝ) t ×ˢ (univ : Set E), ψ ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Ioc (0 : ℝ) t ×ˢ (univ : Set E), ψ ω q.1 q.2
            ∂(Poisson.referenceIntensity ν) := by
  classical
  set A : ℕ → Set E := spanningSets ν with hAdef
  have hAm : ∀ k, MeasurableSet (A k) := measurableSet_spanningSets ν
  have hAν : ∀ k, ν (A k) ≠ ⊤ := fun k => (measure_spanningSets_lt_top ν k).ne
  set W : Set (ℝ × E) := Ioc (0 : ℝ) t ×ˢ (univ : Set E) with hWdef
  set Wk : ℕ → Set (ℝ × E) := fun k => Ioc (0 : ℝ) t ×ˢ A k with hWkdef
  have hWm : MeasurableSet W := measurableSet_Ioc.prod MeasurableSet.univ
  have hWkm : ∀ k, MeasurableSet (Wk k) := fun k => measurableSet_Ioc.prod (hAm k)
  have hWkmono : Monotone Wk := fun k k' h =>
    prod_mono le_rfl (monotone_spanningSets ν h)
  have hWU : (⋃ k, Wk k) = W := by
    simp only [hWkdef, hWdef, ← prod_iUnion, hAdef, iUnion_spanningSets]
  set Ref : Measure (ℝ × E) := Poisson.referenceIntensity ν with hRefdef
  have hψω : ∀ ω, Measurable fun q : ℝ × E => ψ ω q.1 q.2 := fun ω =>
    hm.comp (measurable_const.prodMk measurable_id)
  -- the positive times and the windows in the marked predictable σ-algebra
  have hpos := measurableSet_markedPredictableSigma_pos (Ω := Ω) (E := E) ℱ ν
  have hposA : ∀ k, MeasurableSet[markedPredictableSigma ℱ ν]
      {p : Ω × ℝ × E | 0 < p.2.1 ∧ p.2.2 ∈ A k} := by
    intro k
    have hrw : {p : Ω × ℝ × E | 0 < p.2.1 ∧ p.2.2 ∈ A k}
        = ⋃ n : ℕ, (univ : Set Ω) ×ˢ (Ioc (0 : ℝ) n ×ˢ A k) := by
      ext p
      simp only [mem_setOf_eq, mem_iUnion, mem_prod, mem_univ, true_and, mem_Ioc]
      constructor
      · rintro ⟨hp0, hpA⟩
        obtain ⟨n, hn⟩ := exists_nat_ge p.2.1
        exact ⟨n, ⟨hp0, hn⟩, hpA⟩
      · rintro ⟨n, ⟨hp0, -⟩, hpA⟩
        exact ⟨hp0, hpA⟩
    rw [hrw]
    exact MeasurableSet.iUnion fun n =>
      measurableSet_univ_prod_window_self ℱ (n : ℝ) (hAm k) (hAν k)
  -- the cut integrands
  set ψk : ℕ → Ω → ℝ → E → ℝ := fun k ω s e => if e ∈ A k then ψ ω s e else 0 with hψkdef
  have hψk_eq : ∀ k, (fun p : Ω × ℝ × E => ψk k p.1 p.2.1 p.2.2)
      = {p : Ω × ℝ × E | 0 < p.2.1 ∧ p.2.2 ∈ A k}.indicator
        fun p => ψ p.1 p.2.1 p.2.2 := by
    intro k
    funext p
    by_cases hp0 : 0 < p.2.1
    · by_cases hpA : p.2.2 ∈ A k
      · simp [hψkdef, hpA, hp0]
      · simp [hψkdef, hpA]
    · have hz : ψ p.1 p.2.1 p.2.2 = 0 := h0 _ _ _ (not_lt.mp hp0)
      simp [hψkdef, hz, hp0]
  have hpredk : ∀ k, MarkedPredictable ℱ ν (ψk k) := fun k => by
    unfold MarkedPredictable
    rw [hψk_eq k]
    exact hpred.indicator (hposA k)
  have hmk : ∀ k, Measurable fun p : Ω × ℝ × E => ψk k p.1 p.2.1 p.2.2 := fun k =>
    (hpredk k).mono (markedPredictableSigma_le ℱ ν) le_rfl
  have hpk : ∀ k, MarkedProgressivelyMeasurable ℱ (ψk k) := fun k =>
    (hpredk k).markedProgressivelyMeasurable
  have habsk : ∀ k ω s e, |ψk k ω s e| ≤ |ψ ω s e| := by
    intro k ω s e
    simp only [hψkdef]
    split_ifs
    · exact le_rfl
    · simp
  have hqk : ∀ k, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψk k ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := fun k =>
    markedEnergy_lt_top_of_abs_le (habsk k) hq
  -- the pathwise identity on each window
  have hpw : ∀ k, Poisson.Compensated.stochasticIntegral N ℱ hℱ (ψk k) (hmk k) (hpk k)
      (hqk k) t =ᵐ[P] fun ω => (∫ q in Wk k, ψ ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Wk k, ψ ω q.1 q.2 ∂Ref := by
    intro k
    have h := Poisson.Compensated.stochasticIntegral_ae_eq_pathwise N ℱ hℱ (ψk k) (hmk k)
      (hpk k) (hqk k) (hAm k) (hpredk k) (hAν k) (fun ω s e he => if_neg he) ht
    filter_upwards [h] with ω hω
    rw [hω]
    have hc : ∀ μ : Measure (ℝ × E), ∫ q in Wk k, ψk k ω q.1 q.2 ∂μ
        = ∫ q in Wk k, ψ ω q.1 q.2 ∂μ := fun μ =>
      setIntegral_congr_fun (hWkm k) fun q hq => if_pos hq.2
    rw [hc, hc]
  -- integrability on the window
  have hnorm_pred : Measurable[markedPredictableSigma ℱ ν]
      fun p : Ω × ℝ × E => ‖ψ p.1 p.2.1 p.2.2‖ₑ := measurable_enorm.comp hpred
  obtain ⟨hNae, hNeq⟩ := lintegral_count_eq_lintegral_ref N hℱ t hnorm_pred
  have hRefm : Measurable fun ω => ∫⁻ q in W, ‖ψ ω q.1 q.2‖ₑ ∂Ref := by
    haveI : SFinite Ref := by rw [hRefdef, Poisson.referenceIntensity]; infer_instance
    exact (measurable_enorm.comp (hm.comp (measurable_fst.prodMk
      (measurable_snd.fst.prodMk measurable_snd.snd)))).lintegral_prod_right'
  have hNfin : ∫⁻ ω, ∫⁻ q in W, ‖ψ ω q.1 q.2‖ₑ ∂(N.N ω) ∂P ≠ ⊤ := by
    rw [hNeq]
    exact hL1
  have hint : ∀ᵐ ω ∂P, IntegrableOn (fun q : ℝ × E => ψ ω q.1 q.2) W (N.N ω)
      ∧ IntegrableOn (fun q : ℝ × E => ψ ω q.1 q.2) W Ref := by
    filter_upwards [ae_lt_top' hNae hNfin, ae_lt_top hRefm hL1] with ω h1 h2
    exact ⟨⟨(hψω ω).aestronglyMeasurable, h1⟩, ⟨(hψω ω).aestronglyMeasurable, h2⟩⟩
  -- the tails of the windows
  set Ψk : ℕ → Ω × ℝ × E → ℝ≥0∞ := fun k p => if p.2.2 ∈ A k then 0 else ‖ψ p.1 p.2.1 p.2.2‖ₑ
    with hΨkdef
  have hΨk_pred : ∀ k, Measurable[markedPredictableSigma ℱ ν] (Ψk k) := by
    intro k
    have heq : Ψk k = ({p : Ω × ℝ × E | 0 < p.2.1} \ {p | 0 < p.2.1 ∧ p.2.2 ∈ A k}).indicator
        fun p => ‖ψ p.1 p.2.1 p.2.2‖ₑ := by
      funext p
      by_cases hp0 : 0 < p.2.1
      · by_cases hpA : p.2.2 ∈ A k
        · simp [hΨkdef, hpA, hp0]
        · simp [hΨkdef, hpA, hp0]
      · have hz : ψ p.1 p.2.1 p.2.2 = 0 := h0 _ _ _ (not_lt.mp hp0)
        simp [hΨkdef, hz, hp0]
    rw [heq]
    exact hnorm_pred.indicator (hpos.diff (hposA k))
  have hΨk_m : ∀ k, Measurable (Ψk k) := fun k =>
    (hΨk_pred k).mono (markedPredictableSigma_le ℱ ν) le_rfl
  have hset_eq : ∀ (μ : Measure (ℝ × E)) k (ω : Ω),
      ∫⁻ q in W \ Wk k, ‖ψ ω q.1 q.2‖ₑ ∂μ = ∫⁻ q in W, Ψk k (ω, q) ∂μ := by
    intro μ k ω
    have hdiff : W \ Wk k = {q : ℝ × E | q.2 ∉ A k} ∩ W := by
      ext q
      simp only [hWdef, hWkdef, Set.mem_sdiff, mem_prod, mem_univ, and_true, mem_inter_iff,
        mem_setOf_eq]
      tauto
    have hm2 : MeasurableSet {q : ℝ × E | q.2 ∉ A k} := (measurable_snd (hAm k)).compl
    rw [hdiff, ← Measure.restrict_restrict hm2, ← lintegral_indicator hm2]
    refine lintegral_congr fun q => ?_
    by_cases hq : q.2 ∈ A k
    · simp [hΨkdef, hq]
    · simp [hΨkdef, hq]
  -- the tails tend to zero in mean
  set Dk : ℕ → Ω → ℝ≥0∞ := fun k ω => ∫⁻ q in W, Ψk k (ω, q) ∂Ref with hDkdef
  have hDk_tend : Tendsto (fun k => ∫⁻ ω, Dk k ω ∂P) atTop (𝓝 0) := by
    have hRpm : ∀ k, Measurable (Dk k) := fun k => by
      haveI : SFinite Ref := by rw [hRefdef, Poisson.referenceIntensity]; infer_instance
      exact ((hΨk_m k).comp (measurable_fst.prodMk measurable_snd)).lintegral_prod_right'
    have hlimω : ∀ᵐ ω ∂P, Tendsto (fun k => Dk k ω) atTop (𝓝 0) := by
      filter_upwards [ae_lt_top hRefm hL1] with ω hω
      have hpt : ∀ q : ℝ × E, Tendsto (fun k => Ψk k (ω, q)) atTop (𝓝 0) := by
        intro q
        obtain ⟨k₀, hk₀⟩ : ∃ k₀, q.2 ∈ A k₀ := by
          have hq : q.2 ∈ ⋃ k, A k := by rw [hAdef, iUnion_spanningSets]; exact mem_univ _
          exact mem_iUnion.mp hq
        refine tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => ?_
        have hkA : q.2 ∈ A k := monotone_spanningSets ν hk hk₀
        simp [hΨkdef, hkA]
      have h := tendsto_lintegral_of_dominated_convergence (μ := Ref.restrict W)
        (F := fun k q => Ψk k (ω, q)) (f := fun _ => 0)
        (fun q => ‖ψ ω q.1 q.2‖ₑ) (fun k => (hΨk_m k).comp measurable_prodMk_left)
        (fun k => Eventually.of_forall fun q => by
          by_cases hq : q.2 ∈ A k <;> simp [hΨkdef, hq])
        hω.ne (Eventually.of_forall hpt)
      simpa using h
    have hlim := tendsto_lintegral_of_dominated_convergence (μ := P) (f := fun _ => 0)
      (fun ω => ∫⁻ q in W, ‖ψ ω q.1 q.2‖ₑ ∂Ref) hRpm
      (fun k => Eventually.of_forall fun ω => lintegral_mono fun q => by
        by_cases hq : q.2 ∈ A k <;> simp [hΨkdef, hq])
      hL1 hlimω
    simpa using hlim
  -- the stochastic integrals converge in mean
  have hYm : AEStronglyMeasurable (Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hm hp hq t) P :=
    ((Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱ ψ hm hp hq t).mono
      (ℱ.rightCont.le t) le_rfl).aestronglyMeasurable
  have hXm : ∀ k, AEStronglyMeasurable (Poisson.Compensated.stochasticIntegral N ℱ hℱ (ψk k)
      (hmk k) (hpk k) (hqk k) t) P := fun k =>
    ((Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱ (ψk k) (hmk k) (hpk k) (hqk k)
      t).mono (ℱ.rightCont.le t) le_rfl).aestronglyMeasurable
  have h1 : Tendsto (fun k => ∫⁻ ω, ‖Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hm hp hq t ω
      - Poisson.Compensated.stochasticIntegral N ℱ hℱ (ψk k) (hmk k) (hpk k) (hqk k) t ω‖ₑ ∂P)
      atTop (𝓝 0) := by
    set Ek : ℕ → ℝ≥0∞ := fun k => ∫⁻ p, (‖ψ p.1 p.2.1 p.2.2 - ψk k p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2
      ∂(Poisson.Compensated.markedEnergyMeasure P ν t) with hEkdef
    have hiso : ∀ k, ∫⁻ ω, (‖Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hm hp hq t ω
        - Poisson.Compensated.stochasticIntegral N ℱ hℱ (ψk k) (hmk k) (hpk k) (hqk k) t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P = Ek k := by
      intro k
      rw [Poisson.Compensated.itoIsometry_diff_compensated N ℱ hℱ ψ (ψk k) hm (hmk k) hp
        (hpk k) hq (hqk k) t ht]
      have hme : Measurable fun p : Ω × ℝ × E =>
          (‖ψ p.1 p.2.1 p.2.2 - ψk k p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
        ((measurable_nnnorm.comp (hm.sub (hmk k))).coe_nnreal_ennreal).pow_const 2
      simp only [hEkdef, Poisson.Compensated.markedEnergyMeasure]
      rw [lintegral_prod _ hme.aemeasurable]
      refine lintegral_congr fun ω => ?_
      exact (lintegral_prod (μ := volume.restrict (Icc (0 : ℝ) t)) (ν := ν)
        (fun y : ℝ × E => (‖ψ ω y.1 y.2 - ψk k ω y.1 y.2‖₊ : ℝ≥0∞) ^ 2)
        (hme.comp (measurable_prodMk_left (x := ω))).aemeasurable).symm
    have hEk : Tendsto Ek atTop (𝓝 0) := by
      have hbound : ∫⁻ p, (‖ψ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2
          ∂(Poisson.Compensated.markedEnergyMeasure P ν t) ≠ ⊤ := by
        have h := Poisson.Compensated.markedEnergy_eq_eLpNorm_sq (P := P) (ν := ν) hm t
        rw [Brownian.Ito.eLpNorm_sq_eq_lintegral] at h
        rw [← h]
        exact (hq t ht).ne
      have hpt : ∀ p : Ω × ℝ × E, Tendsto (fun k =>
          (‖ψ p.1 p.2.1 p.2.2 - ψk k p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) atTop (𝓝 0) := by
        intro p
        obtain ⟨k₀, hk₀⟩ : ∃ k₀, p.2.2 ∈ A k₀ := by
          have hq' : p.2.2 ∈ ⋃ k, A k := by rw [hAdef, iUnion_spanningSets]; exact mem_univ _
          exact mem_iUnion.mp hq'
        refine tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => ?_
        have hkA : p.2.2 ∈ A k := monotone_spanningSets ν hk hk₀
        simp [hψkdef, hkA]
      have h := tendsto_lintegral_of_dominated_convergence
        (μ := Poisson.Compensated.markedEnergyMeasure P ν t) (f := fun _ => 0)
        (F := fun k p => (‖ψ p.1 p.2.1 p.2.2 - ψk k p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2)
        (fun p => (‖ψ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2)
        (fun k => ((measurable_nnnorm.comp (hm.sub (hmk k))).coe_nnreal_ennreal).pow_const 2)
        (fun k => Eventually.of_forall fun p => by
          simp only [hψkdef]
          split_ifs <;> simp)
        hbound (Eventually.of_forall hpt)
      simpa using h
    have hle : ∀ k, ∫⁻ ω, ‖Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hm hp hq t ω
        - Poisson.Compensated.stochasticIntegral N ℱ hℱ (ψk k) (hmk k) (hpk k) (hqk k) t ω‖ₑ ∂P
        ≤ Ek k ^ (2 : ℝ)⁻¹ := by
      intro k
      refine (Poisson.lintegral_enorm_le_eLpNorm_two (hYm.sub (hXm k))).trans (le_of_eq ?_)
      rw [Poisson.eLpNorm_two_eq_rpow, ← hiso k]
      simp only [enorm_eq_nnnorm, Pi.sub_apply]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => bot_le) hle
    simpa using hEk.ennrpow_const ((2 : ℝ)⁻¹)
  -- the pathwise forms converge in mean
  set Z : Ω → ℝ := fun ω => (∫ q in W, ψ ω q.1 q.2 ∂(N.N ω)) - ∫ q in W, ψ ω q.1 q.2 ∂Ref
    with hZdef
  have hZm : AEStronglyMeasurable Z P := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun k ω =>
      (∫ q in Wk k, ψ ω q.1 q.2 ∂(N.N ω)) - ∫ q in Wk k, ψ ω q.1 q.2 ∂Ref)
      (fun k => (hXm k).congr (hpw k)) ?_
    filter_upwards [hint] with ω hω
    refine Tendsto.sub ?_ ?_
    · have h := tendsto_setIntegral_of_monotone (μ := N.N ω)
        (f := fun q : ℝ × E => ψ ω q.1 q.2) hWkm hWkmono (by rw [hWU]; exact hω.1)
      rwa [hWU] at h
    · have h := tendsto_setIntegral_of_monotone (μ := Ref)
        (f := fun q : ℝ × E => ψ ω q.1 q.2) hWkm hWkmono (by rw [hWU]; exact hω.2)
      rwa [hWU] at h
  have h2 : Tendsto (fun k => ∫⁻ ω, ‖Poisson.Compensated.stochasticIntegral N ℱ hℱ (ψk k)
      (hmk k) (hpk k) (hqk k) t ω - Z ω‖ₑ ∂P) atTop (𝓝 0) := by
    have hle : ∀ k, ∫⁻ ω, ‖Poisson.Compensated.stochasticIntegral N ℱ hℱ (ψk k) (hmk k)
        (hpk k) (hqk k) t ω - Z ω‖ₑ ∂P ≤ 2 * ∫⁻ ω, Dk k ω ∂P := by
      intro k
      have hNk := lintegral_count_eq_lintegral_ref N hℱ t (hΨk_pred k)
      calc ∫⁻ ω, ‖Poisson.Compensated.stochasticIntegral N ℱ hℱ (ψk k) (hmk k) (hpk k)
            (hqk k) t ω - Z ω‖ₑ ∂P
          ≤ ∫⁻ ω, (∫⁻ q in W, Ψk k (ω, q) ∂(N.N ω) + Dk k ω) ∂P := by
            refine lintegral_mono_ae ?_
            filter_upwards [hpw k, hint] with ω hω hiω
            rw [hω, hZdef]
            have hsN := setIntegral_sdiff (hWkm k) hiω.1 (fun q hq => ⟨hq.1, mem_univ _⟩)
            have hsR := setIntegral_sdiff (hWkm k) hiω.2 (fun q hq => ⟨hq.1, mem_univ _⟩)
            have hrw : (∫ q in Wk k, ψ ω q.1 q.2 ∂(N.N ω)) - (∫ q in Wk k, ψ ω q.1 q.2 ∂Ref)
                - ((∫ q in W, ψ ω q.1 q.2 ∂(N.N ω)) - ∫ q in W, ψ ω q.1 q.2 ∂Ref)
                = -(∫ q in W \ Wk k, ψ ω q.1 q.2 ∂(N.N ω))
                  + ∫ q in W \ Wk k, ψ ω q.1 q.2 ∂Ref := by
              rw [hsN, hsR]
              ring
            rw [hrw]
            refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [enorm_neg, ← hset_eq]
              exact enorm_integral_le_lintegral_enorm _
            · change _ ≤ ∫⁻ q in W, Ψk k (ω, q) ∂Ref
              rw [← hset_eq]
              exact enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ ω, ∫⁻ q in W, Ψk k (ω, q) ∂(N.N ω) ∂P + ∫⁻ ω, Dk k ω ∂P := by
            refine lintegral_add_right' _ ?_
            haveI : SFinite Ref := by rw [hRefdef, Poisson.referenceIntensity]; infer_instance
            exact (((hΨk_m k).comp (measurable_fst.prodMk measurable_snd)).lintegral_prod_right'
              (ν := Ref.restrict W)).aemeasurable
        _ = 2 * ∫⁻ ω, Dk k ω ∂P := by rw [hNk.2, two_mul]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => bot_le) hle
    simpa using ENNReal.Tendsto.const_mul hDk_tend (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  exact Poisson.ae_eq_of_tendsto_lintegral_enorm hYm hZm hXm h1 h2

end MVFBSDEJ.WellPosedness.Martingale
