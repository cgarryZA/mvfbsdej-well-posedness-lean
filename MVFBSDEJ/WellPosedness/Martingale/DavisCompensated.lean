/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Martingale.DavisJumps
import MVFBSDEJ.WellPosedness.Martingale.CompensatedPathwise
import LevyStochCalc.Probability.MarkedPredictableComp

/-!
# The Burkholder–Davis–Gundy inequality at `p = 1` in quadratic-variation form

For a marked predictable integrand `φ` of finite energy and any version `M` of the compensated
integral `∫∫ φ dÑ` with paths right-continuous on `[0, T)`,

`𝔼 sup_{t ≤ T} |M_t| ≤ 24 𝔼 (∫_{(0, T] × E} φ² dN)^{1/2}`,

and the same bound holds for a local compensated integral of a marked predictable integrand.

The proof is Davis's decomposition. With `A_t = ∫_{(0, t] × E} φ² dN`, the integrand splits into
the large jumps `φ 1_{φ² > A_{s−}}` and the rest; both are predictable, since `A_{s−}` is. The
large jumps at least double `A`, so their absolute integral against `N` is at most
`(2 + √2) A_T^{1/2}`, and their compensated integral, which is pathwise, is bounded by twice that
in mean. The rest has jumps at most `A_{s−}`: stopped when `A` reaches `δ`, its energy against
`N` is at most `2 (A_T ∧ δ)`, and Doob's inequality with the compensation formula and Lenglart's
argument over the levels `δ` bound its supremum by `17 𝔼 A_T^{1/2}`.

## Main statements

* `MVFBSDEJ.WellPosedness.Martingale.lintegral_biSup_le_compensated_count` — the inequality
  for the compensated integral.
* `MVFBSDEJ.WellPosedness.Martingale.IsLocalCompensatedIntegral.lintegral_biSup_le_count` —
  the inequality for a local compensated integral.
-/

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace MVFBSDEJ.WellPosedness.Martingale

open LevyStochCalc LevyStochCalc.Probability

universe u v w

section Predictable

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
  {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

/-- **The stochastic interval `[0, τ]` of a stopping time is predictable.** -/
theorem measurableSet_predictableSigma_le_stoppingTime {τ : Ω → WithTop ℝ}
    (hτ : IsStoppingTime ℱ τ) :
    MeasurableSet[predictableSigma ℱ] {p : ℝ × Ω | ((p.1 : ℝ) : WithTop ℝ) ≤ τ p.2} := by
  have hset : {p : ℝ × Ω | ((p.1 : ℝ) : WithTop ℝ) ≤ τ p.2}
      = (⋃ q : ℚ, Ioi (q : ℝ) ×ˢ {ω | τ ω < ((q : ℝ) : WithTop ℝ)})ᶜ := by
    ext p
    simp only [mem_setOf_eq, mem_compl_iff, mem_iUnion, mem_prod, mem_Ioi, not_exists, not_and]
    constructor
    · intro h q hq hτq
      exact absurd (h.trans_lt hτq) (not_lt.mpr (WithTop.coe_le_coe.mpr hq.le))
    · intro h
      by_contra hlt
      push Not at hlt
      rcases hτp : τ p.2 with _ | r
      · rw [hτp] at hlt
        exact absurd hlt (not_lt.mpr le_top)
      · rw [hτp] at hlt
        obtain ⟨q, hrq, hqp⟩ := exists_rat_btwn (WithTop.coe_lt_coe.mp hlt)
        exact h q hqp (by rw [hτp]; exact WithTop.coe_lt_coe.mpr hrq)
  rw [hset]
  refine (MeasurableSet.iUnion fun q => ?_).compl
  exact measurableSet_predictableSigma_Ioi_prod (hτ.measurableSet_lt (q : ℝ))

/-- **A marked predictable integrand vanishing at the nonpositive times, cut off after a
stopping time, is marked predictable.** -/
theorem MarkedPredictable.markedStopped {φ : Ω → ℝ → E → ℝ} (hφ : MarkedPredictable ℱ ν φ)
    (h0 : ∀ ω s e, s ≤ 0 → φ ω s e = 0) {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ) :
    MarkedPredictable ℱ ν (Poisson.Compensated.markedStopped τ φ) := by
  classical
  set Y : Ω → ℝ → ℝ := fun ω s => if ((s : ℝ) : WithTop ℝ) ≤ τ ω then 1 else 0 with hYdef
  have hY : Measurable[predictableSigma ℱ] fun q : ℝ × Ω => Y q.2 q.1 := by
    have heq : (fun q : ℝ × Ω => Y q.2 q.1)
        = {p : ℝ × Ω | ((p.1 : ℝ) : WithTop ℝ) ≤ τ p.2}.indicator 1 := by
      funext q
      by_cases hq : ((q.1 : ℝ) : WithTop ℝ) ≤ τ q.2
      · simp [hYdef, hq]
      · simp [hYdef, hq]
    rw [heq]
    exact measurable_const.indicator (measurableSet_predictableSigma_le_stoppingTime hτ)
  have hF : Measurable fun p : ℝ × ℝ × ℝ => p.2.1 * p.2.2 :=
    measurable_snd.fst.mul measurable_snd.snd
  have h := hφ.comp_measurable hF hY
  have heq : (fun ω s e => if 0 < s then Y ω s * φ ω s e else 0)
      = Poisson.Compensated.markedStopped τ φ := by
    funext ω s e
    simp only [Poisson.Compensated.markedStopped, hYdef]
    by_cases hs : 0 < s
    · by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω <;> simp [hs, hle]
    · simp [hs, h0 ω s e (not_lt.mp hs)]
  rw [← heq]
  exact h

end Predictable

section Split

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- The squared marked integrand, the density of the quadratic variation against `N`. -/
noncomputable def sqDensity (φ : Ω → ℝ → E → ℝ) (p : Ω × ℝ × E) : ℝ≥0∞ :=
  ‖φ p.1 p.2.1 p.2.2‖ₑ ^ 2

/-- The large jumps of `φ`: its values where `φ² > A_{s−}`, `A` the integral of `φ²`
against `N`. -/
noncomputable def bigJumps (φ : Ω → ℝ → E → ℝ) (ω : Ω) (s : ℝ) (e : E) : ℝ :=
  if 0 < s ∧ countIntLeft N (sqDensity φ) s ω < ‖φ ω s e‖ₑ ^ 2 then φ ω s e else 0

/-- The rest of `φ`, whose values satisfy `φ² ≤ A_{s−}`. -/
noncomputable def smallJumps (φ : Ω → ℝ → E → ℝ) (ω : Ω) (s : ℝ) (e : E) : ℝ :=
  if 0 < s ∧ countIntLeft N (sqDensity φ) s ω < ‖φ ω s e‖ₑ ^ 2 then 0 else φ ω s e

variable {φ : Ω → ℝ → E → ℝ}

theorem bigJumps_add_smallJumps (ω : Ω) (s : ℝ) (e : E) :
    bigJumps N φ ω s e + smallJumps N φ ω s e = φ ω s e := by
  simp only [bigJumps, smallJumps]
  split_ifs <;> simp

theorem abs_bigJumps_le (ω : Ω) (s : ℝ) (e : E) : |bigJumps N φ ω s e| ≤ |φ ω s e| := by
  simp only [bigJumps]
  split_ifs <;> simp

theorem abs_smallJumps_le (ω : Ω) (s : ℝ) (e : E) : |smallJumps N φ ω s e| ≤ |φ ω s e| := by
  simp only [smallJumps]
  split_ifs <;> simp

omit [SigmaFinite ν] in
theorem measurable_sqDensity (hφ : MarkedPredictable ℱ ν φ) :
    Measurable[markedPredictableSigma ℱ ν] (sqDensity φ) :=
  (measurable_enorm.comp hφ).pow_const 2

variable (hℱ : Poisson.IsPoissonFiltration N ℱ)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)

include hℱ hnull in
/-- **The large jumps are marked predictable.** -/
theorem markedPredictable_bigJumps (hφ : MarkedPredictable ℱ ν φ) :
    MarkedPredictable ℱ ν (bigJumps N φ) := by
  classical
  have hY := measurable_predictableSigma_countIntLeft N hℱ hnull (measurable_sqDensity hφ)
  have hF : Measurable fun p : ℝ × ℝ≥0∞ × ℝ => if p.2.1 < ‖p.2.2‖ₑ ^ 2 then p.2.2 else 0 :=
    Measurable.ite (measurableSet_lt measurable_snd.fst
      ((measurable_enorm.comp measurable_snd.snd).pow_const 2)) measurable_snd.snd measurable_const
  have h := hφ.comp_measurable (Y := fun ω s => countIntLeft N (sqDensity φ) s ω) hF hY
  have heq : (fun ω s e => if 0 < s then
      (if countIntLeft N (sqDensity φ) s ω < ‖φ ω s e‖ₑ ^ 2 then φ ω s e else 0) else 0)
      = bigJumps N φ := by
    funext ω s e
    simp only [bigJumps]
    by_cases hs : 0 < s <;> simp [hs]
  rw [← heq]
  exact h

include hℱ hnull in
/-- **The rest of the integrand is marked predictable**, for an integrand vanishing at the
nonpositive times. -/
theorem markedPredictable_smallJumps (hφ : MarkedPredictable ℱ ν φ)
    (h0 : ∀ ω s e, s ≤ 0 → φ ω s e = 0) :
    MarkedPredictable ℱ ν (smallJumps N φ) := by
  classical
  have hY := measurable_predictableSigma_countIntLeft N hℱ hnull (measurable_sqDensity hφ)
  have hF : Measurable fun p : ℝ × ℝ≥0∞ × ℝ => if p.2.1 < ‖p.2.2‖ₑ ^ 2 then 0 else p.2.2 :=
    Measurable.ite (measurableSet_lt measurable_snd.fst
      ((measurable_enorm.comp measurable_snd.snd).pow_const 2)) measurable_const measurable_snd.snd
  have h := hφ.comp_measurable (Y := fun ω s => countIntLeft N (sqDensity φ) s ω) hF hY
  have heq : (fun ω s e => if 0 < s then
      (if countIntLeft N (sqDensity φ) s ω < ‖φ ω s e‖ₑ ^ 2 then 0 else φ ω s e) else 0)
      = smallJumps N φ := by
    funext ω s e
    simp only [smallJumps]
    by_cases hs : 0 < s
    · simp [hs]
    · simp [hs, h0 ω s e (not_lt.mp hs)]
  rw [← heq]
  exact h

end Split

section Pathwise

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν) {φ : Ω → ℝ → E → ℝ}

omit [MeasurableSpace Ω] in
/-- The pathwise compensated integral over `(0, t]` is bounded by the absolute integrals over
`(0, T]`, `t ≤ T`. -/
theorem enorm_pathwise_le {ψ : Ω → ℝ → E → ℝ} (ω : Ω) {t T : ℝ} (htT : t ≤ T)
    (μ₁ μ₂ : Measure (ℝ × E)) :
    ‖(∫ q in Ioc (0 : ℝ) t ×ˢ (univ : Set E), ψ ω q.1 q.2 ∂μ₁)
        - ∫ q in Ioc (0 : ℝ) t ×ˢ (univ : Set E), ψ ω q.1 q.2 ∂μ₂‖ₑ
      ≤ ∫⁻ q in Ioc (0 : ℝ) T ×ˢ (univ : Set E), ‖ψ ω q.1 q.2‖ₑ ∂μ₁
        + ∫⁻ q in Ioc (0 : ℝ) T ×ˢ (univ : Set E), ‖ψ ω q.1 q.2‖ₑ ∂μ₂ := by
  have hsub : Ioc (0 : ℝ) t ×ˢ (univ : Set E) ⊆ Ioc (0 : ℝ) T ×ˢ (univ : Set E) :=
    prod_mono (Ioc_subset_Ioc_right htT) le_rfl
  refine enorm_sub_le.trans (add_le_add ?_ ?_)
  · exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_set hsub)
  · exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_set hsub)

variable [MeasurableSpace.CountablyGenerated E]

/-- Almost surely the windows `(0, T] × E_k` carry integer-valued restrictions of `N`. -/
theorem ae_isIntegerValued_window (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ k, IsIntegerValued ((N.N ω).restrict (Ioc (0 : ℝ) T ×ˢ spanningSets ν k)) :=
  ae_all_iff.2 fun k => Poisson.ae_isIntegerValued_restrict N
    (measurableSet_Ioc.prod (measurableSet_spanningSets ν k))
    (Poisson.referenceIntensity_Ioc_prod_ne_top (measure_spanningSets_lt_top ν k).ne T)

/-- **The large jumps against `N`.** Almost surely
`∫_{(0, T] × E} |φ| 1_{φ² > A_{s−}} dN ≤ (2 + √2) (∫_{(0, T] × E} φ² dN)^{1/2}`. -/
theorem ae_lintegral_bigJumps_le (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (T : ℝ) :
    ∀ᵐ ω ∂P, ∫⁻ x in Ioc (0 : ℝ) T ×ˢ (univ : Set E), ‖bigJumps N φ ω x.1 x.2‖ₑ ∂(N.N ω)
      ≤ ENNReal.ofReal (2 + √2)
        * (∫⁻ x in Ioc (0 : ℝ) T ×ˢ (univ : Set E), ‖φ ω x.1 x.2‖ₑ ^ 2 ∂(N.N ω))
          ^ (1 / 2 : ℝ) := by
  filter_upwards [ae_isIntegerValued_window N T, ae_count_time_le_one N, ae_mem_countGood N]
    with ω hint hsimp hG
  have hf : Measurable fun x : ℝ × E => ‖φ ω x.1 x.2‖ₑ :=
    measurable_enorm.comp (hφm.comp (measurable_const.prodMk measurable_id))
  refine le_trans (setLIntegral_mono' (measurableSet_Ioc.prod MeasurableSet.univ)
    fun x hx => ?_) (lintegral_bigJumps_le ν hint hsimp hf)
  have hx0 : 0 < x.1 := hx.1.1
  simp only [bigJumps, countIntLeft_of_mem N hG, sqDensity, hx0, true_and]
  split_ifs <;> simp

omit [MeasurableSpace.CountablyGenerated E] in
/-- **The rest, stopped when `A` reaches `δ`, has energy against `N` at most `2 (A_T ∧ δ)`**, on
the good event at a sample point at which every positive time carries at most one point. -/
theorem lintegral_markedStopped_smallJumps_le {ω : Ω} (hG : ω ∈ countGood N)
    (hsimp : ∀ s : ℝ, 0 < s → N.N ω ({s} ×ˢ (univ : Set E)) ≤ 1) (T : ℝ) (δ : ℝ≥0∞) :
    ∫⁻ x in Ioc (0 : ℝ) T ×ˢ (univ : Set E), ‖Poisson.Compensated.markedStopped
        (levelHit (fun t ω => countInt N (sqDensity φ) t ω) δ) (smallJumps N φ) ω x.1 x.2‖ₑ
          ^ 2 ∂(N.N ω)
      ≤ 2 * min (countInt N (sqDensity φ) T ω) δ := by
  classical
  set X : ℝ → Ω → ℝ≥0∞ := fun t ω => countInt N (sqDensity φ) t ω with hXdef
  set σ := levelHit X δ with hσdef
  set F' : ℝ × E → ℝ≥0∞ := fun x => ‖smallJumps N φ ω x.1 x.2‖ₑ ^ 2 with hF'def
  -- the last time before `T` and `σ`
  obtain ⟨u, huT, huσ, hcover⟩ : ∃ u : ℝ, u ≤ T ∧ ((u : ℝ) : WithTop ℝ) ≤ σ ω
      ∧ ∀ s : ℝ, s ≤ T → ((s : ℝ) : WithTop ℝ) ≤ σ ω → s ≤ u := by
    rcases hσω : σ ω with _ | r
    · exact ⟨T, le_rfl, le_top, fun s hs _ => hs⟩
    · refine ⟨min T r, min_le_left _ _, WithTop.coe_le_coe.mpr (min_le_right _ _),
        fun s hs hsr => le_min hs (WithTop.coe_le_coe.mp hsr)⟩
  have hstep1 : ∫⁻ x in Ioc (0 : ℝ) T ×ˢ (univ : Set E), ‖Poisson.Compensated.markedStopped σ
      (smallJumps N φ) ω x.1 x.2‖ₑ ^ 2 ∂(N.N ω)
      ≤ ∫⁻ x in Ioc (0 : ℝ) u ×ˢ (univ : Set E), F' x ∂(N.N ω) := by
    calc ∫⁻ x in Ioc (0 : ℝ) T ×ˢ (univ : Set E), ‖Poisson.Compensated.markedStopped σ
          (smallJumps N φ) ω x.1 x.2‖ₑ ^ 2 ∂(N.N ω)
        ≤ ∫⁻ x in Ioc (0 : ℝ) T ×ˢ (univ : Set E),
            (Ioc (0 : ℝ) u ×ˢ (univ : Set E)).indicator F' x ∂(N.N ω) := by
          refine setLIntegral_mono' (measurableSet_Ioc.prod MeasurableSet.univ) fun x hx => ?_
          by_cases hxu : x.1 ≤ u
          · rw [indicator_of_mem (show x ∈ Ioc (0 : ℝ) u ×ˢ (univ : Set E) from
              ⟨⟨hx.1.1, hxu⟩, mem_univ _⟩)]
            simp only [Poisson.Compensated.markedStopped, hF'def]
            split_ifs <;> simp
          · have hns : ¬ ((x.1 : ℝ) : WithTop ℝ) ≤ σ ω := fun h => hxu (hcover _ hx.1.2 h)
            simp [Poisson.Compensated.markedStopped, hns]
      _ ≤ ∫⁻ x, (Ioc (0 : ℝ) u ×ˢ (univ : Set E)).indicator F' x ∂(N.N ω) :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ x in Ioc (0 : ℝ) u ×ˢ (univ : Set E), F' x ∂(N.N ω) :=
          lintegral_indicator (measurableSet_Ioc.prod MeasurableSet.univ) _
  set a : ℝ≥0∞ := countIntLeft N (sqDensity φ) u ω with hadef
  have ha_le_T : a ≤ X T ω :=
    (countIntLeft_le_countInt N u ω).trans (countInt_mono N ω huT)
  have ha_le_δ : a ≤ δ := by
    rw [hadef, countIntLeft_eq_iSup]
    refine iSup_le fun n => ?_
    set s : ℝ := u - 1 / ((n : ℝ) + 1) with hsdef
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    rcases lt_or_ge s 0 with hs0 | hs0
    · have h0 : countInt N (sqDensity φ) s ω = 0 := by
        simp [countInt, Ioc_eq_empty (not_lt.mpr hs0.le)]
      rw [h0]
      exact bot_le
    · refine (lt_of_lt_levelHit (X := X) hs0 ?_).le
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by linarith)) huσ
  refine hstep1.trans ?_
  rcases le_or_gt u 0 with hu0 | hu0
  · rw [Ioc_eq_empty (not_lt.mpr hu0), empty_prod, Measure.restrict_empty,
      lintegral_zero_measure]
    exact bot_le
  have hU : Ioc (0 : ℝ) u ×ˢ (univ : Set E)
      = Ioo (0 : ℝ) u ×ˢ (univ : Set E) ∪ ({u} : Set ℝ) ×ˢ (univ : Set E) := by
    rw [← union_prod, Ioo_union_right hu0]
  have hdisj : Disjoint (Ioo (0 : ℝ) u ×ˢ (univ : Set E)) (({u} : Set ℝ) ×ˢ (univ : Set E)) :=
    disjoint_prod.mpr (Or.inl (disjoint_singleton_right.mpr fun h => lt_irrefl u h.2))
  rw [hU, lintegral_union ((measurableSet_singleton u).prod MeasurableSet.univ) hdisj]
  have h1 : ∫⁻ x in Ioo (0 : ℝ) u ×ˢ (univ : Set E), F' x ∂(N.N ω) ≤ a := by
    rw [hadef, countIntLeft_of_mem N hG]
    refine lintegral_mono fun x => ?_
    simp only [hF'def, sqDensity]
    gcongr
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (abs_smallJumps_le N ω x.1 x.2)
  have h2 : ∫⁻ x in ({u} : Set ℝ) ×ˢ (univ : Set E), F' x ∂(N.N ω) ≤ a := by
    calc ∫⁻ x in ({u} : Set ℝ) ×ˢ (univ : Set E), F' x ∂(N.N ω)
        ≤ ∫⁻ x in ({u} : Set ℝ) ×ˢ (univ : Set E), a ∂(N.N ω) := by
          refine setLIntegral_mono' ((measurableSet_singleton u).prod MeasurableSet.univ)
            fun x hx => ?_
          have hx1 : x.1 = u := hx.1
          simp only [hF'def, smallJumps, hx1, hu0, true_and]
          split_ifs with hlt
          · simp
          · push Not at hlt
            simpa [hadef, sqDensity] using hlt
      _ = a * N.N ω (({u} : Set ℝ) ×ˢ (univ : Set E)) := setLIntegral_const _ _
      _ ≤ a * 1 := by gcongr; exact hsimp u hu0
      _ = a := mul_one a
  calc ∫⁻ x in Ioo (0 : ℝ) u ×ˢ (univ : Set E), F' x ∂(N.N ω)
        + ∫⁻ x in ({u} : Set ℝ) ×ˢ (univ : Set E), F' x ∂(N.N ω)
      ≤ a + a := add_le_add h1 h2
    _ = 2 * a := (two_mul a).symm
    _ ≤ 2 * min (countInt N (sqDensity φ) T ω) δ := by
        gcongr
        exact le_min ha_le_T ha_le_δ

end Pathwise

section Main

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)

/-- `17 + 2 (2 + √2) ≤ 24` in `[0, ∞]`. -/
theorem seventeen_add_two_mul_le : (17 : ℝ≥0∞) + 2 * ENNReal.ofReal (2 + √2) ≤ 24 := by
  have h2 : √2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have h : ENNReal.ofReal (2 + √2) ≤ ENNReal.ofReal (7 / 2) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  calc (17 : ℝ≥0∞) + 2 * ENNReal.ofReal (2 + √2) ≤ 17 + 2 * ENNReal.ofReal (7 / 2) := by gcongr
    _ = 24 := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
        show (17 : ℝ≥0∞) = ENNReal.ofReal 17 by norm_num,
        ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num

/-- **The Burkholder–Davis–Gundy inequality at `p = 1` in quadratic-variation form for the
compensated Poisson integral.** Over a right-continuous filtration whose null sets lie in its
time-`0` field, for a marked predictable integrand `φ` of finite energy vanishing at the
nonpositive times, every version `M` of `∫∫ φ dÑ` with paths right-continuous on `[0, T)`
almost surely satisfies
`𝔼 sup_{t ≤ T} |M_t| ≤ 24 𝔼 (∫_{(0, T] × E} φ_s(e)² N(ds, de))^{1/2}`. -/
theorem lintegral_biSup_le_compensated_count [ℱ.IsRightContinuous]
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {φ : Ω → ℝ → E → ℝ} (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hpred : MarkedPredictable ℱ ν φ) (h0 : ∀ ω s e, s ≤ 0 → φ ω s e = 0)
    {T : ℝ} (hT : 0 < T) {M : ℝ → Ω → ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T,
      M t =ᵐ[P] Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t)
    (hMr : ∀ᵐ ω ∂P, ∀ t ∈ Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) :
    ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 24 * ∫⁻ ω, (∫⁻ x in Ioc (0 : ℝ) T ×ˢ (univ : Set E), ‖φ ω x.1 x.2‖ₑ ^ 2 ∂(N.N ω))
        ^ (1 / 2 : ℝ) ∂P := by
  classical
  set W : Set (ℝ × E) := Ioc (0 : ℝ) T ×ˢ (univ : Set E) with hWdef
  have hWm : MeasurableSet W := measurableSet_Ioc.prod MeasurableSet.univ
  set Q : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in W, ‖φ ω x.1 x.2‖ₑ ^ 2 ∂(N.N ω) with hQdef
  set Ref : Measure (ℝ × E) := Poisson.referenceIntensity ν with hRefdef
  set c₁ : ℝ≥0∞ := ENNReal.ofReal (2 + √2) with hc₁
  by_cases hfin : ∫⁻ ω, Q ω ^ (1 / 2 : ℝ) ∂P = ⊤
  · rw [hfin, ENNReal.mul_top (by norm_num)]
    exact le_top
  set g := sqDensity φ with hgdef
  have hgpred : Measurable[markedPredictableSigma ℱ ν] g := measurable_sqDensity hpred
  set A : Ω → ℝ≥0∞ := countInt N g T with hAdef
  have hA_eq : ∀ᵐ ω ∂P, A ω = Q ω := by
    filter_upwards [ae_mem_countGood N] with ω hω
    rw [hAdef, countInt_of_mem N hω]
    rfl
  have hAm : Measurable A := (measurable_countInt N hℱ hnull hgpred T).mono (ℱ.le T) le_rfl
  -- the two parts of the integrand
  set ψb : Ω → ℝ → E → ℝ := bigJumps N φ with hψbdef
  set ψs : Ω → ℝ → E → ℝ := smallJumps N φ with hψsdef
  have hpb : MarkedPredictable ℱ ν ψb := markedPredictable_bigJumps N hℱ hnull hpred
  have hps : MarkedPredictable ℱ ν ψs := markedPredictable_smallJumps N hℱ hnull hpred h0
  have hmb : Measurable fun p : Ω × ℝ × E => ψb p.1 p.2.1 p.2.2 :=
    hpb.mono (markedPredictableSigma_le ℱ ν) le_rfl
  have hms : Measurable fun p : Ω × ℝ × E => ψs p.1 p.2.1 p.2.2 :=
    hps.mono (markedPredictableSigma_le ℱ ν) le_rfl
  have hppb : MarkedProgressivelyMeasurable ℱ ψb := hpb.markedProgressivelyMeasurable
  have hpps : MarkedProgressivelyMeasurable ℱ ψs := hps.markedProgressivelyMeasurable
  have hqb := markedEnergy_lt_top_of_abs_le (P := P) (ν := ν) (abs_bigJumps_le N) hq
  have hqs := markedEnergy_lt_top_of_abs_le (P := P) (ν := ν) (abs_smallJumps_le N) hq
  have h0b : ∀ ω s e, s ≤ 0 → ψb ω s e = 0 := fun ω s e hs => by
    simp [hψbdef, bigJumps, not_lt.mpr hs]
  have h0s : ∀ ω s e, s ≤ 0 → ψs ω s e = 0 := fun ω s e hs => by
    simp [hψsdef, smallJumps, h0 ω s e hs]
  -- the sum of the parts
  have hpa : MarkedPredictable ℱ ν fun ω s e => ψb ω s e + ψs ω s e := hpb.add hps
  have hma : Measurable fun p : Ω × ℝ × E => ψb p.1 p.2.1 p.2.2 + ψs p.1 p.2.1 p.2.2 :=
    hpa.mono (markedPredictableSigma_le ℱ ν) le_rfl
  have hqa := markedEnergy_lt_top_of_abs_le (P := P) (ν := ν)
    (ψ := fun ω s e => ψb ω s e + ψs ω s e)
    (fun ω s e => by rw [bigJumps_add_smallJumps]) hq
  have hsplit : ∀ t, 0 < t → Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t
      =ᵐ[P] fun ω => Poisson.Compensated.stochasticIntegral N ℱ hℱ ψb hmb hppb hqb t ω
        + Poisson.Compensated.stochasticIntegral N ℱ hℱ ψs hms hpps hqs t ω := by
    intro t ht
    have h1 := Poisson.Compensated.stochasticIntegral_congr_ae N hℱ φ
      (fun ω s e => ψb ω s e + ψs ω s e) hm hma hp hpa.markedProgressivelyMeasurable hq hqa ht
      (Eventually.of_forall fun p => (bigJumps_add_smallJumps N p.1 p.2.1 p.2.2).symm)
    have h2 := Poisson.Compensated.stochasticIntegral_add N ℱ hℱ hmb hms hppb hpps hqb hqs hma
      hpa.markedProgressivelyMeasurable hqa ht
    exact h1.trans h2
  -- the large jumps
  have hnb_pred : Measurable[markedPredictableSigma ℱ ν]
      fun p : Ω × ℝ × E => ‖ψb p.1 p.2.1 p.2.2‖ₑ := measurable_enorm.comp hpb
  obtain ⟨hbNae, hbNeq⟩ := lintegral_count_eq_lintegral_ref N hℱ T hnb_pred
  have hbN : ∫⁻ ω, ∫⁻ x in W, ‖ψb ω x.1 x.2‖ₑ ∂(N.N ω) ∂P
      ≤ c₁ * ∫⁻ ω, Q ω ^ (1 / 2 : ℝ) ∂P := by
    calc ∫⁻ ω, ∫⁻ x in W, ‖ψb ω x.1 x.2‖ₑ ∂(N.N ω) ∂P
        ≤ ∫⁻ ω, c₁ * Q ω ^ (1 / 2 : ℝ) ∂P := lintegral_mono_ae (ae_lintegral_bigJumps_le N hm T)
      _ = c₁ * ∫⁻ ω, Q ω ^ (1 / 2 : ℝ) ∂P := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  set Rb : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in W, ‖ψb ω x.1 x.2‖ₑ ∂(N.N ω)
    + ∫⁻ x in W, ‖ψb ω x.1 x.2‖ₑ ∂Ref with hRbdef
  have hRb : ∫⁻ ω, Rb ω ∂P ≤ 2 * (c₁ * ∫⁻ ω, Q ω ^ (1 / 2 : ℝ) ∂P) := by
    rw [hRbdef, lintegral_add_left' hbNae, ← hbNeq, ← two_mul]
    gcongr
  have hbfin : ∫⁻ ω, ∫⁻ x in W, ‖ψb ω x.1 x.2‖ₑ ∂Ref ∂P ≠ ⊤ := by
    rw [← hbNeq]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hbN
  have hpath : ∀ t ∈ Ioc (0 : ℝ) T,
      Poisson.Compensated.stochasticIntegral N ℱ hℱ ψb hmb hppb hqb t =ᵐ[P] fun ω =>
        (∫ q in Ioc (0 : ℝ) t ×ˢ (univ : Set E), ψb ω q.1 q.2 ∂(N.N ω))
          - ∫ q in Ioc (0 : ℝ) t ×ˢ (univ : Set E), ψb ω q.1 q.2 ∂Ref := by
    intro t ht
    refine stochasticIntegral_ae_eq_pathwise_of_integrable N hℱ hmb hppb hqb hpb h0b ht.1 ?_
    refine ne_top_of_le_ne_top hbfin (lintegral_mono fun ω => lintegral_mono_set ?_)
    exact prod_mono (Ioc_subset_Ioc_right ht.2) le_rfl
  -- the rest and the difference of the versions
  set V : ℝ → Ω → ℝ := Poisson.Compensated.stochasticIntegral N ℱ hℱ ψs hms hpps hqs with hVdef
  have hVcad := Poisson.Compensated.stochasticIntegral_cadlag N ℱ hℱ ψs hms hpps hqs
  have hVm : ∀ t, Measurable (V t) := fun t =>
    (Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱ ψs hms hpps hqs t).mono
      (ℱ.rightCont.le t) le_rfl
  set Vb : ℝ → Ω → ℝ := fun t ω => M t ω - V t ω with hVbdef
  have hVb_le : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ ω ∂P, (‖Vb t ω‖₊ : ℝ≥0∞) ≤ Rb ω := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h00 | htpos
    · subst h00
      filter_upwards [hM 0 ht,
        Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ hm hp hq (le_refl (0 : ℝ)),
        Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ hms hpps hqs
          (le_refl (0 : ℝ))] with ω h1 h2 h3
      have h3' : V 0 ω = 0 := h3
      simp only [hVbdef, h1, h2, h3', Pi.zero_apply, sub_zero, nnnorm_zero, ENNReal.coe_zero]
      exact bot_le
    · filter_upwards [hM t ht, hsplit t htpos, hpath t ⟨htpos, ht.2⟩] with ω h1 h2 h3
      have heq : Vb t ω = (∫ q in Ioc (0 : ℝ) t ×ˢ (univ : Set E), ψb ω q.1 q.2 ∂(N.N ω))
          - ∫ q in Ioc (0 : ℝ) t ×ˢ (univ : Set E), ψb ω q.1 q.2 ∂Ref := by
        simp only [hVbdef, h1, h2, hVdef, ← h3]
        ring
      rw [heq, ← enorm_eq_nnnorm]
      exact enorm_pathwise_le ω ht.2 _ _
  have hVbr : ∀ᵐ ω ∂P, ∀ t ∈ Ico (0 : ℝ) T,
      Tendsto (fun s => Vb s ω) (𝓝[>] t) (𝓝 (Vb t ω)) := by
    filter_upwards [hMr, hVcad] with ω h1 h2 t ht
    exact (h1 t ht).sub (h2 t).1
  have hsupVb : ∀ᵐ ω ∂P, ⨆ t ∈ Icc (0 : ℝ) T, (‖Vb t ω‖₊ : ℝ≥0∞) ≤ Rb ω := by
    have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T → (‖Vb q ω‖₊ : ℝ≥0∞) ≤ Rb ω := by
      refine ae_all_iff.2 fun q => ?_
      by_cases hq' : (q : ℝ) ∈ Icc (0 : ℝ) T
      · filter_upwards [hVb_le q hq'] with ω hω _
        exact hω
      · exact ae_of_all _ fun ω h => absurd h hq'
    filter_upwards [hrat, hVb_le T ⟨hT.le, le_rfl⟩, hVbr] with ω h1 h2 h3
    rw [biSup_Icc_eq_of_rightCont hT.le h3]
    exact sup_le (iSup₂_le fun q hq => h1 q ⟨hq.1, hq.2.le⟩) h2
  -- the rest, by Lenglart's argument
  have hS : AEMeasurable (fun ω => ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞)) P :=
    aemeasurable_biSup_Icc hT.le (fun t _ => (hVm t).aemeasurable)
      (by filter_upwards [hVcad] with ω hω t _; exact (hω t).1)
  have hsmall : ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞) ∂P
      ≤ (1 + 2 * 8) * ∫⁻ ω, A ω ^ (1 / 2 : ℝ) ∂P := by
    refine lintegral_le_of_good_lambda hS hAm fun δ hδ => ?_
    set σ := levelHit (fun t ω => countInt N g t ω) (ENNReal.ofReal δ) with hσdef
    have hσ : IsStoppingTime ℱ σ :=
      isStoppingTime_levelHit (fun t => measurable_countInt N hℱ hnull hgpred t)
        (fun ω => countInt_mono N ω) _
    have hmσ := Poisson.Compensated.measurable_markedStopped hσ hms
    have hpσ := Poisson.Compensated.markedProgressivelyMeasurable_markedStopped hσ hpps
    have hqσ := Poisson.Compensated.sq_int_global_markedStopped (τ := σ) hqs
    set M' : ℝ → Ω → ℝ := Poisson.Compensated.stochasticIntegral N ℱ hℱ
      (Poisson.Compensated.markedStopped σ ψs) hmσ hpσ hqσ with hM'def
    have hM'cad := Poisson.Compensated.stochasticIntegral_cadlag N ℱ hℱ
      (Poisson.Compensated.markedStopped σ ψs) hmσ hpσ hqσ
    have hM'm : ∀ t, Measurable (M' t) := fun t =>
      (Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱ _ hmσ hpσ hqσ t).mono
        (ℱ.rightCont.le t) le_rfl
    refine ⟨fun ω => ⨆ t ∈ Icc (0 : ℝ) T, (‖M' t ω‖₊ : ℝ≥0∞), ?_, ?_, ?_⟩
    · exact aemeasurable_biSup_Icc hT.le (fun t _ => (hM'm t).aemeasurable)
        (by filter_upwards [hM'cad] with ω hω t _; exact (hω t).1)
    · have hloc : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
          ((t : ℝ) : WithTop ℝ) ≤ σ ω → V t ω = M' t ω := by
        intro t ht
        rcases eq_or_lt_of_le ht.1 with h00 | h0t
        · subst h00
          filter_upwards [Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ hms hpps
              hqs (le_refl (0 : ℝ)),
            Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ hmσ hpσ hqσ
              (le_refl (0 : ℝ))] with ω h2 h3 _
          rw [hVdef, h2, hM'def, h3]
        · filter_upwards [Poisson.Compensated.stochasticIntegral_markedStopped_eq_of_le N hℱ hms
            hpps hqs hσ h0t] with ω h2 hle
          rw [hM'def, h2 hle]
      have hD : ∀ᵐ ω ∂P, (∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
          (((q : ℝ) : ℝ) : WithTop ℝ) ≤ σ ω → V q ω = M' q ω)
          ∧ (((T : ℝ) : WithTop ℝ) ≤ σ ω → V T ω = M' T ω) := by
        refine (ae_all_iff.2 fun q => ?_).and (hloc T ⟨hT.le, le_rfl⟩)
        by_cases hq' : (q : ℝ) ∈ Icc (0 : ℝ) T
        · filter_upwards [hloc q hq'] with ω hω _ hle
          exact hω hle
        · exact ae_of_all _ fun ω h => absurd h hq'
      filter_upwards [hD, hVcad, hM'cad] with ω hω hr hc hA
      have hTσ : ((T : ℝ) : WithTop ℝ) ≤ σ ω :=
        le_levelHit_of_lt (X := fun t ω => countInt N g t ω) (countInt_mono N ω) hA
      have heq : ∀ t ∈ Icc (0 : ℝ) T, V t ω = M' t ω := by
        intro t ht
        rcases eq_or_lt_of_le ht.2 with htT | htT
        · rw [htT]
          exact hω.2 hTσ
        · refine eq_of_rightCont_of_eq_rat (f := fun s => V s ω) (g := fun s => M' s ω) htT
            (hr t).1 (hc t).1 fun q hq1 hq2 => ?_
          exact hω.1 q ⟨ht.1.trans hq1.le, hq2.le⟩
            (le_trans (WithTop.coe_le_coe.mpr hq2.le) hTσ)
      exact le_of_eq (iSup_congr fun t => iSup_congr fun ht => by rw [heq t ht])
    · have hstopped_pred : MarkedPredictable ℱ ν (Poisson.Compensated.markedStopped σ ψs) :=
        MVFBSDEJ.WellPosedness.Martingale.MarkedPredictable.markedStopped hps h0s hσ
      have hΨ : Measurable[markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
          ‖Poisson.Compensated.markedStopped σ ψs p.1 p.2.1 p.2.2‖ₑ ^ 2 :=
        (measurable_enorm.comp hstopped_pred).pow_const 2
      obtain ⟨-, hΨeq⟩ := lintegral_count_eq_lintegral_ref N hℱ T hΨ
      have henergy : ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
          (‖Poisson.Compensated.markedStopped σ ψs ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
          = ∫⁻ ω, ∫⁻ q in W, ‖Poisson.Compensated.markedStopped σ ψs ω q.1 q.2‖ₑ ^ 2
              ∂(N.N ω) ∂P := by
        rw [hΨeq]
        refine lintegral_congr fun ω => ?_
        have hmeas : Measurable fun q : ℝ × E =>
            ‖Poisson.Compensated.markedStopped σ ψs ω q.1 q.2‖ₑ ^ 2 :=
          (measurable_enorm.comp (hmσ.comp (measurable_const.prodMk measurable_id))).pow_const 2
        dsimp only
        rw [Poisson.lintegral_referenceIntensity_window hmeas univ T, Measure.restrict_univ,
          setLIntegral_congr Ioc_ae_eq_Icc]
        simp only [enorm_eq_nnnorm]
      have hpw : ∀ᵐ ω ∂P, ∫⁻ q in W, ‖Poisson.Compensated.markedStopped σ ψs ω q.1 q.2‖ₑ ^ 2
          ∂(N.N ω) ≤ 2 * min (A ω) (ENNReal.ofReal δ) := by
        filter_upwards [ae_mem_countGood N, ae_count_time_le_one N] with ω hG hsimp
        exact lintegral_markedStopped_smallJumps_le N hG hsimp T (ENNReal.ofReal δ)
      calc ∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ) T, (‖M' t ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
          = ∫⁻ ω, (⨆ t : Icc (0 : ℝ) T, (‖M' (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P := by
            simp_rw [iSup_subtype']
        _ ≤ 4 * ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
              (‖Poisson.Compensated.markedStopped σ ψs ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
            LevyStochCalc.Martingale.lintegral_iSup_sq_le_energy_compensated N ℱ hℱ _ hmσ hpσ
              hqσ hT
        _ = 4 * ∫⁻ ω, ∫⁻ q in W, ‖Poisson.Compensated.markedStopped σ ψs ω q.1 q.2‖ₑ ^ 2
              ∂(N.N ω) ∂P := by rw [henergy]
        _ ≤ 4 * ∫⁻ ω, 2 * min (A ω) (ENNReal.ofReal δ) ∂P := by
            gcongr 1
            exact lintegral_mono_ae hpw
        _ = 8 * ∫⁻ ω, min (A ω) (ENNReal.ofReal δ) ∂P := by
            rw [lintegral_const_mul' _ _ (by norm_num), ← mul_assoc]
            norm_num
  -- assembly
  have hAQ : ∫⁻ ω, A ω ^ (1 / 2 : ℝ) ∂P = ∫⁻ ω, Q ω ^ (1 / 2 : ℝ) ∂P :=
    lintegral_congr_ae (hA_eq.mono fun ω hω => by simp only [hω])
  calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      ≤ ∫⁻ ω, ((⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞)) + Rb ω) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hsupVb] with ω hω
        refine iSup₂_le fun t ht => ?_
        have hMt : M t ω = V t ω + Vb t ω := by simp [hVbdef]
        calc (‖M t ω‖₊ : ℝ≥0∞) ≤ (‖V t ω‖₊ : ℝ≥0∞) + (‖Vb t ω‖₊ : ℝ≥0∞) := by
              rw [hMt]
              exact_mod_cast nnnorm_add_le _ _
          _ ≤ (⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞)) + Rb ω := by
              gcongr
              · exact le_iSup₂_of_le t ht le_rfl
              · exact (le_iSup₂_of_le t ht le_rfl).trans hω
    _ = ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞) ∂P + ∫⁻ ω, Rb ω ∂P :=
        lintegral_add_left' hS _
    _ ≤ (1 + 2 * 8) * ∫⁻ ω, Q ω ^ (1 / 2 : ℝ) ∂P + 2 * (c₁ * ∫⁻ ω, Q ω ^ (1 / 2 : ℝ) ∂P) := by
        rw [← hAQ]
        exact add_le_add hsmall (hAQ ▸ hRb)
    _ = (17 + 2 * c₁) * ∫⁻ ω, Q ω ^ (1 / 2 : ℝ) ∂P := by ring
    _ ≤ 24 * ∫⁻ ω, Q ω ^ (1 / 2 : ℝ) ∂P := by
        gcongr
        exact seventeen_add_two_mul_le

/-- **The Burkholder–Davis–Gundy inequality at `p = 1` in quadratic-variation form for a local
compensated integral.** Over a right-continuous filtration whose null sets lie in its time-`0`
field, for a marked predictable integrand `φ` vanishing at the nonpositive times, every local
compensated integral `M` of `φ` on `[0, T]` satisfies
`𝔼 sup_{t ≤ T} |M_t| ≤ 24 𝔼 (∫_{(0, T] × E} φ_s(e)² N(ds, de))^{1/2}`. -/
theorem IsLocalCompensatedIntegral.lintegral_biSup_le_count [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {T : ℝ} (hT : 0 < T) {φ : Ω → ℝ → E → ℝ} (hpred : MarkedPredictable ℱ ν φ)
    (h0 : ∀ ω s e, s ≤ 0 → φ ω s e = 0) {M : ℝ → Ω → ℝ}
    (hM : IsLocalCompensatedIntegral N ℱ hℱ T φ M) :
    ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 24 * ∫⁻ ω, (∫⁻ x in Ioc (0 : ℝ) T ×ˢ (univ : Set E), ‖φ ω x.1 x.2‖ₑ ^ 2 ∂(N.N ω))
        ^ (1 / 2 : ℝ) ∂P := by
  obtain ⟨-, hMr, -, τ, hτ, hmono, hex, hk⟩ := hM
  set A : ℕ → Set Ω := fun k => {ω | ((T : ℝ) : WithTop ℝ) ≤ τ k ω} with hAdef
  have hAm : ∀ k, MeasurableSet (A k) := fun k => by
    have : A k = {ω | τ k ω < ((T : ℝ) : WithTop ℝ)}ᶜ := by
      ext ω
      simp [hAdef, not_lt]
    rw [this]
    exact (ℱ.le T _ ((hτ k).measurableSet_lt T)).compl
  have hAdir : Directed (· ⊆ ·) A :=
    Monotone.directed_le fun k k' hkk' ω hω => le_trans hω (hmono ω hkk')
  have hAunion : ∀ᵐ ω ∂P, ω ∈ ⋃ k, A k := by
    filter_upwards [hex] with ω hω
    obtain ⟨k, hk⟩ := hω
    exact mem_iUnion.2 ⟨k, hk⟩
  have hbound : ∀ k, ∫⁻ ω in A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 24 * ∫⁻ ω, (∫⁻ x in Ioc (0 : ℝ) T ×ˢ (univ : Set E), ‖φ ω x.1 x.2‖ₑ ^ 2 ∂(N.N ω))
        ^ (1 / 2 : ℝ) ∂P := by
    intro k
    obtain ⟨hm, hp, hq, hagree⟩ := hk k
    have hpredk : MarkedPredictable ℱ ν
        (Poisson.Compensated.markedStopped (τ k) φ) :=
      MVFBSDEJ.WellPosedness.Martingale.MarkedPredictable.markedStopped hpred h0 (hτ k)
    have h0k : ∀ ω s e, s ≤ 0 → Poisson.Compensated.markedStopped (τ k) φ ω s e = 0 :=
      fun ω s e hs => by simp [Poisson.Compensated.markedStopped, h0 ω s e hs]
    obtain ⟨V, -, hVae, hVr, -⟩ := Poisson.Compensated.exists_everywhere_cadlag_stochasticIntegral
      N ℱ hℱ _ hm hp hq hℱ0 hnull
    have hBDG := lintegral_biSup_le_compensated_count N ℱ hℱ hnull hm hp hq hpredk h0k hT
      (M := V) (fun t _ => hVae t) (ae_of_all _ fun ω t _ => hVr ω t)
    have hD : ∀ᵐ ω ∂P, (∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
        (((q : ℝ) : ℝ) : WithTop ℝ) ≤ τ k ω → M q ω = V q ω)
        ∧ (((T : ℝ) : WithTop ℝ) ≤ τ k ω → M T ω = V T ω) := by
      have hloc : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
          ((t : ℝ) : WithTop ℝ) ≤ τ k ω → M t ω = V t ω := by
        intro t ht
        filter_upwards [hagree t ht, hVae t] with ω h1 h2 hle
        rw [h1 hle, h2]
      refine (ae_all_iff.2 fun q => ?_).and (hloc T ⟨hT.le, le_rfl⟩)
      by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
      · filter_upwards [hloc q hq] with ω hω _ hle
        exact hω hle
      · exact ae_of_all _ fun ω h => absurd h hq
    have hle : ∀ᵐ ω ∂P, ω ∈ A k →
        ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ≤ ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞) := by
      filter_upwards [hD] with ω hω hωA
      have hωA' : ((T : ℝ) : WithTop ℝ) ≤ τ k ω := hωA
      have heq : ∀ t ∈ Icc (0 : ℝ) T, M t ω = V t ω := by
        intro t ht
        rcases eq_or_lt_of_le ht.2 with htT | htT
        · rw [htT]
          exact hω.2 hωA'
        · refine eq_of_rightCont_of_eq_rat (f := fun s => M s ω) (g := fun s => V s ω) htT
            (hMr ω t ⟨ht.1, htT⟩) (hVr ω t) fun q hq1 hq2 => ?_
          exact hω.1 q ⟨ht.1.trans hq1.le, hq2.le⟩
            ((WithTop.coe_le_coe.mpr hq2.le).trans hωA')
      exact le_of_eq (iSup_congr fun t => iSup_congr fun ht => by rw [heq t ht])
    calc ∫⁻ ω in A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
        ≤ ∫⁻ ω in A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞) ∂P :=
          lintegral_mono_ae ((ae_restrict_iff' (hAm k)).2 hle)
      _ ≤ ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞) ∂P := setLIntegral_le_lintegral _ _
      _ ≤ _ := hBDG
      _ ≤ 24 * ∫⁻ ω, (∫⁻ x in Ioc (0 : ℝ) T ×ˢ (univ : Set E), ‖φ ω x.1 x.2‖ₑ ^ 2
            ∂(N.N ω)) ^ (1 / 2 : ℝ) ∂P := by
          gcongr with ω x
          split_ifs <;> simp
  calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      = ∫⁻ ω in ⋃ k, A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P := by
        rw [Measure.restrict_eq_self_of_ae_mem hAunion]
    _ = ⨆ k, ∫⁻ ω in A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P :=
        setLIntegral_iUnion_of_directed _ hAdir
    _ ≤ _ := iSup_le hbound

end Main

end MVFBSDEJ.WellPosedness.Martingale
