/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec2Basics
import MVFBSDEJ.WellPosedness.BrownianPoisson.Compensation
import MVFBSDEJ.WellPosedness.Enlarged.Representation
import MVFBSDEJ.WellPosedness.Enlarged.PredictableRepresentation
import MVFBSDEJ.WellPosedness.Enlarged.RepresentationUnique
import MVFBSDEJ.Law.LpSection
import MVFBSDEJ.Law.FubiniLp
import MVFBSDEJ.WellPosedness.Existence.AffineExample

/-!
# Section 2 of the well-posedness paper: proofs for the setting

## Main statements

* `MVFBSDEJ.Acceptance.sec2_separable`, `sec2_infinite_activity` — the first paragraph.
* `MVFBSDEJ.Acceptance.eq_compid`, `eq_zeromean`, `eq_fubiniiso` — (2.1), (2.2), (2.4).
* `MVFBSDEJ.Acceptance.sec2_prp` — the predictable representation property.
* `MVFBSDEJ.Acceptance.sec2_hborel` — joint pointwise measurability of `h` gives (2.3).
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Enlarged
  MVFBSDEJ.WellPosedness.BrownianPoisson

universe u v w

/-- §2, `L²(ν; ℝʲ)` is separable. -/
theorem sec2_separable : PaperSpec.sec2_separable.{v} :=
  fun _ _ _ _ _ => inferInstance

/-- §2, infinitely many atoms on every interval when `ν(E) = ∞`. -/
theorem sec2_infinite_activity : PaperSpec.sec2_infinite_activity.{u, v, w} := by
  intro Ω _ P _ E _ ν _ d D hν
  have hinf : ∀ q r : ℝ, 0 ≤ q → q < r →
      LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc q r ×ˢ Set.univ) = ⊤ := by
    intro q r hq hqr
    rw [LevyStochCalc.Poisson.referenceIntensity, Measure.prod_prod, hν,
      Measure.restrict_apply measurableSet_Ioc,
      Set.inter_eq_left.mpr (fun (x : ℝ) (hx : x ∈ Set.Ioc q r) =>
        Set.mem_Ici.mpr (hq.trans hx.1.le)), Real.volume_Ioc]
    exact ENNReal.mul_top (by simpa using hqr)
  have hq : ∀ᵐ ω ∂P, ∀ q r : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) < r →
      D.N.N ω (Set.Ioc (q : ℝ) r ×ˢ Set.univ) = ⊤ := by
    refine ae_all_iff.mpr fun q => ae_all_iff.mpr fun r => ?_
    by_cases h : 0 ≤ (q : ℝ) ∧ (q : ℝ) < r
    · filter_upwards [D.N.infinite_at_infinite_intensity (measurableSet_Ioc.prod MeasurableSet.univ)
        (hinf q r h.1 h.2)] with ω hω _ _ using hω
    · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ h
  filter_upwards [hq] with ω hω s t hs hst
  obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn hst
  obtain ⟨r, hqr, hrt⟩ := exists_rat_btwn hqt
  refine top_le_iff.mp ((hω q r (hs.trans hsq.le) (by exact_mod_cast hqr)).symm.le.trans ?_)
  refine measure_mono (Set.prod_mono (fun x hx => ⟨hsq.trans hx.1, hx.2.trans hrt.le⟩) le_rfl)

/-- (2.1), the compensation formula. -/
theorem eq_compid : PaperSpec.eq_compid.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ d P _ D h𝒢₀ hind₀ T ψ hψ
  exact (aemeasurable_and_lintegral_compensation (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T
    hψ).2.2

/-- (2.2), the compensated integral has mean zero. -/
theorem eq_zeromean : PaperSpec.eq_zeromean.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ d P _ D h𝒢₀ hind₀ T ψ hψ hfin
  exact integral_compensated_eq_zero (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T hψ hfin

/-- §2, the predictable representation property over the enlarged filtration. -/
theorem sec2_prp : PaperSpec.sec2_prp.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ _ ν _ d P _ D h𝒢₀ hind₀ hd T hT M hM hM2
  set ℱ := enlJoint 𝒢₀ D h𝒢₀ with hℱ
  have hW := isBrownianFiltration_enlJoint D h𝒢₀ hind₀
  have hN := isPoissonFiltration_enlJoint D h𝒢₀ hind₀
  refine ⟨?_, ?_⟩
  · have hMm : AEStronglyMeasurable[ℱ T] (M T) P := (hM.1 T).aestronglyMeasurable
    obtain ⟨G, K, hrep⟩ := exists_jointIntegral_enlJoint D h𝒢₀ hind₀ hd hT (hM2 T) hMm
    obtain ⟨G', K', hG'p, hK'p, hG'K'⟩ :=
      exists_predictable_of_jointIntegral_enlJoint D h𝒢₀ hind₀ hT G K
    have hrep' : M T =ᵐ[P] fun ω => P[M T | ℱ 0] ω
        + LevyStochCalc.Driver.LevyDriver.jointIntegral hW hN G' K' ω := by
      filter_upwards [hrep, hG'K'] with ω h1 h2
      rw [h1, h2]
    refine ⟨fun s ω j => (G' j).toFun ω s, fun s ω e => K'.toFun ω s e, hG'p,
      fun ω s hs => funext fun j => (G' j).vanishing ω s hs, fun j => (G' j).energy_ne_top,
      hK'p, fun ω s e hs => K'.vanishing ω s e hs, K'.energy_ne_top, fun t ht => ?_⟩
    have hc := condExp_enlJoint_eq_jointIntegralProcess D h𝒢₀ hind₀ G' K' hrep' ht.2
    filter_upwards [hc, hM.condExp_ae_eq ht.2, hM.condExp_ae_eq (ht.1.trans ht.2)] with ω h1 h2 h3
    rw [← h2, h1, h3, add_assoc]
    rfl
  · intro Z Z' U U' ⟨hZ, hZv, hZe, hU, hUv, hUe, hrep⟩ ⟨hZ', hZv', hZe', hU', hUv', hUe', hrep'⟩
    let G : ∀ _ : Fin d, LevyStochCalc.Brownian.Ito.HorizonIntegrand P ℱ T := fun j =>
      ⟨fun ω s => Z s ω j, LevyStochCalc.Brownian.Ito.measurable_uncurry_of_predictable (hZ j),
        progressivelyMeasurable_of_predictable_of_vanish hZ hZv j,
        fun ω s hs => by simp only [hZv ω s hs, Pi.zero_apply], hZe j⟩
    let G' : ∀ _ : Fin d, LevyStochCalc.Brownian.Ito.HorizonIntegrand P ℱ T := fun j =>
      ⟨fun ω s => Z' s ω j, LevyStochCalc.Brownian.Ito.measurable_uncurry_of_predictable (hZ' j),
        progressivelyMeasurable_of_predictable_of_vanish hZ' hZv' j,
        fun ω s hs => by simp only [hZv' ω s hs, Pi.zero_apply], hZe' j⟩
    let K : LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T :=
      ⟨fun ω s e => U s ω e, hU.mono (LevyStochCalc.Probability.markedPredictableSigma_le _ ν)
        le_rfl, hU.markedProgressivelyMeasurable, fun ω s e hs => hUv ω s e hs, hUe⟩
    let K' : LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T :=
      ⟨fun ω s e => U' s ω e, hU'.mono (LevyStochCalc.Probability.markedPredictableSigma_le _ ν)
        le_rfl, hU'.markedProgressivelyMeasurable, fun ω s e hs => hUv' ω s e hs, hUe'⟩
    have hc : AEStronglyMeasurable[ℱ 0] (M 0) P := (hM.1 0).aestronglyMeasurable
    have heq : (fun ω => M 0 ω + LevyStochCalc.Driver.LevyDriver.jointIntegral hW hN G K ω)
        =ᵐ[P] fun ω => M 0 ω + LevyStochCalc.Driver.LevyDriver.jointIntegral hW hN G' K' ω := by
      filter_upwards [hrep T ⟨hT.le, le_rfl⟩, hrep' T ⟨hT.le, le_rfl⟩] with ω h1 h2
      have e1 : M 0 ω + LevyStochCalc.Driver.LevyDriver.jointIntegral hW hN G K ω = M T ω := by
        rw [h1, add_assoc]
        rfl
      have e2 : M 0 ω + LevyStochCalc.Driver.LevyDriver.jointIntegral hW hN G' K' ω = M T ω := by
        rw [h2, add_assoc]
        rfl
      rw [e1, e2]
    obtain ⟨-, hZ0, hU0⟩ := add_jointIntegral_unique_enlJoint D h𝒢₀ hind₀ hT hc hc heq
    exact ⟨hZ0, hU0⟩

/-- The paragraph after (2.3): joint pointwise measurability of `h` gives (2.3). -/
theorem sec2_hborel : PaperSpec.sec2_hborel.{v} := by
  intro E mE ν _ _ n m d T C H hH hrep
  letI : MeasurableSpace (Set.Icc (0 : ℝ) T × WellPosedness.System.TupleH ν n m d ×
    WellPosedness.System.TupleP2WH ν n m d) := borel _
  letI : MeasurableSpace (Lp (EuclideanSpace ℝ (Fin n)) 2 ν) := borel _
  haveI : BorelSpace (Lp (EuclideanSpace ℝ (Fin n)) 2 ν) := ⟨rfl⟩
  exact MVFBSDEJ.Law.measurable_lp_of_measurable_uncurry hH hrep

/-- (2.4), the Fubini isometry. -/
theorem eq_fubiniiso : PaperSpec.eq_fubiniiso.{u, v} := by
  intro X _ μ _ E _ ν _ _ j
  refine ⟨⟨MVFBSDEJ.Law.fubiniEquiv, MVFBSDEJ.Law.ae_coeFn_fubiniEquiv⟩,
    fun u => ⟨⇑(MVFBSDEJ.Law.fubiniEquiv.symm u), (Lp.stronglyMeasurable _).measurable, ?_⟩,
    fun u g g' hg hg' h h' => MVFBSDEJ.Law.ae_eq_of_ae_sections hg.stronglyMeasurable
      hg'.stronglyMeasurable h h'⟩
  have h := MVFBSDEJ.Law.ae_coeFn_fubiniEquiv (μ := μ) (ν := ν)
    (MVFBSDEJ.Law.fubiniEquiv.symm u)
  rwa [LinearIsometryEquiv.apply_symm_apply] at h

/-- **The hypotheses of the infinite-activity claim hold.** Lebesgue measure on `ℝ` is σ-finite
of infinite mass, and some probability space carries a Lévy driver with `d = 1` and that
intensity. -/
theorem sec2_infinite_activity_hypotheses :
    (volume : Measure ℝ) Set.univ = ⊤ ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P),
      Nonempty (LevyStochCalc.Driver.LevyDriver P 1 (volume : Measure ℝ)) :=
  ⟨Real.volume_univ, LevyStochCalc.Driver.LevyDriver.exists 1 ℝ volume⟩

/-- **The setting of §2 is realised.** Over a probability space carrying a Lévy driver with
`d = 1` and `ν = δ₀`, `𝒢₀ = ⊥` is independent of the driver, `0 < d`, `T = 1 > 0`, the zero
process is a square-integrable martingale of the enlarged filtration, and `ψ = 0` is measurable
for the marked predictable σ-algebra with `𝔼 ∫_0^1 ∫ |ψ| ν(de) ds < ∞`. -/
theorem sec2_setting_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ))),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P
      ∧ (0 : ℕ) < 1 ∧ (0 : ℝ) < 1
      ∧ Martingale (fun (_ : ℝ) (_ : Ω) => (0 : ℝ)) (enlJoint ⊥ D bot_le) P
      ∧ (∀ t : ℝ, MemLp ((fun (_ : ℝ) (_ : Ω) => (0 : ℝ)) t) 2 P)
      ∧ Measurable[LevyStochCalc.Probability.markedPredictableSigma (enlJoint ⊥ D bot_le)
          (Measure.dirac (0 : ℝ))] (fun _ : Ω × ℝ × ℝ => (0 : ℝ))
      ∧ ∫⁻ ω, (∫⁻ s in Set.Ioc (0 : ℝ) 1, ∫⁻ e, ‖(fun _ : Ω × ℝ × ℝ => (0 : ℝ)) (ω, s, e)‖ₑ
          ∂(Measure.dirac (0 : ℝ))) ∂P < ⊤ := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  refine ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, one_pos, one_pos,
    martingale_zero _ _ _, fun _ => memLp_const 0, measurable_const, by simp⟩

/-- **The hypotheses of the paragraph after (2.3) hold.** At `ν = δ₀`, `n = m = d = 1`, `T = 1`,
the coefficients of Example 5.1(i) with `β₁ = β₂ = 0`, `σ_c = 0`, `h_c = 0` have `h = 0`, and the
zero function on `([0, 1] × H × P₂(H)) × ℝ` is measurable and represents it. -/
theorem sec2_hborel_hypotheses :
    Measurable[(borel (Set.Icc (0 : ℝ) 1 × TupleH (Measure.dirac (0 : ℝ)) 1 1 1
        × TupleP2WH (Measure.dirac (0 : ℝ)) 1 1 1)).prod (inferInstance : MeasurableSpace ℝ)]
      (fun _ => (0 : EuclideanSpace ℝ (Fin 1)))
    ∧ ∀ p : Set.Icc (0 : ℝ) 1 × TupleH (Measure.dirac (0 : ℝ)) 1 1 1
        × TupleP2WH (Measure.dirac (0 : ℝ)) 1 1 1,
      ((MVFBSDEJ.WellPosedness.Existence.affineCoeffs (ν := Measure.dirac (0 : ℝ)) (d := 1)
          0 0 0 0).h p.1 p.2.1 p.2.2.toP2 : ℝ → EuclideanSpace ℝ (Fin 1))
        =ᵐ[Measure.dirac (0 : ℝ)] fun e => (fun _ => (0 : EuclideanSpace ℝ (Fin 1))) (p, e) := by
  refine ⟨measurable_const, fun p => ?_⟩
  simp only [MVFBSDEJ.WellPosedness.Existence.affineCoeffs, zero_smul, sub_zero]
  exact Lp.coeFn_zero _ _ _

end MVFBSDEJ.Acceptance
