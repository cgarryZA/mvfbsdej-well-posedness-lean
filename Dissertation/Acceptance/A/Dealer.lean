/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec5
import Dissertation.Acceptance.A.Sec3
import Dissertation.Law.CrowdTwoPoint
import Dissertation.WellPosedness.Examples.Dealer.ExposureWellPosed
import Dissertation.WellPosedness.Examples.Dealer.ExposureMarks
import Dissertation.WellPosedness.Examples.MeanFieldWP
import Dissertation.WellPosedness.Analysis.SMin
import Dissertation.Acceptance.A.Sec4
import Dissertation.WellPosedness.Examples.Dealer.Inert
import Dissertation.WellPosedness.Examples.Dealer.ExposureInteraction
import Dissertation.WellPosedness.Examples.Dealer.ExposureActivity

/-!
# Example 5.5 of the well-posedness paper: proofs

## Main statements

* `Dissertation.Acceptance.A.ex55Crowd_eq`, `ex55Coeffs_eq` — the crowding correction and the
  coefficients of Example 5.5 are `crowdOp` and `dealerExpCoeffs`.
* `Dissertation.Acceptance.A.ex_dealer_potential`, `ex_dealer_crowd`, `ex_dealer_coeffs`,
  `ex_dealer`, `ex_dealer_mono`, `ex_dealer_wp` — the potential, the crowding correction, the
  coefficients, the assumptions, the monotonicity and well-posedness.
* `Dissertation.Acceptance.A.ex_dealer_twopoint`, `ex_dealer_not_mean_corr`, `ex_dealer_affine` —
  beyond the mean.
* `Dissertation.Acceptance.A.ex_dealer_not_mean_false` — at `ν = 0` the crowding correction
  vanishes, so it is a function of the mean.
* `Dissertation.Acceptance.A.ex_dealer_marks` — the mark measure.
* `Dissertation.Acceptance.A.ex_dealer_inert` — the interaction is inert without the exposure
  term.
* `Dissertation.Acceptance.A.ex_dealer_active_data`, `ex_dealer_active_sde`,
  `ex_dealer_active_sol`, `ex_dealer_active_moments`, `ex_dealer_sym`, `ex_dealer_active_pos`,
  `ex_dealer_active_dep` — the interaction is active.
* `Dissertation.Acceptance.A.ex_dealer_hypotheses`, `ex_dealer_unit_hypotheses`,
  `ex_dealer_marks_hypotheses`, `ex_dealer_active_hypotheses` — the hypotheses hold on the mark
  space of the example.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.Law
  Dissertation.WellPosedness.Stability

universe u v w

/-- The crowding correction of Example 5.5 is `crowdOp`. -/
theorem ex55Crowd_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] (Λ : Measure F) (u : F) :
    PaperSpec.A.ex55Crowd Λ u = crowdOp Λ u :=
  rfl

/-- The coefficients of Example 5.5 are `dealerExpCoeffs`. -/
theorem ex55Coeffs_eq {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (β₁ β₂ : ℝ) (σc : EuclideanSpace ℝ (Fin 1 × Fin 1))
    (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) (hx : Lp ℝ 2 ν) (ε : ℝ) :
    PaperSpec.A.ex55Coeffs ν β₁ β₂ σc hc hx ε = dealerExpCoeffs β₁ β₂ σc hc hx ε := by
  have hb : (PaperSpec.A.ex55Coeffs ν β₁ β₂ σc hc hx ε).b
      = (dealerExpCoeffs β₁ β₂ σc hc hx ε).b := by
    funext t θ μ
    simp [PaperSpec.A.ex55Coeffs, dealerExpCoeffs, dealerCoeffs, Coeffs.perturb, affineCoeffs,
      crowdPert, exposurePert]
  have hσ : (PaperSpec.A.ex55Coeffs ν β₁ β₂ σc hc hx ε).σ
      = (dealerExpCoeffs β₁ β₂ σc hc hx ε).σ := by
    funext t θ μ
    simp [PaperSpec.A.ex55Coeffs, dealerExpCoeffs, dealerCoeffs, Coeffs.perturb, affineCoeffs,
      crowdPert, exposurePert]
  have hh : (PaperSpec.A.ex55Coeffs ν β₁ β₂ σc hc hx ε).h
      = (dealerExpCoeffs β₁ β₂ σc hc hx ε).h := by
    funext t θ μ
    rw [dealerExpCoeffs_h]
    rfl
  have hf : (PaperSpec.A.ex55Coeffs ν β₁ β₂ σc hc hx ε).f
      = (dealerExpCoeffs β₁ β₂ σc hc hx ε).f := by
    funext t θ μ
    rw [dealerExpCoeffs_f, exposurePair_eq_integral]
    rfl
  cases h : PaperSpec.A.ex55Coeffs ν β₁ β₂ σc hc hx ε
  cases h' : dealerExpCoeffs β₁ β₂ σc hc hx ε
  rw [h, h'] at hb hσ hh hf
  simp only at hb hσ hh hf
  subst hb hσ hh hf
  have hg : (PaperSpec.A.ex55Coeffs ν β₁ β₂ σc hc hx ε).g
      = (dealerExpCoeffs β₁ β₂ σc hc hx ε).g := rfl
  rw [h, h'] at hg
  simp only at hg
  rw [hg]

/-- Example 5.5, the potential. -/
theorem ex_dealer_potential : PaperSpec.A.ex_dealer_potential.{v} := by
  intro E _ ν
  exact ⟨crowdPot_neg, convexOn_crowdPot, hasGradientAt_crowdPot, norm_crowdGrad_le_one,
    norm_crowdGrad_sub_le⟩

/-- Example 5.5, the crowding correction is jointly Lipschitz. -/
theorem ex_dealer_crowd : PaperSpec.A.ex_dealer_crowd.{v} := by
  intro E _ ν _ _ Λ Λ' u u'
  exact norm_crowdOp_sub_le Λ Λ' u u'

/-- Example 5.5, the coefficients. -/
theorem ex_dealer_coeffs : PaperSpec.A.ex_dealer_coeffs.{v} := by
  intro E _ ν _ _
  refine ⟨fun β₁ β₂ σc hc => ?_, fun hx u x => ?_⟩
  · rw [ex55Coeffs_eq, dealerExpCoeffs_zero_zero]
  · have e : (fun x' => ⟪exposureOp hx x', u⟫)
        = fun x' => InnerProductSpace.toDual ℝ _ (exposurePair hx u) x' := by
      funext x'
      rw [InnerProductSpace.toDual_apply_apply, inner_exposurePair, real_inner_comm]
    rw [e, ← exposurePair_eq_integral]
    exact hasGradientAt_iff_hasFDerivAt.mpr (ContinuousLinearMap.hasFDerivAt _)

/-- Example 5.5, the assumptions. -/
theorem ex_dealer : PaperSpec.A.ex_dealer.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ _ T _ β₁ β₂ hβ₁ hβ₂ σc hc hx ε hε ξ₀ hξm hξ
  rw [ex55Coeffs_eq]
  obtain ⟨hB, hO, hL, hLT, -, -, -⟩ :=
    dealerExp_assumptions (σc := σc) (hc := hc) (hx := hx) (ℱ := enlJoint 𝒢₀ D h𝒢₀) (P := P)
      T hβ₁ hβ₂ hε
  refine ⟨fun t => ?_, jointBorel_iff.mpr ⟨hB, continuous_fst.borel_measurable⟩,
    ⟨hξm, hξ, originValues_iff_coeffOrigin.mpr hO⟩,
    ⟨zero_le_one.trans (le_max_right _ _), lipInterior_iff_diagonalLipschitzH.mpr hL,
      lipTerminal_iff_terminalLipschitz.mpr hLT⟩, rank_one_eq_min, ?_⟩
  · change (dealerCoeffs β₁ β₂ σc hc ε).h t 0 (P2.dirac 0) + exposureOp hx 0 = hc
    rw [dealerCoeffs_h_origin, map_zero, add_zero]
  · rw [Dissertation.WellPosedness.sMin_one]
    norm_num

/-- Example 5.5, monotonicity at every `ε ≥ 0`. -/
theorem ex_dealer_mono : PaperSpec.A.ex_dealer_mono.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc hx ε hε
  obtain ⟨-, hJ, -, h23, -, -⟩ :=
    ex_dealer 𝒢₀ ν P D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc hx ε hε (fun _ => 0)
      stronglyMeasurable_const (memLp_const _)
  rw [ex55Coeffs_eq] at hJ h23 ⊢
  obtain ⟨-, -, -, -, hconst, hM, hMT⟩ :=
    dealerExp_assumptions (σc := σc) (hc := hc) (hx := hx) (ℱ := enlJoint 𝒢₀ D h𝒢₀) (P := P)
      T hβ₁ hβ₂ hε
  refine ⟨fun t p hp p' hp' => ?_, fun x u => ?_, fun t p hp p' hp' => ?_,
    Assumption25.of_monotone hJ h23 hconst hM hMT⟩
  · obtain ⟨-, h2, h3⟩ := hp
    obtain ⟨-, h2', h3'⟩ := hp'
    rw [h3, h3']
    exact integral_inner_crowdOp_margU_sub_nonneg h2 h2'
  · rw [← exposurePair_eq_integral]
    exact inner_exposureOp_sub_inner_exposurePair hx x u
  · obtain ⟨-, h2, h3⟩ := hp
    obtain ⟨-, h2', h3'⟩ := hp'
    have hle := integral_jump_driver_dealerExp_le (β₁ := β₁) (β₂ := β₂) (σc := σc) (hc := hc)
      (hx := hx) hε t h2 h2'
    rw [← h3, ← h3'] at hle
    refine le_of_eq_of_le (integral_congr_ae (ae_of_all _ fun ω => ?_)) hle
    simp only
    congr 1
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub ((dealerExpCoeffs β₁ β₂ σc hc hx ε).h t (p.1 ω) p.2)
        ((dealerExpCoeffs β₁ β₂ σc hc hx ε).h t (p'.1 ω) p'.2),
      Lp.coeFn_sub (p.1 ω).2.2.2 (p'.1 ω).2.2.2] with e h₁ h₂
    rw [h₁, h₂, Pi.sub_apply, Pi.sub_apply]

/-- Example 5.5, well-posedness at every `ε ≥ 0`. -/
theorem ex_dealer_wp : PaperSpec.A.ex_dealer_wp.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc hx ε hε ξ₀ hξm hξ
  obtain ⟨-, hJ, h22, h23, hG, -⟩ :=
    ex_dealer 𝒢₀ ν P D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc hx ε hε ξ₀ hξm hξ
  obtain ⟨-, -, -, h25⟩ := ex_dealer_mono 𝒢₀ ν P D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc hx ε hε
  exact thm_cwp 𝒢₀ ν 1 1 1 P D h𝒢₀ hind₀ one_pos one_pos one_pos T hT _ 1 β₁ β₂ 1 _ ξ₀ hJ h22
    h23 hG h25

/-- The symmetric two-point law `½ (δ_{−a} + δ_a)` as a measure. -/
theorem twoPoint_law_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (a : F) :
    (P2.twoPoint a).law = (1 / 2 : ℝ≥0∞) • (Measure.dirac (-a) + Measure.dirac a) := by
  have hlaw : (P2.twoPoint a).law
      = ENNReal.ofReal (1 - 1 / 2) • Measure.dirac (-a)
        + ENNReal.ofReal (1 / 2) • Measure.dirac a :=
    rfl
  have h : ENNReal.ofReal (1 / 2) = 1 / 2 := by
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rw [hlaw, smul_add, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, h]

/-- Example 5.5, the two-point laws. -/
theorem ex_dealer_twopoint : PaperSpec.A.ex_dealer_twopoint.{v} := by
  intro E _ ν _ _ w hw
  simp only
  rw [← twoPoint_law_eq, ← twoPoint_law_eq, integral_id_twoPoint, integral_id_twoPoint,
    ex55Crowd_eq, ex55Crowd_eq, crowdOp_twoPoint_one hw, crowdOp_twoPoint_two hw]
  refine ⟨rfl, rfl, ?_⟩
  congr 1
  ring

/-- **Example 5.5, the crowding correction as no function of the mean, is false as printed at
`ν = 0`.** With the intensity `ν = 0` on a one-point mark space the fibre `L²(ν)` is `{0}`, so
`A_λ(u) = Φ(∫ v λ(dv), u)` holds for every `λ` and `u` with `Φ = 0`. -/
theorem ex_dealer_not_mean_false : ¬ PaperSpec.A.ex_dealer_not_mean.{v} := by
  intro h
  exact (h (E := PUnit.{v + 1}) (0 : Measure PUnit.{v + 1})).1
    ⟨fun _ _ => 0, fun _ _ => Subsingleton.elim _ _⟩

/-- The crowding gradient is not homogeneous: `∇V(2 w) ≠ 2 ∇V(w)` for a unit vector `w`. -/
theorem crowdGrad_two_smul_ne {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {w : F} (hw : ‖w‖ = 1) : crowdGrad ((2 : ℝ) • w) ≠ (2 : ℝ) • crowdGrad w := by
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; exact one_ne_zero)
  have h1 : crowdGrad w = (1 / Real.sqrt (1 + 1 ^ 2)) • w := by
    rw [← crowdGrad_smul_of_norm_eq_one hw, one_smul]
  rw [crowdGrad_smul_of_norm_eq_one hw, h1, smul_smul]
  intro h
  have h' := smul_left_injective ℝ hw0 h
  have h5 : Real.sqrt 2 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2p : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  norm_num at h'
  rw [← div_eq_mul_inv] at h'
  linarith [div_lt_div_of_pos_left two_pos h2p h5]

/-- Example 5.5, the crowding correction is no function of the mean and is nonlinear in the
valuation curve when `L²(ν) ≠ 0`. -/
theorem ex_dealer_not_mean_corr : PaperSpec.A.ex_dealer_not_mean_corr.{v} := by
  intro E _ ν _ _ ⟨u, hu⟩
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hw : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  refine ⟨fun ⟨Φ, hΦ⟩ => crowdOp_not_mean_function hw
    ⟨fun m => Φ m (‖u‖⁻¹ • u), fun Λ => hΦ Λ _⟩, P2.dirac 0, fun hL => ?_⟩
  have h := hL.map_smul (2 : ℝ) (‖u‖⁻¹ • u)
  change crowdOp (Measure.dirac 0) _ = (2 : ℝ) • crowdOp (Measure.dirac 0) _ at h
  rw [crowdOp_dirac, crowdOp_dirac, sub_zero, sub_zero] at h
  exact crowdGrad_two_smul_ne hw h

/-- Example 5.5, the crowding correction is affine in the law and an expectation kernel. -/
theorem ex_dealer_affine : PaperSpec.A.ex_dealer_affine.{v} := by
  intro E _ ν _ _
  refine ⟨fun Λ₁ Λ₂ s hs u => crowdOp_smul_add_smul Λ₁.law Λ₂.law hs u, fun μ u => ?_,
    fun θ₁ θ₁' θ₂ θ₂' => ?_⟩
  · rw [ex55Crowd_eq, crowdOp, margU_law, integral_map measurable_projUH.aemeasurable
      (stronglyMeasurable_crowdGrad_sub u).aestronglyMeasurable]
    rfl
  · have h := norm_crowdGrad_sub_le (θ₁.2.2.2 - θ₁'.2.2.2) (θ₂.2.2.2 - θ₂'.2.2.2)
    have e : θ₁.2.2.2 - θ₁'.2.2.2 - (θ₂.2.2.2 - θ₂'.2.2.2)
        = projUH (θ₁ - θ₂) - projUH (θ₁' - θ₂') := by
      rw [map_sub, map_sub]
      simp only [projUH_apply]
      abel
    have h₁ := norm_projUH_le_norm_toL2 (θ₁ - θ₂)
    have h₂ := norm_projUH_le_norm_toL2 (θ₁' - θ₂')
    rw [toL2_sub] at h₁ h₂
    calc _ = ‖crowdGrad (θ₁.2.2.2 - θ₁'.2.2.2) - crowdGrad (θ₂.2.2.2 - θ₂'.2.2.2)‖ := rfl
      _ ≤ ‖projUH (θ₁ - θ₂) - projUH (θ₁' - θ₂')‖ := e ▸ h
      _ ≤ ‖projUH (θ₁ - θ₂)‖ + ‖projUH (θ₁' - θ₂')‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add h₁ h₂

/-- Example 5.5, the mark measure. -/
theorem ex_dealer_marks : PaperSpec.A.ex_dealer_marks := by
  intro c hc ϱ hϱ0 hϱ2
  have e : (fun e : Bool × Set.Ioc (0 : ℝ) 1 => (if e.1 then 1 else -1) * (e.2 : ℝ))
      = signedSize := rfl
  exact ⟨dealerMarks_univ hc hϱ0.le, lintegral_sq_dealerMarks_lt_top c hϱ2,
    e ▸ memLp_signedSize c hϱ2⟩

/-- Example 5.5, the interaction is inert without the exposure term. -/
theorem ex_dealer_inert : PaperSpec.A.ex_dealer_inert.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc ξ₀ hξm hξ
  set p : ℝ → ℝ := fun t => inertP β₁ β₂ T (clampTime T t) with hp_def
  have hpI : ∀ t ∈ Set.Icc (0 : ℝ) T, p t = inertP β₁ β₂ T t := fun t ht => by
    simp only [hp_def, clampTime_of_mem ht]
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt p (β₁ * p t ^ 2 - β₂) (Set.Icc 0 T) t := by
    intro t ht
    rw [hpI t ht]
    exact ((hasDerivAt_inertP hβ₁.le hβ₂.le ht.2).hasDerivWithinAt).congr
      (fun y hy => hpI y hy) (hpI t ht)
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) T, p t / (1 + β₁ * p t) = inertGain β₁ β₂ T t :=
    fun t ht => by rw [hpI t ht]; rfl
  refine ⟨p, fun t ht => ⟨(hpI t ht).symm ▸ inertP_pos hβ₁.le hβ₂.le ht.2, hderiv t ht⟩,
    by rw [hpI T ⟨hT.le, le_rfl⟩, inertP_self], fun q hq hqT t ht => ?_, ?_⟩
  · exact (eqOn_inertP_of_hasDerivWithinAt hβ₁.le hβ₂.le (fun s hs => (hq s hs).2) hqT ht).trans
      (hpI t ht).symm
  intro Z U
  have hZ : Z = inertZ Ω β₁ β₂ T σc := by
    funext k t ω j
    simp only [Z, inertZ]
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, hg t ht]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  have hgI : (Set.Ioc (0 : ℝ) T).indicator (fun s => p s / (1 + β₁ * p s))
      = (Set.Ioc (0 : ℝ) T).indicator (inertGain β₁ β₂ T) :=
    Set.indicator_congr fun t ht => hg t (Set.Ioc_subset_Icc_self ht)
  have hU : U = inertU Ω β₁ β₂ T hc := by
    funext k t ω e
    simp only [U, inertU, hgI]
  rw [hZ, hU, hgI]
  have hξ' : ∀ i, MemLp (fun ω => ξ₀ ω i) 2 P := fun i => memLp_iff_forall_coord.mp hξ i
  have hξm' : ∀ i, Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] (fun ω => ξ₀ ω i) := fun i =>
    stronglyMeasurable_iff_forall_coord.mp hξm i
  obtain ⟨X, hX, hsol, -, -⟩ := exists_paperSolutionEnl_dealer_inert (σc := σc) (hc := hc)
    (ξ₀ := fun i ω => ξ₀ ω i) D h𝒢₀ hind₀ hT hβ₁.le hβ₂.le hξ' hξm'
  obtain ⟨X', Y', h', hX'l, hY'l, hae⟩ := (hsol 0).2.exists_cadlag_version hT.le
    (coeffBorel_dealer T) measurableSet_enlJoint_of_null_all
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0
  -- the tuple of the version is square integrable at almost every time
  have hmem : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      MemLp (tupleAt ν (leftLimProc X') (leftLimProc Y') (inertZ Ω β₁ β₂ T σc)
        (inertU Ω β₁ β₂ T hc) s) 2 P := by
    filter_upwards [h'.ae_ae_tupleAt_leftLimProc_eq hT.le,
      SolvesForced.ae_memLp_tupleAt (solves_dealer_inert hβ₁.le hβ₂.le hT.le hX)
        (crossWitnessEnl D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀) hnull hT,
      ae_restrict_mem measurableSet_Icc] with s hs hL hsI
    refine (hL.ae_eq ?_).ae_eq hs.symm
    filter_upwards [hae] with ω hω
    exact (tupleAt_apply_eq_of_eq (fun i => (hω s hsI).1 i) (fun k => (hω s hsI).2 k)).symm
  have hcrowd : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ ω,
      crowdOp (lawP2 P (tupleAt ν (leftLimProc X') (leftLimProc Y') (inertZ Ω β₁ β₂ T σc)
          (inertU Ω β₁ β₂ T hc) s)).margU.law
        (tupleAt ν (leftLimProc X') (leftLimProc Y') (inertZ Ω β₁ β₂ T σc)
          (inertU Ω β₁ β₂ T hc) s ω).2.2.2 = 0 := by
    filter_upwards [hmem] with s hs ω
    exact crowdOp_margU_inertU hs ω
  refine ⟨X', Y', fun k => ?_, fun ε _ => ⟨⟨inertJump Ω β₁ β₂ T hc, ?_⟩, hX'l, hY'l⟩, ?_⟩
  · filter_upwards [hae] with ω hω t ht
    rw [(hω t ht).2 k, (hω t ht).1 k]
  · rw [ex55Coeffs_eq, dealerExpCoeffs_zero]
    refine PaperSolution.of_h_ae_eq (C := dealerCoeffs β₁ β₂ σc hc 0) rfl rfl rfl rfl ?_ h'
    filter_upwards [hcrowd] with s hs
    refine Eventually.of_forall fun ω => ?_
    rw [dealerCoeffs_h, dealerCoeffs_h, hs ω, smul_zero, smul_zero]
  · filter_upwards [hmem, hcrowd] with s hs hs'
    exact ⟨margU_lawP2_inertU hs, fun ω => hs' ω⟩

/-- A path right-continuous on `[0, T)` with left limits on `(0, T]` agrees with its left limits
at almost every time of `[0, T]`. -/
theorem ae_leftLim_eq_of_rightCont_leftLim {f : ℝ → ℝ} {T : ℝ}
    (hr : ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hl : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L)) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Function.leftLim f s = f s := by
  set g : ℝ → ℝ := fun s => f (max 0 (min s T)) with hg
  have hgr : ∀ t : ℝ, Tendsto g (𝓝[>] t) (𝓝 (g t)) := by
    intro t
    rcases lt_or_ge t 0 with ht0 | ht0
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT ht0] with s hs
      simp only [hg, max_eq_left ((min_le_left s T).trans hs.2.le),
        max_eq_left ((min_le_left t T).trans ht0.le)]
    rcases lt_or_ge t T with htT | htT
    · have hgt : g t = f t := by simp only [hg, min_eq_left htT.le, max_eq_right ht0]
      rw [hgt]
      refine (hr t ⟨ht0, htT⟩).congr' ?_
      filter_upwards [Ioo_mem_nhdsGT htT] with s hs
      simp only [hg, min_eq_left hs.2.le, max_eq_right (ht0.trans hs.1.le)]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s (hs : t < s)
      simp only [hg, min_eq_right (htT.trans hs.le), min_eq_right htT]
  have hgl : ∀ t : ℝ, ∃ L : ℝ, Tendsto g (𝓝[<] t) (𝓝 L) :=
    exists_tendsto_comp_clamp_nhdsLT hl
  have hae := LevyStochCalc.Analysis.ae_eq_leftLim_of_cadlag hgr hgl
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hae, (Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := T)).mem_iff]
    with s hs hIoo hsI
  have hs' : s ∈ Set.Ioo (0 : ℝ) T := hIoo.mpr hsI
  obtain ⟨L, hL⟩ := hl s ⟨hs'.1, hs'.2.le⟩
  have hLg : Tendsto g (𝓝[<] s) (𝓝 L) := by
    refine hL.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hs'.1] with r hr
    simp only [hg, min_eq_left (hr.2.le.trans hs'.2.le), max_eq_right hr.1.le]
  have hgs : g s = f s := by simp only [hg, min_eq_left hs'.2.le, max_eq_right hs'.1.le]
  rw [leftLim_eq_of_tendsto hL, ← leftLim_eq_of_tendsto hLg, ← hs, hgs]

/-- A marked integrand vanishing at almost every time, almost surely, for almost every mark has
zero marked energy. -/
theorem markedEnergy_eq_zero_of_ae_ae_ae {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {ν : Measure E} {T : ℝ} {φ : Ω → ℝ → E → ℝ}
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν, φ ω s e = 0) :
    LevyStochCalc.Poisson.Compensated.markedEnergy P ν T φ = 0 := by
  unfold LevyStochCalc.Poisson.Compensated.markedEnergy
  refine (lintegral_congr_ae (h.mono fun ω hω => ?_)).trans lintegral_zero
  refine (lintegral_congr_ae (hω.mono fun s hs => ?_)).trans lintegral_zero
  refine (lintegral_congr_ae (hs.mono fun e he => ?_)).trans lintegral_zero
  simp [he]

/-- An integrand vanishing at almost every time, almost surely, has zero energy. -/
theorem energy_eq_zero_of_ae_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℝ}
    {H : Ω → ℝ → ℝ} (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), H ω s = 0) :
    LevyStochCalc.Brownian.Ito.energy P T H = 0 := by
  unfold LevyStochCalc.Brownian.Ito.energy
  refine (lintegral_congr_ae (h.mono fun ω hω => ?_)).trans lintegral_zero
  refine (lintegral_congr_ae (hω.mono fun s hs => ?_)).trans lintegral_zero
  simp [hs]

section Active

variable {ϱ : ℝ}

/-- The profile `h_c(ς, q) = ς q` of the active case is `dealerJump`. -/
theorem active_hc_eq (hϱ : ϱ < 2)
    {hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ)}
    (h : (hc : DealerMark → EuclideanSpace ℝ (Fin 1)) =ᵐ[dealerMarks (fun _ => (2 - ϱ) / 2) ϱ]
      (fun e => WithLp.toLp 2 fun _ : Fin 1 => (if e.1 then 1 else -1) * (e.2 : ℝ))) :
    hc = dealerJump (fun _ => (2 - ϱ) / 2) hϱ := by
  refine Lp.ext (h.trans ?_)
  filter_upwards [coeFn_dealerJump (c := fun _ => (2 - ϱ) / 2) hϱ] with e he
  rw [he]
  ext i
  obtain rfl : i = 0 := Subsingleton.elim i 0
  simp [signedSize, markSide]

/-- The profile `h_x(ς, q) = q` of the active case is `dealerSize`. -/
theorem active_hx_eq (hϱ : ϱ < 2) {hx : Lp ℝ 2 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ)}
    (h : (hx : DealerMark → ℝ) =ᵐ[dealerMarks (fun _ => (2 - ϱ) / 2) ϱ] (fun e => (e.2 : ℝ))) :
    hx = dealerSize (fun _ => (2 - ϱ) / 2) hϱ :=
  Lp.ext (h.trans (coeFn_dealerSize hϱ).symm)

/-- The rate of the active case is `(2 − ϱ)/2` on both sides. -/
theorem active_rate (b : Bool) : (fun _ : Bool => (2 - ϱ) / 2) b = (2 - ϱ) / 2 :=
  rfl

end Active

/-- Example 5.5, the data of the active case. -/
theorem ex_dealer_active_data : PaperSpec.A.ex_dealer_active_data := by
  intro ϱ _ hϱ hc hx hhc hhx
  rw [active_hc_eq hϱ hhc, active_hx_eq hϱ hhx, ← exposurePair_eq_integral]
  exact ⟨norm_dealerJump_eq_one hϱ active_rate, norm_dealerSize_eq_one hϱ active_rate,
    exposurePair_dealerSize_dealerJump_eq_zero hϱ active_rate⟩

/-- Example 5.5, the exposure equation. -/
theorem ex_dealer_active_sde : PaperSpec.A.ex_dealer_active_sde.{u, w} := by
  intro Ω 𝒢₀ mΩ P _ ϱ _ hϱ D h𝒢₀ hind₀ T hT Sol
  obtain ⟨X, hX, -, Z, U, -, -, hp⟩ :=
    exists_paperSolutionEnl_activeDealer D h𝒢₀ hind₀ hϱ active_rate hT
  refine ⟨⟨X, hX, ?_⟩, fun X X' h h' =>
    linearFSDEJ_exposure_unique_enlJoint D h𝒢₀ hind₀ hϱ active_rate hT h h'⟩
  have h := hp.X_sup
  simpa [esq] using h

/-- Example 5.5, the solution at `ε = 0` in the active case. -/
theorem ex_dealer_active_sol : PaperSpec.A.ex_dealer_active_sol.{u, w} := by
  intro Ω 𝒢₀ mΩ P _ ϱ _ hϱ D h𝒢₀ hind₀ T hT hc hx hhc hhx
  rw [ex55Coeffs_eq, active_hc_eq hϱ hhc, active_hx_eq hϱ hhx]
  obtain ⟨X, hX, -, Z, U, hZ, hU, hp⟩ :=
    exists_paperSolutionEnl_activeDealer D h𝒢₀ hind₀ hϱ active_rate hT
  obtain ⟨X', Y', h', hX'l, hY'l, hae⟩ := hp.exists_cadlag_version hT.le
    (coeffBorel_dealerExp T) measurableSet_enlJoint_of_null_all
  refine ⟨X', Y', Z, U, ⟨⟨_, h'⟩, hX'l, hY'l⟩, ?_, ?_, ?_, fun X₀ hX₀ => ?_⟩
  · filter_upwards [hae] with ω hω t ht
    rw [(hω t ht).2 0, (hω t ht).1 0]
  · refine energy_eq_zero_of_ae_ae ?_
    filter_upwards [Measure.ae_ae_of_ae_prod (hZ 0 0)] with ω hω
    filter_upwards [hω] with s hs
    rw [← hs]
    simp only [exposureDiffusion, sub_self]
  · refine markedEnergy_eq_zero_of_ae_ae_ae ?_
    have hU' := Measure.ae_ae_of_ae_prod (hU 0)
    filter_upwards [hU', hae] with ω hω hωa
    filter_upwards [Measure.ae_ae_of_ae_prod hω, ae_restrict_mem measurableSet_Icc,
      ae_leftLim_eq_of_rightCont_leftLim (h'.X_rightCont 0 ω) (hX'l 0 ω)] with s hs hsI hsL
    filter_upwards [hs] with e he
    have hleft : leftLimProc X' 0 s ω = X s ω := by
      rw [leftLimProc, hsL, (hωa s hsI).1 0]
    rw [← he]
    simp only [exposureJump, signedSize, markSide, Set.indicator_of_mem hsI, hleft, sub_self]
  · filter_upwards [hae, linearFSDEJ_exposure_unique_enlJoint D h𝒢₀ hind₀ hϱ active_rate hT hX
      hX₀] with ω hω hω' t ht
    rw [(hω t ht).1 0, hω' t ht]

/-- Example 5.5, the moments of the active case. -/
theorem ex_dealer_active_moments : PaperSpec.A.ex_dealer_active_moments.{u, w} := by
  intro Ω 𝒢₀ mΩ P _ ϱ _ hϱ D h𝒢₀ hind₀ T hT hc hx hhc hhx X hX U
  have 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  have hU : ∀ t ∈ Set.Icc (0 : ℝ) T, U t = fun ω =>
      uLift (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ) (fun e (_ : Fin 1) => exposureJump T X t ω e) :=
    fun t ht => funext fun ω => by
      rw [uLift_exposureJump hϱ X ht ω, ← active_hc_eq hϱ hhc, ← active_hx_eq hϱ hhx]
  have hv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ ω, X t ω ^ 2 ∂P = 2 / 7 * (1 - Real.exp (-(7 / 4) * t)) := fun t ht => by
    simp_rw [sq]
    exact integral_mul_self_exposure_eq hϱ active_rate hX 𝒲 hT ht
  have hvar : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ ω, ‖U t ω - ∫ ω', U t ω' ∂P‖ ^ 2 ∂P = 1 / 14 * (1 - Real.exp (-(7 / 4) * t)) :=
    fun t ht => by
      rw [hU t ht]
      exact integral_norm_sub_integral_uLift_exposureJump_sq hϱ active_rate hX 𝒲 hT ht
  refine ⟨fun t ht => ⟨integral_exposure_eq_zero hϱ active_rate hX 𝒲 hT ht, ?_, ?_, ?_⟩,
    fun t ht => ⟨fun a ha => ?_, ?_⟩⟩
  · have hd : HasDerivAt (fun s : ℝ => 2 / 7 * (1 - Real.exp (-(7 / 4) * s)))
        (2 / 7 * (-(Real.exp (-(7 / 4) * t) * (-(7 / 4) * 1)))) t :=
      (((hasDerivAt_id t).const_mul (-(7 / 4))).exp.const_sub 1).const_mul (2 / 7)
    refine (hd.hasDerivWithinAt.congr (fun s hs => hv s hs) (hv t ht)).congr_deriv ?_
    rw [hv t ht]
    ring
  · rw [hvar t ht, hv t ht]
    ring
  · rw [hv t ht]
    ring
  · have htI := Set.Ioc_subset_Icc_self ht
    have hm : AEMeasurable (U t) P := by
      rw [hU t htI]
      exact (memLp_uLift_exposureJump hϱ hX hT htI).aestronglyMeasurable.aemeasurable
    have hae := (ae_eq_const_iff_map_eq_dirac hm a).mpr ha
    have h0 : ∫ ω, ‖U t ω - ∫ ω', U t ω' ∂P‖ ^ 2 ∂P = 0 := by
      rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul]
      refine integral_eq_zero_of_ae (hae.mono fun ω hω => ?_)
      simp [hω]
    rw [hvar t htI] at h0
    have : Real.exp (-(7 / 4) * t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [ht.1])
    linarith
  · have htI := Set.Ioc_subset_Icc_self ht
    have hmem : MemLp (U t) 2 P := by
      rw [hU t htI]
      exact memLp_uLift_exposureJump hϱ hX hT htI
    have h := not_ae_crowdOp_eq_zero_of_ae_eq_exposureJump hϱ active_rate hX 𝒲 hT ht
      (U := U t) (by rw [hU t htI])
    rwa [lawP2_law hmem] at h

/-- Example 5.5, the crowding pairing of a law. -/
theorem ex_dealer_sym : PaperSpec.A.ex_dealer_sym.{v} := by
  intro E _ ν _ _ Λ
  exact ⟨integral_inner_crowdOp_law Λ, integral_inner_crowdOp_law_pos Λ⟩

/-- Example 5.5, the interaction is active. -/
theorem ex_dealer_active_pos : PaperSpec.A.ex_dealer_active_pos.{u, w} := by
  rintro Ω 𝒢₀ mΩ P _ ϱ _ hϱ D h𝒢₀ hind₀ T hT hc hx hhc hhx ε hε X Y Z U ⟨⟨γ, h⟩, -, -⟩
  rw [ex55Coeffs_eq, active_hc_eq hϱ hhc, active_hx_eq hϱ hhx] at h
  exact integral_norm_smul_crowdOp_activeDealer_sq_pos hϱ active_rate hT hε.ne' h

/-- Example 5.5, the solution depends on the interaction strength. -/
theorem ex_dealer_active_dep : PaperSpec.A.ex_dealer_active_dep.{u, w} := by
  rintro Ω 𝒢₀ mΩ P _ ϱ _ hϱ D h𝒢₀ hind₀ T hT hc hx hhc hhx ε ε' _ _ hne X Y Z U ⟨⟨γ, h⟩, -, -⟩
    ⟨⟨γ', h'⟩, -, -⟩
  rw [ex55Coeffs_eq, active_hc_eq hϱ hhc, active_hx_eq hϱ hhx] at h h'
  exact not_paperSolutionEnl_activeDealer_of_ne hϱ active_rate hT hne h h'

/-! ### The hypotheses on the mark space of the example -/

/-- **The hypotheses of Example 5.5 hold on its mark space.** With `c_{±1} = 1/2` and `ϱ = 1`,
the mark measure `ν(dς, dq) = c_ς q^{−2} dq` on `{−1, +1} × (0, 1]` has `ν(E) = ∞`; over a
probability space carrying a Lévy driver with `d = 1` and mark measure `ν`, with `𝒢₀ = ⊥`
independent of the driver, the initial datum `0` is strongly measurable for the time-`0` field
of `enlJoint ⊥ D` and square integrable; and `T = β₁ = ε = 1`, `β₂ = 1/2` satisfy `T > 0`,
`β₁, β₂ > 0` and `ε ≥ 0`. -/
theorem ex_dealer_hypotheses :
    dealerMarks (fun _ => 1 / 2) 1 Set.univ = ⊤
    ∧ ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (dealerMarks (fun _ => 1 / 2) 1)),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P
      ∧ StronglyMeasurable[enlJoint ⊥ D bot_le 0] (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1)))
      ∧ MemLp (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1))) 2 P
      ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 / 2 ∧ (0 : ℝ) ≤ 1 := by
  refine ⟨dealerMarks_univ (fun _ => one_half_pos) zero_le_one, ?_⟩
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 DealerMark (dealerMarks (fun _ => 1 / 2) 1)
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, stronglyMeasurable_const,
    memLp_const _, one_pos, one_half_pos, zero_le_one⟩

/-- **A unit vector of `L²(ν)` on the mark space of the example.** With `c_{±1} = 1/2` and
`ϱ = 1`, the signed size `h_c(ς, q) = ς q` has `‖h_c‖_{L²(ν)} = 1`, so it is nonzero. -/
theorem ex_dealer_unit_hypotheses :
    ∃ w : Lp (EuclideanSpace ℝ (Fin 1)) 2 (dealerMarks (fun _ => 1 / 2) 1), ‖w‖ = 1 ∧ w ≠ 0 := by
  have hc : ∀ b : Bool, (fun _ : Bool => (1 / 2 : ℝ)) b = (2 - 1) / 2 := fun _ => by norm_num
  have hw := norm_dealerJump_eq_one (by norm_num : (1 : ℝ) < 2) hc
  exact ⟨_, hw, fun h => by rw [h, norm_zero] at hw; exact zero_ne_one hw⟩

/-- **The hypotheses of the mark measure of Example 5.5 hold**: `c_{±1} = 1/2 > 0` and
`0 < ϱ = 1 < 2`. -/
theorem ex_dealer_marks_hypotheses :
    (∀ b : Bool, 0 < (fun _ : Bool => (1 / 2 : ℝ)) b) ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) < 2 :=
  ⟨fun _ => one_half_pos, one_pos, one_lt_two⟩

/-- **The hypotheses of the active case of Example 5.5 hold.** With `ϱ = 1`, so
`c_{±1} = (2 − ϱ)/2 = 1/2`: over a probability space carrying a Lévy driver with `d = 1` and the
mark measure of the example, `𝒢₀ = ⊥` is independent of the driver; `T = 1 > 0`; the profiles
`h_c(ς, q) = ς q` and `h_x(ς, q) = q` lie in `L²(ν; ℝ¹)` and `L²(ν)`; and `ε = 1 > 0`,
`ε' = 0 ≠ ε`. -/
theorem ex_dealer_active_hypotheses :
    (0 : ℝ) < 1 ∧ (1 : ℝ) < 2
    ∧ (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (dealerMarks (fun _ => (2 - 1) / 2) 1)),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)
    ∧ (∃ (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 (dealerMarks (fun _ => (2 - 1) / 2) 1))
      (hx : Lp ℝ 2 (dealerMarks (fun _ => (2 - 1) / 2) 1)),
      (hc : DealerMark → EuclideanSpace ℝ (Fin 1)) =ᵐ[dealerMarks (fun _ => (2 - 1) / 2) 1]
        (fun e => WithLp.toLp 2 fun _ : Fin 1 => (if e.1 then 1 else -1) * (e.2 : ℝ))
      ∧ (hx : DealerMark → ℝ) =ᵐ[dealerMarks (fun _ => (2 - 1) / 2) 1] (fun e => (e.2 : ℝ)))
    ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) ≤ 0 ∧ (1 : ℝ) ≠ 0 := by
  have hϱ : (1 : ℝ) < 2 := one_lt_two
  refine ⟨one_pos, hϱ, ?_, ⟨dealerJump _ hϱ, dealerSize _ hϱ, ?_, coeFn_dealerSize hϱ⟩, one_pos,
    le_rfl, one_ne_zero⟩
  · obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
      LevyStochCalc.Driver.LevyDriver.exists 1 DealerMark (dealerMarks (fun _ => (2 - 1) / 2) 1)
    exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _⟩
  · filter_upwards [coeFn_dealerJump (c := fun _ => (2 - 1) / 2) hϱ] with e he
    rw [he]
    ext i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    simp [signedSize, markSide]

end Dissertation.Acceptance.A
