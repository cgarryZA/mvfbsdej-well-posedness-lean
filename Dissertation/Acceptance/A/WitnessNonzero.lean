/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Acceptance.A.Sec2Basics
import Dissertation.Acceptance.A.Witness
import Dissertation.WellPosedness.System.PaperSolutionSolves

/-!
# Nonzero instances of §2 and Theorem 3.1 of the well-posedness paper

Instances, over a probability space carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, in
which the conclusions of the compensation formula, the predictable representation property, the
measurability paragraph after (2.3) and Theorem 3.1 are nonzero.

## Main statements

* `Dissertation.Acceptance.A.sec2_compensation_nonzero_hypotheses` — (2.1) and (2.2) at the
  integrand `1_{(0, 1]}`, where both sides of (2.1) equal `1`.
* `Dissertation.Acceptance.A.sec2_prp_nonzero_hypotheses` — the martingale
  `𝔼[W_1 + Ñ((0, 1] × ℝ) | ℱ_t]`, represented by `Z = U = 1_{(0, 1]}` of energy `1`.
* `Dissertation.Acceptance.A.sec2_hborel_nonzero_hypotheses` — the jump coefficient `h = −u`,
  represented by a jointly measurable function that is not zero.
* `Dissertation.Acceptance.A.thm_stab_nonzero_hypotheses` — two solutions of one system from the
  initial data `e₁` and `0`, with `dataSize = 1` and `supSize ≥ 1`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Dissertation.Acceptance.A

section Window

open Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.System LevyStochCalc

/-- The indicator of the time window `(0, 1]`. -/
noncomputable def unitWindow (s : ℝ) : ℝ := (Set.Ioc (0 : ℝ) 1).indicator (fun _ => 1) s

/-- The window `(0, 1]` vanishes off `[0, 1]`. -/
theorem unitWindow_of_notMem {s : ℝ} (hs : s ∉ Set.Icc (0 : ℝ) 1) : unitWindow s = 0 :=
  Set.indicator_of_notMem (fun h => hs (Set.Ioc_subset_Icc_self h)) _

/-- The indicator of the window `(0, 1]` is measurable. -/
theorem measurable_unitWindow : Measurable unitWindow :=
  measurable_const.indicator measurableSet_Ioc

/-- The deterministic window `(0, 1]` is predictable for every filtration. -/
theorem predictable_unitWindow {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ) :
    Probability.Predictable ℱ fun (_ : Ω) s => unitWindow s := by
  have h1 := Probability.measurableSet_predictableSigma_Ioi_prod (ℱ := ℱ) (r := 0)
    (A := Set.univ) MeasurableSet.univ
  have h2 := Probability.measurableSet_predictableSigma_Ioi_prod (ℱ := ℱ) (r := 1)
    (A := Set.univ) MeasurableSet.univ
  have hS : Set.Ioc (0 : ℝ) 1 ×ˢ (Set.univ : Set Ω)
      = Set.Ioi 0 ×ˢ Set.univ \ Set.Ioi 1 ×ˢ Set.univ := by
    ext p
    simp [Set.mem_Ioc, Set.mem_Ioi, not_lt]
  have hf : (fun p : ℝ × Ω => unitWindow p.1)
      = (Set.Ioc (0 : ℝ) 1 ×ˢ (Set.univ : Set Ω)).indicator fun _ => 1 := by
    funext p
    simp only [unitWindow, Set.indicator, Set.mem_prod, Set.mem_univ, and_true]
  unfold Probability.Predictable
  rw [hf]
  exact stronglyMeasurable_const.indicator (hS ▸ h1.diff h2)

/-- The deterministic window `(0, 1]` is marked predictable at a finite mark measure. -/
theorem markedPredictable_unitWindow {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ)
    {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsFiniteMeasure ν] :
    Probability.MarkedPredictable ℱ ν fun (_ : Ω) s (_ : E) => unitWindow s :=
  Probability.markedPredictable_of_measurable_window (f := fun p : ℝ × E => unitWindow p.1)
    (T := 1) MeasurableSet.univ (measure_ne_top ν _) (measurable_unitWindow.comp measurable_fst)
    fun _ hp => Set.indicator_of_notMem (fun h => hp ⟨h, Set.mem_univ _⟩) _

/-- `∫_0^1 1_{(0, 1]}(s)² ds = 1`. -/
theorem setLIntegral_unitWindow_sq :
    ∫⁻ s in Set.Icc (0 : ℝ) 1, (‖unitWindow s‖₊ : ℝ≥0∞) ^ 2 = 1 := by
  have h : ∀ s, (‖unitWindow s‖₊ : ℝ≥0∞) ^ 2 = (Set.Ioc (0 : ℝ) 1).indicator 1 s := by
    intro s
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1 <;> simp [unitWindow, hs]
  simp_rw [h]
  rw [lintegral_indicator_one measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr Set.Ioc_subset_Icc_self, Real.volume_Ioc]
  simp

/-- `∫_{(0, 1]} 1_{(0, 1]}(s) ds = 1`. -/
theorem setLIntegral_Ioc_ofReal_unitWindow :
    ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (unitWindow s) = 1 := by
  rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => 1) fun s hs => by
    simp [unitWindow, hs]]
  simp

/-- **A nonzero instance of (2.1) and (2.2).** Over a probability space carrying a Lévy driver
with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`, the integrand `ψ_s(e) = 1_{(0, 1]}(s)` is
measurable for the marked predictable σ-algebra, and on `(0, 1]` both sides of (2.1) equal `1`:
`𝔼 N((0, 1] × ℝ) = 𝔼 ∫_0^1 ∫ ψ dν ds = 1`, so `𝔼 ∫_0^1 ∫ |ψ| dν ds = 1 < ∞`. -/
theorem sec2_compensation_nonzero_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (_ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      Measurable[Probability.markedPredictableSigma (enlJoint ⊥ D bot_le) (Measure.dirac (0 : ℝ))]
        (fun q : Ω × ℝ × ℝ => unitWindow q.2.1)
      ∧ Measurable[Probability.markedPredictableSigma (enlJoint ⊥ D bot_le)
          (Measure.dirac (0 : ℝ))] (fun q : Ω × ℝ × ℝ => ENNReal.ofReal (unitWindow q.2.1))
      ∧ ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) 1 ×ˢ Set.univ, ENNReal.ofReal (unitWindow p.1) ∂(D.N.N ω) ∂P
          = 1
      ∧ ∫⁻ _, (∫⁻ s in Set.Ioc (0 : ℝ) 1, ∫⁻ _, ENNReal.ofReal (unitWindow s)
          ∂(Measure.dirac (0 : ℝ))) ∂P = 1
      ∧ ∫⁻ _, (∫⁻ s in Set.Ioc (0 : ℝ) 1, ∫⁻ _, ‖unitWindow s‖ₑ ∂(Measure.dirac (0 : ℝ))) ∂P
          = 1 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  have hm : Measurable[Probability.markedPredictableSigma (enlJoint ⊥ D bot_le)
      (Measure.dirac (0 : ℝ))] (fun q : Ω × ℝ × ℝ => unitWindow q.2.1) :=
    markedPredictable_unitWindow (enlJoint ⊥ D bot_le) (Measure.dirac (0 : ℝ))
  have hm' := ENNReal.measurable_ofReal.comp hm
  have hR : ∫⁻ _, (∫⁻ s in Set.Ioc (0 : ℝ) 1, ∫⁻ _, ENNReal.ofReal (unitWindow s)
      ∂(Measure.dirac (0 : ℝ))) ∂P = 1 := by
    simp [setLIntegral_Ioc_ofReal_unitWindow]
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hm, hm', ?_, hR, ?_⟩
  · exact (eq_compid ⊥ (Measure.dirac (0 : ℝ)) 1 P D bot_le hind₀ 1
      (fun q => ENNReal.ofReal (unitWindow q.2.1)) hm').trans hR
  · have h : ∀ s, ‖unitWindow s‖ₑ = ENNReal.ofReal (unitWindow s) := by
      intro s
      by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1 <;> simp [unitWindow, hs]
    simp_rw [h]
    exact hR

open Dissertation.PaperSpec.A in
/-- **A nonzero instance of the predictable representation property of §2.** Over a probability
space carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`, the martingale
`M_t = 𝔼[W_1 + Ñ((0, 1] × ℝ) | ℱ_t]` is square integrable and is represented on `[0, 1]` by
`Z = U = 1_{(0, 1]}`, both of energy `1`; every pair representing `M` agrees with `(Z, U)` up to
null sets. -/
theorem sec2_prp_nonzero_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P) (M : ℝ → Ω → ℝ),
      Martingale M (enlJoint ⊥ D bot_le) P ∧ (∀ t, MemLp (M t) 2 P)
      ∧ RepresentsMart D bot_le hind₀ 1 M (fun s _ _ => unitWindow s) (fun s _ _ => unitWindow s)
      ∧ Brownian.Ito.energy P 1 (fun _ s => unitWindow s) = 1
      ∧ Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1
          (fun _ s _ => unitWindow s) = 1
      ∧ ∀ (Z : ℝ → Ω → Fin 1 → ℝ) (U : ℝ → Ω → ℝ → ℝ),
        RepresentsMart D bot_le hind₀ 1 M Z U →
        (∀ j, Brownian.Ito.energy P 1 (fun ω s => Z s ω j - unitWindow s) = 0)
          ∧ Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1
              (fun ω s e => U s ω e - unitWindow s) = 0 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  set ℱ := enlJoint ⊥ D bot_le with hℱ
  have hW := isBrownianFiltration_enlJoint D bot_le hind₀
  have hN := isPoissonFiltration_enlJoint D bot_le hind₀
  have hE : Brownian.Ito.energy P 1 (fun (_ : Ω) s => unitWindow s) = 1 := by
    simp [Brownian.Ito.energy, setLIntegral_unitWindow_sq]
  have hEm : Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1
      (fun (_ : Ω) s (_ : ℝ) => unitWindow s) = 1 := by
    simp [Poisson.Compensated.markedEnergy, setLIntegral_unitWindow_sq]
  have hZ : ∀ j : Fin 1, Probability.Predictable ℱ fun (ω : Ω) s =>
      (fun s (_ : Ω) (_ : Fin 1) => unitWindow s) s ω j := fun _ => predictable_unitWindow ℱ
  have hZv : ∀ (ω : Ω) s, s ∉ Set.Icc (0 : ℝ) 1 →
      (fun s (_ : Ω) (_ : Fin 1) => unitWindow s) s ω = 0 :=
    fun _ _ hs => funext fun _ => unitWindow_of_notMem hs
  have hU := markedPredictable_unitWindow ℱ (Measure.dirac (0 : ℝ)) (Ω := Ω)
  let G : ∀ _ : Fin 1, Brownian.Ito.HorizonIntegrand P ℱ 1 := fun j =>
    ⟨fun _ s => unitWindow s, Brownian.Ito.measurable_uncurry_of_predictable (hZ j),
      progressivelyMeasurable_of_predictable_of_vanish hZ hZv j,
      fun _ _ hs => unitWindow_of_notMem hs, by rw [hE]; exact ENNReal.one_ne_top⟩
  let K : Poisson.Compensated.MarkedHorizonIntegrand P (Measure.dirac (0 : ℝ)) ℱ 1 :=
    ⟨fun _ s _ => unitWindow s,
      hU.mono (Probability.markedPredictableSigma_le _ _) le_rfl, hU.markedProgressivelyMeasurable,
      fun _ _ _ hs => unitWindow_of_notMem hs, by rw [hEm]; exact ENNReal.one_ne_top⟩
  set ζ := LevyStochCalc.Driver.LevyDriver.jointIntegral hW hN G K with hζdef
  have hrc : ℱ.rightCont = ℱ := MeasureTheory.Filtration.IsRightContinuous.eq
  have hproc : ∀ t ≤ (1 : ℝ), P[ζ | ℱ t] =ᵐ[P]
      LevyStochCalc.Driver.LevyDriver.jointIntegralProcess hW hN G K t := by
    intro t ht
    have h := LevyStochCalc.Driver.LevyDriver.condExp_jointIntegral_rightCont hW hN G K ht
    rwa [hrc] at h
  have h00 : LevyStochCalc.Driver.LevyDriver.jointIntegralProcess hW hN G K 0 =ᵐ[P] 0 := by
    have hb := Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos (D.W.W 0) ℱ (hW 0)
      (G 0).toFun (G 0).measurable_uncurry (G 0).progressive (G 0).sq_int_global le_rfl
    have hp := Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos (φ := K.toFun) D.N hN
      K.measurable_uncurry K.progressive K.sq_int_global le_rfl
    filter_upwards [hb, hp] with ω h1 h2
    simp only [LevyStochCalc.Driver.LevyDriver.jointIntegralProcess, Fin.sum_univ_one,
      LevyStochCalc.Driver.horizonProcess, LevyStochCalc.Driver.markedHorizonProcess, Pi.zero_apply]
    rw [h1, h2]
    simp
  have hrep : RepresentsMart D bot_le hind₀ 1 (fun t => P[ζ | ℱ t])
      (fun s _ _ => unitWindow s) (fun s _ _ => unitWindow s) := by
    refine ⟨hZ, hZv, fun _ => by rw [hE]; exact ENNReal.one_ne_top, hU,
      fun _ _ _ hs => unitWindow_of_notMem hs, by rw [hEm]; exact ENNReal.one_ne_top,
      fun t ht => ?_⟩
    filter_upwards [hproc t ht.2, hproc 0 zero_le_one, h00] with ω h1 h2 h3
    rw [h1, h2, h3, Pi.zero_apply, zero_add]
    rfl
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, fun t => P[ζ | ℱ t],
    martingale_condExp ζ ℱ P,
    fun t => (LevyStochCalc.Driver.LevyDriver.memLp_jointIntegral hW hN G K).condExp
      (by norm_num), hrep, hE, hEm, fun Z U hZU => ?_⟩
  have huniq := (sec2_prp ⊥ (Measure.dirac (0 : ℝ)) 1 P D bot_le hind₀ one_pos 1 one_pos
    (fun t => P[ζ | ℱ t]) (martingale_condExp ζ ℱ P)
    fun t => (LevyStochCalc.Driver.LevyDriver.memLp_jointIntegral hW hN G K).condExp
      (by norm_num)).2 Z (fun s _ _ => unitWindow s) U (fun s _ _ => unitWindow s) hZU hrep
  exact huniq

end Window

section HBorel

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence Dissertation.Law

/-- The constant unit vector `e₁` of `L²(δ₀; ℝ¹)`. -/
noncomputable def unitDirac : Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ)) :=
  indicatorConstLp 2 MeasurableSet.univ (by simp) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))

/-- **A nonzero instance of the paragraph after (2.3).** At `ν = δ₀`, `n = m = d = 1`, `T = 1`,
the coefficients of Example 5.1(i) with `β₁ = 1`, `β₂ = 0`, `σ_c = 0`, `h_c = 0` have
`h(t, θ, μ) = −u`; the function `H((t, θ, μ), e) = −⟨e₁, u⟩_{L²(δ₀)} e₁` is measurable for the
Borel σ-algebra times `ℰ` and represents it, and it is not the zero function. -/
theorem sec2_hborel_nonzero_hypotheses :
    Measurable[(borel (Set.Icc (0 : ℝ) 1 × TupleH (Measure.dirac (0 : ℝ)) 1 1 1
        × TupleP2WH (Measure.dirac (0 : ℝ)) 1 1 1)).prod (inferInstance : MeasurableSpace ℝ)]
      (fun q => -(inner ℝ unitDirac q.1.2.1.2.2.2) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
    ∧ (∀ p : Set.Icc (0 : ℝ) 1 × TupleH (Measure.dirac (0 : ℝ)) 1 1 1
        × TupleP2WH (Measure.dirac (0 : ℝ)) 1 1 1,
      ((affineCoeffs (ν := Measure.dirac (0 : ℝ)) (d := 1) 1 0 0 0).h p.1 p.2.1 p.2.2.toP2 :
          ℝ → EuclideanSpace ℝ (Fin 1))
        =ᵐ[Measure.dirac (0 : ℝ)] fun _ =>
          -(inner ℝ unitDirac p.2.1.2.2.2) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
    ∧ ∃ p : Set.Icc (0 : ℝ) 1 × TupleH (Measure.dirac (0 : ℝ)) 1 1 1
        × TupleP2WH (Measure.dirac (0 : ℝ)) 1 1 1,
      -(inner ℝ unitDirac p.2.1.2.2.2) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) ≠ 0 := by
  refine ⟨?_, fun p => ?_, ?_⟩
  · have hc : Continuous fun q : Set.Icc (0 : ℝ) 1 × TupleH (Measure.dirac (0 : ℝ)) 1 1 1
        × TupleP2WH (Measure.dirac (0 : ℝ)) 1 1 1 =>
        -(inner ℝ unitDirac q.2.1.2.2.2) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ) :=
      ((innerSL ℝ unitDirac).continuous.comp (continuous_snd.comp (continuous_snd.comp
        (continuous_snd.comp (continuous_fst.comp continuous_snd))))).neg.smul continuous_const
    have hm := hc.borel_measurable
    rw [← BorelSpace.measurable_eq (α := EuclideanSpace ℝ (Fin 1))] at hm
    exact hm.comp measurable_fst
  · have hu := ae_eq_dirac (a := (0 : ℝ)) (p.2.1.2.2.2 : ℝ → EuclideanSpace ℝ (Fin 1))
    have hinner : inner ℝ unitDirac p.2.1.2.2.2
        = (p.2.1.2.2.2 : ℝ → EuclideanSpace ℝ (Fin 1)) 0 0 := by
      rw [unitDirac, L2.inner_indicatorConstLp_eq_setIntegral_inner, Measure.restrict_univ,
        integral_dirac]
      simp [EuclideanSpace.inner_single_left]
    filter_upwards [Lp.coeFn_neg
      (p.2.1.2.2.2 : Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ))), hu] with e h1 h2
    simp only [affineCoeffs, one_smul, zero_sub]
    rw [h1, Pi.neg_apply, h2, hinner]
    ext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp
  · refine ⟨(⟨0, by simp⟩, (0, 0, 0, unitDirac), (P2.dirac 0).toP2WH), ?_⟩
    have hne : unitDirac ≠ 0 := by
      intro h0
      have h1 := congrArg norm h0
      rw [unitDirac, norm_indicatorConstLp (by norm_num) (by simp)] at h1
      simp at h1
    refine smul_ne_zero ?_ (by simp)
    simpa using (inner_self_ne_zero (𝕜 := ℝ)).mpr hne

end HBorel

section Stability

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.PaperSpec.A
  Dissertation.WellPosedness.Stability LevyStochCalc LevyStochCalc.BSDEJ.Solves

/-- The forward component of a solution in `ℍ` starts at the initial datum: `X₀ = ξ₀` almost
surely, coordinatewise. -/
theorem Solution.X_zero_ae {Ω : Type*} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {D : LevyStochCalc.Driver.LevyDriver P d ν} {h𝒢₀ : 𝒢₀ ≤ mΩ}
    {hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P} {T : ℝ} (hT : 0 ≤ T) {C : Coeffs ν n m d}
    {ξ₀ : Ω → EuclideanSpace ℝ (Fin n)} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
    {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
    (hS : Solution D h𝒢₀ hind₀ T C ξ₀ X Y Z U) (i : Fin n) :
    X i 0 =ᵐ[P] fun ω => ξ₀ ω i := by
  obtain ⟨⟨⟨γ, h⟩, -, -⟩, -, -⟩ := hS
  obtain ⟨M, hMae, -, hid⟩ := h.fwd i
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  filter_upwards [hid, hMae 0 h0,
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W _
      (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) _
      (h.σ_meas i) (h.σ_prog i)
      (sq_int_global_of_vanishing (fun ω s hs => diffusionProc_of_notMem hs i ω) (h.σ_sq i))
      le_rfl,
    Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos
      (φ := fun ω s e => jumpProc T γ i s ω e) D.N (isPoissonFiltration_enlJoint D h𝒢₀ hind₀)
      (h.γ_meas i) (h.γ_prog i)
      (marked_sq_int_global_of_vanishing (fun ω s e hs => jumpProc_of_notMem hs i ω e)
        (h.γ_sq i)) le_rfl] with ω hω hM hW hN
  simp only [Pi.zero_apply] at hW hN
  rw [hω 0 h0, hM, hW, hN, Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
    integral_zero_measure]
  ring

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = 1`, `σ_c = 0` and
`h_c = 0`. -/
local notation "sys₁" =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 1 1 0 0

/-- **A nonzero instance of Theorem 3.1.** Over a probability space carrying a Lévy driver with
`d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`, `n = m = 1` and `T = 1`, take the system of
Example 5.1(i) with `β₁ = β₂ = 1`, `σ_c = h_c = 0` as both systems, with the initial data
`ξ¹ ≡ e₁` and `ξ² ≡ 0`: the hypotheses of Theorem 3.1 hold (system 1 with `L = 1`, `G = 1`,
`α = β₁ = β₂ = 1`; system 2 with `L₂ = 1`), each system has a solution, the right-hand side
`dataSize` of (3.1) is `1`, and the left-hand side `supSize` is at least `1`. -/
theorem thm_stab_nonzero_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 sys₁
      ∧ Assumption22 (enlJoint ⊥ D bot_le) P 1 sys₁
          (fun _ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 sys₁
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 sys₁
      ∧ Assumption22 (enlJoint ⊥ D bot_le) P 1 sys₁ (fun _ => 0)
      ∧ ∃ (X₁ X₂ : Fin 1 → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ)
          (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U₁ U₂ : Fin 1 → ℝ → Ω → ℝ → ℝ),
          Solution D bot_le hind₀ 1 sys₁ (fun _ => EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
            X₁ Y₁ Z₁ U₁
          ∧ Solution D bot_le hind₀ 1 sys₁ (fun _ => 0) X₂ Y₂ Z₂ U₂
          ∧ dataSize P (Measure.dirac (0 : ℝ)) 1
              (fun i ω => ((fun _ : Ω => (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) :
                EuclideanSpace ℝ (Fin 1))) ω) i - ((fun _ : Ω => (0 :
                EuclideanSpace ℝ (Fin 1))) ω) i)
              (fun i ω s => driftProc P 1 sys₁ X₂ Y₂ Z₂ U₂ i ω s
                - driftProc P 1 sys₁ X₂ Y₂ Z₂ U₂ i ω s)
              (fun i s ω j => diffusionProc P 1 sys₁ X₂ Y₂ Z₂ U₂ i s ω j
                - diffusionProc P 1 sys₁ X₂ Y₂ Z₂ U₂ i s ω j)
              (fun i s ω e =>
                jumpProc 1 (coeffJump P 1 sys₁ (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e
                  - jumpProc 1 (coeffJump P 1 sys₁ (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂)
                    i s ω e)
              (fun k ω s => driverProc P 1 sys₁ X₂ Y₂ Z₂ U₂ k ω s
                - driverProc P 1 sys₁ X₂ Y₂ Z₂ U₂ k ω s)
              (fun k ω => terminalVal P 1 sys₁ X₂ k ω - terminalVal P 1 sys₁ X₂ k ω) = 1
          ∧ 1 ≤ supSize P (Measure.dirac (0 : ℝ)) 1 (fun i t ω => X₁ i t ω - X₂ i t ω)
              (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
              (fun k t ω e => U₁ k t ω e - U₂ k t ω e) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨hJ, h22, h23, hG, h25⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  obtain ⟨-, h22₀, -, -, -⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (0 : EuclideanSpace ℝ (Fin 1))
  have e₁ : max (max (1 : ℝ) 1) 1 = 1 := by norm_num
  rw [e₁] at h23
  obtain ⟨X₁, Y₁, Z₁, U₁, hS₁⟩ := (thm_cwp ⊥ _ 1 1 1 P D bot_le hind₀ one_pos one_pos one_pos 1
    one_pos 1 1 1 1 1 _ _ hJ h22 h23 hG h25).1
  obtain ⟨X₂, Y₂, Z₂, U₂, hS₂⟩ := (thm_cwp ⊥ _ 1 1 1 P D bot_le hind₀ one_pos one_pos one_pos 1
    one_pos 1 1 1 1 1 _ _ hJ h22₀ h23 hG h25).1
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hJ, h22, h23, hG, h25, h22₀,
    X₁, X₂, Y₁, Y₂, Z₁, Z₂, U₁, U₂, hS₁, hS₂, ?_, ?_⟩
  · simp [dataSize, esq, LevyStochCalc.Brownian.Ito.energy,
      LevyStochCalc.Poisson.Compensated.markedEnergy]
  · have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hX : ∀ᵐ ω ∂P, esq (fun i => X₁ i 0 ω - X₂ i 0 ω) = 1 := by
      filter_upwards [Solution.X_zero_ae zero_le_one hS₁ 0,
        Solution.X_zero_ae zero_le_one hS₂ 0] with ω h1 h2
      have e : (fun i : Fin 1 => X₁ i 0 ω - X₂ i 0 ω) = fun _ => 1 := by
        funext i
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rw [h1, h2]
        simp
      rw [e]
      simp [esq]
    have key : 1 ≤ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) 1, esq (fun i => X₁ i t ω - X₂ i t ω)) ∂P := by
      calc (1 : ℝ≥0∞) = ∫⁻ ω, esq (fun i => X₁ i 0 ω - X₂ i 0 ω) ∂P := by
            rw [lintegral_congr_ae hX]
            simp
        _ ≤ _ := lintegral_mono fun ω => le_iSup₂_of_le (0 : ℝ) h0 le_rfl
    refine key.trans ?_
    simp only [supSize]
    exact le_add_right (le_add_right (le_add_right le_rfl))

end Stability

end Dissertation.Acceptance.A
