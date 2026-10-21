/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Acceptance.A.Sec3
import Dissertation.Acceptance.A.Sec4
import Dissertation.Acceptance.A.Sec5
import Dissertation.WellPosedness.Spec.Examples
import Dissertation.WellPosedness.Robustness.Example
import Dissertation.WellPosedness.Examples.Nemytskii
import Dissertation.WellPosedness.Examples.FullLawBeyond

/-!
# Instances of the hypotheses of the statements of paper A

For a statement with hypotheses, an instance the manuscript intends at which the hypotheses hold.
The setting: a probability space carrying a Lévy driver with one Brownian coordinate and the
intensity `ν = δ₀` on `ℝ` (`LevyStochCalc.Driver.LevyDriver.exists`), the trivial initial
σ-algebra `𝒢₀ = ⊥`, `n = m = d = 1` and `T = 1`; the systems are those of Example 5.1(i) with
`σ_c = 0`, `h_c = 0` and initial datum `0`.

## Main statements

* `Dissertation.Acceptance.A.thm_cwp_hypotheses` — the hypotheses of Theorem 3.5, at the system of
  Example 5.1(i) with `β₁ = β₂ = 1`.
* `Dissertation.Acceptance.A.thm_uniq_hypotheses` — the hypotheses of Theorem 3.3, at the system
  of Example 5.1(i) with `β₁ = β₂ = 1`.
* `Dissertation.Acceptance.A.cor_robust_hypotheses` — the hypotheses of Corollary 3.6, at the
  baseline of Example 5.1(i) with `β₁ = β₂ = 2` and the feedback perturbation `ε = 1/2`.
* `Dissertation.Acceptance.A.cor_robust_lip_hypotheses` — the hypotheses of the (3.5) clause of
  Corollary 3.6, at the perturbation of Example 5.4.
* `Dissertation.Acceptance.A.eq_lipfun_hypotheses` — the hypotheses of (2.10).
* `Dissertation.Acceptance.A.lem_bpbsde_hypotheses` — the hypotheses of Lemma 4.1, at the
  backward equation of the solution of Theorem 3.5 for Example 5.1(i).
* `Dissertation.Acceptance.A.ass_G_hypotheses` — the hypotheses of the bounds of Assumption 2.4.
* `Dissertation.Acceptance.A.prop_strict_hypotheses` — the hypotheses of Proposition 3.8.
* `Dissertation.Acceptance.A.ex_concrete_hypotheses` — the hypotheses of Example 5.1, at the
  initial datum `0`.
* `Dissertation.Acceptance.A.ex_brownian_hypotheses` — the hypotheses of Example 5.2, at a
  Lévy driver with `ν = 0`, `m = 1`, `n = 2` and the initial datum `0`.
* `Dissertation.Acceptance.A.ex_expfunc_hypotheses`, `ex_expfunc_limin_hypotheses`,
  `ex_expfunc_jump_hypotheses` — the hypotheses of Example 5.3, at `ν = δ₀` and the interaction
  kernel `x − x'`.
* `Dissertation.Acceptance.A.ex_fulllaw_hypotheses` — the hypotheses of Example 5.4, at the
  baseline of Corollary 3.6's instance and `ε = 1/4`, profiles `min(|r|, 1)`.
* `Dissertation.Acceptance.A.ex_fulllaw_affineQ_hypotheses`,
  `ex_fulllaw_beyond_hypotheses`, `ex_fulllaw_beyond_Q_hypotheses` — the hypotheses of the
  remaining clauses of Example 5.4.
-/

open MeasureTheory ProbabilityTheory

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.PaperSpec.A
  Dissertation.WellPosedness.Stability LevyStochCalc

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = β`, `σ_c = 0` and
`h_c = 0`. -/
local notation "sys " β:max =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) β β 0 0

/-- **The hypotheses of Theorem 3.5 hold at Example 5.1(i).** Over a probability space carrying a
Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`, `n = m = 1` and `T = 1`, the system
of Example 5.1(i) with `β₁ = β₂ = 1`, `σ_c = 0`, `h_c = 0` and initial datum `0` satisfies (2.3),
Assumption 2.2, Assumption 2.3 with `L = 1`, Assumption 2.4 with `G = 1` and Assumption 2.5 with
`G = 1` and `α = β₁ = β₂ = 1`. -/
theorem thm_cwp_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (_ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 (sys 1)
      ∧ Assumption22 (enlJoint ⊥ D bot_le) P 1 (sys 1) (fun _ => 0)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 (sys 1)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1
          (sys 1) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  obtain ⟨hJ, h22, h23, hG, h25⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (0 : EuclideanSpace ℝ (Fin 1))
  refine ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, hJ, h22, ?_, hG, h25⟩
  simpa using h23

/-- **The hypotheses of Theorem 3.3 hold at Example 5.1(i).** At the instance of
`thm_cwp_hypotheses`, the system satisfies (2.3) and Assumptions 2.3–2.5, and two tuples
satisfy (1.1) in `ℍ²` with the initial datum `0` (both the solution of Theorem 3.5). -/
theorem thm_uniq_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 (sys 1)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 (sys 1)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 (sys 1)
      ∧ ∃ (X₁ X₂ : Fin 1 → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ)
          (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U₁ U₂ : Fin 1 → ℝ → Ω → ℝ → ℝ),
          WeakSolution D bot_le hind₀ 1 (sys 1) (fun _ => 0) X₁ Y₁ Z₁ U₁
          ∧ WeakSolution D bot_le hind₀ 1 (sys 1) (fun _ => 0) X₂ Y₂ Z₂ U₂ := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨hJ, h22, h23, hG, h25⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (0 : EuclideanSpace ℝ (Fin 1))
  have e₁ : max (max (1 : ℝ) 1) 1 = 1 := by norm_num
  rw [e₁] at h23
  obtain ⟨X, Y, Z, U, hw, -, -⟩ := (thm_cwp ⊥ _ 1 1 1 P D bot_le hind₀ one_pos one_pos
    one_pos 1 one_pos 1 1 1 1 1 _ _ hJ h22 h23 hG h25).1
  exact ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hJ, h23, hG, h25, X, X, Y, Y, Z, Z, U, U,
    hw, hw⟩

/-- The feedback perturbation `p_b = ε y`, `p_σ = ε z`, `p_h = ε u`, `p_f = 0` with `ε = 1/2`, as
the system of Example 5.1(i) with constants `(−1/2, 0)`. -/
local notation "feedback" =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) (-(1 / 2)) 0 0 0

/-- The baseline of Example 5.1(i) with `β₁ = β₂ = 2`, perturbed by the feedback with
`ε = 1/2`, is the system of Example 5.1(i) with constants `(3/2, 2)`. -/
theorem sys_two_perturb_feedback : (sys 2).perturb feedback
    = affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) (3 / 2) 2 0 0 := by
  simp only [Coeffs.perturb, affineCoeffs, Coeffs.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩ <;> funext t θ μ <;> module

/-- **The hypotheses of Corollary 3.6 hold at Example 5.1(i).** Over a probability space
carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`, `n = m = 1` and `T = 1`:
the baseline, Example 5.1(i) with `β₁ = β₂ = 2`, `σ_c = 0`, `h_c = 0` and initial datum `0`,
satisfies (2.3) and Assumptions 2.2–2.5 with `L₀ = 2`, `G = 1`, `α = 1`, `β₁ = β₂ = 1`, and
(2.13) with margin `c_diss = 1`; the feedback perturbation with `ε = 1/2` satisfies the origin
values of Assumption 2.2, the interior bound of Assumption 2.3 with `L_p = 1/2`, and (3.4) with
`c_pert = 1/2 < c_diss`; and the perturbed system satisfies (2.3). -/
theorem cor_robust_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (_ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 (sys 2)
      ∧ Assumption22 (enlJoint ⊥ D bot_le) P 1 (sys 2) (fun _ => 0)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 2 (sys 2)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 (sys 2)
      ∧ Margin213 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 (sys 2)
      ∧ (0 : ℝ) < 1
      ∧ OriginValues 1 feedback
      ∧ LipInterior (enlJoint ⊥ D bot_le) P 1 (1 / 2) feedback ∧ (0 : ℝ) ≤ 1 / 2
      ∧ PairingBound34 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 / 2) feedback
      ∧ (0 : ℝ) ≤ 1 / 2
      ∧ JointBorel 1 ((sys 2).perturb feedback)
      ∧ (1 / 2 : ℝ) < 1 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨hJ, h22, h23, hG, -⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
      (σc := 0) (hc := 0) two_pos two_pos (0 : EuclideanSpace ℝ (Fin 1))
  have e₂ : max (max (2 : ℝ) 2) 1 = 2 := by norm_num
  rw [e₂] at h23
  have hM : DiagonalMonotoneMargin (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1
      (sys 2) := by
    have h := diagonalMonotoneMargin_affine (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
      (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) (σc := 0) (hc := 0) 1 1 1
    norm_num at h
    exact h
  have h25 : Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1
      (sys 2) :=
    Assumption25.of_monotone hJ h23 (constants_affine one_pos one_pos)
      (hM.diagonalMonotone zero_le_one) terminalMonotone_affine
  have hJp : JointBorel 1 ((sys 2).perturb feedback) := by
    rw [sys_two_perturb_feedback]
    exact (affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := enlJoint ⊥ D bot_le) (P := P)
      (T := 1) (σc := 0) (hc := 0) (by norm_num : (0 : ℝ) < 3 / 2) two_pos
      (0 : EuclideanSpace ℝ (Fin 1))).1
  have hε : (0 : ℝ) ≤ 1 / 2 := by norm_num
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hJ, h22, h23, hG, h25,
    (margin213_iff one_pos zero_le_one zero_le_one).mpr hM, one_pos,
    originValues_iff_coeffOrigin.mpr (coeffOrigin_affine 1),
    LipInterior.of_diagonalLipschitz (diagonalLipschitz_of_lipschitzCoefficientsP2
      (lipschitzCoefficientsP2_affine_feedback hε)), hε,
    pairingBound34_iff.mpr (diagonalPairingBound_affine_feedback hε), hε, hJp, by norm_num⟩

/-- **The hypotheses of (2.10) hold** at the projection `θ ↦ y` of `H` (`n = m = d = 1`,
`ν = δ₀` on `ℝ`) onto the separable Hilbert space `K = ℝ¹`, with `L = 1`. -/
theorem eq_lipfun_hypotheses :
    (0 : ℝ) ≤ 1 ∧ ∀ θ θ' : TupleH (Measure.dirac (0 : ℝ)) 1 1 1,
      ‖θ.2.1 - θ'.2.1‖ ≤ 1 * ‖toL2 θ - toL2 θ'‖ :=
  ⟨zero_le_one, fun θ θ' => by
    rw [one_mul, ← toL2_sub]
    exact norm_y_le_norm_toL2 (θ - θ')⟩

/-- **The hypotheses of Lemma 4.1 hold at a backward equation of the paper.** Over a probability
space carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`, `m = 1` and `T = 1`:
the backward component `(Y, Z, U)` of the solution of Theorem 3.5 for Example 5.1(i) with
`β₁ = β₂ = 1`, with `δξ = g(X_T, Law X_T)` and `φ` the driver process along the solution,
satisfies every hypothesis of Lemma 4.1. -/
theorem lem_bpbsde_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)
      (δξ : Ω → EuclideanSpace ℝ (Fin 1)) (φ : Fin 1 → Ω → ℝ → ℝ) (δY : Fin 1 → ℝ → Ω → ℝ)
      (δZ : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (δU : Fin 1 → ℝ → Ω → ℝ → ℝ)
      (hZ : ∀ k j, Probability.Predictable (enlJoint ⊥ D bot_le) fun ω s => δZ k s ω j)
      (hZv : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) 1 → δZ k s ω = 0)
      (hZs : ∀ k j, Brownian.Ito.energy P 1 (fun ω s => δZ k s ω j) ≠ ⊤)
      (hU : ∀ k, Probability.MarkedPredictable (enlJoint ⊥ D bot_le) (Measure.dirac (0 : ℝ))
        fun ω s e => δU k s ω e)
      (hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) 1 → δU k s ω e = 0)
      (hUs : ∀ k, Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1
        (fun ω s e => δU k s ω e) ≠ ⊤),
      Measurable[enlJoint ⊥ D bot_le 1] δξ ∧ MemLp δξ 2 P
      ∧ (∀ k, Measurable (Function.uncurry (φ k))) ∧ (∀ k, Brownian.Ito.energy P 1 (φ k) ≠ ⊤)
      ∧ (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) 1, Measurable[enlJoint ⊥ D bot_le t] (δY k t))
      ∧ (∀ k ω, ∀ t ∈ Set.Ico (0 : ℝ) 1,
          Filter.Tendsto (fun s => δY k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (δY k t ω)))
      ∧ (∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∃ l : ℝ,
          Filter.Tendsto (fun s => δY k s ω) (nhdsWithin t (Set.Iio t)) (nhds l))
      ∧ ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂P,
        δY k t ω = δξ ω k + (∫ s in Set.Icc t 1, φ k ω s)
          - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (enlJoint ⊥ D bot_le)
                (isBrownianFiltration_enlJoint D bot_le hind₀) (δZ k)
                (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
                (progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k))
                (BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k)) 1 ω
              - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
                (enlJoint ⊥ D bot_le) (isBrownianFiltration_enlJoint D bot_le hind₀) (δZ k)
                (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
                (progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k))
                (BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k)) t ω)
          - (Poisson.Compensated.stochasticIntegral D.N (enlJoint ⊥ D bot_le)
                (isPoissonFiltration_enlJoint D bot_le hind₀) (fun ω' s e => δU k s ω' e)
                ((hU k).mono (Probability.markedPredictableSigma_le _ _) le_rfl)
                (hU k).markedProgressivelyMeasurable
                (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) 1 ω
              - Poisson.Compensated.stochasticIntegral D.N (enlJoint ⊥ D bot_le)
                (isPoissonFiltration_enlJoint D bot_le hind₀) (fun ω' s e => δU k s ω' e)
                ((hU k).mono (Probability.markedPredictableSigma_le _ _) le_rfl)
                (hU k).markedProgressivelyMeasurable
                (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) t ω) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨hJ, h22, h23, hG, h25⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (0 : EuclideanSpace ℝ (Fin 1))
  have e₁ : max (max (1 : ℝ) 1) 1 = 1 := by norm_num
  rw [e₁] at h23
  obtain ⟨X, Y, Z, U, hS⟩ := (thm_cwp ⊥ _ 1 1 1 P D bot_le hind₀ one_pos one_pos
    one_pos 1 one_pos 1 1 1 1 1 _ _ hJ h22 h23 hG h25).1
  obtain ⟨⟨γ, h⟩, -, hY⟩ := Solution.paperSolutionEnl zero_le_one hJ h22.origin h23 hS
  have hT1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  set ρ := Dissertation.Law.lawP2 P
    fun ω' => (WithLp.toLp 2 fun i => X i 1 ω' : EuclideanSpace ℝ (Fin 1))
  have hXT : Measurable[enlJoint ⊥ D bot_le 1]
      fun ω => (WithLp.toLp 2 fun i => X i 1 ω : EuclideanSpace ℝ (Fin 1)) :=
    (stronglyMeasurable_iff_forall_coord.mpr fun i => h.X_adapted i 1 hT1).measurable
  have hξm : Measurable[enlJoint ⊥ D bot_le 1]
      fun ω => (sys 1).g (WithLp.toLp 2 fun i => X i 1 ω) ρ :=
    (hJ.measurable_g_section ρ).comp hXT
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀,
    fun ω => (sys 1).g (WithLp.toLp 2 fun i => X i 1 ω) ρ,
    fun k => driverProc P 1 (sys 1) X Y Z U k, Y, Z, U, h.Z_pred, h.Z_vanish, h.Z_sq, h.U_pred,
    h.U_vanish, h.U_sq, hξm,
    memLp_iff_forall_coord.mpr fun k => h.memLp_terminal zero_le_one k, h.f_meas, h.f_sq,
    h.Y_adapted, h.Y_rightCont, hY, fun k t ht => ?_⟩
  obtain ⟨M, hM, -, hid⟩ := h.bwd k
  filter_upwards [hid, hM 1 hT1, hM t ht] with ω hω h1 ht'
  rw [hω t ht, ← h1, ← ht']
  rfl

/-- **The hypotheses of the bounds of Assumption 2.4 hold** at `m = n = 1`, `G = 1`, which has
full rank. -/
theorem ass_G_hypotheses : 0 < (1 : ℕ) ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1 :=
  ⟨one_pos, rank_one_eq_min⟩

/-- **The hypotheses of Proposition 3.8 hold**: `ν = δ₀` on `ℝ` is σ-finite on a countably
generated space, and `d = 1`, `β₁ = 2`, `ε = 1` satisfy `d ≥ 1`, `β₁ > 0` and `0 < ε < β₁`. -/
theorem prop_strict_hypotheses :
    SigmaFinite (Measure.dirac (0 : ℝ)) ∧ MeasurableSpace.CountablyGenerated ℝ
      ∧ 0 < (1 : ℕ) ∧ (0 : ℝ) < 2 ∧ (0 : ℝ) < 1 ∧ (1 : ℝ) < 2 :=
  ⟨inferInstance, inferInstance, one_pos, two_pos, one_pos, one_lt_two⟩

/-- **The hypotheses of Example 5.1 hold.** Over a probability space carrying a Lévy driver with
`d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥` independent of the driver, the initial datum `0` is
strongly measurable for the time-`0` field of `enlJoint ⊥ D` and square integrable; the constants
`T = 1`, `β₁ = β₂ = 1`, `ε = 1/2` satisfy `T > 0`, `β₁, β₂ > 0` and `0 < ε < β₁`. -/
theorem ex_concrete_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ))),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P
      ∧ StronglyMeasurable[enlJoint ⊥ D bot_le 0] (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1)))
      ∧ MemLp (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 1))) 2 P
      ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, stronglyMeasurable_const,
    memLp_const _, one_pos, one_half_pos, one_half_lt_one⟩

/-- **The hypotheses of Example 5.2 hold.** Over a probability space carrying a Lévy driver with
`d = 1` and the intensity `ν = 0` on `ℝ`, with `𝒢₀ = ⊥` independent of the driver, the initial
datum `0 ∈ ℝ²` is strongly measurable for the time-`0` field of `enlJoint ⊥ D` and square
integrable, and the dimensions `m = 1 < n = 2` meet the rank condition of the example. -/
theorem ex_brownian_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (0 : Measure ℝ)),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P
      ∧ StronglyMeasurable[enlJoint ⊥ D bot_le 0] (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 2)))
      ∧ MemLp (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin 2))) 2 P
      ∧ 0 < (1 : ℕ) ∧ (1 : ℕ) < 2 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (0 : Measure ℝ)
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, stronglyMeasurable_const,
    memLp_const _, one_pos, one_lt_two⟩

/-- The first channel of a tuple is bounded by its Hilbert norm. -/
theorem norm_fst_le_norm_toL2 {HX HY HZY HUY : Type*} [NormedAddCommGroup HX]
    [InnerProductSpace ℝ HX] [NormedAddCommGroup HY] [InnerProductSpace ℝ HY]
    [NormedAddCommGroup HZY] [InnerProductSpace ℝ HZY] [NormedAddCommGroup HUY]
    [InnerProductSpace ℝ HUY] (θ : WellPosedness.Tuple HX HY HZY HUY) : ‖θ.1‖ ≤ ‖toL2 θ‖ := by
  have h := norm_toL2_sq θ
  unfold channelSq at h
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  nlinarith [sq_nonneg ‖θ.2.1‖, sq_nonneg ‖θ.2.2.1‖, sq_nonneg ‖θ.2.2.2‖]

/-- The first channel of a block difference is bounded by the Euclidean norm of the four channel
differences. -/
theorem norm_fst_sub_le_sqrt {HX HY HZ HV : Type*} [NormedAddCommGroup HX]
    [NormedAddCommGroup HY] [NormedAddCommGroup HZ] [NormedAddCommGroup HV]
    (a b : HX × HY × HZ × HV) :
    ‖a.1 - b.1‖ ≤ Real.sqrt (‖a.1 - b.1‖ ^ 2 + ‖a.2.1 - b.2.1‖ ^ 2 + ‖a.2.2.1 - b.2.2.1‖ ^ 2
      + ‖a.2.2.2 - b.2.2.2‖ ^ 2) := by
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [sq_nonneg ‖a.2.1 - b.2.1‖, sq_nonneg ‖a.2.2.1 - b.2.2.1‖,
    sq_nonneg ‖a.2.2.2 - b.2.2.2‖]

/-- The difference of the first channels, `(x − x') − (y − y')`, bounded by the two differences. -/
theorem norm_sub_sub_sub_le {V : Type*} [NormedAddCommGroup V] (x x' y y' : V) :
    ‖(x - x') - (y - y')‖ ≤ ‖x - y‖ + ‖x' - y'‖ := by
  rw [show (x - x') - (y - y') = (x - y) - (x' - y') by abel]
  exact norm_sub_le _ _

/-- **The hypotheses of Example 5.3, the class, hold**: at `ν = δ₀` on `ℝ` and
`n = m = d = k = 1`, the interaction kernel `φ̄(t, θ, θ') = x − x'` is measurable and Lipschitz in
`(θ, θ')` with constant `1`. -/
theorem ex_expfunc_hypotheses :
    ∃ (φbar : ℝ → TupleH (Measure.dirac (0 : ℝ)) 1 1 1 → TupleH (Measure.dirac (0 : ℝ)) 1 1 1
        → EuclideanSpace ℝ (Fin 1)) (L : ℝ), 0 ≤ L
      ∧ Measurable (fun p : ℝ × TupleH (Measure.dirac (0 : ℝ)) 1 1 1
          × TupleH (Measure.dirac (0 : ℝ)) 1 1 1 => φbar p.1 p.2.1 p.2.2)
      ∧ ∀ (t : ℝ) (θ₁ θ₁' θ₂ θ₂' : TupleH (Measure.dirac (0 : ℝ)) 1 1 1),
        ‖φbar t θ₁ θ₁' - φbar t θ₂ θ₂'‖ ≤ L * (‖toL2 θ₁ - toL2 θ₂‖ + ‖toL2 θ₁' - toL2 θ₂'‖) := by
  refine ⟨fun _ θ θ' => θ.1 - θ'.1, 1, zero_le_one,
    (measurable_fst.comp (measurable_fst.comp measurable_snd)).sub
      (measurable_fst.comp (measurable_snd.comp measurable_snd)), fun t θ₁ θ₁' θ₂ θ₂' => ?_⟩
  have h1 := norm_fst_le_norm_toL2 (θ₁ - θ₂)
  have h2 := norm_fst_le_norm_toL2 (θ₁' - θ₂')
  rw [toL2_sub] at h1 h2
  have h := norm_sub_sub_sub_le θ₁.1 θ₁'.1 θ₂.1 θ₂'.1
  simp only [Prod.fst_sub] at h1 h2
  linarith

/-- **The hypotheses of Example 5.3, the kernels of independent-copy interactions, hold**: at
the finite `ν = δ₀` on `ℝ` and `n = m = d = k = 1`, the kernel `ψ̄(t, p, p') = x − x'` is
Lipschitz with constant `1` for the Euclidean norm on each block. -/
theorem ex_expfunc_limin_hypotheses :
    ∃ (ψbar : ℝ → (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)
        × EuclideanSpace ℝ (Fin 1 × Fin 1) × EuclideanSpace ℝ (Fin 1))
      → (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)
        × EuclideanSpace ℝ (Fin 1 × Fin 1) × EuclideanSpace ℝ (Fin 1))
      → EuclideanSpace ℝ (Fin 1)) (Lip : ℝ), 0 ≤ Lip
      ∧ IsFiniteMeasure (Measure.dirac (0 : ℝ))
      ∧ ∀ t a a' b b', ‖ψbar t a a' - ψbar t b b'‖ ≤ Lip * (Real.sqrt (‖a.1 - b.1‖ ^ 2
        + ‖a.2.1 - b.2.1‖ ^ 2 + ‖a.2.2.1 - b.2.2.1‖ ^ 2 + ‖a.2.2.2 - b.2.2.2‖ ^ 2)
        + Real.sqrt (‖a'.1 - b'.1‖ ^ 2 + ‖a'.2.1 - b'.2.1‖ ^ 2 + ‖a'.2.2.1 - b'.2.2.1‖ ^ 2
          + ‖a'.2.2.2 - b'.2.2.2‖ ^ 2)) := by
  refine ⟨fun _ p p' => p.1 - p'.1, 1, zero_le_one, inferInstance, fun t a a' b b' => ?_⟩
  have h := norm_sub_sub_sub_le a.1 a'.1 b.1 b'.1
  have h1 := norm_fst_sub_le_sqrt a b
  have h2 := norm_fst_sub_le_sqrt a' b'
  dsimp only
  linarith

/-- The block `ℝ × ℝ × ℝ^{1×1} × ℝ` of the pointwise values `(x, y, z, u(e))` at `n = m = d = 1`. -/
local notation "Blk" => EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)
  × EuclideanSpace ℝ (Fin 1 × Fin 1) × EuclideanSpace ℝ (Fin 1)

/-- The jump kernel `h̄(t, p, p', e) = x − x'`. -/
noncomputable def diffJumpKernel : ℝ → Blk → Blk → ℝ → EuclideanSpace ℝ (Fin 1) :=
  fun _ p p' _ => p.1 - p'.1

/-- **The hypotheses of Example 5.3, the jump coefficient, hold**: at the finite `ν = δ₀` on `ℝ`
and `n = m = d = 1`, the class `𝐇_t(θ, θ')` of the Nemytskii map of the kernel
`h̄(t, p, p', e) = x − x'` represents it and is Lipschitz into `L²(ν)` with constant
`max(1, ν(E)^{1/2})`. -/
theorem ex_expfunc_jump_hypotheses :
    ∃ (hbar : ℝ → Blk → Blk → ℝ → EuclideanSpace ℝ (Fin 1))
      (H : ℝ → TupleH (Measure.dirac (0 : ℝ)) 1 1 1 → TupleH (Measure.dirac (0 : ℝ)) 1 1 1
        → Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ))) (C : ℝ), 0 ≤ C
      ∧ (∀ (t : ℝ) (θ θ' : TupleH (Measure.dirac (0 : ℝ)) 1 1 1),
        (H t θ θ' : ℝ → EuclideanSpace ℝ (Fin 1)) =ᵐ[Measure.dirac (0 : ℝ)]
          fun e => hbar t (θ.1, θ.2.1, θ.2.2.1, θ.2.2.2 e) (θ'.1, θ'.2.1, θ'.2.2.1, θ'.2.2.2 e) e)
      ∧ ∀ (t : ℝ) (θ₁ θ₁' θ₂ θ₂' : TupleH (Measure.dirac (0 : ℝ)) 1 1 1),
        ‖H t θ₁ θ₁' - H t θ₂ θ₂'‖ ≤ C * (‖toL2 θ₁ - toL2 θ₂‖ + ‖toL2 θ₁' - toL2 θ₂'‖) := by
  have hm : ∀ t, StronglyMeasurable fun q : (Blk × Blk) × ℝ => diffJumpKernel t q.1.1 q.1.2 q.2 :=
    fun t => ((measurable_fst.comp (measurable_fst.comp measurable_fst)).sub
      (measurable_fst.comp (measurable_snd.comp measurable_fst))).stronglyMeasurable
  have hlip : ∀ t (p₁ p₂ p'₁ p'₂ : Blk) (e : ℝ),
      ‖diffJumpKernel t p₁ p'₁ e - diffJumpKernel t p₂ p'₂ e‖
        ≤ 1 * (‖toL2 p₁ - toL2 p₂‖ + ‖toL2 p'₁ - toL2 p'₂‖) := fun t p₁ p₂ p'₁ p'₂ e => by
    have h1 := norm_fst_le_norm_toL2 (p₁ - p₂)
    have h2 := norm_fst_le_norm_toL2 (p'₁ - p'₂)
    rw [toL2_sub] at h1 h2
    have h := norm_sub_sub_sub_le p₁.1 p'₁.1 p₂.1 p'₂.1
    simp only [Prod.fst_sub] at h1 h2
    simp only [diffJumpKernel]
    linarith
  have h0 : ∀ t, MemLp (diffJumpKernel t 0 0) 2 (Measure.dirac (0 : ℝ)) := fun t => by
    have e : diffJumpKernel t 0 0 = fun _ => (0 : EuclideanSpace ℝ (Fin 1)) := by
      funext x
      simp [diffJumpKernel]
    rw [e]
    exact memLp_const _
  refine ⟨diffJumpKernel, nemytskii diffJumpKernel,
    1 * max 1 (Real.sqrt ((Measure.dirac (0 : ℝ)).real Set.univ)),
    mul_nonneg zero_le_one (le_trans zero_le_one (le_max_left _ _)), fun t θ θ' => ?_,
    fun t θ₁ θ₁' θ₂ θ₂' => kernelLipschitzH_nemytskii zero_le_one hm hlip h0 t θ₁ θ₂ θ₁' θ₂'⟩
  have hmem := memLp_nemytskiiFun (hm t) (hlip t) (h0 t) θ θ'
  rw [nemytskii_of_memLp hmem]
  exact hmem.coeFn_toLp

/-- The profile `min(|r|, 1)` is `1`-Lipschitz. -/
theorem abs_minAbsOne_sub_le (r r' : ℝ) : |min |r| 1 - min |r'| 1| ≤ 1 * |r - r'| := by
  rw [one_mul]
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (abs_abs_sub_abs_le_abs_sub r r') ?_)
  simp

/-- The profile `min(|r|, 1)` is bounded by `1`. -/
theorem abs_minAbsOne_le (r : ℝ) : |min |r| 1| ≤ 1 := by
  rw [abs_of_nonneg (le_min (abs_nonneg r) zero_le_one)]
  exact min_le_right _ _

/-- The feature `min(‖u‖, 1)` is `1`-Lipschitz. -/
theorem abs_minNormOne_sub_le {F : Type*} [NormedAddCommGroup F] (u u' : F) :
    |min ‖u‖ 1 - min ‖u'‖ 1| ≤ 1 * ‖u - u'‖ := by
  rw [one_mul]
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (abs_norm_sub_norm_le u u') ?_)
  simp

/-- The outer function `min(|v₀|, 1)` on `ℝ¹` is `1`-Lipschitz for the Euclidean norm. -/
theorem abs_minCoordOne_sub_le (v v' : EuclideanSpace ℝ (Fin 1)) :
    |min |v 0| 1 - min |v' 0| 1| ≤ 1 * ‖v - v'‖ := by
  refine (abs_minAbsOne_sub_le _ _).trans ?_
  rw [one_mul, one_mul]
  have h := PiLp.norm_apply_le (v - v') 0
  simpa [Real.norm_eq_abs] using h

/-- **The hypotheses of Example 5.4 hold.** The baseline of `cor_robust_hypotheses` (Example
5.1(i) with `β₁ = β₂ = 2`, with (2.3) and Assumptions 2.2–2.5 at `L₀ = 2`, `G = 1`,
`α = β₁ = β₂ = 1`, and (2.13) with margin `c_diss = 1`), and the data `ε = 1/4`,
`𝔮 = 𝔮̃ = 𝔮̂ = min(|·|, 1)`, `Q(s) = min(|s|, 1)`, `φ₁(u) = min(‖u‖, 1)`, unit directions
`w₀ = w₁ = v₀ = e₁`, `ĥ = 0`, with Lipschitz constants `1`: then `L_p = 3/4` and (5.1) reads
`3/4 < 1`. -/
theorem ex_fulllaw_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (_ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 (sys 2)
      ∧ Assumption22 (enlJoint ⊥ D bot_le) P 1 (sys 2) (fun _ => 0)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 2 (sys 2)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 (sys 2)
      ∧ Margin213 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1 (sys 2)
      ∧ (0 : ℝ) < 1
      ∧ ∃ (ε : ℝ) (q qb qh : ℝ → ℝ) (Q : EuclideanSpace ℝ (Fin 1) → ℝ)
        (φ : Fin 1 → Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ)) → ℝ)
        (w₀ w₁ v₀ : EuclideanSpace ℝ (Fin 1))
        (hhat : Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ)))
        (Lq Lqb Lqh LQ : ℝ) (K : Fin 1 → ℝ),
        0 < ε ∧ 0 ≤ Lq ∧ 0 ≤ Lqb ∧ 0 ≤ Lqh ∧ 0 ≤ LQ
        ∧ (∀ r r', |q r - q r'| ≤ Lq * |r - r'|) ∧ (∀ r r', |qb r - qb r'| ≤ Lqb * |r - r'|)
        ∧ (∀ r r', |qh r - qh r'| ≤ Lqh * |r - r'|) ∧ (∀ v v', |Q v - Q v'| ≤ LQ * ‖v - v'‖)
        ∧ (∀ j u u', |φ j u - φ j u'| ≤ K j * ‖u - u'‖)
        ∧ ε * ‖GX (1 : Matrix (Fin 1) (Fin 1) ℝ)‖ * (‖w₀‖ * Lq + ‖v₀‖ * Lqb
          + ‖w₁‖ * (LQ * Real.sqrt (∑ j, K j ^ 2)) + ‖hhat‖ * Lqh) < 1 := by
  obtain ⟨Ω, _, P, _, D, hind, hJ, h22, h23, hG, h25, h213, h01, -⟩ := cor_robust_hypotheses
  have he : ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1))‖ = 1 := by simp
  have hGn : ‖GX (1 : Matrix (Fin 1) (Fin 1) ℝ)‖ = 1 := by
    rw [GX_one]
    exact ContinuousLinearMap.norm_id
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind, hJ, h22, h23, hG, h25, h213, h01, 1 / 4,
    fun r => min |r| 1, fun r => min |r| 1, fun r => min |r| 1, fun v => min |v 0| 1,
    fun _ u => min ‖u‖ 1, EuclideanSpace.single 0 1, EuclideanSpace.single 0 1,
    EuclideanSpace.single 0 1, 0, 1, 1, 1, 1, fun _ => 1, by norm_num, zero_le_one, zero_le_one,
    zero_le_one, zero_le_one, abs_minAbsOne_sub_le, abs_minAbsOne_sub_le, abs_minAbsOne_sub_le,
    abs_minCoordOne_sub_le, fun _ => abs_minNormOne_sub_le, ?_⟩
  rw [hGn, he, norm_zero]
  norm_num

/-- **The hypotheses of the affine cylindrical clause of Example 5.4 hold**: at `ν = δ₀` on `ℝ`,
`J = 1`, the feature `φ₁(u) = min(‖u‖, 1)` is `1`-Lipschitz and `Q(s) = s₁` is affine,
`Q(s) = 0 + 1 · s₁`, on the whole of `ℝ¹`. -/
theorem ex_fulllaw_affineQ_hypotheses :
    ∃ (Q : EuclideanSpace ℝ (Fin 1) → ℝ)
      (φ : Fin 1 → Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ)) → ℝ)
      (K : Fin 1 → ℝ) (a : ℝ) (c : Fin 1 → ℝ),
      (∀ j u u', |φ j u - φ j u'| ≤ K j * ‖u - u'‖)
      ∧ ∀ μ : Dissertation.Law.P2 (TupleH (Measure.dirac (0 : ℝ)) 1 1 1),
        Q (WithLp.toLp 2 fun j => ∫ u, φ j u ∂μ.margU.law)
          = a + ∑ j, c j * ∫ u, φ j u ∂μ.margU.law :=
  ⟨fun v => v 0, fun _ u => min ‖u‖ 1, fun _ => 1, 0, fun _ => 1,
    fun _ => abs_minNormOne_sub_le, fun μ => by simp⟩

/-- A unit vector of `L²(δ₀; ℝ¹)`: the constant `e₁`. -/
theorem norm_const_single_dirac :
    ‖Lp.const 2 (Measure.dirac (0 : ℝ)) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))‖ = 1 := by
  rw [Lp.norm_const' 2 _ _ two_ne_zero ENNReal.ofNat_ne_top]
  simp

/-- **The hypotheses of the no-expectation-functional clauses of Example 5.4 hold**: at `ν = δ₀`
on `ℝ`, `L²(ν; ℝ¹)` contains the unit vector `e₁`, and the profile `min(|r|, 1)` is bounded,
`1`-Lipschitz and not constant on `[0, ∞)`; the kernel `0` is integrable against every law. -/
theorem ex_fulllaw_beyond_hypotheses :
    (∃ u : Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ)), u ≠ 0)
    ∧ ∃ (q : ℝ → ℝ) (Lq B : ℝ), (∀ r r', |q r - q r'| ≤ Lq * |r - r'|) ∧ (∀ r, |q r| ≤ B)
      ∧ (∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ q a ≠ q b)
      ∧ ∀ μ : Dissertation.Law.P2 (TupleH (Measure.dirac (0 : ℝ)) 1 1 1),
        Integrable (fun _ : TupleH (Measure.dirac (0 : ℝ)) 1 1 1 => (0 : ℝ)) μ.law := by
  refine ⟨⟨Lp.const 2 (Measure.dirac (0 : ℝ)) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)),
    fun h => by
      have h1 := norm_const_single_dirac
      rw [h, norm_zero] at h1
      exact zero_ne_one h1⟩, fun r => min |r| 1, 1, 1,
    abs_minAbsOne_sub_le, abs_minAbsOne_le, ⟨0, 1, le_rfl, zero_le_one, by norm_num⟩,
    fun μ => integrable_zero _ _ _⟩

/-- The tuple space at `ν = δ₀` on `ℝ` and `n = m = d = 1` has measurable singletons (the product
instance, beyond the default instance-search size for the fourfold product). -/
instance measurableSingletonClass_tupleH_dirac :
    MeasurableSingletonClass (TupleH (Measure.dirac (0 : ℝ)) 1 1 1) :=
  @Prod.instMeasurableSingletonClass _ _ _ _ _ (@Prod.instMeasurableSingletonClass _ _ _ _ _
    inferInstance)

/-- **The hypotheses of the (3.5) clause of Corollary 3.6 hold at the perturbation of
Example 5.4.** On a probability space carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, over
its filtration `enlJoint ⊥ D`, with `n = 1` and `T = 1`, the perturbation of Example 5.4 with
`ε = 1/4`, the profiles `min(|r|, 1)`, `Q(s) = min(|s₁|, 1)`, the feature `min(‖u‖, 1)`,
`w₀ = w₁ = v₀ = e₁`, `ĥ = 0` and the reference laws `δ₀` depends on the tuple through its law only
and satisfies (3.5) with `L_p = 3/4`. -/
theorem cor_robust_lip_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ))),
      (ex54Pert (Measure.dirac (0 : ℝ)) 1 1 1 (1 / 4) (fun r => min |r| 1) (fun r => min |r| 1)
          (fun r => min |r| 1) (fun v => min |v 0| 1) (fun _ u => min ‖u‖ 1)
          (Dissertation.Law.P2.dirac 0) (Dissertation.Law.P2.dirac 0)
          (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
          0).TupleIndep
      ∧ LawLip35 (enlJoint ⊥ D bot_le) P 1 (3 / 4)
          (ex54Pert (Measure.dirac (0 : ℝ)) 1 1 1 (1 / 4) (fun r => min |r| 1)
            (fun r => min |r| 1) (fun r => min |r| 1) (fun v => min |v 0| 1)
            (fun _ u => min ‖u‖ 1) (Dissertation.Law.P2.dirac 0) (Dissertation.Law.P2.dirac 0)
            (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
            0) := by
  obtain ⟨Ω, _, P, _, D, hind, -⟩ := ex_fulllaw_hypotheses
  obtain ⟨hTI, -, hLL, -, -⟩ := ex_fulllaw_pert ⊥ (Measure.dirac (0 : ℝ)) 1 1 1 P D bot_le hind
    one_pos one_pos 1 one_pos 1 (1 / 4) (fun r => min |r| 1) (fun r => min |r| 1)
    (fun r => min |r| 1) (fun v => min |v 0| 1) (fun _ u => min ‖u‖ 1)
    (Dissertation.Law.P2.dirac 0) (Dissertation.Law.P2.dirac 0) (EuclideanSpace.single 0 1)
    (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) 0 1 1 1 1 (fun _ => 1) (by norm_num)
    zero_le_one zero_le_one zero_le_one zero_le_one abs_minAbsOne_sub_le abs_minAbsOne_sub_le
    abs_minAbsOne_sub_le abs_minCoordOne_sub_le (fun _ => abs_minNormOne_sub_le)
  have he : ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1))‖ = 1 := by simp
  rw [he, norm_zero] at hLL
  norm_num at hLL
  exact ⟨Ω, inferInstance, P, inferInstance, D, hTI, hLL⟩

/-- The feature `min(‖u‖, 1)` of the `U`-marginal of the Dirac mass at a tuple with `U`-channel
`t e₁`, `e₁` the constant unit vector of `L²(δ₀; ℝ¹)`, is `min(|t|, 1)`. -/
theorem integral_minNormOne_margU_dirac (t : ℝ) :
    ∫ u, min ‖u‖ 1 ∂(Dissertation.Law.P2.dirac
        (((0 : EuclideanSpace ℝ (Fin 1)), (0 : EuclideanSpace ℝ (Fin 1)),
          (0 : EuclideanSpace ℝ (Fin 1 × Fin 1)),
          t • Lp.const 2 (Measure.dirac (0 : ℝ)) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) :
          TupleH (Measure.dirac (0 : ℝ)) 1 1 1)).margU.law
      = min |t| 1 := by
  rw [margU_dirac]
  change ∫ u, min ‖u‖ 1 ∂(Measure.dirac _) = _
  rw [integral_dirac, norm_smul, norm_const_single_dirac, mul_one, Real.norm_eq_abs]

/-- **The hypotheses of the cylindrical clause of Example 5.4 hold**: at `ν = δ₀` on `ℝ`, `J = 1`,
the feature `φ₁(u) = min(‖u‖, 1)` is bounded and `1`-Lipschitz, `Q(s) = min(|s₁|, 1/2)` is
`1`-Lipschitz, and `Q` is not affine on the attained range of the feature: at the Dirac masses
with `U`-channel `0`, `e₁/2`, `e₁` the feature takes the values `0, 1/2, 1` and `Q` the values
`0, 1/2, 1/2`. -/
theorem ex_fulllaw_beyond_Q_hypotheses :
    ∃ (Q : EuclideanSpace ℝ (Fin 1) → ℝ)
      (φ : Fin 1 → Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ)) → ℝ)
      (LQ B : ℝ) (K : Fin 1 → ℝ),
      (∀ v v', |Q v - Q v'| ≤ LQ * ‖v - v'‖) ∧ (∀ j u u', |φ j u - φ j u'| ≤ K j * ‖u - u'‖)
      ∧ (∀ j u, |φ j u| ≤ B)
      ∧ ¬ ∃ (a : ℝ) (c : Fin 1 → ℝ),
        ∀ μ : Dissertation.Law.P2 (TupleH (Measure.dirac (0 : ℝ)) 1 1 1),
          Q (WithLp.toLp 2 fun j => ∫ u, φ j u ∂μ.margU.law)
            = a + ∑ j, c j * ∫ u, φ j u ∂μ.margU.law := by
  refine ⟨fun v => min |v 0| (1 / 2), fun _ u => min ‖u‖ 1, 1, 1, fun _ => 1, fun v v' => ?_,
    fun _ => abs_minNormOne_sub_le, fun _ u => ?_, ?_⟩
  · refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ (by simp))
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    rw [one_mul]
    have h := PiLp.norm_apply_le (v - v') 0
    simpa [Real.norm_eq_abs] using h
  · rw [abs_of_nonneg (le_min (norm_nonneg u) zero_le_one)]
    exact min_le_right _ _
  · rintro ⟨a, c, h⟩
    have key : ∀ t : ℝ, min |min |t| 1| (1 / 2) = a + c 0 * min |t| 1 := fun t => by
      have := h (Dissertation.Law.P2.dirac
        (((0 : EuclideanSpace ℝ (Fin 1)), (0 : EuclideanSpace ℝ (Fin 1)),
          (0 : EuclideanSpace ℝ (Fin 1 × Fin 1)),
          t • Lp.const 2 (Measure.dirac (0 : ℝ)) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))) :
          TupleH (Measure.dirac (0 : ℝ)) 1 1 1))
      simpa only [integral_minNormOne_margU_dirac, Fin.sum_univ_one, PiLp.toLp_apply] using this
    have h0 := key 0
    have h1 := key (1 / 2)
    have h2 := key 1
    norm_num at h0 h1 h2
    linarith

end Dissertation.Acceptance.A
