/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec2Remarks
import Dissertation.Acceptance.A.Sec5
import Dissertation.Acceptance.A.Witness
import Dissertation.WellPosedness.Spec.Bridge25
import Dissertation.WellPosedness.Remarks.JumpDichotomy
import Dissertation.WellPosedness.Remarks.Pointwise
import Dissertation.WellPosedness.Remarks.Margin
import Dissertation.WellPosedness.Remarks.CouplingForm
import Dissertation.WellPosedness.Remarks.CouplingRealisation
import Dissertation.WellPosedness.Remarks.UniformVariable

/-!
# Section 2 of the well-posedness paper: proofs of the remarks on the assumptions

## Main statements

* `Dissertation.Acceptance.A.rem_diag_mono`, `rem_diag_mono_converse` — Remark 2.8.
* `Dissertation.Acceptance.A.rem_intrinsic_uniform`, `rem_intrinsic_coupling`,
  `rem_intrinsic_basis` — Remark 2.9.
* `Dissertation.Acceptance.A.rem_beta1_dich`, `rem_beta1_zero` — Remark 2.10.
* `Dissertation.Acceptance.A.rem_margin_reduce`, `rem_margin_unweighted`, `rem_margin_sharp` —
  Remark 2.11.
* `Dissertation.Acceptance.A.rem_affine_hypotheses`, `rem_margin_hypotheses`,
  `rem_coupling_hypotheses` — the hypotheses of the remarks hold for Example 5.1(i) over a Lévy
  driver with `ν = δ₀`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Matrix

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.Law

universe u v w

/-- Remark 2.10, the `β₁` dichotomy. -/
theorem rem_beta1_dich : PaperSpec.A.rem_beta1_dich.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ _ hn hm T hT hν G hG α β₁ β₂ C h
  refine ⟨?_, fun hadd => jump_dichotomy hT hν hG hn hm hadd h.diagonalMonotone h.constants,
    fun hlt => ⟨h.constants.rank_lt hlt,
      not_additive_of_lt hT hν hG hm hlt h.diagonalMonotone h.constants⟩⟩
  filter_upwards [h.interior] with t ht p hp p' hp' heq
  obtain ⟨-, hle⟩ := ht p hp p' hp'
  have e1 : ∀ ω, pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2
      = ∫ e, inner ℝ (C.h t (p.1 ω) p.2 e - C.h t (p'.1 ω) p'.2 e)
          (GX Gᵀ ((p.1 ω).2.2.2 e - (p'.1 ω).2.2.2 e)) ∂ν := fun ω => by
    obtain ⟨h1, h2, h3⟩ := heq ω
    simp only [pairing27, h1, h2, h3, sub_self, map_zero, inner_zero_right, zero_add]
  have e2 : ∀ ω, ‖GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)‖ ^ 2
      + ‖GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)‖ ^ 2
      + ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2
      = ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2 := fun ω => by
    obtain ⟨-, h2, h3⟩ := heq ω
    simp [h2, h3]
  have e3 : ∀ ω, ‖GX G ((p.1 ω).1 - (p'.1 ω).1)‖ ^ 2 = 0 := fun ω => by
    obtain ⟨h1, -, -⟩ := heq ω
    simp [h1]
  rw [integral_congr_ae (ae_of_all _ e1), integral_congr_ae (ae_of_all _ e2),
    integral_congr_ae (ae_of_all _ e3), integral_zero, mul_zero, sub_zero] at hle
  exact hle

/-- Remark 2.10, zero intensity. -/
theorem rem_beta1_zero : PaperSpec.A.rem_beta1_zero.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ _ n d P _ D h𝒢₀ _ hn T _ β₁ β₂ hβ₁ hβ₂ σc hc
  obtain ⟨-, -, -, -, h25⟩ := affine_assumptions (ℱ := enlJoint 𝒢₀ D h𝒢₀) (P := P) (T := T)
    (σc := σc) (hc := hc) hβ₁ hβ₂ (0 : EuclideanSpace ℝ (Fin n))
  exact ⟨fun t θ θ' μ μ' _ => additive_affine_nu_zero t θ θ' μ μ', h25⟩

/-- The printed pointwise form of (2.7) is `PointwiseGMonotone`. -/
theorem pointwise_spec_iff {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] {n m d : ℕ} {T β₁ β₂ : ℝ}
    {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d} :
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ (θ θ' : TupleH ν n m d)
      (μ μ' : P2 (TupleH ν n m d)),
      pairing27 G C t θ θ' μ μ'
        ≤ -β₁ * (‖GX Gᵀ (θ.2.1 - θ'.2.1)‖ ^ 2 + ‖GZ Gᵀ (θ.2.2.1 - θ'.2.2.1)‖ ^ 2
            + ‖GU Gᵀ ν (θ.2.2.2 - θ'.2.2.2)‖ ^ 2)
          - β₂ * ‖GX G (θ.1 - θ'.1)‖ ^ 2)
      ↔ PointwiseGMonotone T G β₁ β₂ C := by
  have e : ∀ (t : ℝ) (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)),
      WellPosedness.dissipation (GX G) (GZ G) (GU G ν) β₁ β₂ (diagDiff C t θ θ' μ μ')
        = -β₁ * (‖GX Gᵀ (θ.2.1 - θ'.2.1)‖ ^ 2 + ‖GZ Gᵀ (θ.2.2.1 - θ'.2.2.1)‖ ^ 2
            + ‖GU Gᵀ ν (θ.2.2.2 - θ'.2.2.2)‖ ^ 2)
          - β₂ * ‖GX G (θ.1 - θ'.1)‖ ^ 2 := fun t θ θ' μ μ' => by
    simp only [WellPosedness.dissipation, diagDiff, adjoint_GX, adjoint_GZ, adjoint_GU]
  unfold PointwiseGMonotone
  simp only [← pairing27_eq, e]

/-- The weighted quantity of (2.12), in the printed order, is `gWeightSq` of the differences. -/
theorem integral_gWeightSq_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Type*}
    [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    {n m d : ℕ} (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d) (t : ℝ)
    (Θ Θ' : Ω → TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)) :
    ∫ ω, gWeightSq (GX G) (GZ G) (GU G ν) (diagDiff C t (Θ ω) (Θ' ω) μ μ') ∂P
      = ∫ ω, (‖GX Gᵀ ((Θ ω).2.1 - (Θ' ω).2.1)‖ ^ 2
          + ‖GZ Gᵀ ((Θ ω).2.2.1 - (Θ' ω).2.2.1)‖ ^ 2
          + ‖GU Gᵀ ν ((Θ ω).2.2.2 - (Θ' ω).2.2.2)‖ ^ 2
          + ‖GX G ((Θ ω).1 - (Θ' ω).1)‖ ^ 2) ∂P := by
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [gWeightSq, diagDiff, adjoint_GX, adjoint_GZ, adjoint_GU]

/-- Remark 2.8, the pointwise condition gives Assumption 2.5. -/
theorem rem_diag_mono : PaperSpec.A.rem_diag_mono.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ _ T L β₁ β₂ G C hJ h23 hpw
  have hL := lipInterior_iff_diagonalLipschitzH.mp h23.interior
  have hB := (jointBorel_iff.mp hJ).1
  have hM := (pointwise_spec_iff.mp hpw).diagonalMonotone_of_coeffBorelW2 hL hB
  filter_upwards [hM, hL, ae_restrict_mem measurableSet_Icc] with t hMt hLt htI p hp p' hp'
  obtain ⟨hs, h2, he⟩ := hp
  obtain ⟨hs', h2', he'⟩ := hp'
  have hi := WellPosedness.integrable_interiorPairing_of_diagonalLipschitzHAt (G := G) hB htI hLt
    hs hs' h2 h2'
  rw [he, he']
  refine ⟨by simpa only [pairing27_eq] using hi, ?_⟩
  rw [← integral_dissipation_eq h2 h2']
  simpa only [pairing27_eq] using hMt p.1 p'.1 hs hs' h2 h2'

/-- Remark 2.8, the converse fails. -/
theorem rem_diag_mono_converse : PaperSpec.A.rem_diag_mono_converse.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ hind T hT
  obtain ⟨hJ, -, ⟨L, h23⟩, -, h25⟩ := ex_concrete_i_clamp 𝒢₀ ν P D h𝒢₀ hind T hT 2 1 1 two_pos
    one_pos one_pos one_lt_two 0 0 (fun _ => 0) stronglyMeasurable_const (memLp_const _)
  exact ⟨_, L, 1, 2 - 1, 1, hJ, h23, h25, fun β β' hβ hpw =>
    not_pointwiseGMonotone_clampAffine (β₁ := 2) (β₂ := 1) two_pos one_pos hT hβ
      (pointwise_spec_iff.mp hpw)⟩

/-- The first Brownian coordinate is adapted to the initially enlarged filtration. -/
theorem measurable_brownian_enlJoint {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ} (hd : 0 < d)
    {P : Measure Ω} [IsProbabilityMeasure P] (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (h𝒢₀ : 𝒢₀ ≤ mΩ) (s : ℝ) : Measurable[enlJoint 𝒢₀ D h𝒢₀ s] ((D.W.W ⟨0, hd⟩).W s) :=
  ((D.isBrownianFiltration ⟨0, hd⟩).measurable s).mono (filtration_le_enlJoint D h𝒢₀ s) le_rfl

/-- Remark 2.9, a uniform variable. -/
theorem rem_intrinsic_uniform : PaperSpec.A.rem_intrinsic_uniform.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ d hd P _ D h𝒢₀ t ht
  exact ⟨fun x => Dissertation.Law.cdfUnit (ProbabilityTheory.gaussianReal 0 1) (x / √t),
    (Dissertation.Law.measurable_cdfUnit _).comp (measurable_id.div_const _),
    measurable_cdfUnit_brownian (D.W.W ⟨0, hd⟩) (measurable_brownian_enlJoint hd D h𝒢₀) t,
    map_cdfUnit_brownian_eq_volume (D.W.W ⟨0, hd⟩) ht⟩

/-- Remark 2.9, couplings are joint laws of inputs. -/
theorem rem_intrinsic_coupling : PaperSpec.A.rem_intrinsic_coupling.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d hd P _ D h𝒢₀ t ht μ μ' γ hγ
  exact exists_pair_of_coupling (D.W.W ⟨0, hd⟩) (measurable_brownian_enlJoint hd D h𝒢₀) ht hγ

/-- Remark 2.9, the diagonal assumptions are intrinsic. -/
theorem rem_intrinsic_basis : PaperSpec.A.rem_intrinsic_basis.{u, v, w} := by
  intro Ω Ω' 𝒢₀ mΩ 𝒢₀' mΩ' E _ ν _ _ n m d hd P _ P' _ D D' h𝒢₀ h𝒢₀' T hT L α β₁ β₂ G C hJ
  have hU := supportsUniform_enlJoint D h𝒢₀ hd
  have hU' := supportsUniform_enlJoint D' h𝒢₀' hd
  have hB := (jointBorel_iff.mp hJ).1.toCoeffBorel
  have hg := hJ.measurable_g_section
  have h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C
      ↔ Assumption23 (enlJoint 𝒢₀' D' h𝒢₀') P' T L C := by
    constructor
    · rintro ⟨hL0, hi, ht⟩
      exact ⟨hL0, lipInterior_iff_diagonalLipschitzH.mpr ((diagonalLipschitzH_congr_basis hB hU
        hU').mp (lipInterior_iff_diagonalLipschitzH.mp hi)),
        lipTerminal_iff_terminalLipschitz.mpr ((terminalLipschitz_congr_basis hg hU hU' hT).mp
          (lipTerminal_iff_terminalLipschitz.mp ht))⟩
    · rintro ⟨hL0, hi, ht⟩
      exact ⟨hL0, lipInterior_iff_diagonalLipschitzH.mpr ((diagonalLipschitzH_congr_basis hB hU
        hU').mpr (lipInterior_iff_diagonalLipschitzH.mp hi)),
        lipTerminal_iff_terminalLipschitz.mpr ((terminalLipschitz_congr_basis hg hU hU' hT).mpr
          (lipTerminal_iff_terminalLipschitz.mp ht))⟩
  refine ⟨h23, fun h => ?_⟩
  rw [assumption25_iff hJ h, assumption25_iff hJ (h23.mp h)]
  exact and_congr (diagonalMonotone_congr_basis hB hU hU')
    (and_congr (terminalMonotone_congr_basis hg hU hU' hT) Iff.rfl)

/-- Remark 2.11, the reduced constants. -/
theorem rem_margin_reduce : PaperSpec.A.rem_margin_reduce.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ _ T β₁ β₂ G C hmono c _ _
  filter_upwards [hmono] with t ht p hp p' hp'
  obtain ⟨hi, hle⟩ := ht p hp p' hp'
  refine ⟨hi, hle.trans (le_of_eq ?_)⟩
  obtain ⟨-, h2, -⟩ := hp
  obtain ⟨-, h2', -⟩ := hp'
  have hY := integrable_norm_sq_comp_sub_Y (GX Gᵀ) h2 h2'
  have hZ := integrable_norm_sq_comp_sub_Z (GZ Gᵀ) h2 h2'
  have hU := integrable_norm_sq_comp_sub_U (GU Gᵀ ν) h2 h2'
  have hX := integrable_norm_sq_comp_sub_X (GX G) h2 h2'
  rw [integral_add ((hY.fun_add hZ).fun_add hU) hX]
  ring

/-- Remark 2.11, the unweighted margin. -/
theorem rem_margin_unweighted : PaperSpec.A.rem_margin_unweighted.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n d P _ D h𝒢₀ _ hn T β₁ β₂ c G C hG hc h
  have hW : DiagonalMonotoneWeightedMargin (enlJoint 𝒢₀ D h𝒢₀) P T G β₁ β₂ c C := by
    filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
    obtain ⟨-, hle⟩ := ht (Θ, lawP2 P Θ) (mk_mem_diagonalInputs hΘ hΘ2) (Θ', lawP2 P Θ')
      (mk_mem_diagonalInputs hΘ' hΘ2')
    rw [integral_dissipation_eq hΘ2 hΘ2', integral_gWeightSq_eq G C t Θ Θ']
    simpa only [pairing27_eq] using hle
  have hM := hW.unweighted_of_rank (by rw [hG, min_self]) hc.le
  filter_upwards [hM, h] with t ht ht' p hp p' hp'
  have hi := (ht' p hp p' hp').1
  obtain ⟨hs, h2, he⟩ := hp
  obtain ⟨hs', h2', he'⟩ := hp'
  refine ⟨hi, ?_⟩
  rw [he, he', integral_margin_eq, ← integral_dissipation_eq h2 h2', div_inv_eq_mul]
  simpa only [pairing27_eq] using ht p.1 p'.1 hs hs' h2 h2'

/-- Remark 2.11, the margin `c` itself does not carry over. -/
theorem rem_margin_sharp : PaperSpec.A.rem_margin_sharp.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ _ T hT
  obtain ⟨hW, hno⟩ := not_diagonalMonotoneMargin_affine_half (ℱ := enlJoint 𝒢₀ D h𝒢₀) (P := P)
    (ν := ν) (d := 1) (β₁ := 2) (β₂ := 2) (σ₁ := 0) (h₁ := 0) hT (c := 1) one_pos
  have h1 : (0 : ℝ) ≤ 2 - 1 := by norm_num
  have hrank : ((2⁻¹ : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).rank = min 1 1 := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (by simp)),
      Fintype.card_fin, min_self]
  refine ⟨_, _, 2 - 1, 2 - 1, 1, hrank, h1, h1, one_pos, ?_,
    fun h => hno h.diagonalMonotoneMargin⟩
  filter_upwards [hW, hW.integrable one_pos h1 h1] with t ht hi p hp p' hp'
  obtain ⟨hs, h2, he⟩ := hp
  obtain ⟨hs', h2', he'⟩ := hp'
  rw [he, he']
  refine ⟨by simpa only [pairing27_eq] using hi p.1 p'.1 hs hs' h2 h2', ?_⟩
  rw [← integral_dissipation_eq h2 h2', ← integral_gWeightSq_eq _ _ t p.1 p'.1]
  simpa only [pairing27_eq] using ht p.1 p'.1 hs hs' h2 h2'

/-! ### The hypotheses at Example 5.1(i) -/

/-- **The hypotheses of Remarks 2.8, 2.10 and 2.11 hold at Example 5.1(i).** Over a probability
space carrying a Lévy driver with `d = 1` and `ν = δ₀ ≠ 0` on `ℝ`, with `𝒢₀ = ⊥` independent of the
driver and `T = 1`, the coefficients of Example 5.1(i) with `β₁ = β₂ = 1`, `σ_c = 0`, `h_c = 0`
satisfy (2.3), Assumption 2.3 with `L = 1`, the pointwise form of (2.7) and Assumption 2.5 with
`G = 1` (of full rank), `α = 1`; and `0 < 1/2 < min{1, 1}`. -/
theorem rem_affine_hypotheses :
    Measure.dirac (0 : ℝ) ≠ 0
    ∧ (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ))),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P
      ∧ JointBorel 1 (affineCoeffs (ν := Measure.dirac (0 : ℝ)) 1 1
          (0 : EuclideanSpace ℝ (Fin 1 × Fin 1)) 0)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 (max (max 1 1) 1)
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) 1 1 (0 : EuclideanSpace ℝ (Fin 1 × Fin 1)) 0)
      ∧ (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ∀ (θ θ' : TupleH (Measure.dirac (0 : ℝ)) 1 1 1)
          (μ μ' : P2 (TupleH (Measure.dirac (0 : ℝ)) 1 1 1)),
        pairing27 (1 : Matrix (Fin 1) (Fin 1) ℝ)
            (affineCoeffs 1 1 (0 : EuclideanSpace ℝ (Fin 1 × Fin 1)) 0) t θ θ' μ μ'
          ≤ -1 * (‖GX (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ (θ.2.1 - θ'.2.1)‖ ^ 2
              + ‖GZ (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ (θ.2.2.1 - θ'.2.2.1)‖ ^ 2
              + ‖GU (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ (Measure.dirac (0 : ℝ))
                (θ.2.2.2 - θ'.2.2.2)‖ ^ 2)
            - 1 * ‖GX (1 : Matrix (Fin 1) (Fin 1) ℝ) (θ.1 - θ'.1)‖ ^ 2)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) 1 1 (0 : EuclideanSpace ℝ (Fin 1 × Fin 1)) 0))
    ∧ (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < min 1 1 := by
  refine ⟨Measure.dirac_ne_zero, ?_, by norm_num, by norm_num⟩
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  obtain ⟨hJ, -, h23, hG, h25⟩ := affine_assumptions (ℱ := enlJoint ⊥ D bot_le) (P := P)
    (T := 1) (σc := (0 : EuclideanSpace ℝ (Fin 1 × Fin 1)))
    (hc := (0 : Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ)))) one_pos one_pos
    (0 : EuclideanSpace ℝ (Fin 1))
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, hJ, h23,
    pointwise_spec_iff.mpr pointwiseGMonotone_affine, hG, h25⟩

/-- **The hypotheses of the unweighted margin hold at Example 5.1(i).** Over a probability space
carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥` independent of the driver,
the coefficients of Example 5.1(i) with `β₁ = β₂ = 1`, `σ_c = 0`, `h_c = 0` satisfy (2.12) at
`G = 1` (of full rank) with the constants `1/2, 1/2` and the margin `1/2 > 0`. -/
theorem rem_margin_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ))),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1 ∧ (0 : ℝ) < 1 / 2
      ∧ PaperSpec.A.Margin212 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ)
          (1 - 1 / 2) (1 - 1 / 2) (1 / 2)
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) 1 1
            (0 : EuclideanSpace ℝ (Fin 1 × Fin 1)) 0) := by
  obtain ⟨-, ⟨Ω, _, P, _, D, hind, -, -, -, hG, h25⟩, h0, h1⟩ := rem_affine_hypotheses
  exact ⟨Ω, inferInstance, P, inferInstance, D, hind, hG, h0,
    rem_margin_reduce ⊥ _ 1 1 1 P D bot_le hind 1 1 1 1 _ h25.interior (1 / 2) h0 h1⟩

/-- **A coupling of two laws of finite second moment**: the Dirac mass at `(0, 0)` couples the
Dirac mass at the origin of `H` with itself. -/
theorem rem_coupling_hypotheses :
    IsCoupling (P2.dirac (0 : TupleH (Measure.dirac (0 : ℝ)) 1 1 1)).law
      (P2.dirac (0 : TupleH (Measure.dirac (0 : ℝ)) 1 1 1)).law
      (Measure.dirac ((0, 0) : TupleH (Measure.dirac (0 : ℝ)) 1 1 1
        × TupleH (Measure.dirac (0 : ℝ)) 1 1 1)) := by
  refine ⟨?_, ?_⟩
  · rw [Measure.fst, Measure.map_dirac' measurable_fst]
    rfl
  · rw [Measure.snd, Measure.map_dirac' measurable_snd]
    rfl

end Dissertation.Acceptance.A
