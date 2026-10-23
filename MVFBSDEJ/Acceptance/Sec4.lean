/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec4
import MVFBSDEJ.WellPosedness.BrownianPoisson.MeasurableDrift
import MVFBSDEJ.WellPosedness.Existence.PredictableWP
import MVFBSDEJ.WellPosedness.Existence.CadlagVersion
import MVFBSDEJ.WellPosedness.System.PaperPerturbationInt
import MVFBSDEJ.Acceptance.Solution

/-!
# Section 4 of the well-posedness paper: proofs of the lemmas

## Main statements

* `MVFBSDEJ.Acceptance.lem_bpbsde` — Lemma 4.1, with `C_BP(T) = 13 e^T + 3T`.
* `MVFBSDEJ.Acceptance.lem_bpbsde_explicit` — Lemma 4.1 with `C_BP = 2 e^T (5 + 4c) + 4T` for every
  `c ≥ 4`.
* `MVFBSDEJ.Acceptance.lem_small` — Lemma 4.2, with `λ*(T, L) = smallCoupling T (2L)`.
* `MVFBSDEJ.Acceptance.lem_pert` — Lemma 4.3, with
  `C_B = aprioriConst T (10 (2L)²) (4 (2L)²) ‖G‖ c_G α β₁ β₂ λ̲`.
* `MVFBSDEJ.Acceptance.lem_cont` — Lemma 4.4, with `ζ₀ = 1 / (2 (1 + K C_B))`,
  `K = lipConst T (2L)` and `C_B` the constant of Lemma 4.3 at `λ̲ = λ*`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Spec LevyStochCalc

universe u v w

/-- Lemma 4.1. -/
theorem lem_bpbsde : PaperSpec.lem_bpbsde.{u, v, w} := by
  refine ⟨fun T => 13 * Real.exp T + 3 * T, ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ hind₀ _ _ T hT δξ φ δY δZ δU hZ hZv hZs hU hUv hUs
    _ hξ hφm hφs hYa hYr _ heq
  have hξk : ∀ k, MemLp (fun ω => δξ ω k) 2 P := memLp_iff_forall_coord.mp hξ
  have key := brownianPoisson_estimate_vec_of_measurable (crossWitnessEnl D h𝒢₀ hind₀)
    (hF0_enlJoint D h𝒢₀) (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT
    (ξ := fun k ω => δξ ω k)
    (fun k j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
    (fun k => progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k)) hZv hZs
    (fun k => (hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
    (fun k => (hU k).markedProgressivelyMeasurable) hUv hUs hφm hφs hξk hYa hYr heq
  refine ⟨?_, key⟩
  have hξe : ∫⁻ ω, (esq fun k => δξ ω k) ∂P < ⊤ := by
    simp only [esq]
    rw [lintegral_finsetSum' _ fun k _ =>
      (hξk k).aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal.pow_const 2]
    exact ENNReal.sum_lt_top.mpr fun k _ =>
      Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two (hξk k)
  refine lt_of_le_of_lt (le_trans le_self_add le_self_add) (key.trans_lt ?_)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr
    ⟨hξe, ENNReal.sum_lt_top.mpr fun k _ => (hφs k).lt_top⟩)

/-- Lemma 4.1 with the constant of its proof. -/
theorem lem_bpbsde_explicit : PaperSpec.lem_bpbsde_explicit.{u, v, w} := by
  intro c hc Ω 𝒢₀ mΩ E _ ν _ _ m d P _ D h𝒢₀ hind₀ _ _ T hT δξ φ δY δZ δU hZ hZv hZs hU hUv
    hUs _ hξ hφm hφs hYa hYr _ heq
  have hξk : ∀ k, MemLp (fun ω => δξ ω k) 2 P := memLp_iff_forall_coord.mp hξ
  have key := brownianPoisson_estimate_vec_of_measurable (crossWitnessEnl D h𝒢₀ hind₀)
    (hF0_enlJoint D h𝒢₀) (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT
    (ξ := fun k ω => δξ ω k)
    (fun k j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
    (fun k => progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k)) hZv hZs
    (fun k => (hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
    (fun k => (hU k).markedProgressivelyMeasurable) hUv hUs hφm hφs hξk hYa hYr heq
  have hC : 13 * Real.exp T + 3 * T ≤ 2 * Real.exp T * (5 + 4 * c) + 4 * T := by
    nlinarith [Real.exp_pos T, mul_le_mul_of_nonneg_right hc (Real.exp_pos T).le]
  refine ⟨?_, key.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hC) (zero_le))⟩
  have hξe : ∫⁻ ω, (esq fun k => δξ ω k) ∂P < ⊤ := by
    simp only [esq]
    rw [lintegral_finsetSum' _ fun k _ =>
      (hξk k).aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal.pow_const 2]
    exact ENNReal.sum_lt_top.mpr fun k _ =>
      Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two (hξk k)
  refine lt_of_le_of_lt (le_trans le_self_add le_self_add) (key.trans_lt ?_)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr
    ⟨hξe, ENNReal.sum_lt_top.mpr fun k _ => (hφs k).lt_top⟩)

section Forced

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {h𝒢₀ : 𝒢₀ ≤ mΩ}
  {hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P} {T L lam : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Ω → EuclideanSpace ℝ (Fin n)}

omit [MeasurableSpace.CountablyGenerated E] in
/-- Every field of `enlJoint` contains the null sets. -/
theorem measurableSet_enlJoint_of_null_all (s : Set Ω) (hs : MeasurableSet s) (h0 : P s = 0)
    (t : ℝ) : MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ t] s := by
  have h0' := measurableSet_enlJoint_of_null D h𝒢₀ hs h0
  rcases le_total 0 t with ht | ht
  · exact (enlJoint 𝒢₀ D h𝒢₀).mono ht _ h0'
  · exact enlJoint_le_of_nonpos D h𝒢₀ ht _ h0'

/-- `WP(λ)` of the paper from `WP(λ)` over the predictable forcings for the implementation's
solution notion, over `enlJoint`, for coefficients with (2.3), the origin bounds of Assumption 2.2
and Assumption 2.3. -/
theorem wp_of_paperForcedWPPred (hJ : JointBorel T C)
    (h22 : Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀)
    (h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C) (hT : 0 ≤ T)
    (h : PaperForcedWPPred D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T lam C (fun i ω => ξ₀ ω i)) :
    PaperSpec.WP D h𝒢₀ hind₀ T lam C ξ₀ := by
  intro qb qσ qh qf qg hq
  refine ⟨?_, ?_⟩
  · obtain ⟨X, Y, Z, U, γ, hs⟩ := h.1 qb qσ qh qf qg hq
    obtain ⟨X', Y', hs', hX', hY', -⟩ := hs.exists_cadlag_version hT
      (jointBorel_iff.mp hJ).1.toCoeffBorel measurableSet_enlJoint_of_null_all
    exact ⟨X', Y', Z, U, forcedSolution_of_paperSolutionForced hT hs' hX' hY'⟩
  · intro X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hS₁ hS₂
    obtain ⟨⟨γ₁, h₁⟩, -, -⟩ := ForcedSolution.paperSolutionForced hT hJ h22.origin h23 hS₁
    obtain ⟨⟨γ₂, h₂⟩, -, -⟩ := ForcedSolution.paperSolutionForced hT hJ h22.origin h23 hS₂
    exact h.2 qb qσ qh qf qg X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ γ₁ γ₂ hq h₁ h₂

/-- `WP(λ)` over the predictable forcings for the implementation's solution notion from `WP(λ)`
of the paper, over `enlJoint`, for coefficients with (2.3), the origin bounds of Assumption 2.2
and Assumption 2.3: a solution in the implementation's sense has a càdlàg version, to which the
uniqueness of `WP(λ)` applies. -/
theorem paperForcedWPPred_of_wp (hJ : JointBorel T C)
    (h22 : Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀)
    (h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C) (hT : 0 ≤ T)
    (h : PaperSpec.WP D h𝒢₀ hind₀ T lam C ξ₀) :
    PaperForcedWPPred D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T lam C (fun i ω => ξ₀ ω i) := by
  refine ⟨fun qb qσ qh qf qg hq => ?_, fun qb qσ qh qf qg X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ γ₁ γ₂ hq h₁ h₂
    => ?_⟩
  · obtain ⟨X, Y, Z, U, hS⟩ := (h qb qσ qh qf qg hq).1
    obtain ⟨⟨γ, hs⟩, -, -⟩ := ForcedSolution.paperSolutionForced hT hJ h22.origin h23 hS
    exact ⟨X, Y, Z, U, γ, hs⟩
  · have hB := (jointBorel_iff.mp hJ).1.toCoeffBorel
    obtain ⟨X₁', Y₁', h₁', hX₁, hY₁, he₁⟩ :=
      h₁.exists_cadlag_version hT hB measurableSet_enlJoint_of_null_all
    obtain ⟨X₂', Y₂', h₂', hX₂, hY₂, he₂⟩ :=
      h₂.exists_cadlag_version hT hB measurableSet_enlJoint_of_null_all
    obtain ⟨hX, hY, hZ, hU⟩ := (h qb qσ qh qf qg hq).2 X₁' X₂' Y₁' Y₂' Z₁ Z₂ U₁ U₂
      (forcedSolution_of_paperSolutionForced hT h₁' hX₁ hY₁)
      (forcedSolution_of_paperSolutionForced hT h₂' hX₂ hY₂)
    refine ⟨fun i => ?_, fun k => ?_, hZ, hU⟩
    · filter_upwards [he₁, he₂, hX i] with ω e₁ e₂ e t ht
      rw [← (e₁ t ht).1 i, ← (e₂ t ht).1 i]
      exact e t ht
    · filter_upwards [he₁, he₂, hY k] with ω e₁ e₂ e t ht
      rw [← (e₁ t ht).2 k, ← (e₂ t ht).2 k]
      exact e t ht

end Forced

/-- Lemma 4.2. -/
theorem lem_small : PaperSpec.lem_small.{u, v, w} := by
  refine ⟨fun T L => smallCoupling T (2 * L), ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ hd T hT L C ξ₀ hJ h22 h23
  obtain ⟨hpos, hle⟩ := smallCoupling_mem hT.le (2 * L)
  refine ⟨hpos, hle, fun lam h0 hl => wp_of_paperForcedWPPred hJ h22 h23 hT.le ?_⟩
  exact paperForcedWP_iff_paperForcedWPPred.mp (paperForcedWP_of_le_smallCoupling
    (crossWitnessEnl D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (hasTerminalRep_enlJoint D h𝒢₀ hind₀ hd hT) hT (jointBorel_iff.mp hJ).1
    (originValues_iff_coeffOrigin.mp h22.origin) h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul hJ.measurable_g_section
    (memLp_iff_forall_coord.mp h22.initial_memLp)
    (stronglyMeasurable_iff_forall_coord.mp h22.initial_meas) h0 hl)

/-- Lemma 4.3. -/
theorem lem_pert : PaperSpec.lem_pert.{u, v, w} := by
  refine ⟨fun T L g c α β₁ β₂ lamLow =>
    aprioriConst T (10 * (2 * L) ^ 2) (4 * (2 * L) ^ 2) g c α β₁ β₂ lamLow, ?_⟩
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ _
  exact PaperWeakSolutionForcedInt.supSize_sub_le h₁ h₂ (crossWitnessEnl D h𝒢₀ hind₀)
    (hF0_enlJoint D h𝒢₀) (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT hlow
    hlam hlam1 h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul
    (inv_nonneg.mpr (sq_nonneg (sMin G))) (fun h => gCoerciveForward_of_rank hG h)
    (fun h => gCoerciveBackward_of_rank hG h) h25.constants h25.diagonalMonotone
    h25.terminalMonotone

/-- Lemma 4.4. -/
theorem lem_cont : PaperSpec.lem_cont.{u, v, w} := by
  refine ⟨fun T L g c α β₁ β₂ lamStar => 1 / (2 * (1 + lipConst T (2 * L)
    * aprioriConst T (10 * (2 * L) ^ 2) (4 * (2 * L) ^ 2) g c α β₁ β₂ lamStar)), ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C ξ₀ hJ h22 h23 hG h25
    lamStar hpos _
  have hK : 0 ≤ lipConst T (2 * L) := lipConst_nonneg T (2 * L)
  have hcG : 0 ≤ (sMin G ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg (sMin G))
  have hCB : 0 ≤ aprioriConst T (10 * (2 * L) ^ 2) (4 * (2 * L) ^ 2) ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁
      β₂ lamStar :=
    (aprioriConst_pos hT.le (by positivity) (by positivity) hcG h25.constants.α_nonneg
      h25.constants.β₁_nonneg h25.constants.β₂_nonneg hpos).le
  refine ⟨(one_div_two_mul_mem hK hCB).1, fun lam0 hl0 hl01 hwp ζ hζ0 hζ _ => ?_⟩
  refine wp_of_paperForcedWPPred hJ h22 h23 hT.le
    ((paperForcedWPPred_of_wp hJ h22 h23 hT.le hwp).add_of_le
    ((jointBorel_iff.mp hJ).1.toCoeffBorel.coeffRegular _ P) (crossWitnessEnl D h𝒢₀ hind₀)
    (hF0_enlJoint D h𝒢₀) (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT hpos
    hl0 hl01 h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul hJ.measurable_g_section hcG
    (fun h => gCoerciveForward_of_rank hG h) (fun h => gCoerciveBackward_of_rank hG h)
    h25.constants h25.diagonalMonotone h25.terminalMonotone ?_)
  exact le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ hζ0 hζ 2) hK) hCB) (sq_one_div_two_mul_le hK hCB)

end MVFBSDEJ.Acceptance
