/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Acceptance.A.Sec3Margin
import Dissertation.Acceptance.A.Sec2Remarks
import Dissertation.Topology.NoInjection

/-!
# The paragraph after Corollary 3.6 of the well-posedness paper: continuous functionals

## Main statements

* `Dissertation.Acceptance.A.cor_margin_separate` — finitely many continuous functionals do not
  separate the points of an infinite-dimensional space (`Topology.NoInjection`).
* `Dissertation.Acceptance.A.cor_margin_continuous` — jump feedback through finitely many
  continuous functionals of `u` supplies no margin on an infinite-dimensional `L²(ν)`: two points
  `a ≠ b` with `F_t a = F_t b`, placed according to the sign of a Brownian increment `B` at a time
  `t > 0`, give two inputs with one law that differ only in `U`, along which `δh = 0` while
  `𝔼‖δU‖² = ‖a − b‖² > 0`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Matrix

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness Dissertation.WellPosedness.System
  Dissertation.WellPosedness.Existence Dissertation.WellPosedness.Enlarged
  Dissertation.WellPosedness.Spec Dissertation.Law

universe u v w

/-- The paragraph after Corollary 3.6, the separation fact. -/
theorem cor_margin_separate : PaperSpec.A.cor_margin_separate.{v} := by
  intro H _ _ hH k F hF
  exact Dissertation.Topology.not_injective_of_continuous_of_infinite_dimensional H hH k F hF

/-- The paragraph after Corollary 3.6, finitely many continuous functionals. -/
theorem cor_margin_continuous : PaperSpec.A.cor_margin_continuous.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ _ hd T hT hinf β₁ β₂ c G C k F hβ₁ hc hFc hfac h
  have hM := h.diagonalMonotoneMargin
  have hne0 : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), t ≠ 0 := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simp
  haveI : (ae (volume.restrict (Set.Icc (0 : ℝ) T))).NeBot := by
    refine ae_restrict_neBot.mpr ?_
    rw [Real.volume_Icc, sub_zero]
    exact (ENNReal.ofReal_pos.mpr hT).ne'
  obtain ⟨t, ht, htI, ht0⟩ := (hM.and ((ae_restrict_mem measurableSet_Icc).and hne0)).exists
  have htpos : 0 < t := lt_of_le_of_ne htI.1 (Ne.symm ht0)
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, F t a = F t b ∧ a ≠ b := by
    have hni := Dissertation.Topology.not_injective_of_continuous_of_infinite_dimensional _
      hinf k (F t) (hFc t)
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    exact ⟨a, b, hab, hne⟩
  set ℱ := enlJoint 𝒢₀ D h𝒢₀
  set B : Ω → ℝ := fun ω => (D.W.W ⟨0, hd⟩).W t ω - (D.W.W ⟨0, hd⟩).W 0 ω with hBdef
  have hBm : Measurable[ℱ t] B :=
    (measurable_brownian_enlJoint hd D h𝒢₀ t).sub
      ((measurable_brownian_enlJoint hd D h𝒢₀ 0).mono (ℱ.mono htI.1) le_rfl)
  have hBmeas : Measurable B := hBm.mono (ℱ.le t) le_rfl
  have hlaw : P.map B = gaussianReal 0 ⟨t, htpos.le⟩ := by
    rw [hBdef, (D.W.W ⟨0, hd⟩).increment_gaussian le_rfl htpos]
    congr 1
    exact Subtype.ext (sub_zero t)
  have hneg : P.map (fun ω => -B ω) = P.map B := by
    rw [show (fun ω => -B ω) = (fun x : ℝ => -x) ∘ B from rfl,
      ← Measure.map_map measurable_neg hBmeas, hlaw, gaussianReal_map_neg, neg_zero]
  have hB0 : ∀ᵐ ω ∂P, B ω ≠ 0 := by
    have hv : (⟨t, htpos.le⟩ : NNReal) ≠ 0 := fun h0 => htpos.ne' (congrArg Subtype.val h0)
    haveI := nullSingletonClass_gaussianReal (μ := 0) hv
    have h0 : P.map B {0} = 0 := by rw [hlaw]; exact measure_singleton 0
    rw [Measure.map_apply hBmeas (measurableSet_singleton 0)] at h0
    rw [ae_iff]
    have hset : {ω | ¬B ω ≠ 0} = B ⁻¹' {0} := by ext ω; simp
    rw [hset]
    exact h0
  let θa : TupleH ν n m d := (0, 0, 0, a)
  let θb : TupleH ν n m d := (0, 0, 0, b)
  let φ : ℝ → TupleH ν n m d := fun x => if 0 < x then θa else if x < 0 then θb else θa
  have hφ : Measurable φ :=
    Measurable.ite measurableSet_Ioi measurable_const
      (Measurable.ite measurableSet_Iio measurable_const measurable_const)
  have hφc : ∀ x, (φ x).1 = 0 ∧ (φ x).2.1 = 0 ∧ (φ x).2.2.1 = 0 := by
    intro x
    simp only [φ]
    split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  set Θ : Ω → TupleH ν n m d := fun ω => φ (B ω) with hΘdef
  set Θ' : Ω → TupleH ν n m d := fun ω => φ (-B ω) with hΘ'def
  have hsm : ∀ {f : Ω → ℝ}, Measurable[ℱ t] f → StronglyMeasurable[ℱ t] fun ω => φ (f ω) := by
    intro f hf
    refine stronglyMeasurable_iff_measurable_separable.mpr ⟨hφ.comp hf, ?_⟩
    refine ((Set.finite_range (fun x : Bool => if x then θa else θb)).subset ?_).isSeparable
    rintro _ ⟨ω, rfl⟩
    simp only [φ]
    split_ifs
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  have hΘs : StronglyMeasurable[ℱ t] Θ := hsm hBm
  have hΘ's : StronglyMeasurable[ℱ t] Θ' := hsm hBm.neg
  have hbd : ∀ x, ‖φ x‖ ≤ max ‖θa‖ ‖θb‖ := by
    intro x
    simp only [φ]
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
    · exact le_max_left _ _
  have hΘ2 : MemLp Θ 2 P :=
    MemLp.of_bound (hΘs.mono (ℱ.le t)).aestronglyMeasurable _ (ae_of_all _ fun ω => hbd _)
  have hΘ'2 : MemLp Θ' 2 P :=
    MemLp.of_bound (hΘ's.mono (ℱ.le t)).aestronglyMeasurable _ (ae_of_all _ fun ω => hbd _)
  have hlawEq : lawP2 P Θ = lawP2 P Θ' := by
    refine P2.ext_law ?_
    rw [lawP2_law hΘ2, lawP2_law hΘ'2]
    calc P.map Θ = (P.map B).map φ := (Measure.map_map hφ hBmeas).symm
      _ = (P.map (fun ω => -B ω)).map φ := by rw [hneg]
      _ = P.map Θ' := Measure.map_map hφ (measurable_neg.comp hBmeas)
  have hh : ∀ (μ : P2 (TupleH ν n m d)) (x : ℝ), C.h t (φ x) μ = C.h t (φ (-x)) μ := by
    intro μ x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · have h1 : φ x = θb := by simp [φ, hx, not_lt.mpr hx.le]
      have h2 : φ (-x) = θa := by simp [φ, neg_pos.mpr hx]
      rw [h1, h2]
      exact hfac t θb θa μ rfl rfl rfl hab.symm
    · rw [hx, neg_zero]
    · have h1 : φ x = θa := by simp [φ, hx]
      have h2 : φ (-x) = θb := by simp [φ, not_lt.mpr (neg_nonpos.mpr hx.le), neg_lt_zero.mpr hx]
      rw [h1, h2]
      exact hfac t θa θb μ rfl rfl rfl hab
  have key := ht Θ Θ' hΘs hΘ's hΘ2 hΘ'2
  have hpair : ∀ ω, interiorPairing (GX G) (GZ G) (GU G ν)
      (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) = 0 := by
    intro ω
    obtain ⟨h1, h2, h3⟩ := hφc (B ω)
    obtain ⟨h1', h2', h3'⟩ := hφc (-B ω)
    have hδh : C.h t (Θ ω) (lawP2 P Θ) - C.h t (Θ' ω) (lawP2 P Θ') = 0 := by
      rw [← hlawEq, sub_eq_zero]
      exact hh _ (B ω)
    simp only [interiorPairing, diagDiff, hΘdef, hΘ'def] at hδh ⊢
    rw [h1, h2, h3, h1', h2', h3', hδh]
    simp
  have hdiss : ∀ ω, dissipation (GX G) (GZ G) (GU G ν) β₁ β₂
      (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ≤ 0 := by
    intro ω
    obtain ⟨h1, h2, h3⟩ := hφc (B ω)
    obtain ⟨h1', h2', h3'⟩ := hφc (-B ω)
    simp only [dissipation, diagDiff, hΘdef, hΘ'def]
    rw [h1, h2, h3, h1', h2', h3']
    simp only [sub_self, map_zero, norm_zero]
    nlinarith [mul_nonneg hβ₁ (sq_nonneg ‖ContinuousLinearMap.adjoint (GU G ν)
      ((φ (B ω)).2.2.2 - (φ (-B ω)).2.2.2)‖)]
  have hchan : ∀ᵐ ω ∂P, channelSq (Θ ω - Θ' ω) = ‖a - b‖ ^ 2 := by
    filter_upwards [hB0] with ω hω
    rcases lt_or_gt_of_ne hω with hx | hx
    · have h1 : φ (B ω) = θb := by simp [φ, hx, not_lt.mpr hx.le]
      have h2 : φ (-B ω) = θa := by simp [φ, neg_pos.mpr hx]
      simp only [hΘdef, hΘ'def, h1, h2, channelSq, θa, θb]
      simp [norm_sub_rev]
    · have h1 : φ (B ω) = θa := by simp [φ, hx]
      have h2 : φ (-B ω) = θb := by
        simp [φ, not_lt.mpr (neg_nonpos.mpr hx.le), neg_lt_zero.mpr hx]
      simp only [hΘdef, hΘ'def, h1, h2, channelSq, θa, θb]
      simp
  rw [integral_congr_ae (ae_of_all _ hpair), integral_zero,
    integral_congr_ae hchan, integral_const, probReal_univ, one_smul] at key
  have hd0 := integral_nonpos (μ := P) hdiss
  have hpos : 0 < ‖a - b‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) 2
  nlinarith [mul_pos hc hpos]

end Dissertation.Acceptance.A
