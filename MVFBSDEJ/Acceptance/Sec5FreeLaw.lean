/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec5FreeLaw
import MVFBSDEJ.Acceptance.Sec2Remarks
import MVFBSDEJ.Acceptance.Sec5Brownian

/-!
# Remark 5.6 of the well-posedness paper: proofs

## Main statements

* `MVFBSDEJ.Acceptance.rem_freelaw` — at almost every `t > 0`, the inputs
  `(0, 0, 0, ±B u₀)`, with `B` a Brownian increment and `Gᵀ u₀ ≠ 0`, have one law and differ only in
  `U`; Remark 2.10's inequality forbids `h` from agreeing at them.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Matrix

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.Law

universe u v w

/-- A nonzero matrix of full rank `min m n ≥ 1` has a transpose that does not vanish on some
vector. -/
theorem exists_GX_transpose_ne_zero {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {G : Matrix (Fin m) (Fin n) ℝ} (hG : G.rank = min m n) :
    ∃ v : EuclideanSpace ℝ (Fin m), GX Gᵀ v ≠ 0 := by
  by_contra! h
  have hT : Gᵀ = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    have := h (WithLp.toLp 2 v)
    rw [GX_toLp] at this
    simpa [Matrix.zero_mulVec] using congrArg (WithLp.ofLp) this
  have h0 : G = 0 := by simpa using congrArg Matrix.transpose hT
  rw [h0, Matrix.rank_zero] at hG
  omega

/-- On a nonzero σ-finite intensity, the operator `Gᵀ` on `L²(ν)` does not vanish on some
element when `Gᵀ` does not vanish on some vector. -/
theorem exists_GU_ne_zero {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
    (hν : ν ≠ 0) {n m : ℕ} {G : Matrix (Fin m) (Fin n) ℝ} {v : EuclideanSpace ℝ (Fin m)}
    (hv : GX Gᵀ v ≠ 0) : ∃ u : Lp (EuclideanSpace ℝ (Fin m)) 2 ν, GU Gᵀ ν u ≠ 0 := by
  obtain ⟨A, hA, hA0, hAt⟩ := exists_measurableSet_pos_lt_top hν
  refine ⟨indicatorConstLp 2 hA hAt.ne v, fun h0 => hv ?_⟩
  have hae : ∀ᵐ e ∂ν, GX Gᵀ (A.indicator (fun _ => v) e) = 0 := by
    filter_upwards [coeFn_GU Gᵀ ν (indicatorConstLp 2 hA hAt.ne v),
      indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hAt.ne) (c := v),
      (Lp.coeFn_zero (EuclideanSpace ℝ (Fin n)) 2 ν)] with e h1 h2 h3
    rw [← h2, ← h1, h0, h3, Pi.zero_apply]
  have hA' : ∀ᵐ e ∂(ν.restrict A), GX Gᵀ v = 0 := by
    rw [ae_restrict_iff' hA]
    filter_upwards [hae] with e he heA
    rwa [Set.indicator_of_mem heA] at he
  haveI : (ae (ν.restrict A)).NeBot := ae_neBot.mpr (by
    rw [Ne, Measure.restrict_eq_zero]
    exact hA0.ne')
  obtain ⟨e, he⟩ := hA'.exists
  exact he

/-- Remark 5.6, the measure argument. -/
theorem rem_freelaw : PaperSpec.rem_freelaw.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT hν G hG α β₁ β₂ C h25 hβ₁
  have hdich := (rem_beta1_dich 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm T hT hν G hG α β₁ β₂ C h25).1
  obtain ⟨v, hv⟩ := exists_GX_transpose_ne_zero hn hm hG
  obtain ⟨u₀, hu₀⟩ := exists_GU_ne_zero hν hv
  have hne0 : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), t ≠ 0 := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simp
  filter_upwards [hdich, ae_restrict_mem measurableSet_Icc, hne0] with t ht htI ht0
  have htpos : 0 < t := lt_of_le_of_ne htI.1 (Ne.symm ht0)
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
  have hB2 : MemLp B 2 P := by
    have h := memLp_id_gaussianReal (μ := 0) (v := ⟨t, htpos.le⟩) 2
    rw [← hlaw] at h
    exact (memLp_map_measure_iff aestronglyMeasurable_id hBmeas.aemeasurable).mp h
  have hneg : P.map (fun ω => -B ω) = P.map B := by
    rw [show (fun ω => -B ω) = (fun x : ℝ => -x) ∘ B from rfl,
      ← Measure.map_map measurable_neg hBmeas, hlaw, gaussianReal_map_neg, neg_zero]
  let L : ℝ →L[ℝ] TupleH ν n m d :=
    (ContinuousLinearMap.inr ℝ _ _).comp ((ContinuousLinearMap.inr ℝ _ _).comp
      ((ContinuousLinearMap.inr ℝ _ _).comp ((ContinuousLinearMap.id ℝ ℝ).smulRight u₀)))
  have hL : ∀ x : ℝ, L x = ((0 : EuclideanSpace ℝ (Fin n)), (0 : EuclideanSpace ℝ (Fin m)),
      (0 : EuclideanSpace ℝ (Fin m × Fin d)), x • u₀) := fun x => rfl
  set Θ : Ω → TupleH ν n m d := fun ω => L (B ω) with hΘdef
  set Θ' : Ω → TupleH ν n m d := fun ω => L (-B ω) with hΘ'def
  have hΘs : StronglyMeasurable[ℱ t] Θ :=
    L.continuous.comp_stronglyMeasurable hBm.stronglyMeasurable
  have hΘ's : StronglyMeasurable[ℱ t] Θ' :=
    L.continuous.comp_stronglyMeasurable hBm.neg.stronglyMeasurable
  have hΘ2 : MemLp Θ 2 P := L.comp_memLp' hB2
  have hΘ'2 : MemLp Θ' 2 P := L.comp_memLp' hB2.neg
  have hLm : Measurable L := L.continuous.measurable
  have hlawEq : lawP2 P Θ = lawP2 P Θ' := by
    refine P2.ext_law ?_
    rw [lawP2_law hΘ2, lawP2_law hΘ'2]
    calc P.map Θ = (P.map B).map L := (Measure.map_map hLm hBmeas).symm
      _ = (P.map (fun ω => -B ω)).map L := by rw [hneg]
      _ = P.map Θ' := Measure.map_map hLm (measurable_neg.comp hBmeas)
  have hmem := mk_mem_diagonalInputs (P := P) hΘs hΘ2
  have hmem' := mk_mem_diagonalInputs (P := P) hΘ's hΘ'2
  refine ⟨(Θ, lawP2 P Θ), hmem, (Θ', lawP2 P Θ'), hmem', hlawEq,
    fun ω => ⟨rfl, rfl, rfl⟩, fun hall => ?_⟩
  have key := ht _ hmem _ hmem' fun ω => ⟨rfl, rfl, rfl⟩
  have hL0 : ∫ ω, (∫ e, inner ℝ (C.h t (Θ ω) (lawP2 P Θ) e - C.h t (Θ' ω) (lawP2 P Θ') e)
      (GX Gᵀ ((Θ ω).2.2.2 e - (Θ' ω).2.2.2 e)) ∂ν) ∂P = 0 := by
    refine (integral_congr_ae ?_).trans (integral_zero Ω ℝ)
    filter_upwards [hall] with ω hω
    simp only [hω, sub_self, inner_zero_left, integral_zero]
  have hdiff : ∀ ω, (Θ ω).2.2.2 - (Θ' ω).2.2.2 = (2 * B ω) • u₀ := by
    intro ω
    simp only [hΘdef, hΘ'def, hL]
    rw [neg_smul, sub_neg_eq_add, ← add_smul, two_mul]
  have hBsq : ∫ ω, B ω ^ 2 ∂P = t := by
    have h := LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment ⟨t, htpos.le⟩
    rw [← hlaw, integral_map hBmeas.aemeasurable (by fun_prop)] at h
    exact h
  have hRHS : ∫ ω, ‖GU Gᵀ ν ((Θ ω).2.2.2 - (Θ' ω).2.2.2)‖ ^ 2 ∂P
      = 4 * t * ‖GU Gᵀ ν u₀‖ ^ 2 := by
    simp_rw [hdiff, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [integral_mul_const]
    simp_rw [mul_pow]
    rw [integral_const_mul, hBsq]
    ring
  rw [hL0, hRHS] at key
  have hpos : 0 < ‖GU Gᵀ ν u₀‖ := norm_pos_iff.mpr hu₀
  have := mul_pos hβ₁ (mul_pos (mul_pos four_pos htpos) (pow_pos hpos 2))
  linarith

end MVFBSDEJ.Acceptance
