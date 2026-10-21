/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Suprema of right-continuous paths over a horizon

A path that is right-continuous on `[0, T)` is determined on `[0, T]` by its values at the
rational times of `[0, T)` and at `T`. Two such paths that agree there agree on `[0, T]`, and the
supremum of the norm over `[0, T]` is the supremum over those countably many times, so it is
measurable for a process whose values are measurable.

## Main statements

* `Dissertation.WellPosedness.Martingale.eq_of_rightCont_of_eq_rat` — agreement on the rationals
  to the right of `t` gives agreement at `t`.
* `Dissertation.WellPosedness.Martingale.biSup_Icc_eq_of_rightCont` — the supremum over `[0, T]`
  as a countable supremum.
* `Dissertation.WellPosedness.Martingale.aemeasurable_biSup_Icc` — its measurability.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace Dissertation.WellPosedness.Martingale

/-- Rational times decreasing to `t` from inside `(t, T)`. -/
theorem exists_seq_rat_tendsto_nhdsGT {t T : ℝ} (htT : t < T) :
    ∃ q : ℕ → ℚ, (∀ n, t < q n ∧ (q n : ℝ) < T)
      ∧ Tendsto (fun n => (q n : ℝ)) atTop (𝓝[>] t) := by
  have hex : ∀ n : ℕ, ∃ q : ℚ, t < q ∧ (q : ℝ) < min T (t + 1 / ((n : ℝ) + 1)) := by
    intro n
    refine exists_rat_btwn (lt_min htT ?_)
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose q hq using hex
  refine ⟨q, fun n => ⟨(hq n).1, (hq n).2.trans_le (min_le_left _ _)⟩, ?_⟩
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => (hq n).1⟩
  have hup : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) atTop (𝓝 t) := by
    have h := (tendsto_const_nhds (x := t)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => (hq n).1.le) (fun n => ?_)
  exact ((hq n).2.trans_le (min_le_right _ _)).le

/-- **Two paths right-continuous at `t` that agree at the rationals of `(t, T)` agree at `t`.** -/
theorem eq_of_rightCont_of_eq_rat {f g : ℝ → ℝ} {t T : ℝ} (htT : t < T)
    (hf : Tendsto f (𝓝[>] t) (𝓝 (f t))) (hg : Tendsto g (𝓝[>] t) (𝓝 (g t)))
    (h : ∀ q : ℚ, t < q → (q : ℝ) < T → f q = g q) : f t = g t := by
  obtain ⟨q, hq, hlim⟩ := exists_seq_rat_tendsto_nhdsGT htT
  have h1 := hf.comp hlim
  have h2 := hg.comp hlim
  have heq : (f ∘ fun n => (q n : ℝ)) = g ∘ fun n => (q n : ℝ) :=
    funext fun n => h (q n) (hq n).1 (hq n).2
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-- **The supremum over `[0, T]` of a path right-continuous on `[0, T)`** is the supremum over the
rational times of `[0, T)` and the time `T`. -/
theorem biSup_Icc_eq_of_rightCont {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ t ∈ Ico 0 T, Tendsto f (𝓝[>] t) (𝓝 (f t))) :
    ⨆ t ∈ Icc 0 T, (‖f t‖₊ : ℝ≥0∞)
      = (⨆ (q : ℚ) (_ : (q : ℝ) ∈ Ico 0 T), (‖f q‖₊ : ℝ≥0∞)) ⊔ (‖f T‖₊ : ℝ≥0∞) := by
  refine le_antisymm (iSup₂_le fun t ht => ?_) (sup_le ?_ ?_)
  · rcases eq_or_lt_of_le ht.2 with htT | htT
    · rw [htT]
      exact le_sup_right
    · obtain ⟨q, hq, hlim⟩ := exists_seq_rat_tendsto_nhdsGT htT
      have hcont : Tendsto (fun n => (‖f (q n)‖₊ : ℝ≥0∞)) atTop (𝓝 (‖f t‖₊ : ℝ≥0∞)) :=
        (ENNReal.continuous_coe.comp continuous_nnnorm).continuousAt.tendsto.comp
          ((hf t ⟨ht.1, htT⟩).comp hlim)
      refine le_of_tendsto' hcont fun n => le_sup_of_le_left ?_
      exact le_iSup₂_of_le (q n) ⟨ht.1.trans (hq n).1.le, (hq n).2⟩ le_rfl
  · exact iSup₂_le fun q hq => le_iSup₂_of_le (q : ℝ) ⟨hq.1, hq.2.le⟩ le_rfl
  · exact le_iSup₂_of_le T ⟨hT, le_rfl⟩ le_rfl

/-- **The supremum over `[0, T]` of a process almost surely right-continuous on `[0, T)`, whose
values are almost everywhere measurable, is almost everywhere measurable.** -/
theorem aemeasurable_biSup_Icc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T) (hM : ∀ t ∈ Icc 0 T, AEMeasurable (M t) P)
    (hr : ∀ᵐ ω ∂P, ∀ t ∈ Ico 0 T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) :
    AEMeasurable (fun ω => ⨆ t ∈ Icc 0 T, (‖M t ω‖₊ : ℝ≥0∞)) P := by
  have hD : AEMeasurable (fun ω => (⨆ (q : ℚ) (_ : (q : ℝ) ∈ Ico 0 T), (‖M q ω‖₊ : ℝ≥0∞))
      ⊔ (‖M T ω‖₊ : ℝ≥0∞)) P := by
    refine AEMeasurable.sup (AEMeasurable.iSup fun q => ?_) ?_
    · by_cases hq : (q : ℝ) ∈ Ico 0 T
      · simp only [hq, ciSup_unique]
        exact (hM q ⟨hq.1, hq.2.le⟩).nnnorm.coe_nnreal_ennreal
      · simp only [hq, iSup_false]
        exact aemeasurable_const
    · exact (hM T ⟨hT, le_rfl⟩).nnnorm.coe_nnreal_ennreal
  refine hD.congr ?_
  filter_upwards [hr] with ω hω
  exact (biSup_Icc_eq_of_rightCont hT hω).symm

/-- **The supremum over `[0, T]` of an extended-real path right-continuous on `[0, T)`** is the
supremum over the rational times of `[0, T)` and the time `T`. -/
theorem biSup_Icc_eq_of_rightCont_ennreal {F : ℝ → ℝ≥0∞} {T : ℝ} (hT : 0 ≤ T)
    (hF : ∀ t ∈ Ico 0 T, Tendsto F (𝓝[>] t) (𝓝 (F t))) :
    ⨆ t ∈ Icc 0 T, F t = (⨆ (q : ℚ) (_ : (q : ℝ) ∈ Ico 0 T), F q) ⊔ F T := by
  refine le_antisymm (iSup₂_le fun t ht => ?_) (sup_le ?_ ?_)
  · rcases eq_or_lt_of_le ht.2 with htT | htT
    · rw [htT]
      exact le_sup_right
    · obtain ⟨q, hq, hlim⟩ := exists_seq_rat_tendsto_nhdsGT htT
      refine le_of_tendsto' ((hF t ⟨ht.1, htT⟩).comp hlim) fun n => le_sup_of_le_left ?_
      exact le_iSup₂_of_le (q n) ⟨ht.1.trans (hq n).1.le, (hq n).2⟩ le_rfl
  · exact iSup₂_le fun q hq => le_iSup₂_of_le (q : ℝ) ⟨hq.1, hq.2.le⟩ le_rfl
  · exact le_iSup₂_of_le T ⟨hT, le_rfl⟩ le_rfl

/-- **The supremum over `[0, T]` of an extended-real process right-continuous on `[0, T)`, whose
values are measurable, is measurable.** -/
theorem measurable_biSup_Icc_ennreal {Ω : Type*} [MeasurableSpace Ω] {F : ℝ → Ω → ℝ≥0∞}
    {T : ℝ} (hT : 0 ≤ T) (hF : ∀ t ∈ Icc 0 T, Measurable (F t))
    (hr : ∀ ω, ∀ t ∈ Ico 0 T, Tendsto (fun s => F s ω) (𝓝[>] t) (𝓝 (F t ω))) :
    Measurable fun ω => ⨆ t ∈ Icc 0 T, F t ω := by
  have hD : Measurable fun ω => (⨆ (q : ℚ) (_ : (q : ℝ) ∈ Ico 0 T), F q ω) ⊔ F T ω := by
    refine Measurable.sup (Measurable.iSup fun q => ?_) (hF T ⟨hT, le_rfl⟩)
    by_cases hq : (q : ℝ) ∈ Ico 0 T
    · simp only [hq, ciSup_unique]
      exact hF q ⟨hq.1, hq.2.le⟩
    · simp only [hq, iSup_false]
      exact measurable_const
  have heq : (fun ω => ⨆ t ∈ Icc 0 T, F t ω)
      = fun ω => (⨆ (q : ℚ) (_ : (q : ℝ) ∈ Ico 0 T), F q ω) ⊔ F T ω :=
    funext fun ω => biSup_Icc_eq_of_rightCont_ennreal hT (hr ω)
  rw [heq]
  exact hD

end Dissertation.WellPosedness.Martingale
