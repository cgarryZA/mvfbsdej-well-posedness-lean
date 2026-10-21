/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Probability.Process.Stopping
import LevyStochCalc.Probability.Progressive

/-!
# The time at which an accumulated energy reaches a level

For a density `a(ω, s) ≥ 0`, the energy `A_t(ω) = ∫_0^t a(ω, s) ds` is nondecreasing and left
continuous in `t`. Its first passage time `σ_δ = inf {t ≥ 0 : A_t ≥ δ}` (`⊤` if there is none) is
a stopping time of a right-continuous filtration for which each `A_t` is `ℱ_t`-measurable, the
energy accumulated up to `σ_δ` is at most `δ`, and `σ_δ ≥ T` whenever `A_T < δ`. For the
quadratic variation of a stochastic integral these are the stopping times of Lenglart's
argument.

## Main definitions

* `Dissertation.WellPosedness.Martingale.energyHit` — the first passage time `σ_δ`.

## Main statements

* `Dissertation.WellPosedness.Martingale.isStoppingTime_energyHit` — `σ_δ` is a stopping time.
* `Dissertation.WellPosedness.Martingale.le_energyHit_of_lt` — `A_T < δ` gives `T ≤ σ_δ`.
* `Dissertation.WellPosedness.Martingale.setLIntegral_ite_energyHit_le` — the energy up to
  `σ_δ ∧ T` is at most `A_T ∧ δ`.
* `Dissertation.WellPosedness.Martingale.measurable_energy_of_progressive`,
  `Dissertation.WellPosedness.Martingale.measurable_markedEnergy_of_progressive` — the energy of
  a (marked) progressively measurable integrand up to `t` is `ℱ_t`-measurable.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace Dissertation.WellPosedness.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The nonnegative times by which the energy `∫_0^t a(ω, s) ds` has reached `δ`. -/
def energyHitSet (a : Ω → ℝ → ℝ≥0∞) (δ : ℝ≥0∞) (ω : Ω) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ δ ≤ ∫⁻ s in Icc 0 t, a ω s}

open scoped Classical in
/-- The first time at which the energy `∫_0^t a(ω, s) ds` reaches `δ`, and `⊤` if it never
does. -/
noncomputable def energyHit (a : Ω → ℝ → ℝ≥0∞) (δ : ℝ≥0∞) (ω : Ω) : WithTop ℝ :=
  if (energyHitSet a δ ω).Nonempty then ((sInf (energyHitSet a δ ω) : ℝ) : WithTop ℝ) else ⊤

variable {a : Ω → ℝ → ℝ≥0∞} {δ : ℝ≥0∞}

theorem bddBelow_energyHitSet (a : Ω → ℝ → ℝ≥0∞) (δ : ℝ≥0∞) (ω : Ω) :
    BddBelow (energyHitSet a δ ω) := ⟨0, fun _ ht => ht.1⟩

/-- The energy is nondecreasing in the horizon. -/
theorem energy_mono (a : Ω → ℝ → ℝ≥0∞) (ω : Ω) {t t' : ℝ} (h : t ≤ t') :
    ∫⁻ s in Icc 0 t, a ω s ≤ ∫⁻ s in Icc 0 t', a ω s :=
  lintegral_mono_set (Icc_subset_Icc_right h)

/-- Strictly before the passage time the energy is below the level. -/
theorem energy_lt_of_lt_energyHit {ω : Ω} {s : ℝ} (hs : 0 ≤ s)
    (h : ((s : ℝ) : WithTop ℝ) < energyHit a δ ω) : ∫⁻ r in Icc 0 s, a ω r < δ := by
  classical
  by_contra hcon
  push Not at hcon
  have hmem : s ∈ energyHitSet a δ ω := ⟨hs, hcon⟩
  have hne : (energyHitSet a δ ω).Nonempty := ⟨s, hmem⟩
  rw [energyHit, if_pos hne] at h
  have hle : sInf (energyHitSet a δ ω) ≤ s := csInf_le (bddBelow_energyHitSet a δ ω) hmem
  exact absurd (WithTop.coe_lt_coe.mp h) (not_lt.mpr hle)

/-- **A horizon whose energy is below the level comes no later than the passage time.** -/
theorem le_energyHit_of_lt {ω : Ω} {T : ℝ} (h : ∫⁻ s in Icc 0 T, a ω s < δ) :
    ((T : ℝ) : WithTop ℝ) ≤ energyHit a δ ω := by
  classical
  rw [energyHit]
  split_ifs with hne
  · refine WithTop.coe_le_coe.mpr (le_csInf hne fun t ht => ?_)
    by_contra htT
    push Not at htT
    exact absurd (ht.2.trans (energy_mono a ω htT.le)) (not_le.mpr h)
  · exact le_top

/-- The energy accumulated up to a finite passage time is at most the level. -/
theorem setLIntegral_Icc_energyHit_le {ω : Ω} {σ : ℝ}
    (hσ : energyHit a δ ω = ((σ : ℝ) : WithTop ℝ)) : ∫⁻ s in Icc 0 σ, a ω s ≤ δ := by
  have hIco : ∫⁻ s in Icc 0 σ, a ω s = ∫⁻ s in Ico 0 σ, a ω s :=
    setLIntegral_congr Ico_ae_eq_Icc.symm
  rw [hIco]
  rcases le_or_gt σ 0 with hσ0 | hσ0
  · rw [Ico_eq_empty (not_lt.mpr hσ0), Measure.restrict_empty, lintegral_zero_measure]
    exact bot_le
  have hU : Ico (0 : ℝ) σ = ⋃ n : ℕ, Icc 0 (σ - 1 / ((n : ℝ) + 1)) := by
    ext s
    simp only [mem_Ico, mem_iUnion, mem_Icc]
    constructor
    · rintro ⟨hs0, hsσ⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hsσ)
      exact ⟨n, hs0, by linarith⟩
    · rintro ⟨n, hs0, hsn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨hs0, by linarith⟩
  have hdir : Directed (· ⊆ ·) fun n : ℕ => Icc (0 : ℝ) (σ - 1 / ((n : ℝ) + 1)) := by
    refine Monotone.directed_le fun n m hnm => Icc_subset_Icc_right ?_
    have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
    linarith
  rw [hU, setLIntegral_iUnion_of_directed _ hdir]
  refine iSup_le fun n => ?_
  set u : ℝ := σ - 1 / ((n : ℝ) + 1) with hu
  rcases lt_or_ge u 0 with hu0 | hu0
  · rw [Icc_eq_empty (not_le.mpr hu0), Measure.restrict_empty, lintegral_zero_measure]
    exact bot_le
  · refine (energy_lt_of_lt_energyHit hu0 ?_).le
    rw [hσ, WithTop.coe_lt_coe, hu]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- **The energy up to the passage time.** On `[0, T]`, the density cut off after `σ_δ` has
energy at most `A_T ∧ δ`. -/
theorem setLIntegral_ite_energyHit_le (ω : Ω) (T : ℝ) :
    ∫⁻ s in Icc 0 T, (if ((s : ℝ) : WithTop ℝ) ≤ energyHit a δ ω then a ω s else 0)
      ≤ min (∫⁻ s in Icc 0 T, a ω s) δ := by
  classical
  refine le_min (lintegral_mono fun s => ?_) ?_
  · split_ifs
    · exact le_rfl
    · exact bot_le
  rcases hσ : energyHit a δ ω with _ | σ
  · -- the energy never reaches the level
    have hne : ¬ (energyHitSet a δ ω).Nonempty := by
      intro hne
      rw [energyHit, if_pos hne] at hσ
      exact WithTop.coe_ne_top hσ
    rcases lt_or_ge T 0 with hT | hT
    · rw [Icc_eq_empty (not_le.mpr hT), Measure.restrict_empty, lintegral_zero_measure]
      exact bot_le
    have hlt : ∫⁻ s in Icc 0 T, a ω s < δ := by
      by_contra hcon
      exact hne ⟨T, hT, not_lt.mp hcon⟩
    refine le_trans (lintegral_mono fun s => ?_) hlt.le
    split_ifs
    · exact le_rfl
    · exact bot_le
  · have hle : ∫⁻ s in Icc 0 T, (if ((s : ℝ) : WithTop ℝ) ≤ ((σ : ℝ) : WithTop ℝ) then a ω s
        else 0) ≤ ∫⁻ s, (Icc 0 σ).indicator (a ω) s := by
      calc ∫⁻ s in Icc 0 T, (if ((s : ℝ) : WithTop ℝ) ≤ ((σ : ℝ) : WithTop ℝ) then a ω s
            else 0)
          ≤ ∫⁻ s in Icc 0 T, (Icc 0 σ).indicator (a ω) s := by
            refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
            split_ifs with h
            · rw [indicator_of_mem (show s ∈ Icc 0 σ from ⟨hs.1, WithTop.coe_le_coe.mp h⟩)]
            · exact bot_le
        _ ≤ ∫⁻ s, (Icc 0 σ).indicator (a ω) s := setLIntegral_le_lintegral _ _
    rw [lintegral_indicator measurableSet_Icc] at hle
    exact hle.trans (setLIntegral_Icc_energyHit_le hσ)

/-- **The passage time is a stopping time** of a right-continuous filtration for which the
energy up to each time `t` is `ℱ_t`-measurable. -/
theorem isStoppingTime_energyHit {ℱ : Filtration ℝ mΩ} [ℱ.IsRightContinuous]
    (ha : ∀ t : ℝ, Measurable[ℱ t] fun ω => ∫⁻ s in Icc 0 t, a ω s) (δ : ℝ≥0∞) :
    IsStoppingTime ℱ (energyHit a δ) := by
  classical
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun i => ?_
  have hset : {ω | energyHit a δ ω < ((i : ℝ) : WithTop ℝ)}
      = ⋃ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) < i), {ω | δ ≤ ∫⁻ s in Icc 0 (q : ℝ), a ω s} := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, exists_prop]
    constructor
    · intro h
      have hne : (energyHitSet a δ ω).Nonempty := by
        by_contra hne
        rw [energyHit, if_neg hne] at h
        exact absurd h (not_lt.mpr le_top)
      rw [energyHit, if_pos hne] at h
      obtain ⟨t, ht, hti⟩ := exists_lt_of_csInf_lt hne (WithTop.coe_lt_coe.mp h)
      obtain ⟨q, htq, hqi⟩ := exists_rat_btwn hti
      exact ⟨q, ⟨ht.1.trans htq.le, hqi⟩, ht.2.trans (energy_mono a ω htq.le)⟩
    · rintro ⟨q, ⟨hq0, hqi⟩, hq⟩
      have hmem : (q : ℝ) ∈ energyHitSet a δ ω := ⟨hq0, hq⟩
      have hne : (energyHitSet a δ ω).Nonempty := ⟨q, hmem⟩
      rw [energyHit, if_pos hne]
      exact WithTop.coe_lt_coe.mpr
        (lt_of_le_of_lt (csInf_le (bddBelow_energyHitSet a δ ω) hmem) hqi)
  rw [hset]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
  exact ℱ.mono hq.2.le _ (measurableSet_le measurable_const (ha q))

/-- **The energy of a progressively measurable integrand up to `t` is `ℱ_t`-measurable.** -/
theorem measurable_energy_of_progressive {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → ℝ}
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H) (t : ℝ) :
    Measurable[ℱ t] fun ω => ∫⁻ s in Icc 0 t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
  letI : MeasurableSpace Ω := ℱ t
  have hF : Measurable fun p : Ω × ℝ =>
      (‖(Iic t).indicator (H p.1) p.2‖₊ : ℝ≥0∞) ^ 2 :=
    (hp t).measurable.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hm := hF.lintegral_prod_right' (ν := volume.restrict (Icc 0 t))
  convert hm using 1
  funext ω
  refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  simp only [indicator_of_mem (mem_Iic.mpr hs.2)]

/-- **The energy of a marked progressively measurable integrand up to `t` is
`ℱ_t`-measurable.** -/
theorem measurable_markedEnergy_of_progressive {E : Type*} [MeasurableSpace E] {ν : Measure E}
    [SFinite ν] {ℱ : Filtration ℝ mΩ} {φ : Ω → ℝ → E → ℝ}
    (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ) (t : ℝ) :
    Measurable[ℱ t] fun ω => ∫⁻ s in Icc 0 t, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
  set G : Ω × ℝ × E → ℝ := fun p => (Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1 with hG
  have hG0 : Measurable[@Prod.instMeasurableSpace Ω (ℝ × E) (ℱ t) inferInstance] G :=
    (hp t).measurable
  clear_value G
  have heq : (fun ω => ∫⁻ s in Icc 0 t, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      = fun ω => ∫⁻ q, (‖G (ω, q)‖₊ : ℝ≥0∞) ^ 2 ∂((volume.restrict (Icc 0 t)).prod ν) := by
    funext ω
    have hω : Measurable fun q : ℝ × E => (‖G (ω, q)‖₊ : ℝ≥0∞) ^ 2 := by
      letI : MeasurableSpace Ω := ℱ t
      exact (hG0.comp (measurable_const.prodMk measurable_id)).nnnorm.coe_nnreal_ennreal.pow_const
        2
    rw [lintegral_prod _ hω.aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    simp only [hG, indicator_of_mem (mem_Iic.mpr hs.2)]
  rw [heq]
  letI : MeasurableSpace Ω := ℱ t
  exact (hG0.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'

end Dissertation.WellPosedness.Martingale
