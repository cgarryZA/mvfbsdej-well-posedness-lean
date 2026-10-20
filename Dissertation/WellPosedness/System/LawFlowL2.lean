/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.FubiniLp
import Dissertation.WellPosedness.System.LawFlow

/-!
# The left-limit tuple in `L²([0, T] × Ω; H)`

Under the hypotheses of Lemma A.1 of the well-posedness paper, the tuple `Θ = (X, Y, Z, U)` and the
left-limit tuple `Θ⁻ = (X₋, Y₋, Z, U)`, read in the tuple space `H` with its Hilbert norm, are
jointly strongly measurable in the time and the sample point and square integrable for
`dt ⊗ dP` on `[0, T] × Ω`: `𝔼 ∫_0^T ‖Θ_t‖²_H dt` is the sum of the energies of the coordinates, and
`Θ⁻ = Θ` `dt ⊗ dP`-almost everywhere. Their sections form a strongly measurable map into
`L²(Ω; H)` (`Dissertation.Law.stronglyMeasurable_secLp`), which represents `t ↦ Θ⁻_t` at almost
every time.

## Main statements

* `CadlagPredTuple.stronglyMeasurable_toL2_tupleAt`, `stronglyMeasurable_toL2_tupleAt_leftLim` —
  joint strong measurability.
* `CadlagPredTuple.memLp_toL2_tupleAt`, `memLp_toL2_tupleAt_leftLim` — square integrability on
  `[0, T] × Ω`.
* `CadlagPredTuple.exists_stronglyMeasurable_lp_leftLim` — a strongly measurable
  `L²(Ω; H)`-valued map equal to `Θ⁻_t` at almost every time.
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.System

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ}

namespace CadlagPredTuple

variable (hΘ : CadlagPredTuple ℱ P ν T X Y Z U)
include hΘ

omit [IsProbabilityMeasure P] in
/-- The tuple `(t, ω) ↦ Θ_t(ω)`, with the Hilbert norm, is jointly strongly measurable. -/
theorem stronglyMeasurable_toL2_tupleAt :
    StronglyMeasurable fun p : ℝ × Ω => toL2 (tupleAt ν X Y Z U p.1 p.2) :=
  continuous_toL2.comp_stronglyMeasurable
    ((measurable_uncurry_tupleAt (ν := ν) hΘ.measurable_X hΘ.measurable_Y hΘ.measurable_Z
      hΘ.measurable_U).comp measurable_swap).stronglyMeasurable

omit [IsProbabilityMeasure P] in
/-- The left-limit tuple `(t, ω) ↦ Θ⁻_t(ω)`, with the Hilbert norm, is jointly strongly
measurable. -/
theorem stronglyMeasurable_toL2_tupleAt_leftLim :
    StronglyMeasurable fun p : ℝ × Ω =>
      toL2 (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U p.1 p.2) :=
  continuous_toL2.comp_stronglyMeasurable
    ((measurable_uncurry_tupleAt (ν := ν)
      (measurable_uncurry_leftLimProc hΘ.measurable_X hΘ.X_leftLim)
      (measurable_uncurry_leftLimProc hΘ.measurable_Y hΘ.Y_leftLim) hΘ.measurable_Z
      hΘ.measurable_U).comp measurable_swap).stronglyMeasurable

/-- **The tuple is square integrable on `[0, T] × Ω`**:
`𝔼 ∫_0^T ‖Θ_t‖²_H dt < ∞`, with the Hilbert norm of `H`. -/
theorem memLp_toL2_tupleAt :
    MemLp (fun p : ℝ × Ω => toL2 (tupleAt ν X Y Z U p.1 p.2)) 2
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) := by
  set μT := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  have hsm := hΘ.stronglyMeasurable_toL2_tupleAt
  refine (memLp_two_iff_integrable_sq_norm hsm.aestronglyMeasurable).mpr
    ⟨(hsm.norm.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p => by positivity)]
  have sq : ∀ {f : ℝ × Ω → ℝ}, Measurable f → Measurable fun p => (‖f p‖₊ : ℝ≥0∞) ^ 2 :=
    fun hf => hf.nnnorm.coe_nnreal_ennreal.pow_const 2
  have mX : ∀ i, Measurable fun p : ℝ × Ω => (‖X i p.1 p.2‖₊ : ℝ≥0∞) ^ 2 := fun i =>
    sq ((hΘ.measurable_X i).comp measurable_swap)
  have mY : ∀ k, Measurable fun p : ℝ × Ω => (‖Y k p.1 p.2‖₊ : ℝ≥0∞) ^ 2 := fun k =>
    sq ((hΘ.measurable_Y k).comp measurable_swap)
  have mZ : ∀ k j, Measurable fun p : ℝ × Ω => (‖Z k p.1 p.2 j‖₊ : ℝ≥0∞) ^ 2 := fun k j =>
    sq ((hΘ.measurable_Z k j).comp measurable_swap)
  have mU : ∀ k, Measurable fun p : ℝ × Ω => ∫⁻ e, (‖U k p.1 p.2 e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
    fun k => (((hΘ.measurable_U k).nnnorm.coe_nnreal_ennreal.pow_const 2).comp (by fun_prop :
      Measurable fun q : (ℝ × Ω) × E => ((q.1.2, q.1.1, q.2) : Ω × ℝ × E))).lintegral_prod_right'
  have mXs : Measurable fun p : ℝ × Ω => ∑ i, (‖X i p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => mX i
  have mYs : Measurable fun p : ℝ × Ω => ∑ k, (‖Y k p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun k _ => mY k
  have mZs : Measurable fun p : ℝ × Ω => ∑ k, ∑ j, (‖Z k p.1 p.2 j‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun j _ => mZ k j
  have m2 : Measurable fun p : ℝ × Ω => ∑ i, (‖X i p.1 p.2‖₊ : ℝ≥0∞) ^ 2
      + ∑ k, (‖Y k p.1 p.2‖₊ : ℝ≥0∞) ^ 2 := mXs.add mYs
  have m3 : Measurable fun p : ℝ × Ω => ∑ i, (‖X i p.1 p.2‖₊ : ℝ≥0∞) ^ 2
      + ∑ k, (‖Y k p.1 p.2‖₊ : ℝ≥0∞) ^ 2 + ∑ k, ∑ j, (‖Z k p.1 p.2 j‖₊ : ℝ≥0∞) ^ 2 :=
    m2.add mZs
  have swapE : ∀ {f : ℝ × Ω → ℝ≥0∞}, Measurable f →
      ∫⁻ p, f p ∂(μT.prod P) = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, f (s, ω) ∂volume ∂P :=
    fun hf => lintegral_prod_symm _ hf.aemeasurable
  calc ∫⁻ p, ENNReal.ofReal (‖toL2 (tupleAt ν X Y Z U p.1 p.2)‖ ^ 2) ∂(μT.prod P)
      ≤ ∫⁻ p, (∑ i, (‖X i p.1 p.2‖₊ : ℝ≥0∞) ^ 2 + ∑ k, (‖Y k p.1 p.2‖₊ : ℝ≥0∞) ^ 2
          + ∑ k, ∑ j, (‖Z k p.1 p.2 j‖₊ : ℝ≥0∞) ^ 2
          + ∑ k, ∫⁻ e, (‖U k p.1 p.2 e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂(μT.prod P) :=
        lintegral_mono fun p => by
          rw [norm_toL2_sq]
          exact ofReal_channelSq_tupleAt_le p.1 p.2
    _ = (∑ i, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => X i s ω)
          + ∑ k, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Y k s ω))
          + ∑ k, ∑ j, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z k s ω j)
          + ∑ k, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
              (fun ω s e => U k s ω e) := by
        rw [lintegral_add_left m3, lintegral_add_left m2,
          lintegral_add_left mXs, lintegral_finsetSum _ fun i _ => mX i,
          lintegral_finsetSum _ fun k _ => mY k,
          lintegral_finsetSum _ fun k _ => Finset.measurable_sum _ fun j _ => mZ k j,
          lintegral_finsetSum _ fun k _ => mU k]
        congr 1
        · congr 1
          · congr 1
            · exact Finset.sum_congr rfl fun i _ => swapE (mX i)
            · exact Finset.sum_congr rfl fun k _ => swapE (mY k)
          · refine Finset.sum_congr rfl fun k _ => ?_
            rw [lintegral_finsetSum _ fun j _ => mZ k j]
            exact Finset.sum_congr rfl fun j _ => swapE (mZ k j)
        · exact Finset.sum_congr rfl fun k _ => swapE (mU k)
    _ < ⊤ := by
        refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
          ⟨ENNReal.sum_lt_top.mpr fun i _ => (hΘ.X_sq i).lt_top,
            ENNReal.sum_lt_top.mpr fun k _ => (hΘ.Y_sq k).lt_top⟩,
          ENNReal.sum_lt_top.mpr fun k _ => ENNReal.sum_lt_top.mpr fun j _ =>
            (hΘ.Z_sq k j).lt_top⟩, ENNReal.sum_lt_top.mpr fun k _ => (hΘ.U_sq k).lt_top⟩

/-- **The left-limit tuple agrees with the tuple `dt ⊗ dP`-almost everywhere** on
`[0, T] × Ω`. -/
theorem ae_toL2_tupleAt_leftLim_eq :
    ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P),
      toL2 (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U p.1 p.2)
        = toL2 (tupleAt ν X Y Z U p.1 p.2) := by
  rw [Measure.ae_prod_iff_ae_ae (hΘ.stronglyMeasurable_toL2_tupleAt_leftLim.measurableSet_eq_fun
    hΘ.stronglyMeasurable_toL2_tupleAt)]
  filter_upwards [ae_restrict_of_ae (ae_ae_tupleAt_leftLimProc_eq (Z := Z) (U := U) (ν := ν)
    (P := P) hΘ.measurable_X hΘ.measurable_Y hΘ.X_rightCont hΘ.X_leftLim hΘ.Y_rightCont
    hΘ.Y_leftLim)] with s hs
  filter_upwards [hs] with ω hω
  rw [hω]

/-- **The left-limit tuple is square integrable on `[0, T] × Ω`**:
`𝔼 ∫_0^T ‖Θ⁻_t‖²_H dt < ∞`, with the Hilbert norm of `H`. -/
theorem memLp_toL2_tupleAt_leftLim :
    MemLp (fun p : ℝ × Ω => toL2 (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U p.1 p.2)) 2
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) :=
  (memLp_congr_ae hΘ.ae_toL2_tupleAt_leftLim_eq).mpr hΘ.memLp_toL2_tupleAt

/-- **A strongly measurable version of `t ↦ Θ⁻_t ∈ L²(Ω; H)`**: the section map of the left-limit
tuple is strongly measurable into `L²(Ω; H)` and is the class of `Θ⁻_t` at almost every
`t ∈ [0, T]`. -/
theorem exists_stronglyMeasurable_lp_leftLim :
    ∃ F : ℝ → Lp (TupleL2 (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)) 2 P,
      StronglyMeasurable F ∧ ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        ∃ h : MemLp (fun ω => toL2 (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U t ω)) 2 P,
          F t = h.toLp _ := by
  have hg := hΘ.stronglyMeasurable_toL2_tupleAt_leftLim
  have hfin : ∫⁻ p, ‖toL2 (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U p.1 p.2)‖ₑ ^ (2 : ℝ)
      ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) < ⊤ := by
    rw [← eLpNorm_two_rpow]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hΘ.memLp_toL2_tupleAt_leftLim.2.ne
  refine ⟨secLp P hg, stronglyMeasurable_secLp hg, ?_⟩
  filter_upwards [ae_mem_goodSet hg hfin] with t ht
  have hm : MemLp (fun ω => toL2 (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U t ω)) 2 P := by
    have h := memLp_cutSec (ν := P) hg t
    simp only [cutSec_apply_of_mem ht] at h
    exact h
  exact ⟨hm, MemLp.toLp_congr _ _ (Eventually.of_forall fun ω => cutSec_apply_of_mem ht ω)⟩

end CadlagPredTuple

end Dissertation.WellPosedness.System
