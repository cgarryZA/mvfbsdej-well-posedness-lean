/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.Tuple
import MVFBSDEJ.Law.LawP2
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# The tuple of coordinate processes as a random element of `H`

The diagonal inputs of the well-posedness paper are pairs `(Θ, Law Θ)` with
`Θ ∈ L²(Ω, ℱ_t; H)`. For the tuple `Θ_s = tupleAt ν X Y Z U s` of the coordinate processes of a
solution, the squared norm is at most the sum of the squares of the coordinates, the jump channel
contributing `∑_k ∫_E U_{k,s}(e)² ν(de)`. So `Θ_s` is square integrable at every time at which it
is almost everywhere strongly measurable and the coordinates have finite second moments, and at
almost every time of `[0, T]` when the coordinates are jointly measurable with finite energy on
`[0, T]`, by Tonelli's theorem. For two such tuples the coupling bound (2.8) reads

`W₂(Law Θ_s, Law Θ'_s)² ≤ 𝔼 (|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²_{L²(ν)})`,

the right-hand side written through the coordinates of the differences.

## Main statements

* `memLp_tupleAt` — square integrability at a time.
* `ae_lintegral_lt_top` — finite energy gives finite second moments at almost every time.
* `ae_memLp_tupleAt` — square integrability at almost every time.
* `ofReal_w2P_lawP2_tupleAt_sq_le` — the coupling bound (2.8) for two tuples.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ν : Measure E} {n m d : ℕ} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}

/-- **The tuple is square integrable at a time** at which it is almost everywhere strongly
measurable and its coordinates have finite second moments. -/
theorem memLp_tupleAt {s : ℝ} (hm : AEStronglyMeasurable (tupleAt ν X Y Z U s) P)
    (hfin : ∫⁻ ω, (∑ i, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ k, (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2
        + ∑ k, ∑ j, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2
        + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P < ⊤) :
    MemLp (tupleAt ν X Y Z U s) 2 P := by
  refine (memLp_two_iff_integrable_sq_norm hm).mpr ⟨(hm.norm.pow 2), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => by positivity)]
  exact lt_of_le_of_lt (lintegral_mono fun ω => (ENNReal.ofReal_le_ofReal
    (norm_sq_le_channelSq _)).trans (ofReal_channelSq_tupleAt_le s ω)) hfin

omit [MeasurableSpace E] in
/-- A jointly measurable function of the sample point and time with finite integral over
`Ω × [0, T]` has finite expectation at almost every time of `[0, T]`. -/
theorem ae_lintegral_lt_top [SFinite P] {φ : Ω → ℝ → ℝ≥0∞}
    (hφ : Measurable (Function.uncurry φ)) {T : ℝ}
    (h : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, φ ω s ∂volume ∂P ≠ ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∫⁻ ω, φ ω s ∂P < ⊤ := by
  refine ae_lt_top hφ.lintegral_prod_left' ?_
  rwa [← lintegral_lintegral_swap hφ.aemeasurable]

/-- **The tuple is square integrable at almost every time** of `[0, T]` when it is almost
everywhere strongly measurable at each time of `[0, T]` and its coordinates are jointly
measurable with finite energy on `[0, T]`. -/
theorem ae_memLp_tupleAt [SFinite P] [SFinite ν] {T : ℝ}
    (hm : ∀ s ∈ Set.Icc (0 : ℝ) T, AEStronglyMeasurable (tupleAt ν X Y Z U s) P)
    (hX : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω))
    (hY : ∀ k, Measurable (Function.uncurry fun ω s => Y k s ω))
    (hZ : ∀ k j, Measurable (Function.uncurry fun ω s => Z k s ω j))
    (hU : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2)
    (hXe : ∀ i, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤)
    (hYe : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤)
    (hZe : ∀ k j, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤)
    (hUe : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      ≠ ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (tupleAt ν X Y Z U s) 2 P := by
  have sq : ∀ {f : Ω × ℝ → ℝ}, Measurable f → Measurable fun p => (‖f p‖₊ : ℝ≥0∞) ^ 2 :=
    fun hf => hf.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hUm : ∀ k, Measurable (Function.uncurry fun ω s =>
      ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) := fun k =>
    (((hU k).nnnorm.coe_nnreal_ennreal.pow_const 2).comp (by fun_prop :
      Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))).lintegral_prod_right'
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_all_iff.mpr fun i => ae_lintegral_lt_top (φ := fun ω s => (‖X i s ω‖₊ : ℝ≥0∞) ^ 2)
      (sq (hX i)) (hXe i),
    ae_all_iff.mpr fun k => ae_lintegral_lt_top (φ := fun ω s => (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2)
      (sq (hY k)) (hYe k),
    ae_all_iff.mpr fun k => ae_all_iff.mpr fun j =>
      ae_lintegral_lt_top (φ := fun ω s => (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2) (sq (hZ k j)) (hZe k j),
    ae_all_iff.mpr fun k => ae_lintegral_lt_top (hUm k) (hUe k)] with s hs hXs hYs hZs hUs
  refine memLp_tupleAt (hm s hs) ?_
  have mXi : ∀ i, Measurable fun ω => (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 := fun i =>
    (sq (hX i)).comp (measurable_id.prodMk measurable_const)
  have mYk : ∀ k, Measurable fun ω => (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2 := fun k =>
    (sq (hY k)).comp (measurable_id.prodMk measurable_const)
  have mZkj : ∀ k j, Measurable fun ω => (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 := fun k j =>
    (sq (hZ k j)).comp (measurable_id.prodMk measurable_const)
  have mX : Measurable fun ω => ∑ i, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => mXi i
  have mY : Measurable fun ω => ∑ k, (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun k _ => mYk k
  have mZ : ∀ k, Measurable fun ω => ∑ j, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 := fun k =>
    Finset.measurable_sum _ fun j _ => mZkj k j
  have mU : ∀ k, Measurable fun ω => ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := fun k =>
    (hUm k).comp (measurable_id.prodMk measurable_const)
  have eX : ∫⁻ ω, ∑ i, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
    rw [lintegral_finsetSum _ fun i _ => mXi i]
    exact ENNReal.sum_lt_top.mpr fun i _ => hXs i
  have eY : ∫⁻ ω, ∑ k, (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
    rw [lintegral_finsetSum _ fun k _ => mYk k]
    exact ENNReal.sum_lt_top.mpr fun k _ => hYs k
  have eZ : ∫⁻ ω, ∑ k, ∑ j, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
    rw [lintegral_finsetSum _ fun k _ => mZ k]
    refine ENNReal.sum_lt_top.mpr fun k _ => ?_
    rw [lintegral_finsetSum _ fun j _ => mZkj k j]
    exact ENNReal.sum_lt_top.mpr fun j _ => hZs k j
  have eU : ∫⁻ ω, ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P < ⊤ := by
    rw [lintegral_finsetSum _ fun k _ => mU k]
    exact ENNReal.sum_lt_top.mpr fun k _ => hUs k
  have m2 : Measurable fun ω => ∑ i, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ k, (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2 :=
    mX.add mY
  have m3 : Measurable fun ω => ∑ i, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ k, (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2
      + ∑ k, ∑ j, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 :=
    m2.add (Finset.measurable_sum _ fun k _ => mZ k)
  rw [lintegral_add_left m3, lintegral_add_left m2, lintegral_add_left mX]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨eX, eY⟩, eZ⟩, eU⟩

/-- **The coupling bound (2.8) for two tuples.** For a σ-finite `ν` on a countably generated mark
space, if the tuples `Θ_s` and `Θ'_s` are square integrable and almost surely their jump channels
are, then `W₂(Law Θ_s, Law Θ'_s)²` is at most the expected sum of the squares of the coordinate
differences. -/
theorem ofReal_w2P_lawP2_tupleAt_sq_le [IsProbabilityMeasure P] [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] {X' : Fin n → ℝ → Ω → ℝ} {Y' : Fin m → ℝ → Ω → ℝ}
    {Z' : Fin m → ℝ → Ω → Fin d → ℝ} {U' : Fin m → ℝ → Ω → E → ℝ} {s : ℝ}
    (h : MemLp (tupleAt ν X Y Z U s) 2 P) (h' : MemLp (tupleAt ν X' Y' Z' U' s) 2 P)
    (hU : ∀ᵐ ω ∂P, ∀ k, MemLp (fun e => U k s ω e) 2 ν)
    (hU' : ∀ᵐ ω ∂P, ∀ k, MemLp (fun e => U' k s ω e) 2 ν) :
    ENNReal.ofReal (w2P (lawP2 P (tupleAt ν X Y Z U s)) (lawP2 P (tupleAt ν X' Y' Z' U' s)) ^ 2)
      ≤ ∫⁻ ω, (∑ i, (‖X i s ω - X' i s ω‖₊ : ℝ≥0∞) ^ 2
        + ∑ k, (‖Y k s ω - Y' k s ω‖₊ : ℝ≥0∞) ^ 2
        + ∑ k, ∑ j, (‖Z k s ω j - Z' k s ω j‖₊ : ℝ≥0∞) ^ 2
        + ∑ k, ∫⁻ e, (‖U k s ω e - U' k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P := by
  refine (ofReal_w2P_lawP2_sq_le h h').trans (lintegral_mono_ae ?_)
  filter_upwards [hU, hU'] with ω h1 h2
  exact ofReal_norm_tupleAt_sub_sq_le h1 h2

end MVFBSDEJ.WellPosedness.System
