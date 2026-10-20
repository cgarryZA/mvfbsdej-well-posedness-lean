/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.Convex.StdSimplex
import MVFBSDEJ.Law.P2Metric

/-!
# Reweighting a finitely supported law

For finitely many atoms `x : ι → E` and a weight vector `w` of the standard simplex, `finLaw x w`
is the law `∑ᵢ wᵢ δ_{xᵢ}`. A nonnegative matrix `c` with row sums `w` and column sums `w'` gives
the coupling `∑ᵢⱼ cᵢⱼ δ_{(xᵢ, xⱼ)}` of `finLaw x w` and `finLaw x w'`, of quadratic cost
`∑ᵢⱼ cᵢⱼ ‖xᵢ − xⱼ‖²`. The maximal coupling keeps the common mass `min(wᵢ, w'ᵢ)` on the diagonal
and spreads the excess `aᵢ = wᵢ − min(wᵢ, w'ᵢ)` over the deficit `bⱼ = w'ⱼ − min(wⱼ, w'ⱼ)` in
proportion, `cᵢⱼ = min(wᵢ, w'ᵢ) 1_{i = j} + aᵢ bⱼ / m` with `m = ∑ᵢ aᵢ = ∑ⱼ bⱼ`. Only the
spread mass moves, by at most `D = maxᵢⱼ ‖xᵢ − xⱼ‖`, so

`W₂(∑ᵢ wᵢ δ_{xᵢ}, ∑ᵢ w'ᵢ δ_{xᵢ})² ≤ D² m ≤ D² ∑ᵢ |wᵢ − w'ᵢ|`,

and the map `w ↦ finLaw x w` from the standard simplex into the 2-Wasserstein space is
continuous.

## Main definitions

* `MVFBSDEJ.Law.finLaw`: the finitely supported law `∑ᵢ wᵢ δ_{xᵢ}`.
* `MVFBSDEJ.Law.matCoupling`: the measure `∑ᵢⱼ cᵢⱼ δ_{(xᵢ, xⱼ)}` of a matrix.
* `MVFBSDEJ.Law.maxCouplingMat`: the maximal coupling matrix of two weight vectors.

## Main statements

* `MVFBSDEJ.Law.isCoupling_matCoupling`: a nonnegative matrix with row sums `w` and column
  sums `w'` gives a coupling of `finLaw x w` and `finLaw x w'`.
* `MVFBSDEJ.Law.transportCostSq_matCoupling`: its quadratic cost.
* `MVFBSDEJ.Law.w2P_finLaw_sq_le`: the reweighting bound
  `W₂(finLaw x w, finLaw x w')² ≤ D² ∑ᵢ |wᵢ − w'ᵢ|`.
* `MVFBSDEJ.Law.continuous_finLaw`: `w ↦ finLaw x w` is continuous into the 2-Wasserstein
  space.
-/

namespace MVFBSDEJ.Law

open MeasureTheory Filter Topology
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {ι : Type*} [Fintype ι]

/-! ### Finitely supported laws and their matrix couplings -/

section Matrix

/-- The finitely supported law `∑ᵢ wᵢ δ_{xᵢ}` with atoms `x` and weights `w` in the standard
simplex. -/
noncomputable def finLaw (x : ι → E) (w : stdSimplex ℝ ι) : P2 E where
  law := ∑ i, ENNReal.ofReal (w.1 i) • Measure.dirac (x i)
  isProbabilityMeasure := ⟨by
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => w.2.1 i), w.2.2, ENNReal.ofReal_one]⟩
  secondMoment_ne_top := by
    rw [secondMoment, lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac' _ (by fun_prop : Measurable
      fun y : E => ENNReal.ofReal (‖y‖ ^ 2)), smul_eq_mul]
    exact ENNReal.sum_ne_top.mpr fun i _ =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- The underlying measure of `finLaw x w` is `∑ᵢ wᵢ δ_{xᵢ}`. -/
theorem finLaw_law (x : ι → E) (w : stdSimplex ℝ ι) :
    (finLaw x w).law = ∑ i, ENNReal.ofReal (w.1 i) • Measure.dirac (x i) :=
  rfl

/-- The measure `∑ᵢⱼ cᵢⱼ δ_{(xᵢ, xⱼ)}` on `E × E` of a matrix `c`. -/
noncomputable def matCoupling (x : ι → E) (c : ι → ι → ℝ) : Measure (E × E) :=
  ∑ i, ∑ j, ENNReal.ofReal (c i j) • Measure.dirac (x i, x j)

/-- **A matrix coupling**: a nonnegative matrix with row sums `w` and column sums `w'` gives a
coupling of `finLaw x w` and `finLaw x w'`. -/
theorem isCoupling_matCoupling (x : ι → E) {w w' : stdSimplex ℝ ι} {c : ι → ι → ℝ}
    (hc : ∀ i j, 0 ≤ c i j) (hrow : ∀ i, ∑ j, c i j = w.1 i)
    (hcol : ∀ j, ∑ i, c i j = w'.1 j) :
    IsCoupling (finLaw x w).law (finLaw x w').law (matCoupling x c) := by
  classical
  constructor
  · ext A hA
    rw [Measure.fst_apply hA, matCoupling, finLaw_law, Measure.finsetSum_apply,
      Measure.finsetSum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurable_fst hA),
      Measure.dirac_apply' _ hA, Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hc i j), hrow i]
  · ext A hA
    rw [Measure.snd_apply hA, matCoupling, finLaw_law, Measure.finsetSum_apply,
      Measure.finsetSum_apply]
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurable_snd hA), Measure.dirac_apply' _ hA,
      Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hc i j), hcol j]

/-- **The quadratic cost of a matrix coupling** is `∑ᵢⱼ cᵢⱼ ‖xᵢ − xⱼ‖²`. -/
theorem transportCostSq_matCoupling (x : ι → E) {c : ι → ι → ℝ} (hc : ∀ i j, 0 ≤ c i j) :
    transportCostSq (matCoupling x c) = ENNReal.ofReal (∑ i, ∑ j, c i j * ‖x i - x j‖ ^ 2) := by
  rw [transportCostSq, matCoupling, lintegral_finsetSum_measure,
    ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hc i j) (sq_nonneg _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_finsetSum_measure,
    ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (hc i j) (sq_nonneg _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ measurable_normSq_sub, smul_eq_mul,
    ENNReal.ofReal_mul (hc i j)]

end Matrix

/-! ### The maximal coupling -/

section Maximal

/-- The maximal coupling matrix of two weight vectors: the common mass `min(wᵢ, w'ᵢ)` on the
diagonal, and the excess `aᵢ = wᵢ − min(wᵢ, w'ᵢ)` spread over the deficit
`bⱼ = w'ⱼ − min(wⱼ, w'ⱼ)` in proportion, `aᵢ bⱼ / ∑ₖ aₖ`. -/
noncomputable def maxCouplingMat [DecidableEq ι] (w w' : ι → ℝ) (i j : ι) : ℝ :=
  (if i = j then min (w i) (w' i) else 0)
    + (w i - min (w i) (w' i)) * (w' j - min (w j) (w' j)) / ∑ k, (w k - min (w k) (w' k))

variable {w w' : stdSimplex ℝ ι}

/-- The total excess of `w` over `w'` equals the total deficit. -/
theorem sum_excess_eq_sum_deficit (w w' : stdSimplex ℝ ι) :
    ∑ k, (w.1 k - min (w.1 k) (w'.1 k)) = ∑ k, (w'.1 k - min (w.1 k) (w'.1 k)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, w.2.2, w'.2.2]

/-- If the total excess vanishes, so does every excess. -/
theorem excess_eq_zero_of_sum (w w' : stdSimplex ℝ ι)
    (h : ∑ k, (w.1 k - min (w.1 k) (w'.1 k)) = 0) (i : ι) :
    w.1 i - min (w.1 i) (w'.1 i) = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sub_nonneg.mpr (min_le_left _ _)).mp h i
    (Finset.mem_univ i)

/-- The entries of the maximal coupling matrix are nonnegative. -/
theorem maxCouplingMat_nonneg [DecidableEq ι] (i j : ι) : 0 ≤ maxCouplingMat w.1 w'.1 i j := by
  have ha : ∀ k, 0 ≤ w.1 k - min (w.1 k) (w'.1 k) := fun k => sub_nonneg.mpr (min_le_left _ _)
  have hb : ∀ k, 0 ≤ w'.1 k - min (w.1 k) (w'.1 k) := fun k =>
    sub_nonneg.mpr (min_le_right _ _)
  have hmin : 0 ≤ min (w.1 i) (w'.1 i) := le_min (w.2.1 i) (w'.2.1 i)
  unfold maxCouplingMat
  refine add_nonneg (by split_ifs <;> simp [hmin]) (div_nonneg (mul_nonneg (ha i) (hb j))
    (Finset.sum_nonneg fun k _ => ha k))

/-- The row sums of the maximal coupling matrix are `w`. -/
theorem sum_maxCouplingMat_row [DecidableEq ι] (i : ι) :
    ∑ j, maxCouplingMat w.1 w'.1 i j = w.1 i := by
  set m := ∑ k, (w.1 k - min (w.1 k) (w'.1 k)) with hm
  have hsum : ∑ j, (w.1 i - min (w.1 i) (w'.1 i)) * (w'.1 j - min (w.1 j) (w'.1 j)) / m
      = w.1 i - min (w.1 i) (w'.1 i) := by
    rw [← Finset.sum_div, ← Finset.mul_sum, ← sum_excess_eq_sum_deficit, ← hm]
    by_cases h0 : m = 0
    · rw [excess_eq_zero_of_sum w w' h0 i]
      simp
    · field_simp
  unfold maxCouplingMat
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ i), ← hm, hsum]
  ring

/-- The column sums of the maximal coupling matrix are `w'`. -/
theorem sum_maxCouplingMat_col [DecidableEq ι] (j : ι) :
    ∑ i, maxCouplingMat w.1 w'.1 i j = w'.1 j := by
  set m := ∑ k, (w.1 k - min (w.1 k) (w'.1 k)) with hm
  have hsum : ∑ i, (w.1 i - min (w.1 i) (w'.1 i)) * (w'.1 j - min (w.1 j) (w'.1 j)) / m
      = w'.1 j - min (w.1 j) (w'.1 j) := by
    rw [← Finset.sum_div, ← Finset.sum_mul, ← hm]
    by_cases h0 : m = 0
    · have hb : w'.1 j - min (w.1 j) (w'.1 j) = 0 := by
        have h' : ∑ k, (w'.1 k - min (w.1 k) (w'.1 k)) = 0 := by
          rw [← sum_excess_eq_sum_deficit]
          exact h0
        exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
          sub_nonneg.mpr (min_le_right _ _)).mp h' j (Finset.mem_univ j)
      rw [hb]
      simp
    · field_simp
  unfold maxCouplingMat
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ j), ← hm, hsum]
  ring

/-- **The reweighting bound**: for atoms at mutual distances at most `D`,
`W₂(∑ᵢ wᵢ δ_{xᵢ}, ∑ᵢ w'ᵢ δ_{xᵢ})² ≤ D² ∑ᵢ |wᵢ − w'ᵢ|`. -/
theorem w2P_finLaw_sq_le (x : ι → E) (w w' : stdSimplex ℝ ι) {D : ℝ}
    (hD : ∀ i j, ‖x i - x j‖ ≤ D) :
    w2P (finLaw x w) (finLaw x w') ^ 2 ≤ D ^ 2 * ∑ i, |w.1 i - w'.1 i| := by
  classical
  set c := maxCouplingMat w.1 w'.1 with hc_def
  set m := ∑ k, (w.1 k - min (w.1 k) (w'.1 k)) with hm
  have hc : ∀ i j, 0 ≤ c i j := maxCouplingMat_nonneg
  have ha : ∀ k, 0 ≤ w.1 k - min (w.1 k) (w'.1 k) := fun k => sub_nonneg.mpr (min_le_left _ _)
  have hb : ∀ k, 0 ≤ w'.1 k - min (w.1 k) (w'.1 k) := fun k =>
    sub_nonneg.mpr (min_le_right _ _)
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun k _ => ha k
  -- the cost of the maximal coupling
  have hcost : ∑ i, ∑ j, c i j * ‖x i - x j‖ ^ 2 ≤ D ^ 2 * m := by
    have hterm : ∀ i j, c i j * ‖x i - x j‖ ^ 2
        ≤ (w.1 i - min (w.1 i) (w'.1 i)) * (w'.1 j - min (w.1 j) (w'.1 j)) / m * D ^ 2 := by
      intro i j
      have hq : 0 ≤ (w.1 i - min (w.1 i) (w'.1 i)) * (w'.1 j - min (w.1 j) (w'.1 j)) / m :=
        div_nonneg (mul_nonneg (ha i) (hb j)) hm0
      have hsq : ‖x i - x j‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hD i j) 2
      rw [hc_def, maxCouplingMat, add_mul]
      by_cases hij : i = j
      · subst hij
        simp only [if_pos rfl, sub_self, norm_zero]
        rw [← hm]
        nlinarith [sq_nonneg D]
      · rw [if_neg hij, zero_mul, zero_add, ← hm]
        exact mul_le_mul_of_nonneg_left hsq hq
    calc ∑ i, ∑ j, c i j * ‖x i - x j‖ ^ 2
        ≤ ∑ i, ∑ j, (w.1 i - min (w.1 i) (w'.1 i)) * (w'.1 j - min (w.1 j) (w'.1 j)) / m
            * D ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = (∑ i, (w.1 i - min (w.1 i) (w'.1 i))) * (∑ j, (w'.1 j - min (w.1 j) (w'.1 j))) / m
            * D ^ 2 := by
          rw [Finset.sum_mul_sum, Finset.sum_div, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_div, Finset.sum_mul]
      _ = D ^ 2 * (m * m / m) := by
          rw [← sum_excess_eq_sum_deficit w w', ← hm]
          ring
      _ ≤ D ^ 2 * m := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg D)
          by_cases h0 : m = 0
          · simp [h0]
          · rw [mul_div_assoc, div_self h0, mul_one]
  have hmle : m ≤ ∑ i, |w.1 i - w'.1 i| := by
    refine Finset.sum_le_sum fun i _ => ?_
    rcases le_total (w.1 i) (w'.1 i) with h | h
    · rw [min_eq_left h, sub_self]
      exact abs_nonneg _
    · rw [min_eq_right h]
      exact le_abs_self _
  have hS : 0 ≤ ∑ i, ∑ j, c i j * ‖x i - x j‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hc i j) (sq_nonneg _)
  have hw2 : w2sq (finLaw x w).law (finLaw x w').law
      ≤ ENNReal.ofReal (∑ i, ∑ j, c i j * ‖x i - x j‖ ^ 2) := by
    rw [← transportCostSq_matCoupling x hc]
    exact w2sq_le_transportCostSq
      (isCoupling_matCoupling x hc sum_maxCouplingMat_row sum_maxCouplingMat_col)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hw2
  rw [ENNReal.toReal_ofReal hS] at hreal
  rw [w2P, w2, Real.sq_sqrt ENNReal.toReal_nonneg]
  calc (w2sq (finLaw x w).law (finLaw x w').law).toReal
      ≤ ∑ i, ∑ j, c i j * ‖x i - x j‖ ^ 2 := hreal
    _ ≤ D ^ 2 * m := hcost
    _ ≤ D ^ 2 * ∑ i, |w.1 i - w'.1 i| := mul_le_mul_of_nonneg_left hmle (sq_nonneg D)

/-- **Reweighting is continuous**: for fixed atoms, `w ↦ ∑ᵢ wᵢ δ_{xᵢ}` is continuous from the
standard simplex into the 2-Wasserstein space. -/
theorem continuous_finLaw [CompleteSpace E] (x : ι → E) :
    Continuous fun w : stdSimplex ℝ ι => (finLaw x w).toP2W := by
  set D := ∑ i, ∑ j, ‖x i - x j‖ with hD_def
  have hD : ∀ i j, ‖x i - x j‖ ≤ D := fun i j =>
    (Finset.single_le_sum (f := fun j => ‖x i - x j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖x i - x j‖)
        (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
  refine continuous_iff_continuousAt.mpr fun w => ?_
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hcont : Continuous fun w' : stdSimplex ℝ ι =>
      Real.sqrt (D ^ 2 * ∑ i, |w'.1 i - w.1 i|) :=
    Real.continuous_sqrt.comp (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp continuous_subtype_val).sub continuous_const).abs))
  have hg : Tendsto (fun w' : stdSimplex ℝ ι => Real.sqrt (D ^ 2 * ∑ i, |w'.1 i - w.1 i|))
      (𝓝 w) (𝓝 0) := by
    simpa using hcont.tendsto w
  refine squeeze_zero (fun w' => dist_nonneg) (fun w' => ?_) hg
  rw [P2W.dist_toP2W]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (w2P_finLaw_sq_le x w' w hD))

end Maximal

end MVFBSDEJ.Law
