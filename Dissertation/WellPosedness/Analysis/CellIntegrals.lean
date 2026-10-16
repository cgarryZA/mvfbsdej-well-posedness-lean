/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Analysis.SquareBounds
import Dissertation.WellPosedness.Analysis.Grid
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integration by parts against a deterministic weight, from increment bounds

Let `V : ℝ → Ω → ℝ` be a jointly measurable process and `q` a real function on `[0, t]` with
continuous derivative `q'`. Suppose that the increments of `V` have second moments controlled by
a time density `g` of finite mass on `[0, t]`,

`𝔼|V_b − V_a|² ≤ ∫_a^b g`,   `0 ≤ a ≤ b ≤ t`,

and that a second process `M`, given at each time up to a null set, is the integral of `q`
against `V` in the following sense: for every constant `c` within `δ` of `q` on `[a, b]`,

`𝔼|(M_b − M_a) − c (V_b − V_a)|² ≤ δ² ∫_a^b g`.

Then `M` is determined by `V` and `q` through the integration by parts formula

`M_t − M_0 = q(t) V_t − q(0) V_0 − ∫_0^t q'(s) V_s ds`

almost surely. On the uniform grid `t_j = j t / N` the difference of the two sides is the sum
over the cells of `(ΔM_j − q(t_{j+1}) ΔV_j) + ∫_{t_j}^{t_{j+1}} q'(s) (V_s − V_{t_j}) ds`. With
`K` a bound of `|q'|` on `[0, t]`, both summands of the cell `j` have second moment at most
`K² (t / N)² ∫_{t_j}^{t_{j+1}} g`, the second by the Cauchy–Schwarz inequality and the increment
bound of `V`. The Cauchy–Schwarz inequality over the `N` cells bounds the second moment of the
difference by `4 K² t² ∫_0^t g / N`, which tends to `0`.

## Main statements

* `setIntegral_Icc_eq_sub_of_hasDerivWithinAt` — the fundamental theorem of calculus on a
  subinterval of `[0, t]`.
* `sum_setIntegral_cells` — the integral over `[0, t]` is the sum of those over the grid cells.
* `ae_sub_eq_of_increment_le` — the integration by parts formula from the increment bounds.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness

/-! ### Calculus on a subinterval -/

section Calculus

variable {q q' : ℝ → ℝ} {t : ℝ}

/-- **The fundamental theorem of calculus on a subinterval**: for `q` with derivative `q'` on
`[0, t]`, `q'` continuous, and `0 ≤ a ≤ b ≤ t`, `∫_a^b q' = q(b) − q(a)`. -/
theorem setIntegral_Icc_eq_sub_of_hasDerivWithinAt
    (hq : ∀ s ∈ Set.Icc 0 t, HasDerivWithinAt q (q' s) (Set.Icc 0 t) s) (hq' : Continuous q')
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ t) :
    ∫ s in Set.Icc a b, q' s = q b - q a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (fun s hs => ?_) (fun s hs => ?_)
    (hq'.intervalIntegrable a b)
  · exact (hq s ⟨ha.trans hs.1, hs.2.trans hb⟩).continuousWithinAt.mono
      (Set.Icc_subset_Icc ha hb)
  · exact (hq s ⟨ha.trans hs.1.le, hs.2.le.trans hb⟩).hasDerivAt
      (Icc_mem_nhds (ha.trans_lt hs.1) (hs.2.trans_le hb))

/-- **The integral over `[0, t]` is the sum of the integrals over the grid cells**, for a
function integrable on `[0, t]`. -/
theorem sum_setIntegral_cells {f : ℝ → ℝ} (ht : 0 ≤ t) {N : ℕ} (hN : N ≠ 0)
    (hf : IntegrableOn f (Set.Icc 0 t)) :
    ∑ j ∈ Finset.range N, ∫ s in Set.Icc (gridPt t N j) (gridPt t N (j + 1)), f s
      = ∫ s in Set.Icc 0 t, f s := by
  have hle : ∀ j, gridPt t N j ≤ gridPt t N (j + 1) := fun j => gridPt_mono ht N (Nat.le_succ j)
  have hconv : ∀ a b : ℝ, a ≤ b → ∫ s in Set.Icc a b, f s = ∫ s in a..b, f s := fun a b hab => by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]
  rw [Finset.sum_congr rfl fun j _ => hconv _ _ (hle j),
    intervalIntegral.sum_integral_adjacent_intervals (a := gridPt t N) fun j hj => ?_,
    gridPt_zero, gridPt_self t hN, hconv 0 t ht]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (hle j)]
  exact hf.mono_set (Set.Ioc_subset_Icc_self.trans (Icc_gridPt_subset ht hj))

end Calculus

/-! ### The integration by parts formula -/

section IntegrationByParts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Integration by parts against a deterministic weight, from increment bounds.** Let `V` be
jointly measurable with almost surely integrable paths on `[0, t]`, let `q` have continuous
derivative `q'` on `[0, t]`, and let `g` have finite mass on `[0, t]`. If

* `𝔼|V_b − V_a|² ≤ ∫_a^b g` for `0 ≤ a ≤ b ≤ t`, and
* `𝔼|(M_b − M_a) − c (V_b − V_a)|² ≤ δ² ∫_a^b g` whenever `|q − c| ≤ δ` on `[a, b]`,

then `M_t − M_0 = q(t) V_t − q(0) V_0 − ∫_0^t q'(s) V_s ds` almost surely. -/
theorem ae_sub_eq_of_increment_le [SFinite P] {V M : ℝ → Ω → ℝ} {q q' : ℝ → ℝ}
    {g : ℝ → ℝ≥0∞} {t : ℝ} (ht : 0 ≤ t)
    (hq : ∀ s ∈ Set.Icc 0 t, HasDerivWithinAt q (q' s) (Set.Icc 0 t) s) (hq' : Continuous q')
    (hVm : Measurable (Function.uncurry V))
    (hVi : ∀ᵐ ω ∂P, IntegrableOn (fun s => V s ω) (Set.Icc 0 t))
    (hMm : ∀ s, AEMeasurable (M s) P) (hg : ∫⁻ s in Set.Icc 0 t, g s ≠ ⊤)
    (hV : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t →
      ∫⁻ ω, ‖V b ω - V a ω‖ₑ ^ 2 ∂P ≤ ∫⁻ s in Set.Icc a b, g s)
    (hM : ∀ a b c δ, 0 ≤ a → a ≤ b → b ≤ t → (∀ s ∈ Set.Icc a b, |q s - c| ≤ δ) →
      ∫⁻ ω, ‖M b ω - M a ω - c * (V b ω - V a ω)‖ₑ ^ 2 ∂P
        ≤ ENNReal.ofReal (δ ^ 2) * ∫⁻ s in Set.Icc a b, g s) :
    ∀ᵐ ω ∂P, M t ω - M 0 ω
      = q t * V t ω - q 0 * V 0 ω - ∫ s in Set.Icc 0 t, q' s * V s ω := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hq'.continuousOn (s := Set.Icc 0 t))
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, ht⟩)
  have hlip : ∀ x ∈ Set.Icc 0 t, ∀ y ∈ Set.Icc 0 t, |q y - q x| ≤ K * |y - x| :=
    fun x hx y hy => (convex_Icc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le hq hK hx hy
  have hVs : ∀ s, Measurable (V s) := fun s => hVm.comp (measurable_const.prodMk measurable_id)
  have hVω : ∀ ω, Measurable fun s => V s ω := fun ω =>
    hVm.comp (measurable_id.prodMk measurable_const)
  have hVsw : Measurable fun p : Ω × ℝ => V p.2 p.1 := hVm.comp measurable_swap
  -- integrals in time of measurable integrands are measurable in the sample point
  have hIm : ∀ (S : Set ℝ) (F : Ω × ℝ → ℝ), Measurable F →
      Measurable fun ω => ∫ s in S, F (ω, s) :=
    fun S F hF => (hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict S)).measurable
  set G := ∫⁻ s in Set.Icc 0 t, g s with hG
  set D : Ω → ℝ := fun ω => M t ω - M 0 ω
    - (q t * V t ω - q 0 * V 0 ω - ∫ s in Set.Icc 0 t, q' s * V s ω) with hD
  have hDm : AEMeasurable D P :=
    ((hMm t).sub (hMm 0)).sub ((((hVs t).const_mul _).sub ((hVs 0).const_mul _)).sub
      (hIm _ (fun p => q' p.2 * V p.2 p.1) ((hq'.measurable.comp measurable_snd).mul
        hVsw))).aemeasurable
  -- the second moment of the difference is at most `4 K² t² G / N`
  have hbound : ∀ N : ℕ, 1 ≤ N →
      ∫⁻ ω, ‖D ω‖ₑ ^ 2 ∂P ≤ 4 * ENNReal.ofReal (K ^ 2 * t ^ 2 / N) * G := by
    intro N hN1
    have hN : N ≠ 0 := by omega
    have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    set τ : ℝ := t / N with hτ
    have hτ0 : 0 ≤ τ := div_nonneg ht N.cast_nonneg
    set u : ℕ → ℝ := gridPt t N with hu
    have hu0 : ∀ j, 0 ≤ u j := fun j => gridPt_nonneg ht N j
    have hule : ∀ j, u j ≤ u (j + 1) := fun j => gridPt_mono ht N (Nat.le_succ j)
    have hut : ∀ j, j < N → u (j + 1) ≤ t := fun j hj => gridPt_le ht hj
    have hstep : ∀ j, u (j + 1) - u j = τ := fun j => gridPt_succ_sub t N j
    set c : ℝ≥0∞ := ENNReal.ofReal (K ^ 2 * τ ^ 2) with hc
    set I : ℕ → ℝ≥0∞ := fun j => ∫⁻ s in Set.Icc (u j) (u (j + 1)), g s with hI
    let A : ℕ → Ω → ℝ := fun j ω =>
      M (u (j + 1)) ω - M (u j) ω - q (u (j + 1)) * (V (u (j + 1)) ω - V (u j) ω)
    let B : ℕ → Ω → ℝ := fun j ω =>
      ∫ s in Set.Icc (u j) (u (j + 1)), q' s * (V s ω - V (u j) ω)
    have hAm : ∀ j, AEMeasurable (A j) P := fun j =>
      ((hMm _).sub (hMm _)).sub (((hVs _).sub (hVs _)).const_mul _).aemeasurable
    have hBm : ∀ j, Measurable (B j) := fun j =>
      hIm _ (fun p => q' p.2 * (V p.2 p.1 - V (u j) p.1))
        ((hq'.measurable.comp measurable_snd).mul (hVsw.sub ((hVs _).comp measurable_fst)))
    -- the difference is the sum of the cell errors
    have hsplit : ∀ᵐ ω ∂P, D ω = ∑ j ∈ Finset.range N, (A j ω + B j ω) := by
      filter_upwards [hVi] with ω hω
      have hqV : IntegrableOn (fun s => q' s * V s ω) (Set.Icc 0 t) :=
        IntegrableOn.continuousOn_mul hq'.continuousOn hω isCompact_Icc
      have hcell : ∀ j ∈ Finset.range N, A j ω + B j ω
          = (M (u (j + 1)) ω - M (u j) ω)
            - (q (u (j + 1)) * V (u (j + 1)) ω - q (u j) * V (u j) ω)
            + ∫ s in Set.Icc (u j) (u (j + 1)), q' s * V s ω := by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hsub := Icc_gridPt_subset ht hj'
        have hB : B j ω = (∫ s in Set.Icc (u j) (u (j + 1)), q' s * V s ω)
            - (q (u (j + 1)) - q (u j)) * V (u j) ω := by
          rw [← setIntegral_Icc_eq_sub_of_hasDerivWithinAt hq hq' (hu0 j) (hule j) (hut j hj'),
            ← integral_mul_const, ← integral_sub (hqV.mono_set hsub)
              ((hq'.integrableOn_Icc).mul_const _)]
          refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
          ring
        simp only [A]
        rw [hB]
        ring
      have hM' : ∑ j ∈ Finset.range N, (M (u (j + 1)) ω - M (u j) ω) = M (u N) ω - M (u 0) ω :=
        Finset.sum_range_sub (fun j => M (u j) ω) N
      have hqV' : ∑ j ∈ Finset.range N,
          (q (u (j + 1)) * V (u (j + 1)) ω - q (u j) * V (u j) ω)
            = q (u N) * V (u N) ω - q (u 0) * V (u 0) ω :=
        Finset.sum_range_sub (fun j => q (u j) * V (u j) ω) N
      rw [Finset.sum_congr rfl hcell, Finset.sum_add_distrib, Finset.sum_sub_distrib, hM', hqV',
        sum_setIntegral_cells ht hN hqV]
      simp only [hD, hu, gridPt_zero, gridPt_self t hN]
      ring
    -- the first error of each cell: `ΔM_j − q(t_{j+1}) ΔV_j`
    have hA : ∀ j, j < N → ∫⁻ ω, ‖A j ω‖ₑ ^ 2 ∂P ≤ c * I j := by
      intro j hj
      have h := hM (u j) (u (j + 1)) (q (u (j + 1))) (K * τ) (hu0 j) (hule j) (hut j hj)
        fun s hs => by
          have hs' : s ∈ Set.Icc 0 t := Icc_gridPt_subset ht hj hs
          have hj1 : u (j + 1) ∈ Set.Icc 0 t := Icc_gridPt_subset ht hj ⟨hule j, le_rfl⟩
          rw [abs_sub_comm]
          calc |q (u (j + 1)) - q s| ≤ K * |u (j + 1) - s| := hlip s hs' _ hj1
            _ ≤ K * τ := by
              refine mul_le_mul_of_nonneg_left ?_ hK0
              rw [abs_of_nonneg (sub_nonneg.mpr hs.2), ← hstep j]
              linarith [hs.1]
      rwa [mul_pow] at h
    -- the second error of each cell: `∫_{t_j}^{t_{j+1}} q'(s) (V_s − V_{t_j}) ds`
    have hB : ∀ j, j < N → ∫⁻ ω, ‖B j ω‖ₑ ^ 2 ∂P ≤ c * I j := by
      intro j hj
      set C := Set.Icc (u j) (u (j + 1)) with hC
      have hCsub : C ⊆ Set.Icc 0 t := Icc_gridPt_subset ht hj
      have hvol : volume C = ENNReal.ofReal τ := volume_Icc_gridPt t N j
      have hpt : ∀ ω, ‖B j ω‖ₑ ^ 2
          ≤ ENNReal.ofReal τ * (ENNReal.ofReal (K ^ 2)
            * ∫⁻ s in C, ‖V s ω - V (u j) ω‖ₑ ^ 2) := by
        intro ω
        have h := enorm_setIntegral_sq_le (μ := volume)
          (f := fun s => q' s * (V s ω - V (u j) ω)) C
          (hq'.measurable.mul ((hVω ω).sub measurable_const)).aestronglyMeasurable
        rw [hvol] at h
        refine h.trans ?_
        gcongr ENNReal.ofReal τ * ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
        rw [enorm_mul, mul_pow]
        gcongr ?_ * _
        have hKs : ‖q' s‖ₑ ≤ ENNReal.ofReal K := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hK s (hCsub hs))
        calc ‖q' s‖ₑ ^ 2 ≤ ENNReal.ofReal K ^ 2 := pow_le_pow_left' hKs 2
          _ = ENNReal.ofReal (K ^ 2) := (ENNReal.ofReal_pow hK0 2).symm
      have hswap : ∫⁻ ω, ∫⁻ s in C, ‖V s ω - V (u j) ω‖ₑ ^ 2 ∂volume ∂P
          = ∫⁻ s in C, ∫⁻ ω, ‖V s ω - V (u j) ω‖ₑ ^ 2 ∂P ∂volume :=
        lintegral_lintegral_swap (μ := P) (ν := volume.restrict C)
          ((show Measurable fun p : Ω × ℝ => ‖V p.2 p.1 - V (u j) p.1‖ₑ ^ 2 from
            (hVsw.sub ((hVs _).comp measurable_fst)).enorm.pow_const 2).aemeasurable)
      have hinc : ∫⁻ s in C, ∫⁻ ω, ‖V s ω - V (u j) ω‖ₑ ^ 2 ∂P ∂volume
          ≤ I j * ENNReal.ofReal τ := by
        calc ∫⁻ s in C, ∫⁻ ω, ‖V s ω - V (u j) ω‖ₑ ^ 2 ∂P ∂volume ≤ ∫⁻ _ in C, I j := by
              refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
              exact (hV (u j) s (hu0 j) hs.1 (hs.2.trans (hut j hj))).trans
                (lintegral_mono_set (Set.Icc_subset_Icc le_rfl hs.2))
          _ = I j * ENNReal.ofReal τ := by rw [setLIntegral_const, hvol]
      calc ∫⁻ ω, ‖B j ω‖ₑ ^ 2 ∂P
          ≤ ∫⁻ ω, ENNReal.ofReal τ * (ENNReal.ofReal (K ^ 2)
              * ∫⁻ s in C, ‖V s ω - V (u j) ω‖ₑ ^ 2) ∂P := lintegral_mono hpt
        _ = ENNReal.ofReal τ * (ENNReal.ofReal (K ^ 2)
              * ∫⁻ ω, ∫⁻ s in C, ‖V s ω - V (u j) ω‖ₑ ^ 2 ∂volume ∂P) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal τ * (ENNReal.ofReal (K ^ 2) * (I j * ENNReal.ofReal τ)) := by
            rw [hswap]
            gcongr
        _ = (ENNReal.ofReal τ * (ENNReal.ofReal (K ^ 2) * ENNReal.ofReal τ)) * I j := by ring
        _ = c * I j := by
            rw [hc, ← ENNReal.ofReal_mul (sq_nonneg K), ← ENNReal.ofReal_mul hτ0]
            congr 2
            ring
    -- summing over the cells
    have hNc : (N : ℝ≥0∞) * c = ENNReal.ofReal (K ^ 2 * t ^ 2 / N) := by
      rw [hc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul N.cast_nonneg, hτ]
      congr 1
      field_simp
    calc ∫⁻ ω, ‖D ω‖ₑ ^ 2 ∂P
        ≤ ∫⁻ ω, N * ∑ j ∈ Finset.range N, (2 * ‖A j ω‖ₑ ^ 2 + 2 * ‖B j ω‖ₑ ^ 2) ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hsplit] with ω hω
          rw [hω]
          calc ‖∑ j ∈ Finset.range N, (A j ω + B j ω)‖ₑ ^ 2
              ≤ (∑ j ∈ Finset.range N, ‖A j ω + B j ω‖ₑ) ^ 2 :=
                pow_le_pow_left' (enorm_sum_le _ _) 2
            _ ≤ (Finset.range N).card * ∑ j ∈ Finset.range N, ‖A j ω + B j ω‖ₑ ^ 2 :=
                sq_finsetSum_le_card_mul _ _
            _ ≤ N * ∑ j ∈ Finset.range N, (2 * ‖A j ω‖ₑ ^ 2 + 2 * ‖B j ω‖ₑ ^ 2) := by
                rw [Finset.card_range]
                gcongr with j hj
                exact enorm_add_sq_le _ _
      _ = N * ∑ j ∈ Finset.range N,
            (2 * ∫⁻ ω, ‖A j ω‖ₑ ^ 2 ∂P + 2 * ∫⁻ ω, ‖B j ω‖ₑ ^ 2 ∂P) := by
          rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top N),
            lintegral_finsetSum' (f := fun j ω => 2 * ‖A j ω‖ₑ ^ 2 + 2 * ‖B j ω‖ₑ ^ 2) _
              fun j _ =>
              (((hAm j).enorm.pow_const 2).const_mul 2).add
                (((hBm j).enorm.pow_const 2).const_mul 2).aemeasurable]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [lintegral_add_left' (((hAm j).enorm.pow_const 2).const_mul 2),
            lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ N * ∑ j ∈ Finset.range N, (2 * (c * I j) + 2 * (c * I j)) := by
          gcongr with j hj
          · exact hA j (Finset.mem_range.mp hj)
          · exact hB j (Finset.mem_range.mp hj)
      _ = 4 * ((N : ℝ≥0∞) * c) * ∑ j ∈ Finset.range N, I j := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 4 * ENNReal.ofReal (K ^ 2 * t ^ 2 / N) * G := by
          rw [hNc, hI, sum_setLIntegral_cells ht hN]
  -- the bound tends to `0`
  have hlim : Tendsto (fun N : ℕ => 4 * ENNReal.ofReal (K ^ 2 * t ^ 2 / N) * G) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ENNReal.ofReal (K ^ 2 * t ^ 2 / N)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat (K ^ 2 * t ^ 2))
    have h2 := ENNReal.Tendsto.mul_const
      (ENNReal.Tendsto.const_mul h1 (Or.inr (by norm_num : (4 : ℝ≥0∞) ≠ ⊤))) (Or.inr hg)
    simpa using h2
  have h0 : ∫⁻ ω, ‖D ω‖ₑ ^ 2 ∂P = 0 :=
    le_antisymm (ge_of_tendsto hlim (eventually_atTop.mpr ⟨1, hbound⟩)) bot_le
  filter_upwards [(lintegral_eq_zero_iff' (hDm.enorm.pow_const 2)).mp h0] with ω hω
  have hω' : D ω = 0 := by simpa using hω
  simp only [hD] at hω'
  linarith

end IntegrationByParts

end Dissertation.WellPosedness
