/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Martingale.CountIntegral

/-!
# The large jumps of an integer-valued measure

Let `μ` be a measure on `ℝ × E` whose restriction to each window `(0, T] × E_k` of a σ-finite
mark measure is integer-valued, with at most one point at each positive time, and let `f ≥ 0`
with `A(s) = ∫_{(0, s] × E} f² dμ` and `A(s−) = ∫_{(0, s) × E} f² dμ`. At a time whose points
carry `f² > A(s−)` the jump of `A` is at least `A(s−)`, so `A` at least doubles there; read from
the last such time, the values of `A` decay geometrically, and

`∫_{(0, T] × E} f 1_{f² > A(s−)} dμ ≤ (2 + √2) A(T)^{1/2}`.

This bounds the large jumps in the Davis decomposition of a compensated Poisson integral.

## Main statements

* `Dissertation.WellPosedness.Martingale.sum_sqrt_le_of_doubling` — the geometric bound.
* `Dissertation.WellPosedness.Martingale.lintegral_bigJumps_le` — the bound on the large jumps.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Dissertation.WellPosedness.Martingale

open LevyStochCalc LevyStochCalc.Probability

/-- **Square roots of values that at least double along a finite set of times** sum to at most
`(2 + √2)` times the square root of a bound for the values. -/
theorem sum_sqrt_le_of_doubling (S : Finset ℝ) {a : ℝ → ℝ} (M : ℝ)
    (ha0 : ∀ s ∈ S, 0 ≤ a s) (haM : ∀ s ∈ S, a s ≤ M)
    (hdbl : ∀ s ∈ S, ∀ s' ∈ S, s < s' → 2 * a s ≤ a s') :
    ∑ s ∈ S, √(a s) ≤ (2 + √2) * √M := by
  classical
  induction S using Finset.induction_on_max generalizing M with
  | empty =>
    simp only [Finset.sum_empty]
    positivity
  | insert m S hlt ih =>
    have hmS : m ∉ S := fun h => lt_irrefl _ (hlt m h)
    rw [Finset.sum_insert hmS]
    have hm := haM m (Finset.mem_insert_self _ _)
    have hS := ih (a m / 2) (fun s hs => ha0 s (Finset.mem_insert_of_mem hs))
      (fun s hs => by
        have := hdbl s (Finset.mem_insert_of_mem hs) m (Finset.mem_insert_self _ _) (hlt s hs)
        linarith)
      (fun s hs s' hs' h =>
        hdbl s (Finset.mem_insert_of_mem hs) s' (Finset.mem_insert_of_mem hs') h)
    have h2 : (0 : ℝ) < √2 := by positivity
    have h22 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hsq : √(a m / 2) = √(a m) / √2 := Real.sqrt_div' _ (by norm_num)
    have hkey : (2 + √2) * √(a m / 2) = (√2 + 1) * √(a m) := by
      rw [hsq]
      field_simp
      linear_combination (-√(a m)) * h22
    calc √(a m) + ∑ s ∈ S, √(a s) ≤ √(a m) + (2 + √2) * √(a m / 2) := by gcongr
      _ = √(a m) + (√2 + 1) * √(a m) := by rw [hkey]
      _ = (2 + √2) * √(a m) := by ring
      _ ≤ (2 + √2) * √M := by gcongr

/-- **Square roots of values in `[0, ∞]` that at least double along a finite set of times** sum
to at most `(2 + √2)` times the square root of a bound for the values. -/
theorem sum_rpow_half_le_of_doubling (S : Finset ℝ) {a : ℝ → ℝ≥0∞} (M : ℝ≥0∞)
    (haM : ∀ s ∈ S, a s ≤ M) (hdbl : ∀ s ∈ S, ∀ s' ∈ S, s < s' → 2 * a s ≤ a s') :
    ∑ s ∈ S, a s ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (2 + √2) * M ^ (1 / 2 : ℝ) := by
  rcases eq_or_ne M ⊤ with rfl | hM
  · rw [ENNReal.top_rpow_of_pos (by norm_num), ENNReal.mul_top]
    · exact le_top
    · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hfin : ∀ s ∈ S, a s ≠ ⊤ := fun s hs => ne_top_of_le_ne_top hM (haM s hs)
  have hconv : ∀ x : ℝ≥0∞, x ≠ ⊤ → x ^ (1 / 2 : ℝ) = ENNReal.ofReal (√x.toReal) := by
    intro x hx
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hx]
  rw [Finset.sum_congr rfl fun s hs => hconv (a s) (hfin s hs), hconv M hM,
    ← ENNReal.ofReal_sum_of_nonneg (fun s _ => Real.sqrt_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (sum_sqrt_le_of_doubling S M.toReal
    (fun s _ => ENNReal.toReal_nonneg) (fun s hs => ENNReal.toReal_mono hM (haM s hs))
    fun s hs s' hs' h => ?_)
  have := ENNReal.toReal_mono (hfin s' hs') (hdbl s hs s' hs' h)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this

section Jumps

variable {E : Type*} [MeasurableSpace E]

/-- **The large jumps over a window.** For a measure `μ` on `ℝ × E` whose restriction to the
window `(0, T] × A` is integer-valued and which carries at most one point at each positive time,
and a measurable `f ≥ 0`, the integral over the window of `f` at the points where
`f² > ∫_{(0, s) × E} f² dμ` is at most `(2 + √2) (∫_{(0, T] × E} f² dμ)^{1/2}`. -/
theorem lintegral_window_bigJumps_le {μ : Measure (ℝ × E)} {T : ℝ} {A : Set E}
    (hA : MeasurableSet A) (hint : IsIntegerValued (μ.restrict (Ioc (0 : ℝ) T ×ˢ A)))
    (hsimple : ∀ s : ℝ, 0 < s → μ ({s} ×ˢ (univ : Set E)) ≤ 1)
    {f : ℝ × E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in Ioc (0 : ℝ) T ×ˢ A,
        (if ∫⁻ y in Ioo (0 : ℝ) x.1 ×ˢ (univ : Set E), f y ^ 2 ∂μ < f x ^ 2 then f x else 0) ∂μ
      ≤ ENNReal.ofReal (2 + √2)
        * (∫⁻ y in Ioc (0 : ℝ) T ×ˢ (univ : Set E), f y ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  classical
  set W : Set (ℝ × E) := Ioc (0 : ℝ) T ×ˢ A with hWdef
  have hWm : MeasurableSet W := measurableSet_Ioc.prod hA
  set a : ℝ → ℝ≥0∞ := fun s => ∫⁻ y in Ioo (0 : ℝ) s ×ˢ (univ : Set E), f y ^ 2 ∂μ with hadef
  set B : ℝ → ℝ≥0∞ := fun s => ∫⁻ y in Ioc (0 : ℝ) s ×ˢ (univ : Set E), f y ^ 2 ∂μ with hBdef
  set J : ℝ → ℝ≥0∞ := fun s => ∫⁻ y in ({s} : Set ℝ) ×ˢ (univ : Set E), f y ^ 2 ∂μ with hJdef
  have hamono : Monotone a := fun s s' h =>
    lintegral_mono_set (prod_mono (Ioo_subset_Ioo_right h) le_rfl)
  have ham : Measurable a := hamono.measurable
  have hBaJ : ∀ s, 0 < s → B s = a s + J s := by
    intro s hs
    have hU : Ioc (0 : ℝ) s ×ˢ (univ : Set E)
        = Ioo (0 : ℝ) s ×ˢ (univ : Set E) ∪ ({s} : Set ℝ) ×ˢ (univ : Set E) := by
      rw [← union_prod, Ioo_union_right hs]
    have hdisj : Disjoint (Ioo (0 : ℝ) s ×ˢ (univ : Set E)) (({s} : Set ℝ) ×ˢ (univ : Set E)) :=
      disjoint_prod.mpr (Or.inl (disjoint_singleton_right.mpr fun h => lt_irrefl s h.2))
    simp only [hBdef, hadef, hJdef]
    rw [hU, lintegral_union (measurableSet_singleton s |>.prod MeasurableSet.univ) hdisj]
  have hBle : ∀ s s', s < s' → B s ≤ a s' := fun s s' h =>
    lintegral_mono_set (prod_mono (fun r hr => ⟨hr.1, hr.2.trans_lt h⟩) le_rfl)
  have hBmono : Monotone B := fun s s' h =>
    lintegral_mono_set (prod_mono (Ioc_subset_Ioc_right h) le_rfl)
  set h : ℝ × E → ℝ≥0∞ := fun x => if a x.1 < f x ^ 2 then f x else 0 with hhdef
  change ∫⁻ x in W, h x ∂μ ≤ _
  set μW : Measure (ℝ × E) := μ.restrict W with hμW
  -- the time marginal is a finite sum of Dirac masses
  have hmarg : IsIntegerValued (μW.map Prod.fst) := fun S hS => by
    obtain ⟨n, hn⟩ := hint _ (measurable_fst hS)
    exact ⟨n, by rw [Measure.map_apply measurable_fst hS, hn]⟩
  obtain ⟨S, hSeq⟩ := exists_eq_sum_dirac hmarg
  have hSm : MeasurableSet ((S : Set ℝ)) := S.finite_toSet.measurableSet
  have hnull : μW (Prod.fst ⁻¹' (S : Set ℝ)ᶜ) = 0 := by
    have h0 : (μW.map Prod.fst) ((S : Set ℝ)ᶜ) = 0 := by
      rw [hSeq, Measure.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_eq_zero fun s hs => ?_
      rw [Measure.smul_apply, Measure.dirac_apply' _ hSm.compl,
        indicator_of_notMem (Set.notMem_compl_iff.mpr (Finset.mem_coe.mpr hs)), smul_zero]
    rwa [Measure.map_apply measurable_fst hSm.compl] at h0
  have hae : ∀ᵐ x ∂μW, x ∈ Prod.fst ⁻¹' (S : Set ℝ) := by
    rw [ae_iff]
    exact hnull
  have hcover : Prod.fst ⁻¹' (S : Set ℝ) = ⋃ s ∈ S, ({s} : Set ℝ) ×ˢ (univ : Set E) := by
    ext x
    simp
  have hsplit : ∫⁻ x, h x ∂μW
      = ∑ s ∈ S, ∫⁻ x in ({s} : Set ℝ) ×ˢ (univ : Set E), h x ∂μW := by
    conv_lhs => rw [← Measure.restrict_eq_self_of_ae_mem hae, hcover]
    refine lintegral_biUnion_finset ?_ (fun s _ => (measurableSet_singleton s).prod
      MeasurableSet.univ) _
    intro s _ s' _ hss'
    exact disjoint_prod.mpr (Or.inl (disjoint_singleton.mpr hss'))
  -- the points of large jumps at a time
  set Bs : ℝ → Set (ℝ × E) := fun s =>
    (({s} : Set ℝ) ×ˢ (univ : Set E)) ∩ {x | a x.1 < f x ^ 2} with hBsdef
  have hBsm : ∀ s, MeasurableSet (Bs s) := fun s =>
    ((measurableSet_singleton s).prod MeasurableSet.univ).inter
      (measurableSet_lt (ham.comp measurable_fst) (hf.pow_const 2))
  have hterm_eq : ∀ s, ∫⁻ x in ({s} : Set ℝ) ×ˢ (univ : Set E), h x ∂μW
      = ∫⁻ x in Bs s, f x ∂μW := by
    intro s
    have hss : MeasurableSet (({s} : Set ℝ) ×ˢ (univ : Set E)) :=
      (measurableSet_singleton s).prod MeasurableSet.univ
    rw [setLIntegral_congr_fun hss (g := (Bs s).indicator f) fun x hx => ?_,
      lintegral_indicator (hBsm s), Measure.restrict_restrict (hBsm s),
      inter_eq_left.mpr inter_subset_left]
    have hx1 : x.1 = s := hx.1
    by_cases hxB : a x.1 < f x ^ 2
    · rw [indicator_of_mem (show x ∈ Bs s from ⟨hx, hxB⟩)]
      simp only [hhdef, if_pos hxB]
    · rw [indicator_of_notMem (fun hmem => hxB hmem.2)]
      simp only [hhdef, if_neg hxB]
  -- a time with large jumps
  have hterm : ∀ s, μW (Bs s) ≠ 0 →
      ∫⁻ x in Bs s, f x ∂μW ≤ B s ^ (1 / 2 : ℝ) ∧ s ∈ Ioc (0 : ℝ) T ∧ 2 * a s ≤ B s := by
    intro s hne
    have hWs : (Bs s ∩ W).Nonempty := by
      by_contra hem
      rw [not_nonempty_iff_eq_empty] at hem
      exact hne (by rw [hμW, Measure.restrict_apply (hBsm s), hem, measure_empty])
    obtain ⟨x, ⟨⟨hx1, -⟩, -⟩, hxW⟩ := hWs
    have hx1' : x.1 = s := hx1
    have hsI : s ∈ Ioc (0 : ℝ) T := hx1' ▸ hxW.1
    obtain ⟨n, hn⟩ := hint (Bs s) (hBsm s)
    have hn' : μW (Bs s) = n := hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (by rw [hn', Nat.cast_zero])
    have hone : 1 ≤ μW (Bs s) := by
      rw [hn']
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    have hBsub : Bs s ⊆ ({s} : Set ℝ) ×ˢ (univ : Set E) := inter_subset_left
    have hle1 : μW (Bs s) ≤ 1 :=
      (Measure.restrict_le_self (Bs s)).trans
        ((measure_mono hBsub).trans (hsimple s hsI.1))
    have hJ : ∫⁻ x in Bs s, f x ^ 2 ∂μW ≤ J s :=
      (lintegral_mono' (Measure.restrict_mono hBsub
        (Measure.restrict_le_self)) le_rfl)
    have haJ : a s ≤ J s := by
      calc a s ≤ a s * μW (Bs s) := le_mul_of_one_le_right' hone
        _ = ∫⁻ x in Bs s, a s ∂μW := by rw [setLIntegral_const]
        _ ≤ ∫⁻ x in Bs s, f x ^ 2 ∂μW := by
            refine setLIntegral_mono' (hBsm s) fun y hy => ?_
            have hy1 : y.1 = s := hy.1.1
            have := hy.2
            simp only [mem_setOf_eq, hy1] at this
            exact this.le
        _ ≤ J s := hJ
    refine ⟨?_, hsI, ?_⟩
    · have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (μW.restrict (Bs s))
        Real.HolderConjugate.two_two hf.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
      simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul,
        Measure.restrict_apply MeasurableSet.univ, univ_inter] at hcs
      have hsq : ∀ y : ℝ × E, f y ^ (2 : ℝ) = f y ^ 2 := fun y => ENNReal.rpow_two (f y)
      simp only [hsq] at hcs
      calc ∫⁻ x in Bs s, f x ∂μW
          ≤ (∫⁻ x in Bs s, f x ^ 2 ∂μW) ^ (1 / 2 : ℝ) * μW (Bs s) ^ (1 / 2 : ℝ) := hcs
        _ ≤ J s ^ (1 / 2 : ℝ) * 1 := by
            gcongr
            exact ENNReal.rpow_le_one hle1 (by norm_num)
        _ ≤ B s ^ (1 / 2 : ℝ) := by
            rw [mul_one, hBaJ s hsI.1]
            gcongr
            exact le_add_self
    · rw [hBaJ s hsI.1, two_mul]
      gcongr
  -- assemble
  set S' := S.filter fun s => μW (Bs s) ≠ 0 with hS'
  have hsum : ∫⁻ x, h x ∂μW ≤ ∑ s ∈ S', B s ^ (1 / 2 : ℝ) := by
    rw [hsplit, hS', Finset.sum_filter]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [hterm_eq s]
    split_ifs with hne
    · exact (hterm s hne).1
    · push Not at hne
      rw [Measure.restrict_eq_zero.mpr hne, lintegral_zero_measure]
  refine hsum.trans (sum_rpow_half_le_of_doubling S' (B T) (fun s hs => ?_)
    fun s hs s' hs' hlt => ?_)
  · exact hBmono (hterm s (Finset.mem_filter.mp hs).2).2.1.2
  · have h1 := (hterm s' (Finset.mem_filter.mp hs').2).2.2
    calc 2 * B s ≤ 2 * a s' := by gcongr; exact hBle s s' hlt
      _ ≤ B s' := h1

/-- **The large jumps of an integer-valued, time-simple measure.** For a measure `μ` on `ℝ × E`
whose restrictions to the windows `(0, T] × E_k`, `E_k` the spanning sets of a σ-finite `ν`, are
integer-valued and which carries at most one point at each positive time, and a measurable
`f ≥ 0`, `∫_{(0, T] × E} f 1_{f² > A(s−)} dμ ≤ (2 + √2) A(T)^{1/2}` with
`A(s) = ∫_{(0, s] × E} f² dμ` and `A(s−) = ∫_{(0, s) × E} f² dμ`. -/
theorem lintegral_bigJumps_le (ν : Measure E) [SigmaFinite ν] {μ : Measure (ℝ × E)} {T : ℝ}
    (hint : ∀ k, IsIntegerValued (μ.restrict (Ioc (0 : ℝ) T ×ˢ spanningSets ν k)))
    (hsimple : ∀ s : ℝ, 0 < s → μ ({s} ×ˢ (univ : Set E)) ≤ 1)
    {f : ℝ × E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in Ioc (0 : ℝ) T ×ˢ (univ : Set E),
        (if ∫⁻ y in Ioo (0 : ℝ) x.1 ×ˢ (univ : Set E), f y ^ 2 ∂μ < f x ^ 2 then f x else 0) ∂μ
      ≤ ENNReal.ofReal (2 + √2)
        * (∫⁻ y in Ioc (0 : ℝ) T ×ˢ (univ : Set E), f y ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  conv_lhs => rw [← iUnion_Ioc_prod_spanningSets (ν := ν) T,
    setLIntegral_iUnion_of_directed _ (directed_Ioc_prod_spanningSets (ν := ν) T)]
  exact iSup_le fun k => lintegral_window_bigJumps_le (measurableSet_spanningSets ν k) (hint k)
    hsimple hf

end Jumps

end Dissertation.WellPosedness.Martingale
