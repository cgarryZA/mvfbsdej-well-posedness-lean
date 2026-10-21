/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.Compensation
import LevyStochCalc.Probability.MarkedPredictableComp
import LevyStochCalc.Ito.JumpCoefficientPredictableCriteria
import LevyStochCalc.Poisson.CompensatedIntegrandComplete

/-!
# The quadratic integrand of the Poisson martingale `M²`

In the proof of Lemma 4.1 of the well-posedness paper, the Poisson martingale
`M²_t = ∫_0^t ∫_E e^s |U_s(e)|² Ñ(ds, de)` has the nonnegative predictable integrand
`e^s |U_s(e)|²`. For `U ∈ H²_N` vanishing off `[0, T]` this integrand lies in
`L¹(dP ⊗ ds ⊗ ν)`, with `𝔼 ∫_0^T ∫_E e^s |U_s(e)|² ν(de) ds ≤ e^T 𝔼 ∫_0^T ‖U_s‖² ds`, so its
Poisson integral and its compensator over `(t, T] × E` have finite expectation and the increment
`M²_T − M²_t`, read pathwise, has mean zero by the compensation formula (2.1).

## Main statements

* `lintegral_lintegral_lintegral_eq_prod` — a triple lower integral over the sample point, a set
  of times and the marks is the lower integral over the product measure.
* `markedPredictable_exp_mul_sum_sq` — the quadratic integrand is marked predictable.
* `lintegral_exp_mul_sum_sq_le` — the `L¹` bound of the quadratic integrand.
* `quadratic_compensation` — the finite expectations and the mean zero of `M²_T − M²_t`.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness.BrownianPoisson

open LevyStochCalc

universe u' v' w'

section Triple

variable {Ω : Type u'} [MeasurableSpace Ω] {E : Type v'} [MeasurableSpace E] {P : Measure Ω}
  {ν : Measure E}

/-- A triple lower integral over the sample point, a set `S` of times and the marks is the lower
integral over the product of `P`, Lebesgue measure on `S` and `ν`. -/
theorem lintegral_lintegral_lintegral_eq_prod [SFinite P] [SFinite ν] {f : Ω × ℝ × E → ℝ≥0∞}
    (hf : Measurable f) (S : Set ℝ) :
    ∫⁻ ω, ∫⁻ s in S, ∫⁻ e, f (ω, s, e) ∂ν ∂volume ∂P
      = ∫⁻ p, f p ∂(P.prod ((volume.restrict S).prod ν)) := by
  rw [lintegral_prod _ hf.aemeasurable]
  refine lintegral_congr fun ω => ?_
  exact (lintegral_prod _ (hf.comp measurable_prodMk_left).aemeasurable).symm

end Triple

variable {Ω : Type u'} [MeasurableSpace Ω] {E : Type v'} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {N : Poisson.PoissonRandomMeasure.{u', v', w'} P ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {m : ℕ} {T : ℝ} {U : Fin m → ℝ → Ω → E → ℝ}

/-- The square of the extended norm of a real number is the extended real of its square. -/
theorem coe_nnnorm_sq_eq_ofReal (x : ℝ) : (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from rfl, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

/-- **The quadratic integrand is marked predictable.** For `U` marked predictable,
coordinatewise, and vanishing off `[0, T]`, `e^s |U_s(e)|²` is marked predictable. -/
theorem markedPredictable_exp_mul_sum_sq
    (hU : ∀ k, Probability.MarkedPredictable ℱ ν fun ω s e => U k s ω e)
    (hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → U k s ω e = 0) :
    Probability.MarkedPredictable ℱ ν fun ω s e => Real.exp s * ∑ k, U k s ω e ^ 2 := by
  classical
  have hF : Measurable fun q : ℝ × ℝ × (Fin m → ℝ) => Real.exp q.1 * ∑ k, q.2.2 k ^ 2 :=
    (Real.measurable_exp.comp measurable_fst).mul
      (Finset.measurable_sum _ fun k _ => ((measurable_pi_apply k).comp
        measurable_snd.snd).pow_const 2)
  have hΓ : Probability.MarkedPredictable ℱ ν fun ω s e => (fun k => U k s ω e : Fin m → ℝ) := by
    unfold Probability.MarkedPredictable
    letI : MeasurableSpace (Ω × ℝ × E) := Probability.markedPredictableSigma ℱ ν
    exact measurable_pi_lambda _ fun k => hU k
  have hcomp := Probability.MarkedPredictable.comp_measurable (ν := ν) hF
    (Y := fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) measurable_const hΓ
  have heq : (fun ω s e => Real.exp s * ∑ k, U k s ω e ^ 2)
      = fun ω s e => if 0 < s then Real.exp s * ∑ k, U k s ω e ^ 2 else 0 := by
    funext ω s e
    split_ifs with hs
    · rfl
    · have h0 : ∀ k, U k s ω e = 0 := fun k => by
        have h := (hU k).eq_of_nonpos (ω := ω) (ω' := ω) (s := s) (s' := -1) (e := e) (e' := e)
          (not_lt.mp hs) (by norm_num)
        rw [h]
        exact hUv k ω (-1) e fun h1 => by linarith [h1.1]
      simp [h0]
  rw [heq]
  exact hcomp

/-- **The `L¹` bound of the quadratic integrand.** For `U` marked predictable, coordinatewise,
and vanishing off `[0, T]`,
`𝔼 ∫_0^T ∫_E e^s |U_s(e)|² ν(de) ds ≤ e^T ∑_k 𝔼 ∫_0^T ‖U^k_s‖²_{L²(ν)} ds`. -/
theorem lintegral_exp_mul_sum_sq_le
    (hU : ∀ k, Probability.MarkedPredictable ℱ ν fun ω s e => U k s ω e)
    (hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → U k s ω e = 0) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        ENNReal.ofReal (Real.exp s * ∑ k, U k s ω e ^ 2) ∂ν ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp T)
        * ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) := by
  have hUm : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2 := fun k =>
    (hU k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hf : Measurable fun p : Ω × ℝ × E =>
      ENNReal.ofReal (Real.exp p.2.1 * ∑ k, U k p.2.1 p.1 p.2.2 ^ 2) :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp measurable_snd.fst).mul
      (Finset.measurable_sum _ fun k _ => (hUm k).pow_const 2))
  have hg : ∀ k, Measurable fun p : Ω × ℝ × E => (‖U k p.2.1 p.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    fun k => (hUm k).nnnorm.coe_nnreal_ennreal.pow_const 2
  rw [lintegral_lintegral_lintegral_eq_prod hf]
  have hE : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)
      = ∫⁻ p, (‖U k p.2.1 p.1 p.2.2‖₊ : ℝ≥0∞) ^ 2
        ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := fun k =>
    lintegral_lintegral_lintegral_eq_prod (hg k) _
  simp only [hE]
  rw [← lintegral_finsetSum _ fun k _ => hg k, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun p => ?_
  by_cases hs : p.2.1 ∈ Set.Icc (0 : ℝ) T
  · simp only [coe_nnnorm_sq_eq_ofReal]
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _,
      ← ENNReal.ofReal_mul (Real.exp_pos T).le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr hs.2) (Finset.sum_nonneg fun k _ => sq_nonneg _))
  · simp only [hUv _ _ _ _ hs]
    simp

/-- **The compensated increment of the quadratic integrand.** For a filtration carrying `N`, `U`
marked predictable with finite energy, coordinatewise, and vanishing off `[0, T]`, and
`t ≥ 0`: the Poisson integral and the compensator of `e^s |U_s(e)|²` over `(t, T] × E` have
finite expectation, and the pathwise compensated integral
`∫_{(t, T] × E} e^s |U_s(e)|² N(ds, de) − ∫_t^T ∫_E e^s |U_s(e)|² ν(de) ds` has mean zero. -/
theorem quadratic_compensation (hℱN : Poisson.IsPoissonFiltration N ℱ) {t : ℝ} (ht : 0 ≤ t)
    (hU : ∀ k, Probability.MarkedPredictable ℱ ν fun ω s e => U k s ω e)
    (hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → U k s ω e = 0)
    (hUs : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) ≠ ⊤) :
    ∫⁻ ω, ∫⁻ p in Set.Ioc t T ×ˢ Set.univ,
        ENNReal.ofReal (Real.exp p.1 * ∑ k, U k p.1 ω p.2 ^ 2) ∂(N.N ω) ∂P < ⊤
    ∧ ∫⁻ ω, ∫⁻ s in Set.Ioc t T, ∫⁻ e,
        ENNReal.ofReal (Real.exp s * ∑ k, U k s ω e ^ 2) ∂ν ∂volume ∂P < ⊤
    ∧ ∫ ω, ((∫ p in Set.Ioc t T ×ˢ Set.univ, Real.exp p.1 * ∑ k, U k p.1 ω p.2 ^ 2
          ∂(N.N ω))
        - ∫ s in Set.Ioc t T, ∫ e, Real.exp s * ∑ k, U k s ω e ^ 2 ∂ν) ∂P = 0 := by
  classical
  -- the integrand cut to `(t, T]`
  set g : Ω × ℝ × E → ℝ := fun p => Real.exp p.2.1 * ∑ k, U k p.2.1 p.1 p.2.2 ^ 2 with hgdef
  have hg0 : ∀ p, 0 ≤ g p := fun p =>
    mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun k _ => sq_nonneg _)
  set ψ : Ω × ℝ × E → ℝ := fun p => (Set.Ioc t T).indicator (fun _ => g p) p.2.1 with hψdef
  have hψ0 : ∀ p, 0 ≤ ψ p := fun p => Set.indicator_nonneg (fun _ _ => hg0 p) _
  have hψg : ∀ p, ψ p ≤ g p := fun p =>
    Set.indicator_le_self' (fun _ _ => hg0 p) p.2.1
  -- `ψ` is marked predictable
  have hF : Measurable fun q : ℝ × ℝ × (Fin m → ℝ) =>
      (Set.Ioc t T).indicator (fun s => Real.exp s) q.1 * ∑ k, q.2.2 k ^ 2 :=
    ((Real.measurable_exp.indicator measurableSet_Ioc).comp measurable_fst).mul
      (Finset.measurable_sum _ fun k _ => ((measurable_pi_apply k).comp
        measurable_snd.snd).pow_const 2)
  have hΓ : Probability.MarkedPredictable ℱ ν fun ω s e => (fun k => U k s ω e : Fin m → ℝ) := by
    unfold Probability.MarkedPredictable
    letI : MeasurableSpace (Ω × ℝ × E) := Probability.markedPredictableSigma ℱ ν
    exact measurable_pi_lambda _ fun k => hU k
  have hcomp := Probability.MarkedPredictable.comp_measurable (ν := ν) hF
    (Y := fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) measurable_const hΓ
  have hψm : Measurable[Probability.markedPredictableSigma ℱ ν] ψ := by
    have heq : ψ = fun p : Ω × ℝ × E => if 0 < p.2.1 then
        (Set.Ioc t T).indicator (fun s => Real.exp s) p.2.1 * ∑ k, U k p.2.1 p.1 p.2.2 ^ 2
        else 0 := by
      funext p
      by_cases hs : p.2.1 ∈ Set.Ioc t T
      · have hp : 0 < p.2.1 := lt_of_le_of_lt ht hs.1
        simp only [hψdef, hgdef, Set.indicator_of_mem hs, if_pos hp]
      · simp only [hψdef, Set.indicator_of_notMem hs, zero_mul, ite_self]
    rw [heq]
    exact hcomp
  have hψm' : Measurable ψ := hψm.mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  -- the `L¹` bound
  have hbound := lintegral_exp_mul_sum_sq_le hU hUv (P := P)
  have hfin0 : ENNReal.ofReal (Real.exp T)
      * ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.mpr fun k _ => (hUs k).lt_top)
  have hsub : Set.Ioc (0 : ℝ) T ⊆ Set.Icc (0 : ℝ) T := Set.Ioc_subset_Icc_self
  have hsubt : Set.Ioc t T ⊆ Set.Icc (0 : ℝ) T := fun s hs => ⟨ht.trans hs.1.le, hs.2⟩
  have hψfin : ∫⁻ ω, (∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (ψ (ω, s, e)) ∂ν) ∂P
      < ⊤ := by
    refine lt_of_le_of_lt ?_ (hbound.trans_lt hfin0)
    refine lintegral_mono fun ω => (lintegral_mono_set hsub).trans ?_
    exact lintegral_mono fun s => lintegral_mono fun e => ENNReal.ofReal_le_ofReal (hψg _)
  have hkey : ∀ x : ℝ, (0 < x ∧ x ≤ T) ∧ (t < x ∧ x ≤ T) ↔ t < x ∧ x ≤ T := fun x =>
    ⟨fun h => h.2, fun h => ⟨⟨ht.trans_lt h.1, h.2⟩, h⟩⟩
  -- the compensation formula for `ψ`
  have hcomp2 := (aemeasurable_and_lintegral_compensation (N := N) hℱN T
    (ψ := fun x => ENNReal.ofReal (ψ x)) (ENNReal.measurable_ofReal.comp hψm)).2.2
  have hN : ∀ ω, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ, ENNReal.ofReal (ψ (ω, p)) ∂(N.N ω)
      = ∫⁻ p in Set.Ioc t T ×ˢ Set.univ, ENNReal.ofReal (Real.exp p.1 * ∑ k, U k p.1 ω p.2 ^ 2)
        ∂(N.N ω) := by
    intro ω
    have he : (fun p : ℝ × E => ENNReal.ofReal (ψ (ω, p)))
        = (Set.Ioc t T ×ˢ (Set.univ : Set E)).indicator
          fun p => ENNReal.ofReal (Real.exp p.1 * ∑ k, U k p.1 ω p.2 ^ 2) := by
      funext p
      by_cases hs : p.1 ∈ Set.Ioc t T
      · rw [Set.indicator_of_mem (show p ∈ Set.Ioc t T ×ˢ (Set.univ : Set E) from
          ⟨hs, Set.mem_univ _⟩)]
        simp only [hψdef, hgdef, Set.indicator_of_mem hs]
      · rw [Set.indicator_of_notMem (show p ∉ Set.Ioc t T ×ˢ (Set.univ : Set E) from
          fun h => hs h.1)]
        simp only [hψdef, Set.indicator_of_notMem hs, ENNReal.ofReal_zero]
    rw [he, setLIntegral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]
    congr 2
    ext p
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true]
    first
      | exact hkey p.1
      | exact and_comm.trans (hkey p.1)
  have hNfin : ∫⁻ ω, ∫⁻ p in Set.Ioc t T ×ˢ Set.univ,
      ENNReal.ofReal (Real.exp p.1 * ∑ k, U k p.1 ω p.2 ^ 2) ∂(N.N ω) ∂P < ⊤ := by
    simp only [← hN]
    rw [hcomp2]
    exact hψfin
  refine ⟨hNfin, ?_, ?_⟩
  · refine lt_of_le_of_lt ?_ (hbound.trans_lt hfin0)
    exact lintegral_mono fun ω => lintegral_mono_set hsubt
  · have hz := integral_compensated_eq_zero (N := N) hℱN T hψm (by
      refine lt_of_le_of_lt (le_of_eq ?_) hψfin
      refine lintegral_congr fun ω => lintegral_congr fun s => lintegral_congr fun e => ?_
      exact Real.enorm_of_nonneg (hψ0 _))
    rw [← hz]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have hPN : ∫ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ, ψ (ω, p) ∂(N.N ω)
        = ∫ p in Set.Ioc t T ×ˢ Set.univ, Real.exp p.1 * ∑ k, U k p.1 ω p.2 ^ 2 ∂(N.N ω) := by
      have he : (fun p : ℝ × E => ψ (ω, p))
          = (Set.Ioc t T ×ˢ (Set.univ : Set E)).indicator
            fun p => Real.exp p.1 * ∑ k, U k p.1 ω p.2 ^ 2 := by
        funext p
        by_cases hs : p.1 ∈ Set.Ioc t T
        · rw [Set.indicator_of_mem (show p ∈ Set.Ioc t T ×ˢ (Set.univ : Set E) from
            ⟨hs, Set.mem_univ _⟩)]
          simp only [hψdef, hgdef, Set.indicator_of_mem hs]
        · rw [Set.indicator_of_notMem (show p ∉ Set.Ioc t T ×ˢ (Set.univ : Set E) from
            fun h => hs h.1)]
          simp only [hψdef, Set.indicator_of_notMem hs]
      rw [he, setIntegral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]
      congr 2
      ext p
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true]
      exact hkey p.1
    have hPC : ∫ s in Set.Ioc (0 : ℝ) T, ∫ e, ψ (ω, s, e) ∂ν
        = ∫ s in Set.Ioc t T, ∫ e, Real.exp s * ∑ k, U k s ω e ^ 2 ∂ν := by
      have he : (fun s => ∫ e, ψ (ω, s, e) ∂ν)
          = (Set.Ioc t T).indicator fun s => ∫ e, Real.exp s * ∑ k, U k s ω e ^ 2 ∂ν := by
        funext s
        by_cases hs : s ∈ Set.Ioc t T
        · simp only [hψdef, hgdef, Set.indicator_of_mem hs]
        · simp only [hψdef, Set.indicator_of_notMem hs, integral_zero]
      rw [he, setIntegral_indicator measurableSet_Ioc]
      congr 2
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc]
      exact hkey x
    dsimp only
    rw [hPN, hPC]

end Dissertation.WellPosedness.BrownianPoisson
