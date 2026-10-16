/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Analysis.GronwallIntegral
import LevyStochCalc.Ito.SecondMoment
import Dissertation.WellPosedness.Examples.Dealer.ExposureSDE

/-!
# Example 5.5: the moments of the exposure process

Let `X⁰` solve the exposure equation of Example 5.5 of the well-posedness paper,

`X⁰_t = ∫_0^t (−X⁰_s ds + ½ dW_s) + ½ ∫_0^t ∫_E (ς q + q X⁰_s) Ñ(ds, dς, dq)`,   `X⁰_0 = 0`,

on the dealer mark space with `c_{±1} = (2 − ϱ)/2`, `ϱ < 2`, over a filtration carrying the
driver which admits a cross witness. Frozen at the horizon, `X⁰ + a` is an Itô–Lévy process for
every constant `a`, and the expectation form of the quadratic Itô formula gives, for
`t ∈ (0, T]`,

`𝔼 (X⁰_t + a)² = a² + ∫_0^t (−2 𝔼[(X⁰_s + a) X⁰_s] + ¼ + ¼ (1 + 𝔼 |X⁰_s|²)) ds`,

since the diffusion contributes `¼` and, by `∫_E (ς q + q x)² ν(dς, dq) = 1 + x²`, the jumps
contribute `¼ (1 + 𝔼 |X⁰_s|²)`. At `a = 0` and `a = 1` this gives, with `v(t) = 𝔼 |X⁰_t|²` and
`m(t) = 𝔼 X⁰_t`,

`v(t) = ∫_0^t (−(7/4) v(s) + ½) ds`,   `m(t) = −∫_0^t m(s) ds`,

so by Grönwall `m = 0` and `v(t) = (2/7) (1 − e^{−7t/4})` on `[0, T]`; in particular
`v(t) > 0` for `t ∈ (0, T]`.

## Main statements

* `integral_half_signedSize_add_mul_sq_lintegral` — `∫_E (½ (ς q + q r))² ν(dς, dq) = ¼ (1 + r²)`
  as an extended integral.
* `integral_add_mul_self_exposure` — the second moment of `X⁰ + a`.
* `integral_mul_self_exposure_eq_setIntegral` — `v(t) = ∫_0^t (−(7/4) v(s) + ½) ds`.
* `integral_exposure_eq_neg_setIntegral`, `integral_exposure_eq_zero` — `m(t) = −∫_0^t m`, and
  `m = 0`.
* `integral_mul_self_exposure_eq` — `v(t) = (2/7) (1 − e^{−7t/4})`.
* `integral_mul_self_exposure_pos` — `v(t) > 0` for `t ∈ (0, T]`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.Stability LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u w

/-! ### The jump energy over the marks -/

variable {c : Bool → ℝ} {ϱ : ℝ}

/-- The squared jump integrand `(½ (ς q + q r))²` is integrable against the mark measure. -/
theorem integrable_half_signedSize_add_mul_sq (hϱ : ϱ < 2) (r : ℝ) :
    Integrable (fun e : DealerMark => ((signedSize e + (e.2 : ℝ) * r) / 2) ^ 2)
      (dealerMarks c ϱ) := by
  have hpt : ∀ e : DealerMark, ((signedSize e + (e.2 : ℝ) * r) / 2) ^ 2
      = (1 + r ^ 2) / 4 * (e.2 : ℝ) ^ 2 + r / 2 * (markSide e.1 * (e.2 : ℝ) ^ 2) := fun e => by
    have h := markSide_sq e.1
    rw [signedSize]
    linear_combination (e.2 : ℝ) ^ 2 / 4 * h
  simp_rw [hpt]
  exact ((integrable_markSize_sq c hϱ).const_mul _).add
    ((integrable_markSide_mul_sq c hϱ).const_mul _)

/-- **The energy of half the jump coefficient over the marks, as an extended integral**: with
`c_{±1} = (2 − ϱ)/2`, `∫_E (½ (ς q + q r))² ν(dς, dq) = ¼ (1 + r²)`. -/
theorem integral_half_signedSize_add_mul_sq_lintegral (hϱ : ϱ < 2)
    (hc : ∀ b, c b = (2 - ϱ) / 2) (r : ℝ) :
    ∫⁻ e, ENNReal.ofReal (((signedSize e + (e.2 : ℝ) * r) / 2) ^ 2) ∂dealerMarks c ϱ
      = ENNReal.ofReal ((1 + r ^ 2) / 4) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_half_signedSize_add_mul_sq hϱ r)
    (Eventually.of_forall fun _ => sq_nonneg _), integral_half_signedSize_add_mul_sq hϱ hc r]

/-! ### Grönwall -/

/-- A function integrable on `[0, T]` with `f(t) = −k ∫_0^t f` on `[0, T]`, `k ≥ 0`, vanishes
there. -/
theorem eq_zero_of_eq_neg_mul_setIntegral {f : ℝ → ℝ} {k T : ℝ} (hk : 0 ≤ k)
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T))
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, f t = -k * ∫ s in Set.Icc (0 : ℝ) t, f s) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, f t = 0 := by
  have hle : ∀ t ∈ Set.Icc (0 : ℝ) T, |f t| ≤ k * ∫ s in Set.Icc (0 : ℝ) t, |f s| := by
    intro t ht
    rw [h t ht, abs_mul, abs_neg, abs_of_nonneg hk]
    exact mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs) hk
  have hB : ∀ t ∈ Set.Icc (0 : ℝ) T, |f t| ≤ k * ∫ s in Set.Icc (0 : ℝ) T, |f s| := by
    intro t ht
    refine (hle t ht).trans (mul_le_mul_of_nonneg_left ?_ hk)
    exact setIntegral_mono_set hf.abs (Eventually.of_forall fun _ => abs_nonneg _)
      (Set.Icc_subset_Icc le_rfl ht.2).eventuallyLE
  have h0 := LevyStochCalc.Analysis.eq_zero_of_le_mul_setIntegral hk hf.1.norm
    (fun t => abs_nonneg (f t)) hB (fun t ht => by
      rw [← integral_Icc_eq_integral_Ioc]
      exact hle t ht)
  exact fun t ht => abs_eq_zero.mp (h0 t ht)

/-- **The closed form of the second moment**: `φ(t) = (2/7) (1 − e^{−7t/4})` satisfies
`φ(t) = ∫_0^t (−(7/4) φ(s) + ½) ds` for `t ≥ 0`. -/
theorem setIntegral_exposureVariance {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Set.Icc (0 : ℝ) t, (-(7 / 4) * (2 / 7 * (1 - Real.exp (-(7 / 4) * s))) + 1 / 2)
      = 2 / 7 * (1 - Real.exp (-(7 / 4) * t)) := by
  have hF : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (fun s => -(2 / 7) * Real.exp (-(7 / 4) * s))
      (-(7 / 4) * (2 / 7 * (1 - Real.exp (-(7 / 4) * x))) + 1 / 2) x := by
    intro x _
    have h := (((hasDerivAt_id' x).const_mul (-(7 / 4 : ℝ))).exp).const_mul (-(2 / 7 : ℝ))
    exact h.congr_deriv (by ring)
  have hi : IntervalIntegrable
      (fun s => -(7 / 4) * (2 / 7 * (1 - Real.exp (-(7 / 4) * s))) + 1 / 2) volume 0 t :=
    (by fun_prop : Continuous fun s : ℝ =>
      -(7 / 4) * (2 / 7 * (1 - Real.exp (-(7 / 4) * s))) + 1 / 2).intervalIntegrable _ _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hF hi, mul_zero, Real.exp_zero]
  ring

/-! ### The moments -/

section Moments

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (dealerMarks c ϱ)}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {X : ℝ → Ω → ℝ}

/-- Frozen at the horizon and shifted by a constant `a`, a solution of the exposure equation is
an Itô–Lévy process started at `X_0 + a`. -/
theorem isItoLevyProcess_exposure_add_const
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) (hT : 0 < T) (a : ℝ) :
    Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN (fun t ω => clampT T X t ω + a)
      (fun ω => X 0 ω + a) (fun s ω => exposureDrift T X ω s) (exposureDiffusion Ω T)
      (fun ω s e => exposureJump T X s ω e) := by
  have h := hX.isItoLevyProcess_clampT hT
  exact { h with
    measurable_path := h.measurable_path.add_const a
    decomposition := fun t ht => (h.decomposition t ht).mono fun ω hω => by
      rw [hω]
      ring }

/-- A solution of the exposure equation is square integrable at every time of the horizon. -/
theorem memLp_exposure
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) (hT : 0 < T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) : MemLp (X t) 2 P := by
  have hX0 : (fun ω => X 0 ω + 0) =ᵐ[P] fun _ => (0 : ℝ) :=
    (hX.initial_ae_eq hT.le).mono fun ω hω => by simp only [hω, add_zero]
  have h := Ito.SecondMoment.memLp_two_of_isItoLevyProcess
    (isItoLevyProcess_exposure_add_const hX hT 0) ((memLp_const (0 : ℝ)).ae_eq hX0.symm)
    hX.b_meas (fun T' _ => drift_sq_int_global hX.b_vanish hX.b_sq T') ht.1
  simpa only [add_zero, clampT_apply_of_le ht.2] using h

/-- **The second moment of the shifted exposure process.** For a solution `X` of the exposure
equation over a filtration admitting a cross witness, with `c_{±1} = (2 − ϱ)/2`, every constant
`a` and `t ∈ (0, T]`,

`𝔼 (X_t + a)² = a² + ∫_0^t (−2 𝔼[(X_s + a) X_s] + ½ + ¼ 𝔼 |X_s|²) ds`. -/
theorem integral_add_mul_self_exposure (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2)
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    (a : ℝ) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T) :
    ∫ ω, (X t ω + a) * (X t ω + a) ∂P
      = a ^ 2 + ∫ s in Set.Icc (0 : ℝ) t,
          (-2 * ∫ ω, (X s ω + a) * X s ω ∂P + 1 / 2 + 1 / 4 * ∫ ω, X s ω * X s ω ∂P) := by
  have hI := isItoLevyProcess_exposure_add_const hX hT a
  have h0m : StronglyMeasurable[ℱ 0] (fun ω => X 0 ω + a) :=
    ((hX.X_adapted 0).add_const a).stronglyMeasurable
  have hX0 : (fun ω => X 0 ω + a) =ᵐ[P] fun _ => a :=
    (hX.initial_ae_eq hT.le).mono fun ω hω => by simp only [hω, zero_add]
  have h02 : MemLp (fun ω => X 0 ω + a) 2 P := (memLp_const a).ae_eq hX0.symm
  have key := Ito.SecondMoment.integral_mul_self_eq_add_setIntegral hI 𝒲 h0m h02 hX.b_meas
    hX.b_prog (fun T' _ => drift_sq_int_global hX.b_vanish hX.b_sq T') ht0
  simp only [clampT_apply_of_le htT] at key
  rw [key]
  congr 1
  · rw [integral_congr_ae (g := fun _ => a * a) (hX0.mono fun ω hω => by simp only [hω])]
    simp [sq]
  · refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    have hsI : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans htT⟩
    have hmem := memLp_exposure hX hT hsI
    have hσ : ∑ j : Fin 1, (∫⁻ ω, (‖exposureDiffusion Ω T s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
        = 1 / 4 := by
      simp only [exposureDiffusion, Set.indicator_of_mem hsI, Finset.univ_unique,
        Finset.sum_singleton, lintegral_const, measure_univ, mul_one,
        Ito.Picard.sq_coe_nnnorm_real]
      rw [ENNReal.toReal_ofReal (by positivity)]
      norm_num
    have hγ : (∫⁻ ω, ∫⁻ e, (‖exposureJump T X s ω e‖₊ : ℝ≥0∞) ^ 2 ∂dealerMarks c ϱ ∂P).toReal
        = 1 / 4 + 1 / 4 * ∫ ω, X s ω * X s ω ∂P := by
      have hin : ∀ ω, ∫⁻ e, (‖exposureJump T X s ω e‖₊ : ℝ≥0∞) ^ 2 ∂dealerMarks c ϱ
          = ENNReal.ofReal ((1 + X s ω ^ 2) / 4) := fun ω => by
        simp only [exposureJump, Set.indicator_of_mem hsI, Ito.Picard.sq_coe_nnnorm_real]
        exact integral_half_signedSize_add_mul_sq_lintegral hϱ hc (X s ω)
      have hint : Integrable (fun ω => (1 + X s ω ^ 2) / 4) P :=
        ((integrable_const 1).add hmem.integrable_sq).div_const 4
      rw [lintegral_congr hin, ← ofReal_integral_eq_lintegral_ofReal hint
        (Eventually.of_forall fun ω => by positivity),
        ENNReal.toReal_ofReal (integral_nonneg fun ω => by positivity), integral_div,
        integral_add (integrable_const 1) hmem.integrable_sq]
      simp only [integral_const, probReal_univ, one_smul, sq]
      ring
    have hb : ∫ ω, (X s ω + a) * exposureDrift T X ω s ∂P
        = -∫ ω, (X s ω + a) * X s ω ∂P := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [exposureDrift, Set.indicator_of_mem hsI]
      ring
    simp only [clampT_apply_of_le hsI.2]
    rw [hb, hσ, hγ]
    ring

/-- **The second moment of the exposure process solves a linear integral equation**:
`v(t) = ∫_0^t (−(7/4) v(s) + ½) ds` on `[0, T]`, with `v(t) = 𝔼 |X_t|²`. -/
theorem integral_mul_self_exposure_eq_setIntegral (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2)
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ ω, X t ω * X t ω ∂P
      = ∫ s in Set.Icc (0 : ℝ) t, (-(7 / 4) * ∫ ω, X s ω * X s ω ∂P + 1 / 2) := by
  rcases ht.1.eq_or_lt with h0 | h0
  · subst h0
    rw [Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
      integral_zero_measure]
    rw [integral_congr_ae (g := fun _ => (0 : ℝ))
      ((hX.initial_ae_eq hT.le).mono fun ω hω => by simp only [hω, mul_zero]), integral_zero]
  · have h := integral_add_mul_self_exposure hϱ hc hX 𝒲 hT 0 h0 ht.2
    simp only [add_zero] at h
    rw [h]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
    refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    ring

/-- The second moment of the exposure process is integrable on the horizon. -/
theorem integrableOn_integral_mul_self_exposure
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) :
    IntegrableOn (fun s => ∫ ω, X s ω * X s ω ∂P) (Set.Icc (0 : ℝ) T) := by
  have hX0 : (fun ω => X 0 ω + 0) =ᵐ[P] fun _ => (0 : ℝ) :=
    (hX.initial_ae_eq hT.le).mono fun ω hω => by simp only [hω, add_zero]
  have h := Ito.SecondMoment.integrableOn_integral_mul_self
    (isItoLevyProcess_exposure_add_const hX hT 0) 𝒲
    ((hX.X_adapted 0).add_const 0).stronglyMeasurable ((memLp_const (0 : ℝ)).ae_eq hX0.symm)
    hX.b_meas hX.b_prog (fun T' _ => drift_sq_int_global hX.b_vanish hX.b_sq T') hT
  refine h.congr_fun (fun s hs => ?_) measurableSet_Icc
  simp only [add_zero, clampT_apply_of_le hs.2]

/-- The mean of the exposure process is integrable on the horizon. -/
theorem integrableOn_integral_exposure
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) (hT : 0 < T) :
    IntegrableOn (fun s => ∫ ω, X s ω ∂P) (Set.Icc (0 : ℝ) T) := by
  have hbq := fun T' (_ : 0 < T') => drift_sq_int_global hX.b_vanish hX.b_sq T'
  have h02 : ∀ a : ℝ, MemLp (fun ω => X 0 ω + a) 2 P := fun a => by
    have hX0 : (fun ω => X 0 ω + a) =ᵐ[P] fun _ => a :=
      (hX.initial_ae_eq hT.le).mono fun ω hω => by simp only [hω, zero_add]
    exact (memLp_const a).ae_eq hX0.symm
  have h1 := Ito.SecondMoment.integrableOn_integral_mul_drift
    (isItoLevyProcess_exposure_add_const hX hT 1) (h02 1) hX.b_meas hX.b_prog hbq hT
  have h0 := Ito.SecondMoment.integrableOn_integral_mul_drift
    (isItoLevyProcess_exposure_add_const hX hT 0) (h02 0) hX.b_meas hX.b_prog hbq hT
  refine (h0.sub h1).congr_fun (fun s hs => ?_) measurableSet_Icc
  have hmem := memLp_exposure hX hT hs
  simp only [Pi.sub_apply, clampT_apply_of_le hs.2, exposureDrift, Set.indicator_of_mem hs,
    add_zero]
  have i1 : Integrable (fun ω => X s ω * -X s ω) P := hmem.integrable_mul hmem.neg
  have i2 : Integrable (fun ω => (X s ω + 1) * -X s ω) P :=
    (hmem.add (memLp_const 1)).integrable_mul hmem.neg
  rw [← integral_sub i1 i2]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [Pi.neg_apply, Pi.add_apply]
  ring

/-- **The mean of the exposure process solves `m(t) = −∫_0^t m(s) ds`** on `[0, T]`. -/
theorem integral_exposure_eq_neg_setIntegral (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2)
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ ω, X t ω ∂P = -1 * ∫ s in Set.Icc (0 : ℝ) t, ∫ ω, X s ω ∂P := by
  rcases ht.1.eq_or_lt with h0 | h0
  · subst h0
    rw [Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
      integral_zero_measure, mul_zero]
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (hX.initial_ae_eq hT.le), integral_zero]
  · have htI : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
    have h1 := integral_add_mul_self_exposure hϱ hc hX 𝒲 hT 1 h0 ht.2
    have h0' := integral_mul_self_exposure_eq_setIntegral hϱ hc hX 𝒲 hT ht
    have hv := (integrableOn_integral_mul_self_exposure hX 𝒲 hT).mono_set htI
    have hm := (integrableOn_integral_exposure hX hT).mono_set htI
    have hmem := memLp_exposure hX hT ht
    have hsq : ∫ ω, (X t ω + 1) * (X t ω + 1) ∂P
        = ∫ ω, X t ω * X t ω ∂P + 2 * ∫ ω, X t ω ∂P + 1 := by
      have e : (fun ω => (X t ω + 1) * (X t ω + 1))
          = fun ω => (X t ω * X t ω + 2 * X t ω) + 1 := by funext ω; ring
      have i1 : Integrable (fun ω => X t ω * X t ω) P := hmem.integrable_mul hmem
      have i2 : Integrable (fun ω => 2 * X t ω) P := (hmem.integrable one_le_two).const_mul 2
      have i12 : Integrable (fun ω => X t ω * X t ω + 2 * X t ω) P := i1.add i2
      rw [e, integral_add i12 (integrable_const 1), integral_add i1 i2, integral_const_mul]
      simp only [integral_const, probReal_univ, one_smul]
    have hrate : ∫ s in Set.Icc (0 : ℝ) t,
        (-2 * ∫ ω, (X s ω + 1) * X s ω ∂P + 1 / 2 + 1 / 4 * ∫ ω, X s ω * X s ω ∂P)
        = (∫ s in Set.Icc (0 : ℝ) t, (-(7 / 4) * ∫ ω, X s ω * X s ω ∂P + 1 / 2))
          - 2 * ∫ s in Set.Icc (0 : ℝ) t, ∫ ω, X s ω ∂P := by
      have hA : IntegrableOn (fun s => -(7 / 4) * ∫ ω, X s ω * X s ω ∂P + 1 / 2)
          (Set.Icc (0 : ℝ) t) := (hv.const_mul _).add (integrableOn_const
            (by simp [Real.volume_Icc]))
      have hB : IntegrableOn (fun s => 2 * ∫ ω, X s ω ∂P) (Set.Icc (0 : ℝ) t) := hm.const_mul 2
      rw [← integral_const_mul, ← integral_sub hA hB]
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      have hms := memLp_exposure hX hT (htI hs)
      have e : (fun ω => (X s ω + 1) * X s ω) = fun ω => X s ω * X s ω + X s ω := by
        funext ω; ring
      have i1 : Integrable (fun ω => X s ω * X s ω) P := hms.integrable_mul hms
      have i2 : Integrable (fun ω => X s ω) P := hms.integrable one_le_two
      rw [e, integral_add i1 i2]
      ring
    rw [hsq, hrate, ← h0'] at h1
    linarith

/-- **The exposure process has mean zero**: `𝔼 X_t = 0` for `t ∈ [0, T]`. -/
theorem integral_exposure_eq_zero (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2)
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) : ∫ ω, X t ω ∂P = 0 :=
  eq_zero_of_eq_neg_mul_setIntegral zero_le_one (integrableOn_integral_exposure hX hT)
    (fun _ hs => integral_exposure_eq_neg_setIntegral hϱ hc hX 𝒲 hT hs) t ht

/-- **The second moment of the exposure process**: `𝔼 |X_t|² = (2/7) (1 − e^{−7t/4})` for
`t ∈ [0, T]`. -/
theorem integral_mul_self_exposure_eq (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2)
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ ω, X t ω * X t ω ∂P = 2 / 7 * (1 - Real.exp (-(7 / 4) * t)) := by
  have hφi : IntegrableOn (fun s => 2 / 7 * (1 - Real.exp (-(7 / 4) * s))) (Set.Icc (0 : ℝ) T) :=
    (by fun_prop : Continuous fun s : ℝ => 2 / 7 * (1 - Real.exp (-(7 / 4) * s))).integrableOn_Icc
  have hv := integrableOn_integral_mul_self_exposure hX 𝒲 hT
  have h := eq_zero_of_eq_neg_mul_setIntegral
    (f := fun s => ∫ ω, X s ω * X s ω ∂P - 2 / 7 * (1 - Real.exp (-(7 / 4) * s)))
    (k := 7 / 4) (by norm_num) (hv.sub hφi) (fun s hs => by
      have htI : Set.Icc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl hs.2
      have hA : IntegrableOn (fun r => -(7 / 4) * ∫ ω, X r ω * X r ω ∂P + 1 / 2)
          (Set.Icc (0 : ℝ) s) :=
        ((hv.mono_set htI).const_mul _).add (integrableOn_const (by simp [Real.volume_Icc]))
      have hB : IntegrableOn
          (fun r => -(7 / 4) * (2 / 7 * (1 - Real.exp (-(7 / 4) * r))) + 1 / 2)
          (Set.Icc (0 : ℝ) s) :=
        ((hφi.mono_set htI).const_mul _).add (integrableOn_const (by simp [Real.volume_Icc]))
      rw [integral_mul_self_exposure_eq_setIntegral hϱ hc hX 𝒲 hT hs,
        ← setIntegral_exposureVariance hs.1, ← integral_sub hA hB, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
      ring) t ht
  linarith

/-- **The exposure process is not degenerate**: `𝔼 |X_t|² > 0` for `t ∈ (0, T]`. -/
theorem integral_mul_self_exposure_pos (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2)
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) T) : 0 < ∫ ω, X t ω * X t ω ∂P := by
  rw [integral_mul_self_exposure_eq hϱ hc hX 𝒲 hT (Set.Ioc_subset_Icc_self ht)]
  have : Real.exp (-(7 / 4) * t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [ht.1])
  nlinarith

end Moments

end Dissertation.WellPosedness.Existence
