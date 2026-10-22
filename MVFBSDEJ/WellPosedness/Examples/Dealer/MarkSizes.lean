/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Examples.Dealer.Marks
import MVFBSDEJ.WellPosedness.Examples.Dealer.CrowdAffine

/-!
# Example 5.5: the sizes on the dealer mark space

On the mark space `E = {−1, +1} × (0, 1]` of the dealer market, with the mark measure
`ν(dς, dq) = c_ς q^{−1−ϱ} dς dq`, `c_ς ≥ 0`, a function of the mark integrates side by side:

`∫_E G(ς, q) ν(dς, dq) = c_{+1} ∫_0^1 q^{−1−ϱ} G(+1, q) dq + c_{−1} ∫_0^1 q^{−1−ϱ} G(−1, q) dq`.

For `ϱ < 2`, `∫_0^1 q^{1−ϱ} dq = 1/(2 − ϱ)`, so the size `q` lies in `L²(ν)` with
`∫_E q² ν(dς, dq) = (c_{+1} + c_{−1}) / (2 − ϱ)`, and the signed size `h_c(ς, q) = ς q` has
`‖h_c‖²_{L²(ν)} = (c_{+1} + c_{−1}) / (2 − ϱ)`, which is `1` at `c_{±1} = (2 − ϱ)/2`.

## Main statements

* `integral_dealerMarks_sides` — the integral against the mark measure, side by side.
* `integral_Ioc_rpow_one_sub`, `integral_Ioc_rpow_mul_sq` — `∫_0^1 q^{1−ϱ} dq = 1/(2 − ϱ)`.
* `memLp_markSize`, `integrable_markSize_sq`, `integral_markSize_sq` — the size `q` lies in
  `L²(ν)`, and `∫ q² dν`.
* `coeFn_dealerJump` — the class `dealerJump` as a function of the mark.
* `norm_dealerJump_sq`, `rate_sum_div_eq_one`, `norm_dealerJump_eq_one` —
  `‖h_c‖² = (c_{+1} + c_{−1})/(2 − ϱ)`, which is `1` at `c_{±1} = (2 − ϱ)/2`.
-/

open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace

namespace MVFBSDEJ.WellPosedness.Existence

/-! ### Integrals against the mark measure, side by side -/

/-- **The integral of an integrable function of the mark, side by side**: for `c_ς ≥ 0` and `g`
integrable against `ν`,
`∫_E g(ς, q) ν(dς, dq) = c_{+1} ∫_0^1 q^{−1−ϱ} g(+1, q) dq + c_{−1} ∫_0^1 q^{−1−ϱ} g(−1, q) dq`. -/
theorem integral_dealerMarks_sides {c : Bool → ℝ} (hc : ∀ b, 0 ≤ c b) (ϱ : ℝ)
    {g : Bool → ℝ → ℝ} (hg : Integrable (fun e : DealerMark => g e.1 e.2) (dealerMarks c ϱ)) :
    ∫ e, g e.1 e.2 ∂dealerMarks c ϱ
      = c true * (∫ x in Set.Ioc (0 : ℝ) 1, x ^ (-1 - ϱ) * g true x)
        + c false * ∫ x in Set.Ioc (0 : ℝ) 1, x ^ (-1 - ϱ) * g false x := by
  have hq : Measurable fun e : DealerMark => (e.2 : ℝ) := measurable_subtype_coe.comp measurable_snd
  have hf : Measurable fun e : DealerMark => ENNReal.ofReal (c e.1 * (e.2 : ℝ) ^ (-1 - ϱ)) :=
    (((measurable_of_countable c).comp measurable_fst).mul (hq.pow_const _)).ennreal_ofReal
  have hlt : ∀ᵐ e ∂(Measure.count.prod sizeLeb),
      ENNReal.ofReal (c e.1 * (e.2 : ℝ) ^ (-1 - ϱ)) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hρ : ∀ (b : Bool) (q : Set.Ioc (0 : ℝ) 1),
      (ENNReal.ofReal (c b * (q : ℝ) ^ (-1 - ϱ))).toReal = c b * (q : ℝ) ^ (-1 - ϱ) :=
    fun b q => ENNReal.toReal_ofReal (mul_nonneg (hc b) (Real.rpow_nonneg q.2.1.le _))
  have hint := (integrable_withDensity_iff_integrable_smul' hf hlt).mp hg
  have hside : ∀ b : Bool,
      ∫ q, (ENNReal.ofReal (c b * (q : ℝ) ^ (-1 - ϱ))).toReal • g b q ∂sizeLeb
        = c b * ∫ x in Set.Ioc (0 : ℝ) 1, x ^ (-1 - ϱ) * g b x := fun b => by
    have e : ∀ q : Set.Ioc (0 : ℝ) 1, (ENNReal.ofReal (c b * (q : ℝ) ^ (-1 - ϱ))).toReal • g b q
        = c b * ((q : ℝ) ^ (-1 - ϱ) * g b q) := fun q => by
      rw [hρ b q, smul_eq_mul, mul_assoc]
    simp_rw [e]
    rw [integral_const_mul]
    congr 1
    exact integral_subtype_comap measurableSet_Ioc (fun x => x ^ (-1 - ϱ) * g b x)
  rw [dealerMarks, integral_withDensity_eq_integral_toReal_smul hf hlt, integral_prod _ hint,
    integral_count, Fintype.sum_bool]
  exact congrArg₂ (· + ·) (hside true) (hside false)

/-! ### Powers on the unit interval -/

/-- **`∫_0^1 q^{1−ϱ} dq = 1/(2 − ϱ)` for `ϱ < 2`.** -/
theorem integral_Ioc_rpow_one_sub {ϱ : ℝ} (hϱ : ϱ < 2) :
    ∫ x in Set.Ioc (0 : ℝ) 1, x ^ (1 - ϱ) = 1 / (2 - ϱ) := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by linarith)),
    Real.one_rpow, Real.zero_rpow (by linarith : (0 : ℝ) < 1 - ϱ + 1).ne', sub_zero,
    show 1 - ϱ + 1 = 2 - ϱ by ring]

/-- **`∫_0^1 q^{−1−ϱ} q² dq = 1/(2 − ϱ)` for `ϱ < 2`.** -/
theorem integral_Ioc_rpow_mul_sq {ϱ : ℝ} (hϱ : ϱ < 2) :
    ∫ x in Set.Ioc (0 : ℝ) 1, x ^ (-1 - ϱ) * x ^ 2 = 1 / (2 - ϱ) := by
  rw [← integral_Ioc_rpow_one_sub hϱ]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_add hx.1]
  congr 1
  push_cast
  ring

/-! ### The size and the signed size -/

/-- **The size is square integrable**: `(ς, q) ↦ q` lies in `L²(ν)` for `ϱ < 2`. -/
theorem memLp_markSize (c : Bool → ℝ) {ϱ : ℝ} (hϱ : ϱ < 2) :
    MemLp (fun e : DealerMark => (e.2 : ℝ)) 2 (dealerMarks c ϱ) := by
  have hm : Measurable fun e : DealerMark => (e.2 : ℝ) := measurable_subtype_coe.comp measurable_snd
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  exact ⟨(hm.pow_const 2).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)).mpr
      (lintegral_sq_dealerMarks_lt_top c hϱ)⟩

variable {c : Bool → ℝ} {ϱ : ℝ}

/-- The class `dealerJump` is the signed size `ς q` of the mark in the coordinate of `ℝ¹`,
`ν`-almost everywhere. -/
theorem coeFn_dealerJump (hϱ : ϱ < 2) :
    dealerJump c hϱ =ᵐ[dealerMarks c ϱ] fun e => PiLp.single 2 (0 : Fin 1) (signedSize e) :=
  MemLp.coeFn_toLp _

/-- The squared size `q²` is integrable against `ν` for `ϱ < 2`. -/
theorem integrable_markSize_sq (c : Bool → ℝ) (hϱ : ϱ < 2) :
    Integrable (fun e : DealerMark => (e.2 : ℝ) ^ 2) (dealerMarks c ϱ) :=
  (memLp_markSize c hϱ).integrable_sq

/-- **The second moment of the size**: for `c_ς ≥ 0` and `ϱ < 2`,
`∫_E q² ν(dς, dq) = (c_{+1} + c_{−1}) / (2 − ϱ)`. -/
theorem integral_markSize_sq (hc : ∀ b, 0 ≤ c b) (hϱ : ϱ < 2) :
    ∫ e, (e.2 : ℝ) ^ 2 ∂dealerMarks c ϱ = (c true + c false) / (2 - ϱ) := by
  rw [integral_dealerMarks_sides hc ϱ (g := fun _ x => x ^ 2) (integrable_markSize_sq c hϱ),
    integral_Ioc_rpow_mul_sq hϱ]
  ring

/-! ### Norms and pairing -/

/-- **The norm of the signed size**: for `c_ς ≥ 0` and `ϱ < 2`,
`‖h_c‖²_{L²(ν; ℝ¹)} = (c_{+1} + c_{−1}) / (2 − ϱ)`. -/
theorem norm_dealerJump_sq (hc : ∀ b, 0 ≤ c b) (hϱ : ϱ < 2) :
    ‖dealerJump c hϱ‖ ^ 2 = (c true + c false) / (2 - ϱ) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_markSize_sq hc hϱ]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_dealerJump (c := c) hϱ] with e he
  rw [real_inner_self_eq_norm_sq, he, PiLp.norm_single, signedSize, Real.norm_eq_abs, sq_abs,
    mul_pow, markSide_sq, one_mul]

/-- With `c_{±1} = (2 − ϱ)/2`, `(c_{+1} + c_{−1}) / (2 − ϱ) = 1`. -/
theorem rate_sum_div_eq_one (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) :
    (c true + c false) / (2 - ϱ) = 1 := by
  rw [hc, hc, add_halves, div_self (sub_pos.mpr hϱ).ne']

/-- **The signed size has unit norm**: with `c_{±1} = (2 − ϱ)/2`, `‖h_c‖_{L²(ν; ℝ¹)} = 1`. -/
theorem norm_dealerJump_eq_one (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) :
    ‖dealerJump c hϱ‖ = 1 := by
  have h0 : ∀ b, 0 ≤ c b := fun b => by rw [hc]; linarith
  have h := norm_dealerJump_sq h0 hϱ
  rw [rate_sum_div_eq_one hϱ hc] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

/-- **The second moment of the signed size**: for `c_ς ≥ 0` and `ϱ < 2`,
`∫_E (ς q)² ν(dς, dq) = (c_{+1} + c_{−1}) / (2 − ϱ)`. -/
theorem integral_signedSize_sq (hc : ∀ b, 0 ≤ c b) (hϱ : ϱ < 2) :
    ∫ e, signedSize e ^ 2 ∂dealerMarks c ϱ = (c true + c false) / (2 - ϱ) := by
  simp_rw [signedSize, mul_pow, markSide_sq, one_mul]
  exact integral_markSize_sq hc hϱ

/-- **The pairing of the signed size with the size**: for `c_ς ≥ 0` and `ϱ < 2`,
`∫_E ς q · q ν(dς, dq) = (c_{+1} − c_{−1}) / (2 − ϱ)`. -/
theorem integral_signedSize_mul_markSize (hc : ∀ b, 0 ≤ c b) (hϱ : ϱ < 2) :
    ∫ e, signedSize e * (e.2 : ℝ) ∂dealerMarks c ϱ = (c true - c false) / (2 - ϱ) := by
  have hm : Measurable fun e : DealerMark => signedSize e * (e.2 : ℝ) :=
    (((measurable_of_countable markSide).comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd)).mul
      (measurable_subtype_coe.comp measurable_snd)
  have hi : Integrable (fun e : DealerMark => markSide e.1 * (e.2 : ℝ) * e.2)
      (dealerMarks c ϱ) := by
    refine (integrable_markSize_sq c hϱ).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun e => ?_)
    have h1 : |markSide e.1| = 1 := by cases e.1 <;> norm_num [markSide]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, h1, one_mul, ← sq, sq_abs]
  rw [show (fun e : DealerMark => signedSize e * (e.2 : ℝ))
      = fun e => markSide e.1 * (e.2 : ℝ) * e.2 from rfl,
    integral_dealerMarks_sides hc ϱ (g := fun b x => markSide b * x * x) hi]
  have e1 : ∀ b, (fun x : ℝ => x ^ (-1 - ϱ) * (markSide b * x * x))
      = fun x => markSide b * (x ^ (-1 - ϱ) * x ^ 2) := fun b => funext fun x => by ring
  rw [e1, e1, integral_const_mul, integral_const_mul, integral_Ioc_rpow_mul_sq hϱ]
  have h1 : markSide true = 1 := rfl
  have h2 : markSide false = -1 := rfl
  rw [h1, h2]
  ring

end MVFBSDEJ.WellPosedness.Existence
