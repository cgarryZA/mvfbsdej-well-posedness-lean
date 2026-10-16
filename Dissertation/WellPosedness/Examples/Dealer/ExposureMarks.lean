/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Dissertation.WellPosedness.Examples.Dealer.Marks
import Dissertation.WellPosedness.Examples.Dealer.ExposureCoeffs

/-!
# Example 5.5: the exposure profile on the dealer mark space

On the mark space `E = {−1, +1} × (0, 1]` of the dealer market, with the mark measure
`ν(dς, dq) = c_ς q^{−1−ϱ} dς dq`, `c_ς ≥ 0`, a function of the mark integrates side by side:

`∫_E G(ς, q) ν(dς, dq) = c_{+1} ∫_0^1 q^{−1−ϱ} G(+1, q) dq + c_{−1} ∫_0^1 q^{−1−ϱ} G(−1, q) dq`.

For `ϱ < 2`, `∫_0^1 q^{1−ϱ} dq = 1/(2 − ϱ)`, so the size `h_x(ς, q) = q` lies in `L²(ν)`, and

`∫_E q² ν(dς, dq) = (c_{+1} + c_{−1}) / (2 − ϱ)`,
`∫_E ς q² ν(dς, dq) = (c_{+1} − c_{−1}) / (2 − ϱ)`.

With `c_{±1} = (2 − ϱ)/2` the signed size `h_c(ς, q) = ς q` and the size `h_x(ς, q) = q` are
orthonormal: `‖h_c‖_{L²(ν)} = ‖h_x‖_{L²(ν)} = 1` and `⟨h_x, h_c⟩_{L²(ν)} = 0`.

For every real profile `h_x ∈ L²(ν)` on any mark space, the exposure pairing inverts the exposure
operator up to `‖h_x‖²`: `⟨h_x, h_x x⟩_{L²(ν)} = ‖h_x‖² x`, and `‖h_x x‖_{L²(ν)} = ‖h_x‖ |x|`.
Hence on the dealer mark space, in dimension `n = 1` and with `c_{±1} = (2 − ϱ)/2`, the
cross term of `h_c + h_x x` vanishes and

`‖½ (h_c + h_x x)‖²_{L²(ν)} = ¼ (1 + |x|²)`,   `∫_E (ς q + q x)² ν(dς, dq) = 1 + x²`.

## Main definitions

* `dealerSize` — the size `h_x(ς, q) = q`, as an element of `L²(ν)`.

## Main statements

* `integral_dealerMarks_sides` — the integral against the mark measure, side by side.
* `integral_Ioc_rpow_one_sub`, `integral_Ioc_rpow_mul_sq` — `∫_0^1 q^{1−ϱ} dq = 1/(2 − ϱ)`.
* `integral_markSize_sq`, `integral_markSide_mul_sq` — `∫ q² dν` and `∫ ς q² dν`.
* `coeFn_dealerSize`, `coeFn_dealerJump` — the classes `dealerSize` and `dealerJump` as
  functions of the mark.
* `norm_dealerSize_sq`, `norm_dealerJump_sq`, `norm_dealerSize_eq_one`, `norm_dealerJump_eq_one` —
  `‖h_x‖² = ‖h_c‖² = (c_{+1} + c_{−1})/(2 − ϱ)`, which is `1` at `c_{±1} = (2 − ϱ)/2`.
* `exposurePair_dealerSize_dealerJump`, `exposurePair_dealerSize_dealerJump_eq_zero`,
  `inner_dealerJump_exposureOp_dealerSize` — `⟨h_x, h_c⟩_{L²(ν)}`, which vanishes at
  `c_{+1} = c_{−1}`.
* `exposurePair_exposureOp`, `norm_exposureOp_apply_sq` — `⟨h_x, h_x x⟩_{L²(ν)} = ‖h_x‖² x` and
  `‖h_x x‖² = ‖h_x‖² |x|²`, for any profile.
* `norm_half_smul_dealerJump_add_exposureOp_sq`, `integral_signedSize_add_mul_sq`,
  `integral_half_signedSize_add_mul_sq` — the energy of `½ (h_c + h_x x)`.
-/

open MeasureTheory Filter
open scoped ENNReal RealInnerProductSpace

namespace Dissertation.WellPosedness.Existence

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

/-- The side `ς ∈ {−1, +1}` of a mark has absolute value `1`. -/
theorem abs_markSide (b : Bool) : |markSide b| = 1 := by
  cases b <;> norm_num [markSide]

/-- **The size is square integrable**: `h_x(ς, q) = q` lies in `L²(ν)` for `ϱ < 2`. -/
theorem memLp_markSize (c : Bool → ℝ) {ϱ : ℝ} (hϱ : ϱ < 2) :
    MemLp (fun e : DealerMark => (e.2 : ℝ)) 2 (dealerMarks c ϱ) := by
  have hm : Measurable fun e : DealerMark => (e.2 : ℝ) := measurable_subtype_coe.comp measurable_snd
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  exact ⟨(hm.pow_const 2).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)).mpr
      (lintegral_sq_dealerMarks_lt_top c hϱ)⟩

/-- The size `h_x(ς, q) = q`, as an element of `L²(ν)`, for `ϱ < 2`. -/
noncomputable def dealerSize (c : Bool → ℝ) {ϱ : ℝ} (hϱ : ϱ < 2) : Lp ℝ 2 (dealerMarks c ϱ) :=
  (memLp_markSize c hϱ).toLp _

variable {c : Bool → ℝ} {ϱ : ℝ}

/-- The class `dealerSize` is the size `q` of the mark, `ν`-almost everywhere. -/
theorem coeFn_dealerSize (hϱ : ϱ < 2) :
    dealerSize c hϱ =ᵐ[dealerMarks c ϱ] fun e => (e.2 : ℝ) :=
  MemLp.coeFn_toLp _

/-- The class `dealerJump` is the signed size `ς q` of the mark in the coordinate of `ℝ¹`,
`ν`-almost everywhere. -/
theorem coeFn_dealerJump (hϱ : ϱ < 2) :
    dealerJump c hϱ =ᵐ[dealerMarks c ϱ] fun e => PiLp.single 2 (0 : Fin 1) (signedSize e) :=
  MemLp.coeFn_toLp _

/-- The squared size `q²` is integrable against `ν` for `ϱ < 2`. -/
theorem integrable_markSize_sq (c : Bool → ℝ) (hϱ : ϱ < 2) :
    Integrable (fun e : DealerMark => (e.2 : ℝ) ^ 2) (dealerMarks c ϱ) :=
  (memLp_markSize c hϱ).integrable_sq

/-- The signed squared size `ς q²` is integrable against `ν` for `ϱ < 2`. -/
theorem integrable_markSide_mul_sq (c : Bool → ℝ) (hϱ : ϱ < 2) :
    Integrable (fun e : DealerMark => markSide e.1 * (e.2 : ℝ) ^ 2) (dealerMarks c ϱ) := by
  refine (integrable_markSize_sq c hϱ).mono'
    (((measurable_of_countable markSide).comp measurable_fst).mul
      ((measurable_subtype_coe.comp measurable_snd).pow_const 2)).aestronglyMeasurable
    (Eventually.of_forall fun e => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_markSide, one_mul, abs_of_nonneg (sq_nonneg _)]

/-- **The second moment of the size**: for `c_ς ≥ 0` and `ϱ < 2`,
`∫_E q² ν(dς, dq) = (c_{+1} + c_{−1}) / (2 − ϱ)`. -/
theorem integral_markSize_sq (hc : ∀ b, 0 ≤ c b) (hϱ : ϱ < 2) :
    ∫ e, (e.2 : ℝ) ^ 2 ∂dealerMarks c ϱ = (c true + c false) / (2 - ϱ) := by
  rw [integral_dealerMarks_sides hc ϱ (g := fun _ x => x ^ 2) (integrable_markSize_sq c hϱ),
    integral_Ioc_rpow_mul_sq hϱ]
  ring

/-- **The signed second moment of the size**: for `c_ς ≥ 0` and `ϱ < 2`,
`∫_E ς q² ν(dς, dq) = (c_{+1} − c_{−1}) / (2 − ϱ)`. -/
theorem integral_markSide_mul_sq (hc : ∀ b, 0 ≤ c b) (hϱ : ϱ < 2) :
    ∫ e, markSide e.1 * (e.2 : ℝ) ^ 2 ∂dealerMarks c ϱ = (c true - c false) / (2 - ϱ) := by
  rw [integral_dealerMarks_sides hc ϱ (g := fun b x => markSide b * x ^ 2)
    (integrable_markSide_mul_sq c hϱ)]
  have e : ∀ b, ∫ x in Set.Ioc (0 : ℝ) 1, x ^ (-1 - ϱ) * (markSide b * x ^ 2)
      = markSide b * (1 / (2 - ϱ)) := fun b => by
    rw [← integral_Ioc_rpow_mul_sq hϱ, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have h1 : markSide true = 1 := by simp [markSide]
  have h2 : markSide false = -1 := by simp [markSide]
  rw [e, e, h1, h2]
  ring

/-! ### Norms and pairing -/

/-- **The norm of the size**: for `c_ς ≥ 0` and `ϱ < 2`,
`‖h_x‖²_{L²(ν)} = (c_{+1} + c_{−1}) / (2 − ϱ)`. -/
theorem norm_dealerSize_sq (hc : ∀ b, 0 ≤ c b) (hϱ : ϱ < 2) :
    ‖dealerSize c hϱ‖ ^ 2 = (c true + c false) / (2 - ϱ) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_markSize_sq hc hϱ]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_dealerSize (c := c) hϱ] with e he
  rw [real_inner_self_eq_norm_sq, he, Real.norm_eq_abs, sq_abs]

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

/-- **The size has unit norm**: with `c_{±1} = (2 − ϱ)/2`, `‖h_x‖_{L²(ν)} = 1`. -/
theorem norm_dealerSize_eq_one (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) :
    ‖dealerSize c hϱ‖ = 1 := by
  have h0 : ∀ b, 0 ≤ c b := fun b => by rw [hc]; linarith
  have h := norm_dealerSize_sq h0 hϱ
  rw [rate_sum_div_eq_one hϱ hc] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

/-- **The signed size has unit norm**: with `c_{±1} = (2 − ϱ)/2`, `‖h_c‖_{L²(ν; ℝ¹)} = 1`. -/
theorem norm_dealerJump_eq_one (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) :
    ‖dealerJump c hϱ‖ = 1 := by
  have h0 : ∀ b, 0 ≤ c b := fun b => by rw [hc]; linarith
  have h := norm_dealerJump_sq h0 hϱ
  rw [rate_sum_div_eq_one hϱ hc] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

/-- **The pairing of the size with the signed size**: for `c_ς ≥ 0` and `ϱ < 2`,
`⟨h_x, h_c⟩_{L²(ν)} = ∫_E q · ς q ν(dς, dq) = ((c_{+1} − c_{−1}) / (2 − ϱ)) e₀` in `ℝ¹`. -/
theorem exposurePair_dealerSize_dealerJump (hc : ∀ b, 0 ≤ c b) (hϱ : ϱ < 2) :
    exposurePair (dealerSize c hϱ) (dealerJump c hϱ)
      = ((c true - c false) / (2 - ϱ)) • PiLp.single 2 (0 : Fin 1) (1 : ℝ) := by
  rw [exposurePair_eq_integral, ← integral_markSide_mul_sq hc hϱ, ← integral_smul_const]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_dealerSize (c := c) hϱ, coeFn_dealerJump (c := c) hϱ] with e h1 h2
  rw [h1, h2, signedSize]
  ext i
  simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
  split_ifs <;> ring

/-- **The size and the signed size are orthogonal**: with `c_{±1} = (2 − ϱ)/2`,
`⟨h_x, h_c⟩_{L²(ν)} = 0`. -/
theorem exposurePair_dealerSize_dealerJump_eq_zero (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) :
    exposurePair (dealerSize c hϱ) (dealerJump c hϱ) = 0 := by
  have h0 : ∀ b, 0 ≤ c b := fun b => by rw [hc]; linarith
  rw [exposurePair_dealerSize_dealerJump h0 hϱ, hc, hc, sub_self, zero_div, zero_smul]

/-- **The cross term of the jump coefficient vanishes**: with `c_{±1} = (2 − ϱ)/2`,
`⟨h_c, h_x x⟩_{L²(ν; ℝ¹)} = 0` for every `x ∈ ℝ¹`. -/
theorem inner_dealerJump_exposureOp_dealerSize (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2)
    (x : EuclideanSpace ℝ (Fin 1)) : ⟪dealerJump c hϱ, exposureOp (dealerSize c hϱ) x⟫ = 0 := by
  rw [← inner_exposurePair, exposurePair_dealerSize_dealerJump_eq_zero hϱ hc, inner_zero_left]

/-! ### The exposure pairing against the exposure operator -/

section Exposure

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n : ℕ}

/-- **The exposure pairing against the exposure operator**: for every real profile
`h_x ∈ L²(ν)` and `x ∈ ℝⁿ`, `⟨h_x, h_x x⟩_{L²(ν)} = ‖h_x‖² x`. -/
theorem exposurePair_exposureOp (hx : Lp ℝ 2 ν) (x : EuclideanSpace ℝ (Fin n)) :
    exposurePair hx (exposureOp hx x) = ‖hx‖ ^ 2 • x := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_exposurePair, inner_exposureOp, real_inner_smul_left, ← real_inner_self_eq_norm_sq,
    L2.inner_def, ← integral_mul_const]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_exposureOp hx v] with e he
  rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  ring

/-- **The norm of the exposure operator at a point**: `‖h_x x‖²_{L²(ν)} = ‖h_x‖² |x|²`. -/
theorem norm_exposureOp_apply_sq (hx : Lp ℝ 2 ν) (x : EuclideanSpace ℝ (Fin n)) :
    ‖exposureOp hx x‖ ^ 2 = ‖hx‖ ^ 2 * ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← inner_exposurePair, exposurePair_exposureOp,
    real_inner_smul_left, real_inner_self_eq_norm_sq]

end Exposure

/-! ### The energy of the jump coefficient -/

/-- The class of `h_c + h_x x` is `(ς, q) ↦ ς q e₀ + q x`, `ν`-almost everywhere. -/
theorem coeFn_dealerJump_add_exposureOp (hϱ : ϱ < 2) (x : EuclideanSpace ℝ (Fin 1)) :
    (dealerJump c hϱ + exposureOp (dealerSize c hϱ) x : Lp (EuclideanSpace ℝ (Fin 1)) 2 _)
      =ᵐ[dealerMarks c ϱ] fun e => PiLp.single 2 (0 : Fin 1) (signedSize e) + (e.2 : ℝ) • x := by
  filter_upwards [Lp.coeFn_add (dealerJump c hϱ) (exposureOp (dealerSize c hϱ) x),
    coeFn_dealerJump (c := c) hϱ, coeFn_exposureOp (dealerSize c hϱ) x,
    coeFn_dealerSize (c := c) hϱ] with e h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, h3, h4]

/-- **The energy of the jump coefficient in `L²(ν)`**: in dimension `n = 1` with
`c_{±1} = (2 − ϱ)/2`, `‖½ (h_c + h_x x)‖²_{L²(ν; ℝ¹)} = ¼ (1 + |x|²)` for every `x ∈ ℝ¹`. -/
theorem norm_half_smul_dealerJump_add_exposureOp_sq (hϱ : ϱ < 2)
    (hc : ∀ b, c b = (2 - ϱ) / 2) (x : EuclideanSpace ℝ (Fin 1)) :
    ‖(1 / 2 : ℝ) • (dealerJump c hϱ + exposureOp (dealerSize c hϱ) x)‖ ^ 2
      = (1 + ‖x‖ ^ 2) / 4 := by
  rw [norm_smul, mul_pow, norm_add_sq_real, inner_dealerJump_exposureOp_dealerSize hϱ hc,
    norm_exposureOp_apply_sq, norm_dealerSize_eq_one hϱ hc, norm_dealerJump_eq_one hϱ hc,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  ring

/-- **The energy of the jump coefficient, over the marks**: with `c_{±1} = (2 − ϱ)/2`,
`∫_E (ς q + q r)² ν(dς, dq) = 1 + r²` for every `r ∈ ℝ`. -/
theorem integral_signedSize_add_mul_sq (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) (r : ℝ) :
    ∫ e, (signedSize e + (e.2 : ℝ) * r) ^ 2 ∂dealerMarks c ϱ = 1 + r ^ 2 := by
  have h0 : ∀ b, 0 ≤ c b := fun b => by rw [hc]; linarith
  have hpt : ∀ e : DealerMark, (signedSize e + (e.2 : ℝ) * r) ^ 2
      = (1 + r ^ 2) * (e.2 : ℝ) ^ 2 + 2 * r * (markSide e.1 * (e.2 : ℝ) ^ 2) := fun e => by
    have h := markSide_sq e.1
    rw [signedSize]
    linear_combination (e.2 : ℝ) ^ 2 * h
  simp_rw [hpt]
  rw [integral_add ((integrable_markSize_sq c hϱ).const_mul _)
      ((integrable_markSide_mul_sq c hϱ).const_mul _), integral_const_mul, integral_const_mul,
    integral_markSize_sq h0 hϱ, integral_markSide_mul_sq h0 hϱ, rate_sum_div_eq_one hϱ hc, hc,
    hc, sub_self, zero_div]
  ring

/-- **The energy of half the jump coefficient, over the marks**: with `c_{±1} = (2 − ϱ)/2`,
`∫_E (½ (ς q + q r))² ν(dς, dq) = ¼ (1 + r²)` for every `r ∈ ℝ`. -/
theorem integral_half_signedSize_add_mul_sq (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2)
    (r : ℝ) :
    ∫ e, ((signedSize e + (e.2 : ℝ) * r) / 2) ^ 2 ∂dealerMarks c ϱ = (1 + r ^ 2) / 4 := by
  simp_rw [div_pow]
  rw [integral_div, integral_signedSize_add_mul_sq hϱ hc r]
  norm_num

/-- The squared norm of a vector of `ℝ¹` is the square of its coordinate. -/
theorem norm_sq_euclidean_fin_one (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ ^ 2 = x 0 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_one]

end Dissertation.WellPosedness.Existence
