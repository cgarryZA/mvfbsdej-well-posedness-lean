/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import MVFBSDEJ.WellPosedness.Examples.Dealer.Monotone
import MVFBSDEJ.WellPosedness.Existence.GlobalEnl
import MVFBSDEJ.WellPosedness.Robustness.Corollary
import MVFBSDEJ.WellPosedness.System.PaperUniquenessInt
import LevyStochCalc.Driver.GaussianInitial

/-!
# Example 5.5: the mark space of the dealer market

The mark `e = (ς, q)` of a request for quote records its side `ς ∈ {−1, +1}` and its size
`q ∈ (0, 1]`. The mark space `E = {−1, +1} × (0, 1]` is realised as `Bool × (0, 1]`, the side
`true` standing for `+1` and `false` for `−1`, with the product of the discrete σ-algebra and the
Borel σ-algebra of the subtype `(0, 1] ⊆ ℝ`; it is countably generated and nonempty. For
constants `c_ς` and `ϱ`, the mark measure of Example 5.5 of the well-posedness paper is

`ν(dς, dq) = c_ς q^{−1−ϱ} dς dq`,

the density `c_ς q^{−1−ϱ}` against counting measure on the sides times Lebesgue measure on the
sizes. It is σ-finite, and for a function `G` of the size alone,

`∫_E G(q) ν(dς, dq) = (c_{+1} + c_{−1}) ∫_0^1 G(q) q^{−1−ϱ} dq`   (`c_ς ≥ 0`).

Since `q ↦ q^s` is integrable on `(0, 1)` exactly when `s > −1`, for `c_ς > 0` and `ϱ ≥ 0` the
total mass is infinite, `ν(E) = ∞`, while for `ϱ < 2` the aggregate size is square integrable,
`∫_E q² ν(dς, dq) = (c_{+1} + c_{−1}) ∫_0^1 q^{1−ϱ} dq < ∞`; so the signed size
`h_c(ς, q) = ς q` lies in `L²(ν)`.

## Main definitions

* `DealerMark` — the mark space `{−1, +1} × (0, 1]`.
* `markSide` — the side `ς ∈ {−1, +1}` of a mark.
* `sizeLeb` — Lebesgue measure on the sizes `(0, 1]`.
* `dealerMarks` — the mark measure `ν(dς, dq) = c_ς q^{−1−ϱ} dς dq`.
* `dealerJump` — the signed size `h_c(ς, q) = ς q`, as an element of `L²(ν; ℝ¹)`.

## Main statements

* `lintegral_Ioc_rpow_eq_top`, `lintegral_Ioc_rpow_lt_top` — `∫_0^1 q^s dq` is infinite for
  `s ≤ −1` and finite for `s > −1`.
* `lintegral_dealerMarks` — the integral of a function of the size.
* `dealerMarks_univ` — `ν(E) = ∞` for `c_ς > 0` and `ϱ ≥ 0`.
* `lintegral_sq_dealerMarks_lt_top`, `memLp_signedSize` — `∫ q² dν < ∞` and `h_c ∈ L²(ν)` for
  `ϱ < 2`.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.System LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u w

/-! ### Powers on the unit interval -/

/-- **`∫_0^1 q^s dq = ∞` for `s ≤ −1`.** -/
theorem lintegral_Ioc_rpow_eq_top {s : ℝ} (hs : s ≤ -1) :
    ∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ s) = ⊤ := by
  by_contra h
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun x : ℝ => x ^ s :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => Real.rpow_nonneg hx.1.le s
  have hi : IntegrableOn (fun x : ℝ => x ^ s) (Set.Ioc (0 : ℝ) 1) :=
    ⟨(measurable_id.pow_const s).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnn).mpr (lt_top_iff_ne_top.mpr h)⟩
  have hlt := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := s) one_pos).mp
    (hi.mono_set Set.Ioo_subset_Ioc_self)
  linarith

/-- **`∫_0^1 q^s dq < ∞` for `s > −1`.** -/
theorem lintegral_Ioc_rpow_lt_top {s : ℝ} (hs : -1 < s) :
    ∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ s) < ⊤ := by
  have hi : IntegrableOn (fun x : ℝ => x ^ s) (Set.Ioc (0 : ℝ) 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo (by simp)).mpr
      ((intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mpr hs)
  exact hi.lintegral_lt_top

/-! ### The mark space and the mark measure -/

/-- The mark space `E = {−1, +1} × (0, 1]` of the dealer market: a side, `true` for `+1` and
`false` for `−1`, and a size `q ∈ (0, 1]`. -/
abbrev DealerMark : Type := Bool × Set.Ioc (0 : ℝ) 1

/-- The side `ς ∈ {−1, +1}` of a mark: `+1` for `true`, `−1` for `false`. -/
def markSide (b : Bool) : ℝ :=
  if b then 1 else -1

/-- The side has square `1`. -/
theorem markSide_sq (b : Bool) : markSide b ^ 2 = 1 := by
  cases b <;> norm_num [markSide]

/-- Lebesgue measure on the sizes `(0, 1]`. -/
noncomputable def sizeLeb : Measure (Set.Ioc (0 : ℝ) 1) :=
  Measure.comap Subtype.val volume

/-- The integral against `sizeLeb` of a function of the size is its integral over `(0, 1]`. -/
theorem lintegral_sizeLeb (f : ℝ → ℝ≥0∞) :
    ∫⁻ q, f q ∂sizeLeb = ∫⁻ x in Set.Ioc (0 : ℝ) 1, f x :=
  lintegral_subtype_comap measurableSet_Ioc f

/-- Lebesgue measure on the sizes is finite. -/
instance isFiniteMeasure_sizeLeb : IsFiniteMeasure sizeLeb :=
  ⟨by
    have h : ∫⁻ _q, (1 : ℝ≥0∞) ∂sizeLeb = ∫⁻ _x in Set.Ioc (0 : ℝ) 1, 1 :=
      lintegral_sizeLeb fun _ => 1
    rw [lintegral_one, setLIntegral_one, Real.volume_Ioc] at h
    rw [h]
    exact ENNReal.ofReal_lt_top⟩

/-- The mark measure of Example 5.5, `ν(dς, dq) = c_ς q^{−1−ϱ} dς dq`: the density
`c_ς q^{−1−ϱ}` against counting measure on the sides times Lebesgue measure on the sizes. -/
noncomputable def dealerMarks (c : Bool → ℝ) (ϱ : ℝ) : Measure DealerMark :=
  (Measure.count.prod sizeLeb).withDensity fun e =>
    ENNReal.ofReal (c e.1 * (e.2 : ℝ) ^ (-1 - ϱ))

/-- The mark measure is σ-finite. -/
instance sigmaFinite_dealerMarks (c : Bool → ℝ) (ϱ : ℝ) : SigmaFinite (dealerMarks c ϱ) := by
  unfold dealerMarks
  infer_instance

/-- **The integral of a function of the size against the mark measure**: for `G` measurable,
`∫_E G(q) ν(dς, dq) = (c_{+1} + c_{−1}) ∫_0^1 q^{−1−ϱ} G(q) dq`, `c_ς` read through `ofReal`. -/
theorem lintegral_dealerMarks (c : Bool → ℝ) (ϱ : ℝ) {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ e, G e.2 ∂dealerMarks c ϱ
      = (ENNReal.ofReal (c true) + ENNReal.ofReal (c false))
        * ∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ (-1 - ϱ)) * G x := by
  have hq : Measurable fun e : DealerMark => (e.2 : ℝ) := measurable_subtype_coe.comp measurable_snd
  have hf : Measurable fun e : DealerMark => ENNReal.ofReal (c e.1 * (e.2 : ℝ) ^ (-1 - ϱ)) :=
    (((measurable_of_countable c).comp measurable_fst).mul (hq.pow_const _)).ennreal_ofReal
  have hside : ∀ b : Bool, ∫⁻ q, ENNReal.ofReal (c b * (q : ℝ) ^ (-1 - ϱ)) * G q ∂sizeLeb
      = ENNReal.ofReal (c b) * ∫⁻ x in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ (-1 - ϱ)) * G x := by
    intro b
    have e : ∀ q : Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (c b * (q : ℝ) ^ (-1 - ϱ)) * G q
        = ENNReal.ofReal (c b) * (ENNReal.ofReal ((q : ℝ) ^ (-1 - ϱ)) * G q) := fun q => by
      rw [ENNReal.ofReal_mul' (Real.rpow_nonneg q.2.1.le _), mul_assoc]
    simp only [e]
    rw [lintegral_const_mul (f := fun q : Set.Ioc (0 : ℝ) 1 =>
        ENNReal.ofReal ((q : ℝ) ^ (-1 - ϱ)) * G q) _
        (((measurable_subtype_coe.pow_const _).ennreal_ofReal).mul
          (hG.comp measurable_subtype_coe)),
      lintegral_sizeLeb (fun x => ENNReal.ofReal (x ^ (-1 - ϱ)) * G x)]
  rw [dealerMarks, lintegral_withDensity_eq_lintegral_mul _ hf (g := fun e : DealerMark => G e.2)
    (hG.comp hq)]
  simp only [Pi.mul_apply]
  rw [lintegral_prod (fun e : DealerMark => ENNReal.ofReal (c e.1 * (e.2 : ℝ) ^ (-1 - ϱ)) * G e.2)
    (hf.mul (hG.comp hq)).aemeasurable, lintegral_count, tsum_fintype, Fintype.sum_bool, add_mul,
    hside, hside]

/-- **The mark measure has infinite total mass**: `ν(E) = ∞` for `c_ς > 0` and `ϱ ≥ 0`. -/
theorem dealerMarks_univ {c : Bool → ℝ} (hc : ∀ b, 0 < c b) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) :
    dealerMarks c ϱ Set.univ = ⊤ := by
  have h := lintegral_dealerMarks c ϱ (G := fun _ => 1) measurable_const
  simp only [mul_one] at h
  rw [lintegral_one] at h
  rw [h, lintegral_Ioc_rpow_eq_top (by linarith), ENNReal.mul_top]
  exact (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (hc true)) le_self_add).ne'

/-- **The aggregate size is square integrable**: `∫_E q² ν(dς, dq) < ∞` for `ϱ < 2`. -/
theorem lintegral_sq_dealerMarks_lt_top (c : Bool → ℝ) {ϱ : ℝ} (hϱ : ϱ < 2) :
    ∫⁻ e, ENNReal.ofReal ((e.2 : ℝ) ^ 2) ∂dealerMarks c ϱ < ⊤ := by
  rw [lintegral_dealerMarks c ϱ (G := fun x => ENNReal.ofReal (x ^ 2)) (by fun_prop)]
  refine ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
    ENNReal.ofReal_lt_top⟩) ?_
  have e : ∀ x ∈ Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (x ^ (-1 - ϱ)) * ENNReal.ofReal (x ^ 2)
      = ENNReal.ofReal (x ^ (1 - ϱ)) := fun x hx => by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx.1.le _), ← Real.rpow_natCast,
      ← Real.rpow_add hx.1]
    norm_num
    ring_nf
  rw [setLIntegral_congr_fun measurableSet_Ioc e]
  exact lintegral_Ioc_rpow_lt_top (by linarith)

/-- The signed size `h_c(ς, q) = ς q` of a mark. -/
noncomputable def signedSize (e : DealerMark) : ℝ :=
  markSide e.1 * e.2

/-- **The signed size is square integrable**: `h_c ∈ L²(ν)` for `ϱ < 2`. -/
theorem memLp_signedSize (c : Bool → ℝ) {ϱ : ℝ} (hϱ : ϱ < 2) :
    MemLp signedSize 2 (dealerMarks c ϱ) := by
  have hm : Measurable signedSize :=
    ((measurable_of_countable markSide).comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd)
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have e : (fun e => signedSize e ^ 2) = fun e : DealerMark => (e.2 : ℝ) ^ 2 := funext fun e => by
    rw [signedSize, mul_pow, markSide_sq, one_mul]
  rw [e]
  exact ⟨((measurable_subtype_coe.comp measurable_snd).pow_const 2).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)).mpr
      (lintegral_sq_dealerMarks_lt_top c hϱ)⟩

/-- The embedding `x ↦ x e₀` of `ℝ` into `ℝ¹` is continuous. -/
theorem continuous_euclideanSingle_zero :
    Continuous fun x : ℝ => (PiLp.single 2 (0 : Fin 1) x : EuclideanSpace ℝ (Fin 1)) :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun a b => by
    rw [dist_eq_norm, dist_eq_norm, ← PiLp.single_sub, PiLp.norm_single, NNReal.coe_one,
      one_mul]).continuous

/-- The signed size `h_c(ς, q) = ς q`, as an element of `L²(ν; ℝ¹)`, for `ϱ < 2`. -/
noncomputable def dealerJump (c : Bool → ℝ) {ϱ : ℝ} (hϱ : ϱ < 2) :
    Lp (EuclideanSpace ℝ (Fin 1)) 2 (dealerMarks c ϱ) :=
  MemLp.toLp (fun e => PiLp.single 2 (0 : Fin 1) (signedSize e))
    ((memLp_signedSize c hϱ).congr_norm
      (continuous_euclideanSingle_zero.comp_aestronglyMeasurable (memLp_signedSize c hϱ).1)
      (Eventually.of_forall fun _ => (PiLp.norm_single 2 (fun _ : Fin 1 => ℝ) 0 _).symm))

end MVFBSDEJ.WellPosedness.Existence
