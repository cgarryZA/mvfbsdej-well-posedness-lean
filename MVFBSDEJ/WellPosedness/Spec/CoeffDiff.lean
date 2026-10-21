/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Spec.Assumptions
import MVFBSDEJ.WellPosedness.Robustness.Margin

/-!
# The interior bound of Assumption 2.3 in mean square

For two diagonal inputs `(Θ, Law Θ)` and `(Θ', Law Θ')` at a time `t` at which the interior bound
of Assumption 2.3 holds with the constant `L`, almost surely

`S ≤ L (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + W₂(Law Θ, Law Θ'))`,

`S = |δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf|`, with `W₂` the 2-Wasserstein distance of the Hilbert norm
of `H`. Squaring with `(a + b + c + e + W)² ≤ 5 (a² + b² + c² + e² + W²)` and bounding `W₂²` by
the coupling bound (2.8), `W₂(Law Θ, Law Θ')² ≤ 𝔼 |Θ − Θ'|²_H`, gives

`𝔼 S² ≤ 10 L² 𝔼 |Θ − Θ'|²_H`,

the first step of (4.9) of the well-posedness paper at a fixed time.

## Main statements

* `sq_le_five_mul_sq_add` — `(|L| (a + b + c + e + W))² ≤ 5 L² (a² + b² + c² + e² + W²)`.
* `LipInteriorAt.lintegral_sq_coeffDiff_le` — `𝔼 S² ≤ 10 L² 𝔼 |Θ − Θ'|²_H`.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.Spec

open MVFBSDEJ.WellPosedness.System

/-- `x ≤ |L| (a + b + c + e + W)` with `x` nonnegative gives
`x² ≤ 5 L² (a² + b² + c² + e² + W²)`. -/
theorem sq_le_five_mul_sq_add {x L a b c e W : ℝ} (hx : 0 ≤ x)
    (h : x ≤ |L| * (a + b + c + e + W)) :
    x ^ 2 ≤ 5 * L ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 + W ^ 2) := by
  have hs : (a + b + c + e + W) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 + W ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (a - W),
      sq_nonneg (b - c), sq_nonneg (b - e), sq_nonneg (b - W), sq_nonneg (c - e),
      sq_nonneg (c - W), sq_nonneg (e - W)]
  set S := a + b + c + e + W with hS
  have hL2 : |L| ^ 2 = L ^ 2 := sq_abs L
  have h1 : x ^ 2 ≤ (|L| * S) ^ 2 := pow_le_pow_left₀ hx h 2
  rw [mul_pow, hL2] at h1
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg L)]

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P] {t L : ℝ}
  {C : Coeffs ν n m d}

/-- **The interior bound of Assumption 2.3 in mean square.** If the interior bound holds at the
time `t` with the constant `L`, then for two strongly `ℱ_t`-measurable square-integrable tuples
`Θ, Θ'`, with `δψ = ψ(t, Θ, Law Θ) − ψ(t, Θ', Law Θ')`,
`𝔼 (|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf|)² ≤ 10 L² 𝔼 |Θ − Θ'|²_H`, in `[0, ∞]`. -/
theorem LipInteriorAt.lintegral_sq_coeffDiff_le (hL : LipInteriorAt ℱ P t L C)
    {Θ Θ' : Ω → TupleH ν n m d} (hΘ : StronglyMeasurable[ℱ t] Θ) (hΘ2 : MemLp Θ 2 P)
    (hΘ' : StronglyMeasurable[ℱ t] Θ') (hΘ'2 : MemLp Θ' 2 P) :
    ∫⁻ ω, (‖C.b t (Θ ω) (lawP2 P Θ) - C.b t (Θ' ω) (lawP2 P Θ')‖ₑ
        + ‖C.σ t (Θ ω) (lawP2 P Θ) - C.σ t (Θ' ω) (lawP2 P Θ')‖ₑ
        + ‖C.h t (Θ ω) (lawP2 P Θ) - C.h t (Θ' ω) (lawP2 P Θ')‖ₑ
        + ‖C.f t (Θ ω) (lawP2 P Θ) - C.f t (Θ' ω) (lawP2 P Θ')‖ₑ) ^ 2 ∂P
      ≤ ENNReal.ofReal (10 * L ^ 2) * ∫⁻ ω, ENNReal.ofReal (channelSq (Θ ω - Θ' ω)) ∂P := by
  have hb := hL (Θ, lawP2 P Θ) (mk_mem_diagonalInputs hΘ hΘ2) (Θ', lawP2 P Θ')
    (mk_mem_diagonalInputs hΘ' hΘ'2)
  set W := w2H (lawP2 P Θ) (lawP2 P Θ') with hW
  have hW0 : 0 ≤ W := w2H_nonneg _ _
  have hW2 : ENNReal.ofReal (W ^ 2) ≤ ∫⁻ ω, ENNReal.ofReal (channelSq (Θ ω - Θ' ω)) ∂P := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_channelSq_sub hΘ2 hΘ'2)
      (ae_of_all _ fun ω => channelSq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (w2H_lawP2_sq_le hΘ2 hΘ'2)
  have key : ∀ᵐ ω ∂P, (‖C.b t (Θ ω) (lawP2 P Θ) - C.b t (Θ' ω) (lawP2 P Θ')‖ₑ
        + ‖C.σ t (Θ ω) (lawP2 P Θ) - C.σ t (Θ' ω) (lawP2 P Θ')‖ₑ
        + ‖C.h t (Θ ω) (lawP2 P Θ) - C.h t (Θ' ω) (lawP2 P Θ')‖ₑ
        + ‖C.f t (Θ ω) (lawP2 P Θ) - C.f t (Θ' ω) (lawP2 P Θ')‖ₑ) ^ 2
      ≤ ENNReal.ofReal (5 * L ^ 2)
        * (ENNReal.ofReal (channelSq (Θ ω - Θ' ω)) + ENNReal.ofReal (W ^ 2)) := by
    filter_upwards [hb] with ω hω
    set x := ‖C.b t (Θ ω) (lawP2 P Θ) - C.b t (Θ' ω) (lawP2 P Θ')‖
        + ‖C.σ t (Θ ω) (lawP2 P Θ) - C.σ t (Θ' ω) (lawP2 P Θ')‖
        + ‖C.h t (Θ ω) (lawP2 P Θ) - C.h t (Θ' ω) (lawP2 P Θ')‖
        + ‖C.f t (Θ ω) (lawP2 P Θ) - C.f t (Θ' ω) (lawP2 P Θ')‖ with hx
    have hx0 : 0 ≤ x := by positivity
    have h1 : x ≤ |L| * (‖(Θ ω).1 - (Θ' ω).1‖ + ‖(Θ ω).2.1 - (Θ' ω).2.1‖
        + ‖(Θ ω).2.2.1 - (Θ' ω).2.2.1‖ + ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ + W) :=
      hω.trans (mul_le_mul_of_nonneg_right (le_abs_self L) (by positivity))
    have h2 := sq_le_five_mul_sq_add hx0 h1
    have hcs : channelSq (Θ ω - Θ' ω) = ‖(Θ ω).1 - (Θ' ω).1‖ ^ 2 + ‖(Θ ω).2.1 - (Θ' ω).2.1‖ ^ 2
        + ‖(Θ ω).2.2.1 - (Θ' ω).2.2.1‖ ^ 2 + ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2 := by
      simp only [channelSq, Prod.fst_sub, Prod.snd_sub]
    have hlhs : (‖C.b t (Θ ω) (lawP2 P Θ) - C.b t (Θ' ω) (lawP2 P Θ')‖ₑ
        + ‖C.σ t (Θ ω) (lawP2 P Θ) - C.σ t (Θ' ω) (lawP2 P Θ')‖ₑ
        + ‖C.h t (Θ ω) (lawP2 P Θ) - C.h t (Θ' ω) (lawP2 P Θ')‖ₑ
        + ‖C.f t (Θ ω) (lawP2 P Θ) - C.f t (Θ' ω) (lawP2 P Θ')‖ₑ) ^ 2 = ENNReal.ofReal (x ^ 2) := by
      rw [hx, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_add (by positivity)
        (norm_nonneg _), ENNReal.ofReal_add (by positivity) (norm_nonneg _),
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _), ofReal_norm, ofReal_norm,
        ofReal_norm, ofReal_norm]
    rw [hlhs, ← ENNReal.ofReal_add (channelSq_nonneg _) (sq_nonneg W),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hcs]
    linarith
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal (5 * L ^ 2)
          * (ENNReal.ofReal (channelSq (Θ ω - Θ' ω)) + ENNReal.ofReal (W ^ 2)) ∂P :=
        lintegral_mono_ae key
    _ = ENNReal.ofReal (5 * L ^ 2)
          * (∫⁻ ω, ENNReal.ofReal (channelSq (Θ ω - Θ' ω)) ∂P + ENNReal.ofReal (W ^ 2)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ measurable_const,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (5 * L ^ 2)
          * (∫⁻ ω, ENNReal.ofReal (channelSq (Θ ω - Θ' ω)) ∂P
            + ∫⁻ ω, ENNReal.ofReal (channelSq (Θ ω - Θ' ω)) ∂P) := by gcongr
    _ = ENNReal.ofReal (10 * L ^ 2) * ∫⁻ ω, ENNReal.ofReal (channelSq (Θ ω - Θ' ω)) ∂P := by
        have h10 : ENNReal.ofReal (10 * L ^ 2) = ENNReal.ofReal (5 * L ^ 2) * 2 := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
          ring_nf
        rw [h10, ← two_mul]
        ring

end MVFBSDEJ.WellPosedness.Spec
