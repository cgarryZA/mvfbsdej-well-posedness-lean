/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.Sub
import Dissertation.WellPosedness.Analysis.LegIncrements
/-!
# Increments of a solution of the linear forward equation, plain and weighted

For a solution `X` of the linear forward equation

`X_t = ξ₀ + ∫_0^t b_s ds + ∫_0^t σ_s dW_s + ∫_0^t ∫_E γ_s(e) Ñ(ds, de)`,   `t ∈ [0, T]`,

the second moment of an increment across `[a, t] ⊆ [0, T]` is at most the integral over `[a, t]`
of the time density

`g(s) = 3 (T 𝔼|b_s|² + d ∑_j 𝔼|σ_j(s)|² + 𝔼 ∫_E |γ_s(e)|² ν(de))`,

by the Cauchy–Schwarz inequality for the drift leg and the isometries of the two stochastic legs.
For a bounded measurable deterministic weight `w`, write `M^w` for the sum of the three legs of
the weighted data `(w b, w σ, w γ)`. If `|w − c| ≤ δ` on `[a, t]` for a constant `c`, then
`M^w_t − M^w_a − c (X_t − X_a)` is the increment of the three legs of the data
`((w − c) b, (w − c) σ, (w − c) γ)`, so its second moment is at most `δ² ∫_a^t g`.

## Main definitions

* `forwardIncrementDensity` — the time density `g`.

## Main statements

* `progressivelyMeasurable_weight_mul`, `markedProgressivelyMeasurable_weight_mul` — a
  deterministic measurable weight preserves progressive measurability.
* `energy_weight_mul_le`, `markedEnergy_weight_mul_le` — a weight bounded by `B` multiplies the
  energy by at most `B²`.
* `setLIntegral_forwardIncrementDensity` — the integral of `g` over a set of times.
* `lintegral_sq_legs_sub_le` — the second moment of an increment of the three legs.
* `LinearFSDEJ.setLIntegral_forwardIncrementDensity_ne_top` — the density of a solution has
  finite mass on the horizon.
* `LinearFSDEJ.lintegral_sq_sub_le` — the increments of a solution.
* `LinearFSDEJ.lintegral_sq_weight_sub_le` — the weighted increments.
* `LinearFSDEJ.energy_state_ne_top` — a solution has finite energy on the horizon.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc Dissertation.WellPosedness.BrownianPoisson
  Dissertation.WellPosedness

universe u v w

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

/-! ### Deterministic weights -/

section Weight

variable {ℱ : Filtration ℝ mΩ} {w : ℝ → ℝ}

/-- A deterministic measurable weight times a progressively measurable process is progressively
measurable. -/
theorem progressivelyMeasurable_weight_mul (hw : Measurable w) {H : Ω → ℝ → ℝ}
    (hH : Probability.ProgressivelyMeasurable ℱ H) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => w s * H ω s := by
  have hdet : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) s => w s := by
    intro t
    letI : MeasurableSpace Ω := ℱ t
    exact ((hw.indicator measurableSet_Iic).comp measurable_snd).stronglyMeasurable
  exact hdet.mul hH

/-- A deterministic measurable weight times a progressively measurable marked process is
progressively measurable. -/
theorem markedProgressivelyMeasurable_weight_mul (hw : Measurable w) {φ : Ω → ℝ → E → ℝ}
    (hφ : Probability.MarkedProgressivelyMeasurable ℱ φ) :
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => w s * φ ω s e := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hrw : (fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => w s * φ p.1 s p.2.2) p.2.1)
      = fun p => w p.2.1 * (Set.Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1 := by
    funext p
    exact Set.indicator_mul_right _ _ _
  rw [hrw]
  exact (hw.comp measurable_snd.fst).stronglyMeasurable.mul (hφ t)

/-- `‖a x‖² ≤ δ² ‖x‖²` for `|a| ≤ δ`. -/
theorem enorm_mul_sq_le_of_abs_le {a x δ : ℝ} (h : |a| ≤ δ) :
    ‖a * x‖ₑ ^ 2 ≤ ENNReal.ofReal (δ ^ 2) * ‖x‖ₑ ^ 2 := by
  rw [enorm_mul, mul_pow, ENNReal.ofReal_pow ((abs_nonneg a).trans h), Real.enorm_eq_ofReal_abs a]
  gcongr

variable {P : Measure Ω} {ν : Measure E}

/-- A weight bounded by `B` multiplies the energy by at most `B²`. -/
theorem energy_weight_mul_le {B : ℝ} (hw : ∀ s, |w s| ≤ B) (H : Ω → ℝ → ℝ) (T : ℝ) :
    Brownian.Ito.energy P T (fun ω s => w s * H ω s)
      ≤ ENNReal.ofReal (B ^ 2) * Brownian.Ito.energy P T H := by
  unfold Brownian.Ito.energy
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun s => ?_
  simpa only [enorm_eq_nnnorm] using enorm_mul_sq_le_of_abs_le (x := H ω s) (hw s)

/-- A weight bounded by `B` multiplies the marked energy by at most `B²`. -/
theorem markedEnergy_weight_mul_le {B : ℝ} (hw : ∀ s, |w s| ≤ B) (φ : Ω → ℝ → E → ℝ) (T : ℝ) :
    Poisson.Compensated.markedEnergy P ν T (fun ω s e => w s * φ ω s e)
      ≤ ENNReal.ofReal (B ^ 2) * Poisson.Compensated.markedEnergy P ν T φ := by
  unfold Poisson.Compensated.markedEnergy
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun s => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun e => ?_
  simpa only [enorm_eq_nnnorm] using enorm_mul_sq_le_of_abs_le (x := φ ω s e) (hw s)

/-- On a set of times where `|w| ≤ δ`, the weight multiplies the energy by at most `δ²`. -/
theorem lintegral_setLIntegral_weight_mul_le {F : Ω → ℝ → ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    {δ : ℝ} (hw : ∀ s ∈ S, |w s| ≤ δ) :
    ∫⁻ ω, ∫⁻ s in S, ‖w s * F ω s‖ₑ ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (δ ^ 2) * ∫⁻ ω, ∫⁻ s in S, ‖F ω s‖ₑ ^ 2 ∂volume ∂P := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact setLIntegral_mono' hS fun s hs => enorm_mul_sq_le_of_abs_le (hw s hs)

/-- On a set of times where `|w| ≤ δ`, the weight multiplies the marked energy by at most
`δ²`. -/
theorem lintegral_setLIntegral_weight_mul_le_marked {F : Ω → ℝ → E → ℝ} {S : Set ℝ}
    (hS : MeasurableSet S) {δ : ℝ} (hw : ∀ s ∈ S, |w s| ≤ δ) :
    ∫⁻ ω, ∫⁻ s in S, ∫⁻ e, ‖w s * F ω s e‖ₑ ^ 2 ∂ν ∂volume ∂P
      ≤ ENNReal.ofReal (δ ^ 2) * ∫⁻ ω, ∫⁻ s in S, ∫⁻ e, ‖F ω s e‖ₑ ^ 2 ∂ν ∂volume ∂P := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hS fun s hs => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact lintegral_mono fun e => enorm_mul_sq_le_of_abs_le (hw s hs)

end Weight

/-! ### The increment density -/

section Density

variable {d : ℕ}

/-- The time density `3 (T 𝔼|b_s|² + d ∑_j 𝔼|σ_j(s)|² + 𝔼 ∫_E |γ_s(e)|² ν(de))`, which controls the
second moments of the increments of a solution of the linear forward equation. -/
noncomputable def forwardIncrementDensity (P : Measure Ω) (ν : Measure E) (T : ℝ)
    (b : Ω → ℝ → ℝ) (σ : ℝ → Ω → Fin d → ℝ) (γ : ℝ → Ω → E → ℝ) (s : ℝ) : ℝ≥0∞ :=
  3 * (ENNReal.ofReal T * ∫⁻ ω, ‖b ω s‖ₑ ^ 2 ∂P + d * ∑ j, ∫⁻ ω, ‖σ s ω j‖ₑ ^ 2 ∂P
    + ∫⁻ ω, ∫⁻ e, ‖γ s ω e‖ₑ ^ 2 ∂ν ∂P)

variable {P : Measure Ω} [SFinite P] {ν : Measure E} [SFinite ν] {T : ℝ} {b : Ω → ℝ → ℝ}
  {σ : ℝ → Ω → Fin d → ℝ} {γ : ℝ → Ω → E → ℝ}

/-- **The integral of the increment density over a set of times** `S` is
`3 (T 𝔼 ∫_S |b|² + d ∑_j 𝔼 ∫_S |σ_j|² + 𝔼 ∫_S ∫_E |γ|² dν)`. -/
theorem setLIntegral_forwardIncrementDensity (hb : Measurable (Function.uncurry b))
    (hσ : ∀ j, Measurable (Function.uncurry fun ω s => σ s ω j))
    (hγ : Measurable fun p : Ω × ℝ × E => γ p.2.1 p.1 p.2.2) (S : Set ℝ) :
    ∫⁻ s in S, forwardIncrementDensity P ν T b σ γ s
      = 3 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in S, ‖b ω s‖ₑ ^ 2 ∂volume ∂P
        + d * ∑ j, ∫⁻ ω, ∫⁻ s in S, ‖σ s ω j‖ₑ ^ 2 ∂volume ∂P
        + ∫⁻ ω, ∫⁻ s in S, ∫⁻ e, ‖γ s ω e‖ₑ ^ 2 ∂ν ∂volume ∂P) := by
  have hb2 : Measurable fun p : Ω × ℝ => ‖b p.1 p.2‖ₑ ^ 2 := hb.enorm.pow_const 2
  have hσ2 : ∀ j, Measurable fun p : Ω × ℝ => ‖σ p.2 p.1 j‖ₑ ^ 2 := fun j =>
    (hσ j).enorm.pow_const 2
  have hγ2 : Measurable fun p : Ω × ℝ => ∫⁻ e, ‖γ p.2 p.1 e‖ₑ ^ 2 ∂ν :=
    ((hγ.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk
      measurable_snd))).enorm.pow_const 2).lintegral_prod_right'
  have eb : ∫⁻ ω, ∫⁻ s in S, ‖b ω s‖ₑ ^ 2 ∂volume ∂P = ∫⁻ s in S, ∫⁻ ω, ‖b ω s‖ₑ ^ 2 ∂P :=
    lintegral_lintegral_swap hb2.aemeasurable
  have eσ : ∀ j, ∫⁻ ω, ∫⁻ s in S, ‖σ s ω j‖ₑ ^ 2 ∂volume ∂P
      = ∫⁻ s in S, ∫⁻ ω, ‖σ s ω j‖ₑ ^ 2 ∂P := fun j =>
    lintegral_lintegral_swap (hσ2 j).aemeasurable
  have eγ : ∫⁻ ω, ∫⁻ s in S, ∫⁻ e, ‖γ s ω e‖ₑ ^ 2 ∂ν ∂volume ∂P
      = ∫⁻ s in S, ∫⁻ ω, ∫⁻ e, ‖γ s ω e‖ₑ ^ 2 ∂ν ∂P :=
    lintegral_lintegral_swap hγ2.aemeasurable
  have hbm : Measurable fun s => ∫⁻ ω, ‖b ω s‖ₑ ^ 2 ∂P := hb2.lintegral_prod_left'
  have hσm : ∀ j, Measurable fun s => ∫⁻ ω, ‖σ s ω j‖ₑ ^ 2 ∂P := fun j =>
    (hσ2 j).lintegral_prod_left'
  have hsum : Measurable fun s => ∑ j, ∫⁻ ω, ‖σ s ω j‖ₑ ^ 2 ∂P :=
    Finset.measurable_sum _ fun j _ => hσm j
  unfold forwardIncrementDensity
  rw [lintegral_const_mul' _ _ (by norm_num : (3 : ℝ≥0∞) ≠ ⊤), eb, eγ,
    Finset.sum_congr rfl fun j _ => eσ j]
  congr 1
  rw [lintegral_add_left (show Measurable fun s => ENNReal.ofReal T * ∫⁻ ω, ‖b ω s‖ₑ ^ 2 ∂P
      + (d : ℝ≥0∞) * ∑ j, ∫⁻ ω, ‖σ s ω j‖ₑ ^ 2 ∂P from (hbm.const_mul _).add (hsum.const_mul _)),
    lintegral_add_left (show Measurable fun s => ENNReal.ofReal T * ∫⁻ ω, ‖b ω s‖ₑ ^ 2 ∂P from
      hbm.const_mul _),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ (ENNReal.natCast_ne_top d), lintegral_finsetSum _ fun j _ => hσm j]

end Density

/-! ### Increments of the three legs -/

section Legs

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- **The second moment of an increment of the three legs**: for data `(b, σ, φ)` with almost
surely integrable drift paths on `[0, T]` and `0 ≤ a ≤ t ≤ T`, the increment across `[a, t]` of
`∫_0^· b ds + ∫_0^· σ dW + ∫_0^· ∫_E φ dÑ` has second moment at most
`3 ((t − a) 𝔼 ∫_a^t |b|² + d ∑_j 𝔼 ∫_a^t |σ_j|² + 𝔼 ∫_a^t ∫_E |φ|² dν ds)`. -/
theorem lintegral_sq_legs_sub_le (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ mΩ)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ) {T : ℝ} {b : Ω → ℝ → ℝ}
    (hbm : Measurable (Function.uncurry b)) (hbi : ∀ᵐ ω ∂P, IntegrableOn (b ω) (Set.Icc 0 T))
    {σ : ℝ → Ω → Fin d → ℝ} (hσm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ s ω j))
    (hσp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => σ s ω j)
    (hσq : ∀ (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : Ω → ℝ → E → ℝ} (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hφq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (htT : t ≤ T) :
    ∫⁻ ω, ‖((∫ s in Set.Icc 0 t, b ω s)
          + Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW σ hσm hσp hσq
            t ω
          + Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφq t ω)
        - ((∫ s in Set.Icc 0 a, b ω s)
          + Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW σ hσm hσp hσq
            a ω
          + Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφq a ω)‖ₑ ^ 2 ∂P
      ≤ 3 * (ENNReal.ofReal (t - a) * ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖b ω s‖ₑ ^ 2 ∂volume ∂P
        + d * ∑ j, ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖σ s ω j‖ₑ ^ 2 ∂volume ∂P
        + ∫⁻ ω, ∫⁻ s in Set.Icc a t, ∫⁻ e, ‖φ ω s e‖ₑ ^ 2 ∂ν ∂volume ∂P) := by
  set W := Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW σ hσm hσp hσq
    with hW
  set N := Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφq with hN
  have hWm : ∀ r, AEMeasurable (W r) P := fun r =>
    (show MemLp (W r) 2 P from memLp_finsetSum Finset.univ fun i _ =>
      Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W i) ℱ (hℱW i) (fun ω s => σ s ω i)
        (hσm i) (hσp i) (hσq i) r).aestronglyMeasurable.aemeasurable
  have hFm : Measurable fun ω => ∫⁻ s in Set.Icc a t, ‖b ω s‖ₑ ^ 2 :=
    (hbm.enorm.pow_const 2).lintegral_prod_right'
  have hpt : ∀ᵐ ω ∂P, ‖((∫ s in Set.Icc 0 t, b ω s) + W t ω + N t ω)
        - ((∫ s in Set.Icc 0 a, b ω s) + W a ω + N a ω)‖ₑ ^ 2
      ≤ 3 * (ENNReal.ofReal (t - a) * (∫⁻ s in Set.Icc a t, ‖b ω s‖ₑ ^ 2)
        + ‖W t ω - W a ω‖ₑ ^ 2 + ‖N t ω - N a ω‖ₑ ^ 2) := by
    filter_upwards [hbi] with ω hω
    have hsplit : ((∫ s in Set.Icc 0 t, b ω s) + W t ω + N t ω)
          - ((∫ s in Set.Icc 0 a, b ω s) + W a ω + N a ω)
        = ((∫ s in Set.Icc 0 t, b ω s) - ∫ s in Set.Icc 0 a, b ω s)
          + (W t ω - W a ω) + (N t ω - N a ω) := by ring
    rw [hsplit]
    have hb := enorm_setIntegral_Icc_sub_sq_le hω ha hat htT
    refine (enorm_add_add_sq_le _ _ _).trans ?_
    gcongr
  have hWa : AEMeasurable (fun ω => ‖W t ω - W a ω‖ₑ ^ 2) P :=
    ((hWm t).sub (hWm a)).enorm.pow_const 2
  calc _ ≤ ∫⁻ ω, 3 * (ENNReal.ofReal (t - a) * (∫⁻ s in Set.Icc a t, ‖b ω s‖ₑ ^ 2)
        + ‖W t ω - W a ω‖ₑ ^ 2 + ‖N t ω - N a ω‖ₑ ^ 2) ∂P := lintegral_mono_ae hpt
    _ = 3 * (ENNReal.ofReal (t - a) * ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖b ω s‖ₑ ^ 2 ∂volume ∂P
        + ∫⁻ ω, ‖W t ω - W a ω‖ₑ ^ 2 ∂P + ∫⁻ ω, ‖N t ω - N a ω‖ₑ ^ 2 ∂P) := by
        have e1 : AEMeasurable (fun ω => ENNReal.ofReal (t - a) * (∫⁻ s in Set.Icc a t,
            ‖b ω s‖ₑ ^ 2) + ‖W t ω - W a ω‖ₑ ^ 2) P :=
          (hFm.const_mul (ENNReal.ofReal (t - a))).aemeasurable.add hWa
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left' e1,
          lintegral_add_left' (hFm.const_mul _).aemeasurable,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := mul_le_mul_right (add_le_add (add_le_add le_rfl
          (lintegral_multidim_sub_sq_le D.W ℱ hℱW σ hσm hσp hσq ha hat))
          (lintegral_compensated_sub_sq_le D.N ℱ hℱN φ hφm hφp hφq ha hat)) 3

end Legs

/-! ### Increments of a solution of the linear forward equation -/

section Forward

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ mΩ}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {T : ℝ} {ξ₀ : Ω → ℝ} {b : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ} {σ : ℝ → Ω → (Fin d → ℝ)}
  {γ : ℝ → Ω → E → ℝ}

namespace LinearFSDEJ

/-- A solution of the linear forward equation is progressively measurable. -/
theorem progressivelyMeasurable_state (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω :=
  Probability.progressivelyMeasurable_of_rightContinuous h.X_adapted h.X_rightCont

/-- The integral of the increment density of a solution over a set of times in `[0, T]` is
finite. -/
theorem setLIntegral_forwardIncrementDensity_ne_top
    (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) {S : Set ℝ} (hS : S ⊆ Set.Icc 0 T) :
    ∫⁻ s in S, forwardIncrementDensity P ν T b σ γ s ≠ ⊤ := by
  rw [setLIntegral_forwardIncrementDensity h.b_meas h.σ_meas h.γ_meas]
  have hb : ∫⁻ ω, ∫⁻ s in S, ‖b ω s‖ₑ ^ 2 ∂volume ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top h.b_sq (lintegral_mono fun ω => by
      simp only [enorm_eq_nnnorm]
      exact lintegral_mono_set hS)
  have hσ : ∀ j, ∫⁻ ω, ∫⁻ s in S, ‖σ s ω j‖ₑ ^ 2 ∂volume ∂P ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top (h.σ_sq j) (lintegral_mono fun ω => by
      simp only [enorm_eq_nnnorm]
      exact lintegral_mono_set hS)
  have hγ : ∫⁻ ω, ∫⁻ s in S, ∫⁻ e, ‖γ s ω e‖ₑ ^ 2 ∂ν ∂volume ∂P ≠ ⊤ :=
    ne_top_of_le_ne_top h.γ_sq (lintegral_mono fun ω => by
      simp only [enorm_eq_nnnorm]
      exact lintegral_mono_set hS)
  refine ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb, ENNReal.mul_ne_top (by simp) ?_⟩, hγ⟩)
  exact (ENNReal.sum_lt_top.mpr fun j _ => (hσ j).lt_top).ne

/-- **The increments of a solution of the linear forward equation**: for `0 ≤ a ≤ t ≤ T`,
`𝔼|X_t − X_a|² ≤ ∫_a^t g`, with `g` the increment density. -/
theorem lintegral_sq_sub_le (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) {a t : ℝ} (ha : 0 ≤ a)
    (hat : a ≤ t) (htT : t ≤ T) :
    ∫⁻ ω, ‖X t ω - X a ω‖ₑ ^ 2 ∂P ≤ ∫⁻ s in Set.Icc a t, forwardIncrementDensity P ν T b σ γ s := by
  have hinc := lintegral_sq_legs_sub_le D ℱ hℱW hℱN h.b_meas
    (ae_mem_integrablePaths h.b_meas h.b_sq) h.σ_meas h.σ_prog
    (sq_int_global_of_vanishing h.σ_vanish h.σ_sq) (φ := fun ω s e => γ s ω e) h.γ_meas h.γ_prog
    (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) ha hat htT
  rw [setLIntegral_forwardIncrementDensity h.b_meas h.σ_meas h.γ_meas]
  refine (le_of_eq (lintegral_congr_ae ?_)).trans (hinc.trans ?_)
  · filter_upwards [h.eqn t ⟨ha.trans hat, htT⟩, h.eqn a ⟨ha, hat.trans htT⟩] with ω e1 e2
    rw [e1, e2]
    ring_nf
  · gcongr
    linarith

/-- **A solution of the linear forward equation has finite energy on the horizon.** -/
theorem energy_state_ne_top (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) (hT : 0 ≤ T) :
    Brownian.Ito.energy P T (fun ω s => X s ω) ≠ ⊤ := by
  set G := ∫⁻ s in Set.Icc 0 T, forwardIncrementDensity P ν T b σ γ s with hG
  have hGf : G ≠ ⊤ := h.setLIntegral_forwardIncrementDensity_ne_top subset_rfl
  have hξ : ∫⁻ ω, ‖ξ₀ ω‖ₑ ^ 2 ∂P ≠ ⊤ := (lintegral_enorm_sq_lt_top h.ξ₀_sq).ne
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) :=
    h.progressivelyMeasurable_state.measurable_uncurry
  have hXs : ∀ s, Measurable (X s) := fun s => (h.X_adapted s).mono (ℱ.le s) le_rfl
  have hmom : ∀ s ∈ Set.Icc 0 T, ∫⁻ ω, ‖X s ω‖ₑ ^ 2 ∂P ≤ 2 * G + 2 * ∫⁻ ω, ‖ξ₀ ω‖ₑ ^ 2 ∂P := by
    intro s hs
    calc ∫⁻ ω, ‖X s ω‖ₑ ^ 2 ∂P
        ≤ ∫⁻ ω, (2 * ‖X s ω - X 0 ω‖ₑ ^ 2 + 2 * ‖X 0 ω‖ₑ ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          simpa using enorm_add_sq_le (X s ω - X 0 ω) (X 0 ω)
      _ = 2 * ∫⁻ ω, ‖X s ω - X 0 ω‖ₑ ^ 2 ∂P + 2 * ∫⁻ ω, ‖X 0 ω‖ₑ ^ 2 ∂P := by
          rw [lintegral_add_left (show Measurable fun ω => 2 * ‖X s ω - X 0 ω‖ₑ ^ 2 from
              (((hXs s).sub (hXs 0)).enorm.pow_const 2).const_mul 2),
            lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ 2 * G + 2 * ∫⁻ ω, ‖ξ₀ ω‖ₑ ^ 2 ∂P := by
          have h1 : ∫⁻ ω, ‖X s ω - X 0 ω‖ₑ ^ 2 ∂P ≤ G :=
            (h.lintegral_sq_sub_le le_rfl hs.1 hs.2).trans
              (lintegral_mono_set (Set.Icc_subset_Icc le_rfl hs.2))
          have h0 : ∫⁻ ω, ‖X 0 ω‖ₑ ^ 2 ∂P = ∫⁻ ω, ‖ξ₀ ω‖ₑ ^ 2 ∂P := lintegral_congr_ae (by
            filter_upwards [h.initial_ae_eq hT] with ω hω
            rw [hω])
          rw [h0]
          exact add_le_add (mul_le_mul_right h1 2) le_rfl
  have hswap : Brownian.Ito.energy P T (fun ω s => X s ω)
      = ∫⁻ s in Set.Icc 0 T, ∫⁻ ω, ‖X s ω‖ₑ ^ 2 ∂P := by
    unfold Brownian.Ito.energy
    simp only [← enorm_eq_nnnorm]
    exact lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Icc (0 : ℝ) T))
      ((show Measurable fun p : Ω × ℝ => ‖X p.2 p.1‖ₑ ^ 2 from
        hXm.enorm.pow_const 2).aemeasurable)
  rw [hswap]
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' measurableSet_Icc hmom)
  rw [setLIntegral_const]
  exact ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hGf,
    ENNReal.mul_ne_top (by norm_num) hξ⟩) (by simp)

/-- **The weighted increments of a solution of the linear forward equation.** Let `w` be a
bounded measurable deterministic weight and write
`M^w_r = ∫_0^r w b ds + ∫_0^r w σ dW + ∫_0^r ∫_E w γ dÑ`. If `|w − c| ≤ δ` on `[a, t]` with
`0 ≤ a ≤ t ≤ T`, then `𝔼|M^w_t − M^w_a − c (X_t − X_a)|² ≤ δ² ∫_a^t g`, with `g` the increment
density. -/
theorem lintegral_sq_weight_sub_le (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) {w : ℝ → ℝ}
    (hwm : Measurable w) {B : ℝ} (hwB : ∀ s, |w s| ≤ B)
    (hσm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => w s * σ s ω j))
    (hσp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => w s * σ s ω j)
    (hσq : ∀ (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖w s * σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγm : Measurable fun p : Ω × ℝ × E => w p.2.1 * γ p.2.1 p.1 p.2.2)
    (hγp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => w s * γ s ω e)
    (hγq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖w s * γ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {a t c δ : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (htT : t ≤ T)
    (hδ : ∀ s ∈ Set.Icc a t, |w s - c| ≤ δ) :
    ∫⁻ ω, ‖((∫ s in Set.Icc 0 t, w s * b ω s)
          + Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW
            (fun s ω j => w s * σ s ω j) hσm hσp hσq t ω
          + Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω s e => w s * γ s ω e) hγm hγp
            hγq t ω)
        - ((∫ s in Set.Icc 0 a, w s * b ω s)
          + Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW
            (fun s ω j => w s * σ s ω j) hσm hσp hσq a ω
          + Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω s e => w s * γ s ω e) hγm hγp
            hγq a ω)
        - c * (X t ω - X a ω)‖ₑ ^ 2 ∂P
      ≤ ENNReal.ofReal (δ ^ 2) * ∫⁻ s in Set.Icc a t, forwardIncrementDensity P ν T b σ γ s := by
  have hσ0q := sq_int_global_of_vanishing h.σ_vanish h.σ_sq
  have hγ0q := marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq
  -- the data `((w − c) b, (w − c) σ, (w − c) γ)`, written as linear combinations
  have hm₂ : ∀ j : Fin d,
      Measurable (Function.uncurry fun ω s => 1 * (w s * σ s ω j) + -c * σ s ω j) := fun j =>
    ((hσm j).const_mul 1).add ((h.σ_meas j).const_mul (-c))
  have hp₂ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ
      fun ω s => 1 * (w s * σ s ω j) + -c * σ s ω j := fun j =>
    ((continuous_const_mul 1).comp_progressivelyMeasurable (mul_zero 1) (hσp j)).add
      ((continuous_const_mul (-c)).comp_progressivelyMeasurable (mul_zero (-c)) (h.σ_prog j))
  have hq₂ : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖1 * (w s * σ s ω j) + -c * σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun j T' hT' =>
    lt_top_iff_ne_top.mpr (Brownian.Ito.energy_add_ne_top ((hσm j).const_mul 1)
      ((h.σ_meas j).const_mul (-c)) (Brownian.Ito.energy_const_mul_ne_top (hσm j)
        (hσq j T' hT').ne 1)
      (Brownian.Ito.energy_const_mul_ne_top (h.σ_meas j) (hσ0q j T' hT').ne (-c)))
  have hγm₂ : Measurable fun p : Ω × ℝ × E =>
      1 * (w p.2.1 * γ p.2.1 p.1 p.2.2) + -c * γ p.2.1 p.1 p.2.2 :=
    (hγm.const_mul 1).add (h.γ_meas.const_mul (-c))
  have hγp₂ : Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => 1 * (w s * γ s ω e) + -c * γ s ω e :=
    Poisson.Compensated.markedProgressivelyMeasurable_add
      (Poisson.Compensated.markedProgressivelyMeasurable_const_mul hγp 1)
      (Poisson.Compensated.markedProgressivelyMeasurable_const_mul h.γ_prog (-c))
  have hγq₂ : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖1 * (w s * γ s ω e) + -c * γ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := fun T' hT' =>
    lt_top_iff_ne_top.mpr (Poisson.Compensated.markedEnergy_add_ne_top (hγm.const_mul 1)
      (h.γ_meas.const_mul (-c))
      (Poisson.Compensated.markedEnergy_const_mul_ne_top hγm (hγq T' hT').ne 1)
      (Poisson.Compensated.markedEnergy_const_mul_ne_top h.γ_meas (hγ0q T' hT').ne (-c)))
  have hbm₂ : Measurable (Function.uncurry fun ω s => 1 * (w s * b ω s) + -c * b ω s) :=
    (((hwm.comp measurable_snd).mul h.b_meas).const_mul 1).add (h.b_meas.const_mul (-c))
  have hbi : ∀ᵐ ω ∂P, IntegrableOn (b ω) (Set.Icc 0 T) := ae_mem_integrablePaths h.b_meas h.b_sq
  have hwbi : ∀ᵐ ω ∂P, IntegrableOn (fun s => w s * b ω s) (Set.Icc 0 T) :=
    hbi.mono fun ω hω => Integrable.bdd_mul hω hwm.aestronglyMeasurable
      (ae_of_all _ fun s => (Real.norm_eq_abs _).le.trans (hwB s))
  have hbi₂ : ∀ᵐ ω ∂P, IntegrableOn (fun s => 1 * (w s * b ω s) + -c * b ω s) (Set.Icc 0 T) := by
    filter_upwards [hbi, hwbi] with ω h1 h2
    exact (h2.const_mul 1).add (h1.const_mul (-c))
  -- linearity of the three legs
  have hW := fun r => multidimStochasticIntegral_linComb_ae D.W hℱW
    (Z₁ := fun s ω j => w s * σ s ω j) (Z₂ := σ) 1 (-c) hσm h.σ_meas hσp h.σ_prog hσq hσ0q hm₂ hp₂
    hq₂ r
  have hN := fun r => compensatedIntegral_linComb_ae D.N hℱN
    (φ₁ := fun ω s e => w s * γ s ω e) (φ₂ := fun ω s e => γ s ω e) 1 (-c) hγm h.γ_meas hγp
    h.γ_prog hγq hγ0q hγm₂ hγp₂ hγq₂ r
  have hB := fun r (hr : r ≤ T) => ae_setIntegral_linComb_of_integrableOn (T := T)
    (φ₁ := fun ω s => w s * b ω s) (φ₂ := b) 1 (-c) hwbi hbi (S := Set.Icc 0 r)
    (Set.Icc_subset_Icc le_rfl hr)
  have hinc := lintegral_sq_legs_sub_le D ℱ hℱW hℱN (b := fun ω s => 1 * (w s * b ω s) + -c * b ω s)
    hbm₂ hbi₂ (σ := fun s ω j => 1 * (w s * σ s ω j) + -c * σ s ω j) hm₂ hp₂ hq₂
    (φ := fun ω s e => 1 * (w s * γ s ω e) + -c * γ s ω e) hγm₂ hγp₂ hγq₂ ha hat htT
  -- the weighted data are within `δ` of the combination
  have hw : ∀ x s, 1 * (w s * x) + -c * x = (w s - c) * x := fun x s => by ring
  have hb' : ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖1 * (w s * b ω s) + -c * b ω s‖ₑ ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (δ ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖b ω s‖ₑ ^ 2 ∂volume ∂P := by
    simp only [hw]
    exact lintegral_setLIntegral_weight_mul_le (w := fun s => w s - c) measurableSet_Icc hδ
  have hσ' : ∀ j : Fin d,
      ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖1 * (w s * σ s ω j) + -c * σ s ω j‖ₑ ^ 2 ∂volume ∂P
        ≤ ENNReal.ofReal (δ ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖σ s ω j‖ₑ ^ 2 ∂volume ∂P := by
    intro j
    simp only [hw]
    exact lintegral_setLIntegral_weight_mul_le (w := fun s => w s - c)
      (F := fun ω s => σ s ω j) measurableSet_Icc hδ
  have hγ' : ∫⁻ ω, ∫⁻ s in Set.Icc a t, ∫⁻ e, ‖1 * (w s * γ s ω e) + -c * γ s ω e‖ₑ ^ 2
        ∂ν ∂volume ∂P
      ≤ ENNReal.ofReal (δ ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc a t, ∫⁻ e, ‖γ s ω e‖ₑ ^ 2
        ∂ν ∂volume ∂P := by
    simp only [hw]
    exact lintegral_setLIntegral_weight_mul_le_marked (w := fun s => w s - c)
      (F := fun ω s e => γ s ω e) measurableSet_Icc hδ
  refine (le_of_eq (lintegral_congr_ae ?_)).trans (hinc.trans ?_)
  · filter_upwards [hW t, hW a, hN t, hN a, hB t htT, hB a (hat.trans htT),
      h.eqn t ⟨ha.trans hat, htT⟩, h.eqn a ⟨ha, hat.trans htT⟩] with ω e1 e2 e3 e4 e5 e6 e7 e8
    rw [e1, e2, e3, e4, e5, e6, e7, e8]
    ring_nf
  · rw [setLIntegral_forwardIncrementDensity h.b_meas h.σ_meas h.γ_meas]
    calc 3 * (ENNReal.ofReal (t - a)
            * ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖1 * (w s * b ω s) + -c * b ω s‖ₑ ^ 2 ∂volume ∂P
          + d * ∑ j, ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖1 * (w s * σ s ω j) + -c * σ s ω j‖ₑ ^ 2
            ∂volume ∂P
          + ∫⁻ ω, ∫⁻ s in Set.Icc a t, ∫⁻ e, ‖1 * (w s * γ s ω e) + -c * γ s ω e‖ₑ ^ 2
            ∂ν ∂volume ∂P)
        ≤ 3 * (ENNReal.ofReal (t - a)
            * (ENNReal.ofReal (δ ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖b ω s‖ₑ ^ 2 ∂volume ∂P)
          + d * ∑ j, ENNReal.ofReal (δ ^ 2)
            * ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖σ s ω j‖ₑ ^ 2 ∂volume ∂P
          + ENNReal.ofReal (δ ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc a t, ∫⁻ e, ‖γ s ω e‖ₑ ^ 2
            ∂ν ∂volume ∂P) :=
          mul_le_mul_right (add_le_add (add_le_add (mul_le_mul_right hb' _)
            (mul_le_mul_right (Finset.sum_le_sum fun j _ => hσ' j) _)) hγ') 3
      _ = ENNReal.ofReal (δ ^ 2) * (3 * (ENNReal.ofReal (t - a)
            * ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖b ω s‖ₑ ^ 2 ∂volume ∂P
          + d * ∑ j, ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖σ s ω j‖ₑ ^ 2 ∂volume ∂P
          + ∫⁻ ω, ∫⁻ s in Set.Icc a t, ∫⁻ e, ‖γ s ω e‖ₑ ^ 2 ∂ν ∂volume ∂P)) := by
          rw [← Finset.mul_sum]
          ring
      _ ≤ _ := by
          gcongr
          linarith

end LinearFSDEJ

end Forward

end Dissertation.WellPosedness.Stability
