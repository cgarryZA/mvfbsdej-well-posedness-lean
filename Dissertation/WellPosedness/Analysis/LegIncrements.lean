/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoCellIsometry
import LevyStochCalc.Brownian.MultidimIto
import LevyStochCalc.Ito.CompensatedCellIsometry
import LevyStochCalc.Poisson.CompensatedLinear
import LevyStochCalc.BSDEJ.DriftLeg
import Dissertation.WellPosedness.Analysis.SquareBounds
/-!
# Second moments of the increments of the three legs

The increment across `[a, t]` of each leg of an Itô–Lévy process has second moment bounded by the
energy of its integrand on `[a, t]`:

* the drift leg, by the Cauchy–Schwarz inequality:
  `|∫_0^t φ − ∫_0^a φ|² ≤ (t − a) ∫_a^t |φ|²` along every integrable path;
* the multidimensional Brownian leg, by the Itô isometry on the cell for each coordinate and the
  Cauchy–Schwarz inequality over the `d` coordinates:
  `𝔼|∫_a^t σ dW|² ≤ d ∑_j 𝔼 ∫_a^t |σ_j|²`;
* the compensated Poisson leg, by the Itô–Lévy isometry on the cell:
  `𝔼|∫_a^t ∫_E φ dÑ|² = 𝔼 ∫_a^t ∫_E |φ|² ν(de) ds`.

The bounds hold over any filtration for which the drivers are Brownian and Poisson.

## Main statements

* `enorm_setIntegral_Icc_sub_sq_le` — the drift leg.
* `lintegral_multidim_sub_sq_le` — the multidimensional Brownian leg.
* `lintegral_compensated_sub_sq_le` — the compensated Poisson leg.
* `enorm_add_add_sq_le` — `‖x + y + z‖² ≤ 3 (‖x‖² + ‖y‖² + ‖z‖²)`.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness

open LevyStochCalc

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `‖x + y + z‖² ≤ 3 (‖x‖² + ‖y‖² + ‖z‖²)`. -/
theorem enorm_add_add_sq_le {F : Type*} [NormedAddCommGroup F] (x y z : F) :
    ‖x + y + z‖ₑ ^ 2 ≤ 3 * (‖x‖ₑ ^ 2 + ‖y‖ₑ ^ 2 + ‖z‖ₑ ^ 2) := by
  have h := sq_finsetSum_le_card_mul (Finset.univ : Finset (Fin 3)) ![‖x‖ₑ, ‖y‖ₑ, ‖z‖ₑ]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Finset.card_univ,
    Fintype.card_fin, Nat.cast_ofNat] at h
  exact (pow_le_pow_left' ((enorm_add_le (x + y) z).trans
    (add_le_add (enorm_add_le x y) le_rfl)) 2).trans h

/-! ### The drift leg -/

section Drift

/-- **The drift leg across `[a, t]`, forwards**: along a path integrable on `[0, T]`, for
`0 ≤ a ≤ t ≤ T`, `|∫_0^t φ − ∫_0^a φ|² ≤ (t − a) ∫_a^t |φ|²`. -/
theorem enorm_setIntegral_Icc_sub_sq_le {φ : ℝ → ℝ} {T a t : ℝ}
    (hφ : MeasureTheory.IntegrableOn φ (Set.Icc 0 T)) (ha : 0 ≤ a) (hat : a ≤ t) (htT : t ≤ T) :
    ‖(∫ s in Set.Icc 0 t, φ s) - ∫ s in Set.Icc 0 a, φ s‖ₑ ^ 2
      ≤ ENNReal.ofReal (t - a) * ∫⁻ s in Set.Icc a t, ‖φ s‖ₑ ^ 2 := by
  have h1 : IntegrableOn φ (Set.Icc 0 a) := hφ.mono_set (Set.Icc_subset_Icc le_rfl (hat.trans htT))
  have h2 : IntegrableOn φ (Set.Ioc a t) :=
    hφ.mono_set fun s hs => ⟨ha.trans hs.1.le, hs.2.trans htT⟩
  have hdisj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a t) :=
    (Set.Iic_disjoint_Ioi le_rfl).mono Set.Icc_subset_Iic_self Set.Ioc_subset_Ioi_self
  have hsplit : ∫ s in Set.Icc 0 t, φ s = (∫ s in Set.Icc 0 a, φ s) + ∫ s in Set.Ioc a t, φ s := by
    rw [← Set.Icc_union_Ioc_eq_Icc ha hat, setIntegral_union hdisj measurableSet_Ioc h1 h2]
  rw [hsplit, add_sub_cancel_left, setIntegral_congr_set Ioc_ae_eq_Icc]
  have h := enorm_setIntegral_sq_le (μ := volume) (f := φ) (Set.Icc a t)
    (hφ.mono_set fun s hs => ⟨ha.trans hs.1, hs.2.trans htT⟩).aestronglyMeasurable
  rwa [Real.volume_Icc] at h

end Drift

/-! ### The Brownian leg -/

section Brownian

variable {d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ mΩ) (hℱ : ∀ j, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)

include hℱ in
/-- **The multidimensional Brownian leg across `[a, t]`**: for `0 ≤ a ≤ t`,
`𝔼|∫_0^t σ dW − ∫_0^a σ dW|² ≤ d ∑_j 𝔼 ∫_a^t |σ_j|²`. -/
theorem lintegral_multidim_sub_sq_le (σ : ℝ → Ω → Fin d → ℝ)
    (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ s ω j))
    (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => σ s ω j)
    (hq : ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) :
    ∫⁻ ω, ‖Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ σ hm hp hq t ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ σ hm hp hq a ω‖ₑ ^ 2
          ∂P
      ≤ d * ∑ j, ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖σ s ω j‖ₑ ^ 2 ∂volume ∂P := by
  rcases hat.eq_or_lt with rfl | hlt
  · simp
  set I : Fin d → ℝ → Ω → ℝ := fun j t => Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ
    (hℱ j) (fun ω s => σ s ω j) (hm j) (hp j) (hq j) t with hI
  have hdef : ∀ t ω, Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ σ hm hp
      hq t ω = ∑ j, I j t ω := fun _ _ => rfl
  have hmeas : ∀ j, AEMeasurable (fun ω => ‖I j t ω - I j a ω‖ₑ ^ 2) P := fun j =>
    (((Brownian.Ito.stochasticIntegralBrownian_memLp (W.W j) ℱ (hℱ j) _ _ _ _ t).sub
      (Brownian.Ito.stochasticIntegralBrownian_memLp (W.W j) ℱ (hℱ j) _ _ _ _
        a)).aestronglyMeasurable.enorm).pow_const 2
  calc ∫⁻ ω, ‖Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ σ hm hp hq t ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ σ hm hp hq a ω‖ₑ ^ 2
          ∂P
      ≤ ∫⁻ ω, d * ∑ j, ‖I j t ω - I j a ω‖ₑ ^ 2 ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [hdef, hdef, ← Finset.sum_sub_distrib]
        have h := sq_finsetSum_le_card_mul Finset.univ fun j => ‖I j t ω - I j a ω‖ₑ
        rw [Finset.card_univ, Fintype.card_fin] at h
        exact (pow_le_pow_left' (enorm_sum_le _ _) 2).trans h
    _ = d * ∑ j, ∫⁻ ω, ‖I j t ω - I j a ω‖ₑ ^ 2 ∂P := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top d),
          lintegral_finsetSum' _ fun j _ => hmeas j]
    _ ≤ d * ∑ j, ∫⁻ ω, ∫⁻ s in Set.Icc a t, ‖σ s ω j‖ₑ ^ 2 ∂volume ∂P := by
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => ?_)
        have hiso := Brownian.Ito.lintegral_sq_stochasticIntegralBrownian_sub (W.W j) ℱ (hℱ j)
          (fun ω s => σ s ω j) (hm j) (hp j) (hq j) ha hlt
        simp only [← enorm_eq_nnnorm] at hiso
        have key : ∫⁻ ω, ‖I j t ω - I j a ω‖ₑ ^ 2 ∂P
            = ∫⁻ ω, ∫⁻ s in Set.Ioc a t, ‖σ s ω j‖ₑ ^ 2 ∂volume ∂P := hiso
        rw [key]
        exact lintegral_mono fun ω => lintegral_mono_set Set.Ioc_subset_Icc_self

end Brownian

/-! ### The compensated Poisson leg -/

section Poisson

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ mΩ)
  (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)

include hℱ in
/-- **The compensated Poisson leg across `[a, t]`**: for `0 ≤ a ≤ t`,
`𝔼|∫_0^t ∫_E φ dÑ − ∫_0^a ∫_E φ dÑ|² ≤ 𝔼 ∫_a^t ∫_E |φ|² ν(de) ds`. -/
theorem lintegral_compensated_sub_sq_le (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) :
    ∫⁻ ω, ‖Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t ω
        - Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq a ω‖ₑ ^ 2 ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc a t, ∫⁻ e, ‖φ ω s e‖ₑ ^ 2 ∂ν ∂volume ∂P := by
  rcases hat.eq_or_lt with rfl | hlt
  · simp
  have hiso := Poisson.Compensated.isometry_stochasticIntegral_Ioc N hℱ hm hp hq ha hlt
  simp only [← enorm_eq_nnnorm] at hiso
  rw [hiso]
  exact lintegral_mono fun ω => lintegral_mono_set Set.Ioc_subset_Icc_self

end Poisson

end Dissertation.WellPosedness
