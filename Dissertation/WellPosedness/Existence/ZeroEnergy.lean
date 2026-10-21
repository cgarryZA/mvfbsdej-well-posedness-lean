/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.PairDiff
import LevyStochCalc.Brownian.MultidimItoCongr

/-!
# Integrands that differ by zero energy

Two jointly measurable integrands whose difference has zero energy on the horizon `[0, T]` agree
almost everywhere for the product of the sample measure with Lebesgue measure on `[0, T]` (and,
for marked integrands, the mark measure). They have the same energy, their drift integrals over
every window inside `[0, T]` agree almost surely, and their stochastic integrals — the
multidimensional Itô integral and the compensated Poisson integral — agree almost surely at every
time up to `T`. Likewise, two families of square-integrable random variables whose differences
have zero second moment agree almost surely coordinatewise.

These are the facts that make the solution predicates of the linear equations with jumps, and of
the `λ`-system (4.1), insensitive to a change of forcing by zero energy.

## Main statements

* `ae_eq_of_energy_sub_eq_zero`, `ae_ae_eq_of_energy_sub_eq_zero`,
  `energy_eq_of_energy_sub_eq_zero` — integrands with zero energy of difference.
* `ae_eq_of_markedEnergy_sub_eq_zero`, `markedEnergy_eq_of_markedEnergy_sub_eq_zero` — the same
  for marked integrands.
* `ae_setIntegral_congr_of_energy` — the drift integrals agree.
* `multidimStochasticIntegral_congr_of_energy`, `compensatedIntegral_congr_of_markedEnergy` —
  the stochastic integrals agree.
* `ae_eq_of_lintegral_esq_sub_eq_zero` — random vectors with zero second moment of difference.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.Stability LevyStochCalc

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  {ν : Measure E} {T : ℝ}

/-! ### Unmarked integrands -/

section Unmarked

variable {H₁ H₂ : Ω → ℝ → ℝ}

/-- Two jointly measurable integrands whose difference has zero energy on `[0, T]` agree almost
everywhere for the product of `P` with Lebesgue measure on `[0, T]`. -/
theorem ae_eq_of_energy_sub_eq_zero (hm₁ : Measurable (Function.uncurry H₁))
    (hm₂ : Measurable (Function.uncurry H₂))
    (h : Brownian.Ito.energy P T (fun ω s => H₁ ω s - H₂ ω s) = 0) :
    (fun p : Ω × ℝ => H₁ p.1 p.2) =ᵐ[Brownian.Ito.energyMeasure P T] fun p => H₂ p.1 p.2 := by
  have hs : AEStronglyMeasurable (fun p : Ω × ℝ => H₁ p.1 p.2 - H₂ p.1 p.2)
      (Brownian.Ito.energyMeasure P T) := (hm₁.sub hm₂).aestronglyMeasurable
  rw [Brownian.Ito.energy_eq_eLpNorm_sq (H := fun ω s => H₁ ω s - H₂ ω s) (hm₁.sub hm₂),
    pow_eq_zero_iff two_ne_zero] at h
  filter_upwards [(eLpNorm_eq_zero_iff hs two_ne_zero).mp h] with p hp
  exact sub_eq_zero.mp hp

/-- Two jointly measurable integrands whose difference has zero energy on `[0, T]` agree, for
almost every sample point, at almost every time of `[0, T]`. -/
theorem ae_ae_eq_of_energy_sub_eq_zero (hm₁ : Measurable (Function.uncurry H₁))
    (hm₂ : Measurable (Function.uncurry H₂))
    (h : Brownian.Ito.energy P T (fun ω s => H₁ ω s - H₂ ω s) = 0) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), H₁ ω s = H₂ ω s :=
  Measure.ae_ae_of_ae_prod (ae_eq_of_energy_sub_eq_zero hm₁ hm₂ h)

/-- Two jointly measurable integrands whose difference has zero energy on `[0, T]` have the same
energy on `[0, T]`. -/
theorem energy_eq_of_energy_sub_eq_zero (hm₁ : Measurable (Function.uncurry H₁))
    (hm₂ : Measurable (Function.uncurry H₂))
    (h : Brownian.Ito.energy P T (fun ω s => H₁ ω s - H₂ ω s) = 0) :
    Brownian.Ito.energy P T H₂ = Brownian.Ito.energy P T H₁ := by
  rw [Brownian.Ito.energy_eq_eLpNorm_sq hm₁, Brownian.Ito.energy_eq_eLpNorm_sq hm₂,
    eLpNorm_congr_ae (ae_eq_of_energy_sub_eq_zero hm₁ hm₂ h)]

/-- For `t ≤ T`, the energy on `[0, t]` is at most the energy on `[0, T]`. -/
theorem energy_mono {H : Ω → ℝ → ℝ} {t : ℝ} (htT : t ≤ T) :
    Brownian.Ito.energy P t H ≤ Brownian.Ito.energy P T H :=
  lintegral_mono fun _ => lintegral_mono_set (Set.Icc_subset_Icc le_rfl htT)

/-- Two jointly measurable integrands whose difference has zero energy on `[0, T]` have almost
surely equal integrals over every set of times inside `[0, T]`. -/
theorem ae_setIntegral_congr_of_energy (hm₁ : Measurable (Function.uncurry H₁))
    (hm₂ : Measurable (Function.uncurry H₂))
    (h : Brownian.Ito.energy P T (fun ω s => H₁ ω s - H₂ ω s) = 0) {S : Set ℝ}
    (hS : S ⊆ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∫ s in S, H₁ ω s = ∫ s in S, H₂ ω s := by
  filter_upwards [ae_ae_eq_of_energy_sub_eq_zero hm₁ hm₂ h] with ω hω
  exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hS hω)

end Unmarked

/-! ### Marked integrands -/

section Marked

variable [SigmaFinite ν] {φ₁ φ₂ : Ω → ℝ → E → ℝ}

/-- Two jointly measurable marked integrands whose difference has zero marked energy on `[0, T]`
agree almost everywhere for the product of `P`, Lebesgue measure on `[0, T]` and `ν`. -/
theorem ae_eq_of_markedEnergy_sub_eq_zero
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (h : Poisson.Compensated.markedEnergy P ν T (fun ω s e => φ₁ ω s e - φ₂ ω s e) = 0) :
    (fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
      =ᵐ[Poisson.Compensated.markedEnergyMeasure P ν T] fun p => φ₂ p.1 p.2.1 p.2.2 := by
  have hs : AEStronglyMeasurable (fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 - φ₂ p.1 p.2.1 p.2.2)
      (Poisson.Compensated.markedEnergyMeasure P ν T) := (hm₁.sub hm₂).aestronglyMeasurable
  rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq (φ := fun ω s e => φ₁ ω s e - φ₂ ω s e)
      (hm₁.sub hm₂), pow_eq_zero_iff two_ne_zero] at h
  filter_upwards [(eLpNorm_eq_zero_iff hs two_ne_zero).mp h] with p hp
  exact sub_eq_zero.mp hp

/-- Two jointly measurable marked integrands whose difference has zero marked energy on `[0, T]`
have the same marked energy on `[0, T]`. -/
theorem markedEnergy_eq_of_markedEnergy_sub_eq_zero
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (h : Poisson.Compensated.markedEnergy P ν T (fun ω s e => φ₁ ω s e - φ₂ ω s e) = 0) :
    Poisson.Compensated.markedEnergy P ν T φ₂ = Poisson.Compensated.markedEnergy P ν T φ₁ := by
  rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq hm₁,
    Poisson.Compensated.markedEnergy_eq_eLpNorm_sq hm₂,
    eLpNorm_congr_ae (ae_eq_of_markedEnergy_sub_eq_zero hm₁ hm₂ h)]

omit [SigmaFinite ν] in
/-- For `t ≤ T`, the marked energy on `[0, t]` is at most the marked energy on `[0, T]`. -/
theorem markedEnergy_mono {φ : Ω → ℝ → E → ℝ} {t : ℝ} (htT : t ≤ T) :
    Poisson.Compensated.markedEnergy P ν t φ ≤ Poisson.Compensated.markedEnergy P ν T φ :=
  lintegral_mono fun _ => lintegral_mono_set (Set.Icc_subset_Icc le_rfl htT)

end Marked

/-! ### The stochastic integrals -/

section Integrals

variable [IsProbabilityMeasure P] {d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **The multidimensional Itô integral is unchanged by a change of integrand of zero energy**:
if every coordinate of `Z₁ − Z₂` has zero energy on `[0, T]`, the two integrals agree almost
surely at every time `t ≤ T`. -/
theorem multidimStochasticIntegral_congr_of_energy
    (W : Brownian.Multidim.MultidimBrownianMotion P d)
    (hℱ : ∀ j : Fin d, Brownian.IsBrownianFiltration (W.W j) ℱ) {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)}
    (hm₁ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z₁ s ω j))
    (hp₁ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₁ s ω j)
    (hq₁ : ∀ (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z₁ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z₂ s ω j))
    (hp₂ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₂ s ω j)
    (hq₂ : ∀ (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h : ∀ j : Fin d, Brownian.Ito.energy P T (fun ω s => Z₁ s ω j - Z₂ s ω j) = 0) {t : ℝ}
    (htT : t ≤ T) :
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z₁ hm₁ hp₁ hq₁ t
      =ᵐ[P]
        Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z₂ hm₂ hp₂ hq₂ t := by
  rcases le_or_gt t 0 with ht | ht
  · filter_upwards [Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos
        W ℱ hℱ Z₁ hm₁ hp₁ hq₁ ht,
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos
        W ℱ hℱ Z₂ hm₂ hp₂ hq₂ ht] with ω h1 h2
    rw [h1, h2]
  · refine Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_congr_ae W ℱ hℱ hm₁ hp₁
      hq₁ hm₂ hp₂ hq₂ ht ?_
    have hj : ∀ j : Fin d, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
        Z₁ s ω j = Z₂ s ω j := fun j =>
      ae_ae_eq_of_energy_sub_eq_zero (H₁ := fun ω s => Z₁ s ω j) (H₂ := fun ω s => Z₂ s ω j)
        (hm₁ j) (hm₂ j) (nonpos_iff_eq_zero.mp ((energy_mono htT).trans (h j).le))
    filter_upwards [ae_all_iff.2 hj] with ω hω
    filter_upwards [ae_all_iff.2 hω] with s hs
    exact funext hs

/-- **The compensated integral is unchanged by a change of integrand of zero marked energy**: if
`φ₁ − φ₂` has zero marked energy on `[0, T]`, the two integrals agree almost surely at every
time `t ≤ T`. -/
theorem compensatedIntegral_congr_of_markedEnergy [SigmaFinite ν]
    (N : Poisson.PoissonRandomMeasure P ν) (hℱ : Poisson.IsPoissonFiltration N ℱ)
    {φ₁ φ₂ : Ω → ℝ → E → ℝ}
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hp₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (hq₁ : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hp₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (hq₂ : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h : Poisson.Compensated.markedEnergy P ν T (fun ω s e => φ₁ ω s e - φ₂ ω s e) = 0) {t : ℝ}
    (htT : t ≤ T) :
    Poisson.Compensated.stochasticIntegral N ℱ hℱ φ₁ hm₁ hp₁ hq₁ t
      =ᵐ[P] Poisson.Compensated.stochasticIntegral N ℱ hℱ φ₂ hm₂ hp₂ hq₂ t := by
  rcases le_or_gt t 0 with ht | ht
  · filter_upwards [Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ hm₁ hp₁ hq₁ ht,
      Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ hm₂ hp₂ hq₂ ht] with ω h1 h2
    rw [h1, h2]
  · exact Poisson.Compensated.stochasticIntegral_congr_ae N hℱ φ₁ φ₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ ht
      (ae_eq_of_markedEnergy_sub_eq_zero hm₁ hm₂
        (nonpos_iff_eq_zero.mp ((markedEnergy_mono htT).trans h.le)))

end Integrals

/-! ### Random vectors -/

/-- Two families of almost everywhere measurable random variables whose differences have zero
second moment, `𝔼 ∑ₖ |xₖ − yₖ|² = 0`, agree almost surely coordinatewise. -/
theorem ae_eq_of_lintegral_esq_sub_eq_zero {ι : Type*} [Fintype ι] {x y : ι → Ω → ℝ}
    (hx : ∀ k, AEMeasurable (x k) P) (hy : ∀ k, AEMeasurable (y k) P)
    (h : ∫⁻ ω, esq (fun k => x k ω - y k ω) ∂P = 0) (k : ι) : x k =ᵐ[P] y k := by
  have hm : AEMeasurable (fun ω => esq (fun k => x k ω - y k ω)) P :=
    Finset.aemeasurable_fun_sum _ fun k _ =>
      (((hx k).sub (hy k)).nnnorm.coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hm).mp h] with ω hω
  have hk := (Finset.sum_eq_zero_iff.mp hω) k (Finset.mem_univ k)
  have h0 : x k ω - y k ω = 0 := by simpa using hk
  exact sub_eq_zero.mp h0

end Dissertation.WellPosedness.Existence
