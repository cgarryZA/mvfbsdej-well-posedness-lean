/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.ForwardEq

/-!
# Linear combinations of solutions of the linear equations with jumps

The linear backward equation (4.4) and the linear forward equation are linear in all their data:
if `(Y¹, Z¹, U¹)` and `(Y², Z², U²)` solve the backward equation with terminal values `ξ¹, ξ²`
and drifts `φ¹, φ²`, then for real `a, c` the combination `(aY¹ + cY², aZ¹ + cZ², aU¹ + cU²)`
solves it with terminal value `aξ¹ + cξ²` and drift `aφ¹ + cφ²`, and likewise for the forward
equation. The two stochastic integrals are linear in the integrand almost surely at each time,
and the drift integral is linear at every sample point whose drift paths are integrable
(`ae_setIntegral_linComb_of_integrableOn`), in particular for drifts of finite energy. In
particular the difference of two solutions solves the difference equation, which is how the
difference system (4.15)–(4.16) of Lemma 4.3 arises from two solutions of (4.1).

## Main statements

* `stochasticIntegralBrownian_linComb_ae`, `multidimStochasticIntegral_linComb_ae`,
  `compensatedIntegral_linComb_ae` — linearity of the stochastic integrals at each time.
* `ae_setIntegral_linComb_of_integrableOn` — linearity of the drift integral for drifts with
  almost surely integrable paths.
* `LinearBSDEJ.linComb`, `LinearBSDEJ.sub` — the backward equation.
* `LinearFSDEJ.linComb`, `LinearFSDEJ.sub` — the forward equation.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc Dissertation.WellPosedness.BrownianPoisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-! ### Linearity of the stochastic integrals -/

/-- **The Itô integral of `a H₁ + c H₂` is `a ∫ H₁ dW + c ∫ H₂ dW`**, almost surely at each
time. -/
theorem stochasticIntegralBrownian_linComb_ae (W : Brownian.BrownianMotion P)
    (hℱ : Brownian.IsBrownianFiltration W ℱ) {H₁ H₂ : Ω → ℝ → ℝ} (a c : ℝ)
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm : Measurable (Function.uncurry fun ω s => a * H₁ ω s + c * H₂ ω s))
    (hp : Probability.ProgressivelyMeasurable ℱ fun ω s => a * H₁ ω s + c * H₂ ω s)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖a * H₁ ω s + c * H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ) :
    Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => a * H₁ ω s + c * H₂ ω s)
        hm hp hq t
      =ᵐ[P] fun ω => a * Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t ω
        + c * Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t ω := by
  rcases le_or_gt t 0 with ht | ht
  · filter_upwards [Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ _ hm hp hq ht,
      Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ _ hm₁ hp₁ hq₁ ht,
      Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ _ hm₂ hp₂ hq₂ ht]
      with ω e0 e1 e2
    simp only [Pi.zero_apply] at e0 e1 e2
    rw [e0, e1, e2]
    ring
  · have hm₁' : Measurable (Function.uncurry fun ω s => a * H₁ ω s) := hm₁.const_mul a
    have hm₂' : Measurable (Function.uncurry fun ω s => c * H₂ ω s) := hm₂.const_mul c
    have hp₁' : Probability.ProgressivelyMeasurable ℱ fun ω s => a * H₁ ω s :=
      (continuous_const_mul a).comp_progressivelyMeasurable (mul_zero a) hp₁
    have hp₂' : Probability.ProgressivelyMeasurable ℱ fun ω s => c * H₂ ω s :=
      (continuous_const_mul c).comp_progressivelyMeasurable (mul_zero c) hp₂
    have hq₁' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖a * H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun T hT =>
      lt_top_iff_ne_top.mpr (Brownian.Ito.energy_const_mul_ne_top hm₁ (hq₁ T hT).ne a)
    have hq₂' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖c * H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun T hT =>
      lt_top_iff_ne_top.mpr (Brownian.Ito.energy_const_mul_ne_top hm₂ (hq₂ T hT).ne c)
    filter_upwards [Brownian.Ito.stochasticIntegralBrownian_add W ℱ hℱ hm₁' hm₂' hp₁' hp₂' hq₁'
        hq₂' hm hp hq ht,
      Brownian.Ito.stochasticIntegralBrownian_const_mul W ℱ hℱ hm₁ hp₁ hq₁ a hm₁' hp₁' hq₁' ht,
      Brownian.Ito.stochasticIntegralBrownian_const_mul W ℱ hℱ hm₂ hp₂ hq₂ c hm₂' hp₂' hq₂' ht]
      with ω e0 e1 e2
    rw [e0, e1, e2]

/-- **The multidimensional Itô integral of `a Z₁ + c Z₂` is `a ∫ Z₁ dW + c ∫ Z₂ dW`**, almost
surely at each time. -/
theorem multidimStochasticIntegral_linComb_ae (W : Brownian.Multidim.MultidimBrownianMotion P d)
    (hℱ : ∀ j : Fin d, Brownian.IsBrownianFiltration (W.W j) ℱ) {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)}
    (a c : ℝ)
    (hm₁ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z₁ s ω j))
    (hm₂ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z₂ s ω j))
    (hp₁ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₁ s ω j)
    (hp₂ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₂ s ω j)
    (hq₁ : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z₁ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hq₂ : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => a * Z₁ s ω j + c * Z₂ s ω j))
    (hp : ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ fun ω s => a * Z₁ s ω j + c * Z₂ s ω j)
    (hq : ∀ (j : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖a * Z₁ s ω j + c * Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ) :
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ
        (fun s ω j => a * Z₁ s ω j + c * Z₂ s ω j) hm hp hq t
      =ᵐ[P] fun ω =>
        a * Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z₁ hm₁ hp₁ hq₁ t ω
        + c * Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z₂ hm₂ hp₂ hq₂
          t ω := by
  have hj : ∀ j : Fin d, ∀ᵐ ω ∂P,
      Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hℱ j)
          (fun ω s => a * Z₁ s ω j + c * Z₂ s ω j) (hm j) (hp j) (hq j) t ω
        = a * Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hℱ j) (fun ω s => Z₁ s ω j)
            (hm₁ j) (hp₁ j) (hq₁ j) t ω
          + c * Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hℱ j) (fun ω s => Z₂ s ω j)
            (hm₂ j) (hp₂ j) (hq₂ j) t ω := fun j =>
    stochasticIntegralBrownian_linComb_ae (W.W j) (hℱ j) (H₁ := fun ω s => Z₁ s ω j)
      (H₂ := fun ω s => Z₂ s ω j) a c (hm₁ j) (hm₂ j) (hp₁ j) (hp₂ j) (hq₁ j) (hq₂ j) (hm j)
      (hp j) (hq j) t
  filter_upwards [ae_all_iff.mpr hj] with ω hω
  simp only [Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral,
    Brownian.Ito.stochasticIntegral]
  rw [Finset.sum_congr rfl fun j _ => hω j, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.mul_sum]

/-- **The compensated integral of `a φ₁ + c φ₂` is `a ∫∫ φ₁ dÑ + c ∫∫ φ₂ dÑ`**, almost surely at
each time. -/
theorem compensatedIntegral_linComb_ae (N : Poisson.PoissonRandomMeasure P ν)
    (hℱ : Poisson.IsPoissonFiltration N ℱ) {φ₁ φ₂ : Ω → ℝ → E → ℝ} (a c : ℝ)
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hp₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (hp₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (hq₁ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hq₂ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hm : Measurable fun p : Ω × ℝ × E => a * φ₁ p.1 p.2.1 p.2.2 + c * φ₂ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => a * φ₁ ω s e + c * φ₂ ω s e)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖a * φ₁ ω s e + c * φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) (t : ℝ) :
    Poisson.Compensated.stochasticIntegral N ℱ hℱ (fun ω s e => a * φ₁ ω s e + c * φ₂ ω s e)
        hm hp hq t
      =ᵐ[P] fun ω => a * Poisson.Compensated.stochasticIntegral N ℱ hℱ φ₁ hm₁ hp₁ hq₁ t ω
        + c * Poisson.Compensated.stochasticIntegral N ℱ hℱ φ₂ hm₂ hp₂ hq₂ t ω := by
  rcases le_or_gt t 0 with ht | ht
  · filter_upwards [Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ hm hp hq ht,
      Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ hm₁ hp₁ hq₁ ht,
      Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ hm₂ hp₂ hq₂ ht]
      with ω e0 e1 e2
    simp only [Pi.zero_apply] at e0 e1 e2
    rw [e0, e1, e2]
    ring
  · have hm₁' : Measurable fun p : Ω × ℝ × E => a * φ₁ p.1 p.2.1 p.2.2 := hm₁.const_mul a
    have hm₂' : Measurable fun p : Ω × ℝ × E => c * φ₂ p.1 p.2.1 p.2.2 := hm₂.const_mul c
    have hp₁' := Poisson.Compensated.markedProgressivelyMeasurable_const_mul hp₁ a
    have hp₂' := Poisson.Compensated.markedProgressivelyMeasurable_const_mul hp₂ c
    have hq₁' : ∀ T : ℝ, 0 < T → Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => a * φ₁ ω s e) < ⊤ := fun T hT =>
      lt_top_iff_ne_top.mpr (Poisson.Compensated.markedEnergy_const_mul_ne_top hm₁ (hq₁ T hT).ne a)
    have hq₂' : ∀ T : ℝ, 0 < T → Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => c * φ₂ ω s e) < ⊤ := fun T hT =>
      lt_top_iff_ne_top.mpr (Poisson.Compensated.markedEnergy_const_mul_ne_top hm₂ (hq₂ T hT).ne c)
    filter_upwards [Poisson.Compensated.stochasticIntegral_add N ℱ hℱ hm₁' hm₂' hp₁' hp₂' hq₁'
        hq₂' hm hp hq ht,
      Poisson.Compensated.stochasticIntegral_const_mul N ℱ hℱ hm₁ hp₁ hq₁ a hm₁' hp₁' hq₁' ht,
      Poisson.Compensated.stochasticIntegral_const_mul N ℱ hℱ hm₂ hp₂ hq₂ c hm₂' hp₂' hq₂' ht]
      with ω e0 e1 e2
    rw [e0, e1, e2]

/-! ### The linear backward equation -/

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {T : ℝ} {ξ₁ ξ₂ : Ω → ℝ} {φ₁ φ₂ : Ω → ℝ → ℝ} {Y₁ Y₂ : ℝ → Ω → ℝ}
  {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U₁ U₂ : ℝ → Ω → E → ℝ}

omit [IsProbabilityMeasure P] in
/-- On almost every sample point, the drift integral over a set `S ⊆ [0, T]` of `a φ₁ + c φ₂` is
`a ∫_S φ₁ + c ∫_S φ₂`, for drifts whose paths are almost surely integrable on `[0, T]`. -/
theorem ae_setIntegral_linComb_of_integrableOn {φ₁ φ₂ : Ω → ℝ → ℝ} (a c : ℝ)
    (h₁ : ∀ᵐ ω ∂P, IntegrableOn (φ₁ ω) (Set.Icc (0 : ℝ) T))
    (h₂ : ∀ᵐ ω ∂P, IntegrableOn (φ₂ ω) (Set.Icc (0 : ℝ) T)) {S : Set ℝ}
    (hS : S ⊆ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∫ s in S, (a * φ₁ ω s + c * φ₂ ω s)
      = a * (∫ s in S, φ₁ ω s) + c * ∫ s in S, φ₂ ω s := by
  filter_upwards [h₁, h₂] with ω i₁ i₂
  rw [integral_add ((i₁.mono_set hS).const_mul a) ((i₂.mono_set hS).const_mul c),
    integral_const_mul, integral_const_mul]

omit [IsProbabilityMeasure P] in
/-- On almost every sample point, the drift integral over `[t, T] ⊆ [0, T]` of `a φ₁ + c φ₂` is
`a ∫ φ₁ + c ∫ φ₂`, for drifts of finite energy on `[0, T]`. -/
theorem ae_setIntegral_linComb {φ₁ φ₂ : Ω → ℝ → ℝ} (a c : ℝ)
    (hm₁ : Measurable (Function.uncurry φ₁)) (hm₂ : Measurable (Function.uncurry φ₂))
    (hq₁ : Brownian.Ito.energy P T φ₁ ≠ ⊤) (hq₂ : Brownian.Ito.energy P T φ₂ ≠ ⊤) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∫ s in Set.Icc t T, (a * φ₁ ω s + c * φ₂ ω s)
      = a * (∫ s in Set.Icc t T, φ₁ ω s) + c * ∫ s in Set.Icc t T, φ₂ ω s :=
  ae_setIntegral_linComb_of_integrableOn a c (ae_mem_integrablePaths hm₁ hq₁)
    (ae_mem_integrablePaths hm₂ hq₂) (Set.Icc_subset_Icc ht le_rfl)

/-- **Linear combinations of solutions of the linear backward equation are solutions**: for
real `a, c`, `(aY¹ + cY², aZ¹ + cZ², aU¹ + cU²)` solves it with terminal value `aξ¹ + cξ²` and
drift `aφ¹ + cφ²`. -/
theorem _root_.Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ.linComb
    (h₁ : LinearBSDEJ D ℱ hℱW hℱN T ξ₁ φ₁ Y₁ Z₁ U₁)
    (h₂ : LinearBSDEJ D ℱ hℱW hℱN T ξ₂ φ₂ Y₂ Z₂ U₂) (a c : ℝ) :
    LinearBSDEJ D ℱ hℱW hℱN T (fun ω => a * ξ₁ ω + c * ξ₂ ω)
      (fun ω s => a * φ₁ ω s + c * φ₂ ω s) (fun t ω => a * Y₁ t ω + c * Y₂ t ω)
      (fun s ω j => a * Z₁ s ω j + c * Z₂ s ω j) (fun s ω e => a * U₁ s ω e + c * U₂ s ω e) := by
  have hZm : ∀ j : Fin d,
      Measurable (Function.uncurry fun ω s => a * Z₁ s ω j + c * Z₂ s ω j) := fun j =>
    ((h₁.Z_meas j).const_mul a).add ((h₂.Z_meas j).const_mul c)
  have hZp : ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ fun ω s => a * Z₁ s ω j + c * Z₂ s ω j := fun j =>
    ((continuous_const_mul a).comp_progressivelyMeasurable (mul_zero a) (h₁.Z_prog j)).add
      ((continuous_const_mul c).comp_progressivelyMeasurable (mul_zero c) (h₂.Z_prog j))
  have hZv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → (fun j => a * Z₁ s ω j + c * Z₂ s ω j) = 0 :=
    fun ω s hs => by
      funext j
      simp [h₁.Z_vanish ω s hs, h₂.Z_vanish ω s hs]
  have hZq : ∀ j : Fin d, Brownian.Ito.energy P T
      (fun ω s => a * Z₁ s ω j + c * Z₂ s ω j) ≠ ⊤ := fun j =>
    Brownian.Ito.energy_add_ne_top ((h₁.Z_meas j).const_mul a) ((h₂.Z_meas j).const_mul c)
      (Brownian.Ito.energy_const_mul_ne_top (h₁.Z_meas j) (h₁.Z_sq j) a)
      (Brownian.Ito.energy_const_mul_ne_top (h₂.Z_meas j) (h₂.Z_sq j) c)
  have hUm : Measurable fun p : Ω × ℝ × E => a * U₁ p.2.1 p.1 p.2.2 + c * U₂ p.2.1 p.1 p.2.2 :=
    (h₁.U_meas.const_mul a).add (h₂.U_meas.const_mul c)
  have hUp : Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => a * U₁ s ω e + c * U₂ s ω e :=
    Poisson.Compensated.markedProgressivelyMeasurable_add
      (Poisson.Compensated.markedProgressivelyMeasurable_const_mul h₁.U_prog a)
      (Poisson.Compensated.markedProgressivelyMeasurable_const_mul h₂.U_prog c)
  have hUv : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → a * U₁ s ω e + c * U₂ s ω e = 0 :=
    fun ω s e hs => by simp [h₁.U_vanish ω s e hs, h₂.U_vanish ω s e hs]
  have hUq : Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => a * U₁ s ω e + c * U₂ s ω e) ≠ ⊤ :=
    Poisson.Compensated.markedEnergy_add_ne_top (h₁.U_meas.const_mul a)
      (h₂.U_meas.const_mul c)
      (Poisson.Compensated.markedEnergy_const_mul_ne_top h₁.U_meas h₁.U_sq a)
      (Poisson.Compensated.markedEnergy_const_mul_ne_top h₂.U_meas h₂.U_sq c)
  refine
    { Z_meas := hZm
      Z_prog := hZp
      Z_vanish := hZv
      Z_sq := hZq
      U_meas := hUm
      U_prog := hUp
      U_vanish := hUv
      U_sq := hUq
      φ_meas := (h₁.φ_meas.const_mul a).add (h₂.φ_meas.const_mul c)
      φ_prog := ((continuous_const_mul a).comp_progressivelyMeasurable (mul_zero a)
        h₁.φ_prog).add ((continuous_const_mul c).comp_progressivelyMeasurable (mul_zero c)
        h₂.φ_prog)
      φ_vanish := fun ω s hs => by simp [h₁.φ_vanish ω s hs, h₂.φ_vanish ω s hs]
      φ_sq := Brownian.Ito.energy_add_ne_top (h₁.φ_meas.const_mul a) (h₂.φ_meas.const_mul c)
        (Brownian.Ito.energy_const_mul_ne_top h₁.φ_meas h₁.φ_sq a)
        (Brownian.Ito.energy_const_mul_ne_top h₂.φ_meas h₂.φ_sq c)
      ξ_sq := (h₁.ξ_sq.const_mul a).add (h₂.ξ_sq.const_mul c)
      Y_adapted := fun t => ((h₁.Y_adapted t).const_mul a).add ((h₂.Y_adapted t).const_mul c)
      Y_rightCont := fun ω t =>
        ((h₁.Y_rightCont ω t).const_mul a).add ((h₂.Y_rightCont ω t).const_mul c)
      eqn := ?_ }
  intro t ht
  have hW := fun r => multidimStochasticIntegral_linComb_ae D.W hℱW a c h₁.Z_meas h₂.Z_meas
    h₁.Z_prog h₂.Z_prog (sq_int_global_of_vanishing h₁.Z_vanish h₁.Z_sq)
    (sq_int_global_of_vanishing h₂.Z_vanish h₂.Z_sq) hZm hZp
    (sq_int_global_of_vanishing hZv hZq) r
  have hN := fun r => compensatedIntegral_linComb_ae D.N hℱN (φ₁ := fun ω s e => U₁ s ω e)
    (φ₂ := fun ω s e => U₂ s ω e) a c h₁.U_meas h₂.U_meas h₁.U_prog h₂.U_prog
    (marked_sq_int_global_of_vanishing h₁.U_vanish h₁.U_sq)
    (marked_sq_int_global_of_vanishing h₂.U_vanish h₂.U_sq) hUm hUp
    (marked_sq_int_global_of_vanishing hUv hUq) r
  filter_upwards [h₁.eqn t ht, h₂.eqn t ht, hW T, hW t, hN T, hN t,
    ae_setIntegral_linComb a c h₁.φ_meas h₂.φ_meas h₁.φ_sq h₂.φ_sq ht.1]
    with ω e₁ e₂ eWT eWt eNT eNt eφ
  rw [e₁, e₂, eφ, eWT, eWt, eNT, eNt]
  ring

/-- **The difference of two solutions of the linear backward equation solves it** with the
differenced terminal value and drift. -/
theorem _root_.Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ.sub
    (h₁ : LinearBSDEJ D ℱ hℱW hℱN T ξ₁ φ₁ Y₁ Z₁ U₁)
    (h₂ : LinearBSDEJ D ℱ hℱW hℱN T ξ₂ φ₂ Y₂ Z₂ U₂) :
    LinearBSDEJ D ℱ hℱW hℱN T (fun ω => ξ₁ ω - ξ₂ ω) (fun ω s => φ₁ ω s - φ₂ ω s)
      (fun t ω => Y₁ t ω - Y₂ t ω) (fun s ω j => Z₁ s ω j - Z₂ s ω j)
      (fun s ω e => U₁ s ω e - U₂ s ω e) := by
  simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg] using h₁.linComb h₂ 1 (-1)

/-! ### The linear forward equation -/

namespace LinearFSDEJ

variable {ξ₀₁ ξ₀₂ : Ω → ℝ} {b₁ b₂ : Ω → ℝ → ℝ} {X₁ X₂ : ℝ → Ω → ℝ}
  {σ₁ σ₂ : ℝ → Ω → (Fin d → ℝ)} {γ₁ γ₂ : ℝ → Ω → E → ℝ}

/-- **Linear combinations of solutions of the linear forward equation are solutions**: for real
`a, c`, `aX¹ + cX²` solves it with initial value `aξ₀¹ + cξ₀²`, drift `ab¹ + cb²`, diffusion
vector `aσ¹ + cσ²` and jump integrand `aγ¹ + cγ²`. -/
theorem linComb (h₁ : LinearFSDEJ D ℱ hℱW hℱN T ξ₀₁ b₁ X₁ σ₁ γ₁)
    (h₂ : LinearFSDEJ D ℱ hℱW hℱN T ξ₀₂ b₂ X₂ σ₂ γ₂) (a c : ℝ) (hT : 0 ≤ T) :
    LinearFSDEJ D ℱ hℱW hℱN T (fun ω => a * ξ₀₁ ω + c * ξ₀₂ ω)
      (fun ω s => a * b₁ ω s + c * b₂ ω s) (fun t ω => a * X₁ t ω + c * X₂ t ω)
      (fun s ω j => a * σ₁ s ω j + c * σ₂ s ω j) (fun s ω e => a * γ₁ s ω e + c * γ₂ s ω e) := by
  have h := (h₁.linearBSDEJ hT).linComb (h₂.linearBSDEJ hT) a c
  have h0 : (fun ω => a * X₁ 0 ω + c * X₂ 0 ω) =ᵐ[P] fun ω => a * ξ₀₁ ω + c * ξ₀₂ ω := by
    filter_upwards [h₁.initial_ae_eq hT, h₂.initial_ae_eq hT] with ω e₁ e₂
    rw [e₁, e₂]
  have hb : (fun ω s => -(a * -b₁ ω s + c * -b₂ ω s)) = fun ω s => a * b₁ ω s + c * b₂ ω s := by
    funext ω s
    ring
  simpa only [hb] using h.linearFSDEJ h0 hT

/-- **The difference of two solutions of the linear forward equation solves it** with the
differenced initial value, drift, diffusion vector and jump integrand. -/
theorem sub (h₁ : LinearFSDEJ D ℱ hℱW hℱN T ξ₀₁ b₁ X₁ σ₁ γ₁)
    (h₂ : LinearFSDEJ D ℱ hℱW hℱN T ξ₀₂ b₂ X₂ σ₂ γ₂) (hT : 0 ≤ T) :
    LinearFSDEJ D ℱ hℱW hℱN T (fun ω => ξ₀₁ ω - ξ₀₂ ω) (fun ω s => b₁ ω s - b₂ ω s)
      (fun t ω => X₁ t ω - X₂ t ω) (fun s ω j => σ₁ s ω j - σ₂ s ω j)
      (fun s ω e => γ₁ s ω e - γ₂ s ω e) := by
  simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg] using h₁.linComb h₂ 1 (-1) hT

end LinearFSDEJ

end Dissertation.WellPosedness.Stability
