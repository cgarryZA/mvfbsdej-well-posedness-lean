/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.IntegrableDrift
import Dissertation.WellPosedness.System.PaperWeakS2

/-!
# The means of the linear equations with jumps

The Brownian and the compensated Poisson integrals are martingales vanishing at time `0`, so they
have mean zero at every time `t ≥ 0`. For a solution of the linear forward equation

`X_t = ξ₀ + ∫_0^t b_s ds + ∫_0^t σ_s dW_s + ∫_0^t ∫_E γ_s(e) Ñ(ds, de)`

with a deterministic drift, `b_s(ω) = β(s)`, and an integrable `ξ₀`, taking expectations gives
`𝔼 X_t = 𝔼 ξ₀ + ∫_0^t β` for `t ∈ [0, T]`; for `T ≥ 0`, `ξ₀` is integrable as soon as `X_T` is.
For a solution of the linear backward equation

`Y_t = ξ + ∫_t^T φ_s ds − ∫_t^T Z_s dW_s − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`

with a deterministic drift, `φ_s(ω) = β(s)`, and an integrable `ξ`, `𝔼 Y_t = 𝔼 ξ + ∫_t^T β` for
`t ∈ [0, T]`.

## Main statements

* `integral_eq_zero_of_martingale` — a martingale vanishing at `0` has mean zero.
* `integral_multidimStochasticIntegral_eq_zero`, `integral_compensatedStochasticIntegral_eq_zero`
  — the Brownian and the compensated Poisson integrals have mean zero.
* `LinearFSDEJInt.integral_eq_of_deterministic`,
  `LinearFSDEJInt.integrable_initial_of_deterministic`,
  `LinearBSDEJInt.integral_eq_of_deterministic` — the means of the linear equations with a
  deterministic drift.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open LevyStochCalc

/-! ### The means of the stochastic integrals -/

section Martingale

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A real martingale that vanishes almost surely at time `0` has mean `0` at every `t ≥ 0`. -/
theorem integral_eq_zero_of_martingale {F : Filtration ℝ ‹MeasurableSpace Ω›} {M : ℝ → Ω → ℝ}
    (hM : Martingale M F P) (h0 : M 0 =ᵐ[P] 0) {t : ℝ} (ht : 0 ≤ t) : ∫ ω, M t ω ∂P = 0 := by
  have h := hM.setIntegral_eq ht MeasurableSet.univ
  rw [setIntegral_univ, setIntegral_univ, integral_congr_ae h0] at h
  simpa using h.symm

/-- **The multidimensional Itô integral has mean zero** at every time `t ≥ 0`:
`𝔼 ∫_0^t σ_s dW_s = 0`. -/
theorem integral_multidimStochasticIntegral_eq_zero {d : ℕ}
    (W : Brownian.Multidim.MultidimBrownianMotion P d) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : ∀ j, Brownian.IsBrownianFiltration (W.W j) ℱ) (σ : ℝ → Ω → Fin d → ℝ)
    (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ s ω j))
    (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => σ s ω j)
    (hq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ σ hm hp hq t ω ∂P
      = 0 := by
  unfold Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
    Brownian.Ito.stochasticIntegral
  rw [integral_finsetSum _ fun j _ => (Brownian.Ito.stochasticIntegralBrownian_memLp (W.W j) ℱ
    (hℱ j) _ (hm j) (hp j) (hq j) t).integrable one_le_two]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact integral_eq_zero_of_martingale
    (Brownian.Ito.martingale_stochasticIntegralBrownian (W.W j) ℱ (hℱ j) _ (hm j) (hp j) (hq j))
    (Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos (W.W j) ℱ (hℱ j) _ (hm j) (hp j)
      (hq j) le_rfl) ht

/-- **The compensated Poisson integral has mean zero** at every time `t ≥ 0`:
`𝔼 ∫_0^t ∫_E φ_s(e) Ñ(ds, de) = 0`. -/
theorem integral_compensatedStochasticIntegral_eq_zero {E : Type*} [MeasurableSpace E]
    {ν : Measure E} [SigmaFinite ν] (N : Poisson.PoissonRandomMeasure P ν)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ : Poisson.IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ) (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t ω ∂P = 0 :=
  integral_eq_zero_of_martingale
    (Poisson.Compensated.martingale_stochasticIntegral_rightCont N ℱ hℱ φ hm hp hq)
    ((Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ φ hm hp hq 0).trans
      (Poisson.Compensated.process_ae_zero_of_nonpos N ℱ hℱ φ hm hp hq le_rfl)) ht

end Martingale

end Dissertation.WellPosedness.System

/-! ### The means of the linear equations with a deterministic drift -/

namespace Dissertation.WellPosedness.Stability

open Dissertation.WellPosedness.System LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω} [IsProbabilityMeasure P]
  {d : ℕ} {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {β : ℝ → ℝ}

namespace LinearFSDEJInt

variable {ξ : Ω → ℝ} {b : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ} {σ : ℝ → Ω → (Fin d → ℝ)}
  {γ : ℝ → Ω → E → ℝ}

omit [MeasurableSpace.CountablyGenerated E] in
/-- **The mean of a solution of the linear forward equation with a deterministic drift**: if
`b_s(ω) = β(s)` for every `ω` and `s` and `ξ₀` is integrable, then `𝔼 X_t = 𝔼 ξ₀ + ∫_0^t β` for
every `t ∈ [0, T]`. -/
theorem integral_eq_of_deterministic (h : LinearFSDEJInt D ℱ hℱW hℱN T ξ b X σ γ)
    (hξ : Integrable ξ P) (hb : ∀ ω s, b ω s = β s) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ ω, X t ω ∂P = ∫ ω, ξ ω ∂P + ∫ s in Set.Icc 0 t, β s := by
  set M := Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW σ h.σ_meas
    h.σ_prog (sq_int_global_of_vanishing h.σ_vanish h.σ_sq) t with hMdef
  set J := Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => γ s ω' e) h.γ_meas
    h.γ_prog (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) t with hJdef
  set c := ∫ s in Set.Icc (0 : ℝ) t, β s with hcdef
  have hM : Integrable M P := (memLp_multidimStochasticIntegral (D := D) (hℱW := hℱW) σ
    h.σ_meas h.σ_prog (sq_int_global_of_vanishing h.σ_vanish h.σ_sq) t).integrable one_le_two
  have hJ : Integrable J P := (Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN _ h.γ_meas
    h.γ_prog (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) t).integrable one_le_two
  have h1 : Integrable (fun ω => ξ ω + c) P := hξ.add (integrable_const c)
  have h2 : Integrable (fun ω => ξ ω + c + M ω) P := h1.add hM
  have e : (fun ω => X t ω) =ᵐ[P] fun ω => ξ ω + c + M ω + J ω := by
    filter_upwards [h.eqn t ht] with ω hω
    rw [hω, integral_congr_ae (ae_of_all _ fun s => hb ω s)]
  rw [integral_congr_ae e, integral_add h2 hJ, integral_add h1 hM, integral_add hξ
    (integrable_const c), integral_const, hMdef, hJdef,
    integral_multidimStochasticIntegral_eq_zero _ _ _ _ _ _ ht.1,
    integral_compensatedStochasticIntegral_eq_zero _ _ _ _ _ _ ht.1]
  simp

omit [MeasurableSpace.CountablyGenerated E] in
/-- **A solution of the linear forward equation with a deterministic drift has an integrable
initial value** when `X_T` is integrable, for `T ≥ 0`: by the equation at `T`, `ξ₀` is `X_T`
minus a constant and two square-integrable stochastic integrals. -/
theorem integrable_initial_of_deterministic (h : LinearFSDEJInt D ℱ hℱW hℱN T ξ b X σ γ)
    (hX : Integrable (X T) P) (hb : ∀ ω s, b ω s = β s) (hT : 0 ≤ T) : Integrable ξ P := by
  have hM := (memLp_multidimStochasticIntegral (D := D) (hℱW := hℱW) σ h.σ_meas h.σ_prog
    (sq_int_global_of_vanishing h.σ_vanish h.σ_sq) T).integrable one_le_two
  have hN := (Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN _ h.γ_meas h.γ_prog
    (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) T).integrable one_le_two
  refine (((hX.sub (integrable_const (∫ s in Set.Icc (0 : ℝ) T, β s))).sub hM).sub hN).congr ?_
  filter_upwards [h.eqn T ⟨hT, le_rfl⟩] with ω hω
  simp only [Pi.sub_apply]
  rw [hω, integral_congr_ae (ae_of_all _ fun s => hb ω s)]
  ring

end LinearFSDEJInt

omit [MeasurableSpace.CountablyGenerated E] in
/-- **The mean of a solution of the linear backward equation with a deterministic drift**: if
`φ_s(ω) = β(s)` for every `ω` and `s` and the terminal value `ξ` is integrable, then
`𝔼 Y_t = 𝔼 ξ + ∫_t^T β` for every `t ∈ [0, T]`. -/
theorem LinearBSDEJInt.integral_eq_of_deterministic {ξ : Ω → ℝ} {φ : Ω → ℝ → ℝ}
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (h : LinearBSDEJInt D ℱ hℱW hℱN T ξ φ Y Z U) (hξ : Integrable ξ P)
    (hφ : ∀ ω s, φ ω s = β s) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ ω, Y t ω ∂P = ∫ ω, ξ ω ∂P + ∫ s in Set.Icc t T, β s := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  set M := Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z h.Z_meas
    h.Z_prog (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) with hMdef
  set J := Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) h.U_meas
    h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) with hJdef
  set c := ∫ s in Set.Icc t T, β s with hcdef
  have hM : ∀ r, Integrable (M r) P := fun r => (memLp_multidimStochasticIntegral (D := D)
    (hℱW := hℱW) Z h.Z_meas h.Z_prog (sq_int_global_of_vanishing h.Z_vanish h.Z_sq)
    r).integrable one_le_two
  have hJ : ∀ r, Integrable (J r) P := fun r => (Poisson.Compensated.stochasticIntegral_memLp
    D.N ℱ hℱN _ h.U_meas h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq)
    r).integrable one_le_two
  have hM0 : ∀ r, 0 ≤ r → ∫ ω, M r ω ∂P = 0 := fun r hr =>
    integral_multidimStochasticIntegral_eq_zero _ _ _ _ _ _ hr
  have hJ0 : ∀ r, 0 ≤ r → ∫ ω, J r ω ∂P = 0 := fun r hr =>
    integral_compensatedStochasticIntegral_eq_zero _ _ _ _ _ _ hr
  have h1 : Integrable (fun ω => ξ ω + c) P := hξ.add (integrable_const c)
  have h2 : Integrable (fun ω => M T ω - M t ω) P := (hM T).sub (hM t)
  have h3 : Integrable (fun ω => J T ω - J t ω) P := (hJ T).sub (hJ t)
  have h4 : Integrable (fun ω => ξ ω + c - (M T ω - M t ω)) P := h1.sub h2
  have e : (fun ω => Y t ω) =ᵐ[P] fun ω => ξ ω + c - (M T ω - M t ω) - (J T ω - J t ω) := by
    filter_upwards [h.eqn t ht] with ω hω
    rw [hω, integral_congr_ae (ae_of_all _ fun s => hφ ω s)]
  rw [integral_congr_ae e, integral_sub h4 h3, integral_sub h1 h2, integral_add hξ
    (integrable_const c), integral_const, integral_sub (hM T) (hM t),
    integral_sub (hJ T) (hJ t), hM0 T hT, hM0 t ht.1, hJ0 T hT, hJ0 t ht.1]
  simp

end Dissertation.WellPosedness.Stability
