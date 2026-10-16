/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.ForwardEq

/-!
# The weighted second-moment identity of the linear equations

For a solution `(Y, Z, U)` of the linear backward equation with drift `φ` over a filtration
carrying the driver with a cross witness, frozen at the horizon, `Y` is an Itô–Lévy process with
drift `−φ`, and integration by parts against `e^{βs}` gives, for every `β` and `T > 0`,

`e^{βT} 𝔼[Y_T²] = 𝔼[Y_0²] + ∫_0^T e^{βs} (β 𝔼[Y_s²] + 2 𝔼[Y_s (−φ_s)] + ∑_j 𝔼[Z_j(s)²]
  + 𝔼 ∫_E U(s, e)² ν(de)) ds`,

with an integrable time integrand. On `[0, T]` the frozen process is the solution itself, so the
identity is stated for `Y`. For a solution `X` of the linear forward equation with drift `b` the
same identity holds with `2 𝔼[X_s b_s]` as the drift term. The forward and backward estimates of
Lemma 4.3 of the well-posedness paper bound the integrand with Young's inequality in expectation,
`2 a 𝔼[x y] ≤ a² 𝔼[x²] + 𝔼[y²]`.

## Main statements

* `two_mul_integral_mul_le` — Young's inequality in expectation.
* `LinearBSDEJ.exp_mul_integral_mul_self_eq`, `LinearFSDEJ.exp_mul_integral_mul_self_eq` — the
  weighted identities.
* `LinearBSDEJ.integrableOn_exp_mul_rate`, `LinearFSDEJ.integrableOn_exp_mul_rate` — their time
  integrands are integrable.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc Dissertation.WellPosedness.BrownianPoisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {d : ℕ}

/-- **Young's inequality in expectation**: `2 a 𝔼[x y] ≤ a² 𝔼[x²] + 𝔼[y²]` for square-integrable
`x`, `y`. -/
theorem two_mul_integral_mul_le {x y : Ω → ℝ} (hx : MemLp x 2 P) (hy : MemLp y 2 P) (a : ℝ) :
    2 * a * ∫ ω, x ω * y ω ∂P ≤ a ^ 2 * ∫ ω, x ω * x ω ∂P + ∫ ω, y ω * y ω ∂P := by
  have hxy : Integrable (fun ω => x ω * y ω) P := hx.integrable_mul hy
  have hxx : Integrable (fun ω => x ω * x ω) P := hx.integrable_mul hx
  have hyy : Integrable (fun ω => y ω * y ω) P := hy.integrable_mul hy
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hxx.const_mul _) hyy]
  exact integral_mono (hxy.const_mul _) ((hxx.const_mul _).add hyy) fun ω => by
    nlinarith [sq_nonneg (a * x ω - y ω)]

variable [IsProbabilityMeasure P] [SigmaFinite ν]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

section Backward

variable {ξ : Ω → ℝ} {φ : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → Fin d → ℝ}
  {U : ℝ → Ω → E → ℝ}

/-- **The weighted second-moment identity of a solution of the linear backward equation**, over
a filtration with a cross witness. -/
theorem _root_.Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ.exp_mul_integral_mul_self_eq
    (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (𝒲 : D.CrossWitness ℱ) (β : ℝ) (hT : 0 < T) :
    Real.exp (β * T) * ∫ ω, Y T ω * Y T ω ∂P
      = ∫ ω, Y 0 ω * Y 0 ω ∂P + ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s)
          * (β * ∫ ω, Y s ω * Y s ω ∂P + 2 * ∫ ω, Y s ω * -φ ω s ∂P
            + (∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
            + (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) := by
  have key := Ito.SecondMoment.integral_exp_mul_self_eq_of_isItoLevyProcess
    (h.isItoLevyProcess_clampT hT) 𝒲 h.stronglyMeasurable_initial (h.memLp_initial hT.le)
    h.φ_meas.neg (continuous_neg.comp_progressivelyMeasurable neg_zero h.φ_prog)
    (fun T' _ => neg_drift_sq_int_global h.φ_vanish h.φ_sq T') β hT
  rw [clampT_apply_of_le (le_refl T)] at key
  rw [key]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  simp only [clampT_apply_of_le hs.2]

/-- The time integrand of the weighted identity of a solution of the linear backward equation is
integrable on `[0, T]`. -/
theorem _root_.Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ.integrableOn_exp_mul_rate
    (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (𝒲 : D.CrossWitness ℱ) (β : ℝ) (hT : 0 < T) :
    IntegrableOn (fun s => Real.exp (β * s)
      * (β * ∫ ω, Y s ω * Y s ω ∂P + 2 * ∫ ω, Y s ω * -φ ω s ∂P
        + (∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
        + (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)) (Set.Icc (0 : ℝ) T) := by
  have hI := h.isItoLevyProcess_clampT hT
  have hbq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖-φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun T' _ =>
    neg_drift_sq_int_global h.φ_vanish h.φ_sq T'
  have hbp : Probability.ProgressivelyMeasurable ℱ fun ω s => -φ ω s :=
    continuous_neg.comp_progressivelyMeasurable neg_zero h.φ_prog
  have hA := Ito.SecondMoment.integrableOn_integral_mul_self hI 𝒲 h.stronglyMeasurable_initial
    (h.memLp_initial hT.le) h.φ_meas.neg hbp hbq hT
  have hB := Ito.SecondMoment.integrableOn_integral_mul_drift hI (h.memLp_initial hT.le)
    h.φ_meas.neg hbp hbq hT
  have hC : IntegrableOn (fun s => ∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      (Set.Icc (0 : ℝ) T) :=
    integrable_finsetSum _ fun j _ => Ito.SecondMoment.integrableOn_toReal_lintegral
      (Ito.SecondMoment.measurable_uncurry_sq_diffusion hI j) (hI.σ_sq j T hT)
  have hG := Ito.SecondMoment.integrableOn_toReal_lintegral
    (Ito.SecondMoment.measurable_uncurry_lintegral_sq_jump hI) (hI.γ_sq T hT)
  refine (Ito.SecondMoment.integrableOn_exp_mul β ((((hA.const_mul β).add
    (hB.const_mul 2)).add hC).add hG)).congr_fun (fun s hs => ?_) measurableSet_Icc
  simp only [Pi.add_apply, clampT_apply_of_le hs.2]

end Backward

namespace LinearFSDEJ

variable {ξ₀ : Ω → ℝ} {b : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ}
  {γ : ℝ → Ω → E → ℝ}

/-- **The weighted second-moment identity of a solution of the linear forward equation**, over
a filtration with a cross witness. -/
theorem exp_mul_integral_mul_self_eq (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ)
    (𝒲 : D.CrossWitness ℱ) (β : ℝ) (hT : 0 < T) :
    Real.exp (β * T) * ∫ ω, X T ω * X T ω ∂P
      = ∫ ω, X 0 ω * X 0 ω ∂P + ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s)
          * (β * ∫ ω, X s ω * X s ω ∂P + 2 * ∫ ω, X s ω * b ω s ∂P
            + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
            + (∫⁻ ω, ∫⁻ e, (‖γ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) := by
  simpa only [neg_neg] using (h.linearBSDEJ hT.le).exp_mul_integral_mul_self_eq 𝒲 β hT

/-- The time integrand of the weighted identity of a solution of the linear forward equation is
integrable on `[0, T]`. -/
theorem integrableOn_exp_mul_rate (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ)
    (𝒲 : D.CrossWitness ℱ) (β : ℝ) (hT : 0 < T) :
    IntegrableOn (fun s => Real.exp (β * s)
      * (β * ∫ ω, X s ω * X s ω ∂P + 2 * ∫ ω, X s ω * b ω s ∂P
        + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
        + (∫⁻ ω, ∫⁻ e, (‖γ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)) (Set.Icc (0 : ℝ) T) := by
  simpa only [neg_neg] using (h.linearBSDEJ hT.le).integrableOn_exp_mul_rate 𝒲 β hT

end LinearFSDEJ

end Dissertation.WellPosedness.Stability
