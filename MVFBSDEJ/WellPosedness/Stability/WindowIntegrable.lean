/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.ForwardEq

/-!
# Integrability on the window `Ω × [0, T]`

The expectation identities behind Lemma 4.3 of the well-posedness paper are integrals over the
window `Ω × [0, T]` with the product measure `P ⊗ ds`, of pairings of two square-integrable
integrands. This file collects the integrability facts they rest on.

* Two integrands of finite energy on `[0, T]` are square integrable for `P ⊗ ds`, so their
  product is integrable; for marked integrands the same holds for `P ⊗ ds ⊗ ν`, and integrating
  out the mark gives an integrable function of `(ω, s)`, the mark integral being defined at
  almost every `(ω, s)`.
* A solution of the linear forward or backward equation over a filtration carrying the driver
  with a cross witness has finite energy on `[0, T]`: its second moment is integrable in time,
  by the second-moment identity of an Itô–Lévy process.

## Main statements

* `integrable_mul_prod`, `integrable_integral_mul_marked`, `ae_integrable_mul_marked` —
  products on the window.
* `energy_lt_top_of_isItoLevyProcess` — an Itô–Lévy process has finite energy on the window.
* `LinearBSDEJ.energy_lt_top`, `LinearFSDEJ.energy_lt_top` — solutions have finite energy on the
  window.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Products on the window -/

omit [IsProbabilityMeasure P] in
/-- The product of two integrands of finite energy on `[0, T]` is integrable on the window. -/
theorem integrable_mul_prod {f g : Ω → ℝ → ℝ} (hf : Measurable (Function.uncurry f))
    (hg : Measurable (Function.uncurry g)) {T : ℝ} (hfq : Brownian.Ito.energy P T f < ⊤)
    (hgq : Brownian.Ito.energy P T g < ⊤) :
    Integrable (fun p : Ω × ℝ => f p.1 p.2 * g p.1 p.2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  (Ito.SecondMoment.memLp_two_prod hf hfq).integrable_mul
    (Ito.SecondMoment.memLp_two_prod hg hgq)

omit [IsProbabilityMeasure P] in
/-- The product of two marked integrands of finite energy on `[0, T]` is integrable for
`(P ⊗ ds) ⊗ ν`. -/
theorem integrable_mul_prod_marked {φ ψ : Ω → ℝ → E → ℝ}
    (hφ : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2) {T : ℝ}
    (hφq : Poisson.Compensated.markedEnergy P ν T φ < ⊤)
    (hψq : Poisson.Compensated.markedEnergy P ν T ψ < ⊤) :
    Integrable (fun q : (Ω × ℝ) × E => φ q.1.1 q.1.2 q.2 * ψ q.1.1 q.1.2 q.2)
      ((P.prod (volume.restrict (Set.Icc (0 : ℝ) T))).prod ν) := by
  have hF : Integrable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 * ψ p.1 p.2.1 p.2.2)
      (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) :=
    (Ito.SecondMoment.memLp_two_prod_marked hφ hφq).integrable_mul
      (Ito.SecondMoment.memLp_two_prod_marked hψ hψq)
  exact (measurePreserving_prodAssoc P (volume.restrict (Set.Icc (0 : ℝ) T)) ν)
    |>.integrable_comp_of_integrable hF

omit [IsProbabilityMeasure P] in
/-- The mark integral `(ω, s) ↦ ∫_E φ ψ dν` of two marked integrands of finite energy on
`[0, T]` is integrable on the window. -/
theorem integrable_integral_mul_marked {φ ψ : Ω → ℝ → E → ℝ}
    (hφ : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2) {T : ℝ}
    (hφq : Poisson.Compensated.markedEnergy P ν T φ < ⊤)
    (hψq : Poisson.Compensated.markedEnergy P ν T ψ < ⊤) :
    Integrable (fun p : Ω × ℝ => ∫ e, φ p.1 p.2 e * ψ p.1 p.2 e ∂ν)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  (integrable_mul_prod_marked hφ hψ hφq hψq).integral_prod_left

/-- At almost every point of the window, the product of two marked integrands of finite energy
on `[0, T]` is `ν`-integrable in the mark. -/
theorem ae_integrable_mul_marked {φ ψ : Ω → ℝ → E → ℝ}
    (hφ : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2) {T : ℝ}
    (hφq : Poisson.Compensated.markedEnergy P ν T φ < ⊤)
    (hψq : Poisson.Compensated.markedEnergy P ν T ψ < ⊤) :
    ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Integrable (fun e => φ p.1 p.2 e * ψ p.1 p.2 e) ν :=
  (integrable_mul_prod_marked hφ hψ hφq hψq).prod_right_ae

/-! ### Solutions have finite energy on the window -/

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}

/-- **An Itô–Lévy process has finite energy on every window**, for a square-integrable initial
value measurable at time `0` and a square-integrable progressive drift, over a filtration with a
cross witness. -/
theorem energy_lt_top_of_isItoLevyProcess {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ}
    {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}
    (h : Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (𝒲 : D.CrossWitness ℱ) (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) {T : ℝ} (hT : 0 < T) :
    Brownian.Ito.energy P T (fun ω s => X s ω) < ⊤ := by
  have hint := Ito.SecondMoment.integrableOn_integral_mul_self h 𝒲 hX₀ hX₀2 hbm hbp hbq hT
  have hmeas : Measurable (Function.uncurry fun ω s => (‖X s ω‖₊ : ℝ≥0∞) ^ 2) :=
    ((h.measurable_path.comp measurable_swap).nnnorm.coe_nnreal_ennreal).pow_const 2
  unfold Brownian.Ito.energy
  rw [lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Icc (0 : ℝ) T))
    hmeas.aemeasurable]
  have hcongr : ∀ s ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, (‖X s ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal (∫ ω, X s ω * X s ω ∂P) := by
    intro s hs
    have hXs := Ito.SecondMoment.memLp_two_of_isItoLevyProcess h hX₀2 hbm hbq hs.1
    rw [Ito.SecondMoment.integral_mul_self_eq_toReal hXs,
      ENNReal.ofReal_toReal (Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two hXs).ne]
  rw [setLIntegral_congr_fun measurableSet_Icc hcongr]
  exact hint.lintegral_lt_top

variable {T : ℝ}

/-- **A solution of the linear backward equation has finite energy on the window**, over a
filtration with a cross witness. -/
theorem _root_.MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.energy_lt_top
    {ξ : Ω → ℝ} {φ : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → Fin d → ℝ} {U : ℝ → Ω → E → ℝ}
    (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) :
    Brownian.Ito.energy P T (fun ω s => Y s ω) < ⊤ := by
  rw [← energy_clampT]
  exact energy_lt_top_of_isItoLevyProcess (h.isItoLevyProcess_clampT hT) 𝒲
    h.stronglyMeasurable_initial (h.memLp_initial hT.le) h.φ_meas.neg
    (continuous_neg.comp_progressivelyMeasurable neg_zero h.φ_prog)
    (fun T' _ => neg_drift_sq_int_global h.φ_vanish h.φ_sq T') hT

/-- **A solution of the linear forward equation has finite energy on the window**, over a
filtration with a cross witness. -/
theorem LinearFSDEJ.energy_lt_top {ξ₀ : Ω → ℝ} {b : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
    {σ : ℝ → Ω → Fin d → ℝ} {γ : ℝ → Ω → E → ℝ} (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) :
    Brownian.Ito.energy P T (fun ω s => X s ω) < ⊤ :=
  (h.linearBSDEJ hT.le).energy_lt_top 𝒲 hT

end MVFBSDEJ.WellPosedness.Stability
