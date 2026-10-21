/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.AffineExample
import Dissertation.WellPosedness.System.SolvesIntPaper
import Dissertation.WellPosedness.System.PaperUniquenessInt
import Dissertation.WellPosedness.BrownianPoisson.Example

/-!
# A Lipschitz system with two solutions

The affine system of Example 5.1(i) of the well-posedness paper with `n = m = 1`, `σ_c = 0`,
`h_c = 0`, `β₂ = 1` and the reversed sign `β₁ = −1`,

`b(t, x, y, z, u) = y`, `σ = z`, `h = u`, `f = x`, `g(x, ρ) = x`,

satisfies (2.3) and Assumption 2.3 with `L = 1`. On the horizon `T = π/4`, from the initial datum
`0`, it has for every real `a` the deterministic solution

`X_t = a sin t`, `Y_t = a cos t`, `Z = U = 0`,

since `∫_0^t a cos s ds = a sin t` and `a sin T + ∫_t^T a sin s ds = a cos t`, the terminal value
`g(X_T) = a sin(π/4)` being `a cos(π/4)`. The solutions of two values of `a` differ, so the
system is not unique; by Theorem 3.3 it satisfies Assumption 2.5 for no admissible `G` of full
rank.

## Main statements

* `lipschitzCoefficientsP2_affine_abs` — Assumption 2.3, interior, pointwise, for the affine
  system with `|β₁|, |β₂| ≤ L`, of any sign.
* `linearFSDEJInt_deterministic`, `linearBSDEJInt_deterministic` — a deterministic path with a
  continuous rate solves the linear forward or backward equation with no noise.
* `solvesIntAug_rotation`, `paperWeakSolutionIntAug_rotation` — the solution for `a`, over the
  augmented joint filtration of every Lévy driver.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.Existence Dissertation.Law

/-! ### Assumption 2.3 without a sign condition -/

section Coefficients

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n d : ℕ} {β₁ β₂ : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}

/-- **Assumption 2.3, interior, pointwise, for the affine system of Example 5.1(i)**, with any
constant `L ≥ max |β₁| |β₂|`, the signs of `β₁, β₂` free. -/
theorem lipschitzCoefficientsP2_affine_abs {L : ℝ} (hL : max |β₁| |β₂| ≤ L) :
    LipschitzCoefficientsP2 L (affineCoeffs β₁ β₂ σc hc).b (affineCoeffs β₁ β₂ σc hc).σ
      (affineCoeffs β₁ β₂ σc hc).h (affineCoeffs β₁ β₂ σc hc).f := by
  intro t θ θ' μ μ'
  have e₁ : -(β₁ • θ.2.1) - -(β₁ • θ'.2.1) = -(β₁ • (θ.2.1 - θ'.2.1)) := by
    rw [smul_sub]; abel
  have e₂ : σc - β₁ • θ.2.2.1 - (σc - β₁ • θ'.2.2.1) = -(β₁ • (θ.2.2.1 - θ'.2.2.1)) := by
    rw [smul_sub]; abel
  have e₃ : hc - β₁ • θ.2.2.2 - (hc - β₁ • θ'.2.2.2) = -(β₁ • (θ.2.2.2 - θ'.2.2.2)) := by
    rw [smul_sub]; abel
  simp only [affineCoeffs, e₁, e₂, e₃, ← smul_sub, norm_neg, norm_smul, Real.norm_eq_abs]
  have htn : tupleNorm (θ - θ')
      = ‖θ.1 - θ'.1‖ + ‖θ.2.1 - θ'.2.1‖ + ‖θ.2.2.1 - θ'.2.2.1‖ + ‖θ.2.2.2 - θ'.2.2.2‖ := rfl
  rw [htn]
  have hL₁ : |β₁| ≤ L := (le_max_left _ _).trans hL
  have hL₂ : |β₂| ≤ L := (le_max_right _ _).trans hL
  have hw := w2P_nonneg μ μ'
  have h0 := abs_nonneg β₁
  nlinarith [norm_nonneg (θ.1 - θ'.1), norm_nonneg (θ.2.1 - θ'.2.1),
    norm_nonneg (θ.2.2.1 - θ'.2.2.1), norm_nonneg (θ.2.2.2 - θ'.2.2.2)]

end Coefficients

open LevyStochCalc LevyStochCalc.BSDEJ.Solves Dissertation.WellPosedness.BrownianPoisson
  Dissertation.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {T : ℝ}

/-! ### Deterministic solutions of the linear equations -/

section Deterministic

variable (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ)

/-- The canonical stochastic integrals of the zero integrands vanish almost surely at every
nonnegative time. -/
theorem stochasticIntegrals_zero_ae {r : ℝ} (hr : 0 ≤ r) :
    ∀ᵐ ω ∂P, Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW
        (fun _ _ => (0 : Fin d → ℝ)) (fun _ => measurable_const)
        (fun _ => Probability.progressivelyMeasurable_zero _) (fun _ _ _ => by simp) r ω = 0
      ∧ Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun _ _ _ => (0 : ℝ))
        measurable_const (markedProgressivelyMeasurable_zero _) (fun _ _ => by simp) r ω = 0 := by
  have hN : Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun _ _ _ => (0 : ℝ))
      measurable_const (markedProgressivelyMeasurable_zero _) (fun _ _ => by simp) r =ᵐ[P] 0 :=
    Poisson.Compensated.stochasticIntegral_ae_zero_of_vanishing D.N hℱN _ _ _ _ hr
      fun _ _ _ _ => rfl
  have hW := multidimStochasticIntegral_zero_ae D.W ℱ hℱW
    (fun _ => measurable_const) (fun _ => Probability.progressivelyMeasurable_zero _)
    (fun _ _ _ => by simp) r
  filter_upwards [hW, hN] with ω h1 h2
  exact ⟨h1, h2⟩

/-- **A deterministic forward path.** A continuous path `x` with `x_t = x₀ + ∫_0^t b` on `[0, T]`,
for a continuous rate `b`, solves the linear forward equation of `LinearFSDEJInt` from `x₀` with
the drift `b` on `[0, T]` and `0` off it, and no diffusion or jumps, over any filtration. -/
theorem linearFSDEJInt_deterministic {x b : ℝ → ℝ} {x₀ : ℝ} (hx : Continuous x)
    (hb : Continuous b) (hxb : ∀ t ∈ Icc (0 : ℝ) T, x t = x₀ + ∫ s in Icc (0 : ℝ) t, b s) :
    LinearFSDEJInt D ℱ hℱW hℱN T (fun _ => x₀) (fun _ s => (Icc (0 : ℝ) T).indicator b s)
      (fun t _ => x t) (fun _ _ => 0) (fun _ _ _ => 0) where
  σ_meas _ := measurable_const
  σ_prog _ := Probability.progressivelyMeasurable_zero _
  σ_vanish _ _ _ := rfl
  σ_sq _ := by simp [Brownian.Ito.energy]
  γ_meas := measurable_const
  γ_prog := markedProgressivelyMeasurable_zero _
  γ_vanish _ _ _ _ := rfl
  γ_sq := by simp [Poisson.Compensated.markedEnergy]
  b_meas := (hb.measurable.indicator measurableSet_Icc).comp measurable_snd
  b_prog := Brownian.Ito.progressivelyMeasurable_of_time ℱ
    (hb.measurable.indicator measurableSet_Icc)
  b_vanish _ _ hs := indicator_of_notMem hs _
  b_int := ae_of_all _ fun _ =>
    (integrableOn_congr_fun (fun s hs => indicator_of_mem hs _) measurableSet_Icc).mpr
      (hb.continuousOn.integrableOn_Icc)
  X_adapted _ := measurable_const
  X_rightCont _ t := (hx.tendsto t).mono_left nhdsWithin_le_nhds
  eqn := by
    intro t ht
    filter_upwards [stochasticIntegrals_zero_ae D ℱ hℱW hℱN ht.1] with ω hω
    rw [hω.1, hω.2, setIntegral_congr_fun measurableSet_Icc fun s hs => indicator_of_mem
      (show s ∈ Icc (0 : ℝ) T from ⟨hs.1, hs.2.trans ht.2⟩) _, ← hxb t ht]
    ring

/-- **A deterministic backward path.** A continuous path `y` with `y_t = ξ + ∫_t^T φ` on
`[0, T]`, for a continuous rate `φ`, solves the linear backward equation of `LinearBSDEJInt` with
terminal value `ξ`, the drift `φ` on `[0, T]` and `0` off it, and `Z = U = 0`, over any
filtration. -/
theorem linearBSDEJInt_deterministic {y φ : ℝ → ℝ} {ξ : ℝ} (hT : 0 ≤ T) (hy : Continuous y)
    (hφ : Continuous φ) (hyφ : ∀ t ∈ Icc (0 : ℝ) T, y t = ξ + ∫ s in Icc t T, φ s) :
    LinearBSDEJInt D ℱ hℱW hℱN T (fun _ => ξ) (fun _ s => (Icc (0 : ℝ) T).indicator φ s)
      (fun t _ => y t) (fun _ _ => 0) (fun _ _ _ => 0) where
  Z_meas _ := measurable_const
  Z_prog _ := Probability.progressivelyMeasurable_zero _
  Z_vanish _ _ _ := rfl
  Z_sq _ := by simp [Brownian.Ito.energy]
  U_meas := measurable_const
  U_prog := markedProgressivelyMeasurable_zero _
  U_vanish _ _ _ _ := rfl
  U_sq := by simp [Poisson.Compensated.markedEnergy]
  φ_meas := (hφ.measurable.indicator measurableSet_Icc).comp measurable_snd
  φ_prog := Brownian.Ito.progressivelyMeasurable_of_time ℱ
    (hφ.measurable.indicator measurableSet_Icc)
  φ_vanish _ _ hs := indicator_of_notMem hs _
  φ_int := ae_of_all _ fun _ =>
    (integrableOn_congr_fun (fun s hs => indicator_of_mem hs _) measurableSet_Icc).mpr
      (hφ.continuousOn.integrableOn_Icc)
  Y_adapted _ := measurable_const
  Y_rightCont _ t := (hy.tendsto t).mono_left nhdsWithin_le_nhds
  eqn := by
    intro t ht
    filter_upwards [stochasticIntegrals_zero_ae D ℱ hℱW hℱN hT,
      stochasticIntegrals_zero_ae D ℱ hℱW hℱN ht.1] with ω hT' ht'
    rw [hT'.1, hT'.2, ht'.1, ht'.2, setIntegral_congr_fun measurableSet_Icc fun s hs =>
      indicator_of_mem (show s ∈ Icc (0 : ℝ) T from ⟨ht.1.trans hs.1, hs.2⟩) _, ← hyφ t ht]
    ring

end Deterministic

/-! ### The solutions -/

/-- The horizon `π/4`, at which `sin T = cos T`. -/
theorem sin_pi_div_four_eq_cos : Real.sin (Real.pi / 4) = Real.cos (Real.pi / 4) := by
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four]

/-- `∫_0^t a cos s ds = a sin t` for `t ≥ 0`. -/
theorem setIntegral_Icc_const_mul_cos (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Icc (0 : ℝ) t, a * Real.cos s = a * Real.sin t := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_const_mul, integral_cos, Real.sin_zero, sub_zero]

/-- `∫_t^T a sin s ds = a (cos t − cos T)` for `t ≤ T`. -/
theorem setIntegral_Icc_const_mul_sin (a : ℝ) {t T : ℝ} (ht : t ≤ T) :
    ∫ s in Icc t T, a * Real.sin s = a * (Real.cos t - Real.cos T) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_const_mul, integral_sin]

/-- A path bounded by `|a|` on `[0, T]` has finite energy. -/
theorem energy_const_mul_ne_top {c : ℝ → ℝ} (hb : ∀ s, |c s| ≤ 1)
    (a : ℝ) : Brownian.Ito.energy P T (fun (_ : Ω) s => a * c s) ≠ ⊤ := by
  have hle : ∀ s, (‖a * c s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖a‖₊ : ℝ≥0∞) ^ 2 := by
    intro s
    gcongr
    rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg a) (hb s)
  unfold Brownian.Ito.energy
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun _ =>
    setLIntegral_mono_ae (g := fun _ => (‖a‖₊ : ℝ≥0∞) ^ 2) (by fun_prop)
      (ae_of_all _ fun s _ => hle s))
  simp [Real.volume_Icc, ENNReal.mul_eq_top]

variable [MeasurableSpace.CountablyGenerated E]
  (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν)

/-- The system of Example 5.1(i) with `n = m = 1`, `σ_c = 0`, `h_c = 0`, `β₂ = 1` and the
reversed sign `β₁ = −1`: `b = y`, `σ = z`, `h = u`, `f = x`, `g = x`. -/
local notation "rotC" => affineCoeffs (ν := ν) (n := 1) (d := 1) (-1) 1 0 0

/-- **The solution for `a`**: `X_t = a sin t`, `Y_t = a cos t`, `Z = U = 0` solves the system
`rotC` from `ξ₀ = 0` on the horizon `π/4` in the sense of `SolvesInt` over `augJoint D`, with
`γ = 0`. -/
theorem solvesIntAug_rotation (a : ℝ) :
    SolvesIntAug D (Real.pi / 4) rotC 0 (fun _ t _ => a * Real.sin t)
      (fun _ t _ => a * Real.cos t) 0 0 0 where
  forcing := Forcing.zero
  jump_rep := Eventually.of_forall fun s => Eventually.of_forall fun ω => by
    filter_upwards [Lp.coeFn_zero (EuclideanSpace ℝ (Fin 1)) 2 ν] with e he
    simp only [affineCoeffs, tupleAt, Pi.zero_apply, uLift_zero, smul_zero, sub_zero]
    rw [he]
    rfl
  fwd i := by
    have hb : (fun ω s => (1 : ℝ) * driftProc P (Real.pi / 4) rotC (fun _ t _ => a * Real.sin t)
          (fun _ t _ => a * Real.cos t) 0 0 i ω s + (0 : Fin 1 → Ω → ℝ → ℝ) i ω s)
        = fun _ s => (Icc (0 : ℝ) (Real.pi / 4)).indicator (fun s => a * Real.cos s) s := by
      funext ω s
      by_cases hs : s ∈ Icc (0 : ℝ) (Real.pi / 4)
      · simp [driftProc, indicator_of_mem hs, affineCoeffs, tupleAt]
      · simp [driftProc, hs]
    have hσ : (fun s ω j => (1 : ℝ) * diffusionProc P (Real.pi / 4) rotC
          (fun _ t _ => a * Real.sin t) (fun _ t _ => a * Real.cos t) 0 0 i s ω j
          + (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) i s ω j) = fun _ _ _ => 0 := by
      funext s ω j
      by_cases hs : s ∈ Icc (0 : ℝ) (Real.pi / 4)
      · simp [diffusionProc, indicator_of_mem hs, affineCoeffs, tupleAt]
      · simp [diffusionProc, hs]
    have hγ : (fun s ω e => (1 : ℝ) * jumpProc (Real.pi / 4) (0 : Fin 1 → ℝ → Ω → E → ℝ) i s ω e
          + (0 : Fin 1 → ℝ → Ω → E → ℝ) i s ω e) = fun _ _ _ => 0 := by
      funext s ω e
      simp [jumpProc]
    have hξ : (0 : Fin 1 → Ω → ℝ) i = fun _ => 0 := rfl
    rw [hb, hσ, hγ, hξ]
    exact linearFSDEJInt_deterministic D (augJoint D) D.isBrownianFiltration_aug
      D.isPoissonFiltration_aug (T := Real.pi / 4) (x := fun t => a * Real.sin t)
      (b := fun s => a * Real.cos s) (x₀ := 0) (by fun_prop) (by fun_prop)
      (fun t ht => by rw [setIntegral_Icc_const_mul_cos a ht.1, zero_add])
  bwd k := by
    have hT : (0 : ℝ) ≤ Real.pi / 4 := by positivity
    have hφ : (fun ω s => (1 : ℝ) * driverProc P (Real.pi / 4) rotC
          (fun _ t _ => a * Real.sin t) (fun _ t _ => a * Real.cos t) 0 0 k ω s
          + (0 : Fin 1 → Ω → ℝ → ℝ) k ω s)
        = fun _ s => (Icc (0 : ℝ) (Real.pi / 4)).indicator (fun s => a * Real.sin s) s := by
      funext ω s
      by_cases hs : s ∈ Icc (0 : ℝ) (Real.pi / 4)
      · simp [driverProc, indicator_of_mem hs, affineCoeffs, tupleAt]
      · simp [driverProc, hs]
    have hξ : (fun ω => (1 : ℝ) * terminalVal P (Real.pi / 4) rotC
          (fun _ t _ => a * Real.sin t) k ω + (0 : Fin 1 → Ω → ℝ) k ω)
        = fun _ => a * Real.sin (Real.pi / 4) := by
      funext ω
      simp [terminalVal, affineCoeffs]
    rw [hφ, hξ]
    exact linearBSDEJInt_deterministic D (augJoint D) D.isBrownianFiltration_aug
      D.isPoissonFiltration_aug hT (y := fun t => a * Real.cos t)
      (φ := fun s => a * Real.sin s) (ξ := a * Real.sin (Real.pi / 4)) (by fun_prop)
      (by fun_prop) (fun t ht => by
        rw [setIntegral_Icc_const_mul_sin a ht.2, sin_pi_div_four_eq_cos]
        ring)
  X_sq _ := energy_const_mul_ne_top Real.abs_sin_le_one a
  Y_sq _ := energy_const_mul_ne_top Real.abs_cos_le_one a
  XT_sq _ := memLp_const _

/-- **The solution for `a` in `ℍ²_weak`**: `X_t = a sin t`, `Y_t = a cos t`, `Z = U = 0` solves
`rotC` from `ξ₀ = 0` on the horizon `π/4` in the sense of `PaperWeakSolutionInt` over
`augJoint D`, with `γ = 0`. -/
theorem paperWeakSolutionIntAug_rotation (a : ℝ) :
    PaperWeakSolutionIntAug D (Real.pi / 4) rotC 0 (fun _ t _ => a * Real.sin t)
      (fun _ t _ => a * Real.cos t) 0 0 0 :=
  SolvesInt.paperWeakSolutionInt (solvesIntAug_rotation D a)
    (fun _ _ => stronglyMeasurable_const) (fun _ => measurable_const) (by positivity)

end Dissertation.WellPosedness.System
