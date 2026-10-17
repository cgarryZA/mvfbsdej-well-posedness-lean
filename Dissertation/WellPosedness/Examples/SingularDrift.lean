/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.SingularDriftAnalytic
import Dissertation.WellPosedness.Existence.AffineExample
import Dissertation.WellPosedness.System.PaperUniquenessInt
import Dissertation.WellPosedness.System.SolvesIntPaper

/-!
# A singular drift: a solution without Assumption 2.2

Theorem 3.3 of the paper holds under Assumptions 2.3–2.5 only (Remark 3.4), for
solutions in `ℍ²_weak` whose drift and driver are integrable along almost every path. This file
gives a system that meets Assumptions 2.3 and 2.5 but not Assumption 2.2, together with a
solution of it from the initial datum `0` in `ℍ²_weak` with pathwise drift and driver integrals,
over the augmented joint filtration of any Lévy driver.

For `n = m = 1` and any `d`, add the deterministic drift `t ↦ t^{-1/2}` to the affine system of
Example 5.1(i) with `β₁ = 1`, `β₂ = 0`, `σ_c = 0` and `h_c = 0`:

`b(t, x, y, z, u) = t^{-1/2} − y`, `σ = −z`, `h = −u`, `f = 0`, `g(x, ρ) = x`.

* **The assumptions.** The added drift cancels in every difference of coefficients, so
  Assumption 2.3 holds along the diagonal with `L = 1`, and Assumption 2.5 along the diagonal
  with `G = 1`, `α = 1`, `β₁ = 1`, `β₂ = 0`.
  Assumption 2.2 fails: the origin value `b(t, 0, δ₀) = t^{-1/2}` of the drift is not square
  integrable on `[0, T]`.
* **The drift process.** Along a tuple `(X, Y, Z, U)` the drift process on `[0, T]` is
  `t^{-1/2} − Y_t`.
* **The solution.** With `y_T = 2√T / (1 + T)`, the tuple `X_t = 2√t − y_T t`, `Y ≡ y_T`,
  `Z = U = 0` solves the system from `ξ₀ = 0`: `∫_0^t (s^{-1/2} − y_T) ds = 2√t − y_T t`, and
  `X_T = y_T` is the terminal value `g(X_T, Law X_T)`. It solves `SolvesInt` and
  `PaperWeakSolutionInt` over the augmented joint filtration `augJoint D` of every Lévy driver
  `D`.

## Main definitions

* `Coeffs.addDrift` — the coefficients with a deterministic drift added.
* `singularDrift` — the drift `t ↦ t^{-1/2}`.
* `singularCoeffs` — the system above.
* `singularY` — the constant value `2√T / (1 + T)` of the backward component of the solution.

## Main statements

* `DiagonalLipschitz.addDrift`, `DiagonalMonotone.addDrift` — a deterministic drift leaves the
  diagonal conditions unchanged.
* `diagonalLipschitz_singularCoeffs`, `terminalLipschitz_singularCoeffs`,
  `constants_singularCoeffs`, `diagonalMonotone_singularCoeffs`,
  `terminalMonotone_singularCoeffs` — Assumptions 2.3 and 2.5.
* `not_coeffOrigin_singularCoeffs` — Assumption 2.2 fails.
* `driftProc_singularCoeffs` — the drift process along a tuple.
* `solvesIntAug_singularCoeffs`, `paperWeakSolutionIntAug_singularCoeffs` — the solution.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.Existence Dissertation.Law

/-! ### The coefficients -/

section Coefficients

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}

/-- The coefficients `C` with the deterministic drift `c` added: `b(t, θ, μ) = c(t) + b_C(t, θ, μ)`,
the other coefficients unchanged. -/
noncomputable def Coeffs.addDrift (C : Coeffs ν n m d) (c : ℝ → EuclideanSpace ℝ (Fin n)) :
    Coeffs ν n m d :=
  { C with b := fun t θ μ => c t + C.b t θ μ }

/-- A deterministic drift cancels in the channel differences. -/
theorem diagDiff_addDrift (C : Coeffs ν n m d) (c : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)) :
    diagDiff (C.addDrift c) t θ θ' μ μ' = diagDiff C t θ θ' μ μ' := by
  simp only [diagDiff, Coeffs.addDrift, add_sub_add_left_eq_sub]

/-- The drift `t ↦ t^{-1/2}` on `ℝ¹`, `0` for `t ≤ 0`. -/
noncomputable def singularDrift (t : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 fun _ => (Real.sqrt t)⁻¹

/-- The affine system of Example 5.1(i) at `n = 1`, `β₁ = 1`, `β₂ = 0`, `σ_c = 0`, `h_c = 0`,
with the drift `t^{-1/2}` added: `b = t^{-1/2} − y`, `σ = −z`, `h = −u`, `f = 0`,
`g(x, ρ) = x`. -/
noncomputable def singularCoeffs : Coeffs ν 1 1 d :=
  (affineCoeffs 1 0 0 0).addDrift singularDrift

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- The terminal function `g(x, ρ) = x` of `singularCoeffs` meets Assumption 2.3 with `L = 1`. -/
theorem terminalLipschitz_singularCoeffs :
    TerminalLipschitz ℱ P T 1 (singularCoeffs (ν := ν) (d := d)).g :=
  terminalLipschitz_affine (ν := ν) (d := d) (β₁ := 1) (β₂ := 0) (σc := 0) (hc := 0) le_rfl

/-- The terminal function `g(x, ρ) = x` of `singularCoeffs` meets Assumption 2.5 with `G = 1` and
`α = 1`. -/
theorem terminalMonotone_singularCoeffs :
    TerminalMonotone ℱ P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1
      (singularCoeffs (ν := ν) (d := d)).g :=
  terminalMonotone_affine (ν := ν) (d := d) (β₁ := 1) (β₂ := 0) (σc := 0) (hc := 0)

/-- The constants `α = 1`, `β₁ = 1`, `β₂ = 0` are admissible at `n = m = 1`. -/
theorem constants_singularCoeffs : Constants 1 1 1 1 0 :=
  Constants.square zero_le_one zero_le_one le_rfl (by norm_num) (by norm_num)

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **A deterministic drift leaves Assumption 2.3 along the diagonal unchanged.** -/
theorem DiagonalLipschitz.addDrift {L : ℝ} {C : Coeffs ν n m d}
    (h : DiagonalLipschitz ℱ P T L C) (c : ℝ → EuclideanSpace ℝ (Fin n)) :
    DiagonalLipschitz ℱ P T L (C.addDrift c) := by
  filter_upwards [h] with t ht Θ Θ' h1 h2 h3 h4
  simpa only [Coeffs.addDrift, add_sub_add_left_eq_sub] using ht Θ Θ' h1 h2 h3 h4

/-- **A deterministic drift leaves Assumption 2.5 along the diagonal unchanged.** -/
theorem DiagonalMonotone.addDrift {G : Matrix (Fin m) (Fin n) ℝ} {β₁ β₂ : ℝ}
    {C : Coeffs ν n m d} (h : DiagonalMonotone ℱ P T G β₁ β₂ C)
    (c : ℝ → EuclideanSpace ℝ (Fin n)) : DiagonalMonotone ℱ P T G β₁ β₂ (C.addDrift c) := by
  filter_upwards [h] with t ht Θ Θ' h1 h2 h3 h4
  simpa only [diagDiff_addDrift] using ht Θ Θ' h1 h2 h3 h4

/-- The coefficients `singularCoeffs` meet Assumption 2.3 along the diagonal with `L = 1`. -/
theorem diagonalLipschitz_singularCoeffs :
    DiagonalLipschitz ℱ P T 1 (singularCoeffs (ν := ν) (d := d)) :=
  (diagonalLipschitz_affine zero_le_one le_rfl (by simp)).addDrift singularDrift

/-- The coefficients `singularCoeffs` meet Assumption 2.5 along the diagonal with `G = 1`,
`β₁ = 1` and `β₂ = 0`. -/
theorem diagonalMonotone_singularCoeffs :
    DiagonalMonotone ℱ P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 0
      (singularCoeffs (ν := ν) (d := d)) :=
  diagonalMonotone_affine.addDrift singularDrift

/-- **Assumption 2.2 fails for `singularCoeffs`**, for `T > 0`: the origin value
`b(t, 0, δ₀) = t^{-1/2}` of the drift is not square integrable on `[0, T]`. -/
theorem not_coeffOrigin_singularCoeffs (hT : 0 < T) :
    ¬ CoeffOrigin T (singularCoeffs (ν := ν) (d := d)) := by
  intro h
  have hlt := lintegral_enorm_sq_lt_top h.b_memLp
  have e : ∀ t, ‖(singularCoeffs (ν := ν) (d := d)).b t 0 (P2.dirac 0)‖ₑ ^ 2
      = (‖(Real.sqrt t)⁻¹ - (fun _ => (0 : ℝ)) t‖₊ : ℝ≥0∞) ^ 2 := fun t => by
    simp [singularCoeffs, Coeffs.addDrift, singularDrift, affineCoeffs]
    rw [enorm_toLp_sq]
    simp
  simp_rw [e] at hlt
  rw [lintegral_sq_inv_sqrt_sub_eq_top tendsto_const_nhds hT] at hlt
  exact lt_irrefl _ hlt

end Coefficients

/-! ### The drift process -/

open LevyStochCalc LevyStochCalc.BSDEJ.Solves Dissertation.WellPosedness.BrownianPoisson
  Dissertation.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω} [IsProbabilityMeasure P]
  {d : ℕ} {T : ℝ}

/-- On `[0, T]` the drift process of `singularCoeffs` along `(X, Y, Z, U)` is
`s^{-1/2} − Y_s`. -/
theorem driftProc_singularCoeffs (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ)
    (Z : Fin 1 → ℝ → Ω → Fin d → ℝ) (U : Fin 1 → ℝ → Ω → E → ℝ) (ω : Ω) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) :
    driftProc P T (singularCoeffs (ν := ν) (d := d)) X Y Z U 0 ω s
      = (Real.sqrt s)⁻¹ - Y 0 s ω := by
  simp [driftProc, hs, singularCoeffs, Coeffs.addDrift, singularDrift, affineCoeffs, tupleAt]
  ring

variable (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)

/-! ### The solution -/

omit [MeasurableSpace.CountablyGenerated E] in
/-- **The forward equation with the drift `t^{-1/2} − y`**: `X_t = 2√t − y t` solves the linear
forward equation of `LinearFSDEJInt` from `0` with drift `s^{-1/2} − y` on `[0, T]` and `0` off
it, and no diffusion or jumps, over any filtration. -/
theorem linearFSDEJInt_singularDrift (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ) (y : ℝ) :
    LinearFSDEJInt D ℱ hℱW hℱN T (fun _ => 0)
      (fun _ s => (Icc (0 : ℝ) T).indicator (fun s => (Real.sqrt s)⁻¹ - y) s)
      (fun t _ => 2 * Real.sqrt t - y * t) (fun _ _ => 0) (fun _ _ _ => 0) where
  σ_meas _ := measurable_const
  σ_prog _ := Probability.progressivelyMeasurable_zero _
  σ_vanish _ _ _ := rfl
  σ_sq _ := by simp [Brownian.Ito.energy]
  γ_meas := measurable_const
  γ_prog := markedProgressivelyMeasurable_zero _
  γ_vanish _ _ _ _ := rfl
  γ_sq := by simp [Poisson.Compensated.markedEnergy]
  b_meas := (((by fun_prop : Measurable fun s : ℝ => (Real.sqrt s)⁻¹ - y)).indicator
    measurableSet_Icc).comp measurable_snd
  b_prog := Brownian.Ito.progressivelyMeasurable_of_time ℱ
    (((by fun_prop : Measurable fun s : ℝ => (Real.sqrt s)⁻¹ - y)).indicator measurableSet_Icc)
  b_vanish _ _ hs := indicator_of_notMem hs _
  b_int := ae_of_all _ fun _ => by
    refine (integrableOn_congr_fun (fun s hs => indicator_of_mem hs _) measurableSet_Icc).mpr ?_
    exact (integrableOn_inv_sqrt T).sub (integrableOn_const (by simp [Real.volume_Icc]))
  X_adapted _ := measurable_const
  X_rightCont _ t := (((continuous_const.mul Real.continuous_sqrt).sub
    (continuous_const.mul continuous_id)).tendsto t).mono_left nhdsWithin_le_nhds
  eqn := by
    intro t ht
    have hN : ∀ r : ℝ, 0 ≤ r → Poisson.Compensated.stochasticIntegral D.N ℱ
        hℱN (fun _ _ _ => (0 : ℝ)) measurable_const
        (markedProgressivelyMeasurable_zero _) (fun _ _ => by simp) r =ᵐ[P] 0 := fun r hr =>
      Poisson.Compensated.stochasticIntegral_ae_zero_of_vanishing D.N hℱN
        _ _ _ _ hr fun _ _ _ _ => rfl
    have hW := multidimStochasticIntegral_zero_ae D.W ℱ hℱW
      (fun _ => measurable_const) (fun _ => Probability.progressivelyMeasurable_zero _)
      (fun _ _ _ => by simp)
    have hI : ∫ s in Icc (0 : ℝ) t, (Icc (0 : ℝ) T).indicator (fun s => (Real.sqrt s)⁻¹ - y) s
        = 2 * Real.sqrt t - y * t := by
      rw [setIntegral_congr_fun measurableSet_Icc fun s hs => indicator_of_mem
        (show s ∈ Icc (0 : ℝ) T from ⟨hs.1, hs.2.trans ht.2⟩) _,
        integral_sub (integrableOn_inv_sqrt t) (integrableOn_const (by simp [Real.volume_Icc])),
        integral_inv_sqrt ht.1]
      simp [Real.volume_real_Icc, ht.1]
      ring
    filter_upwards [hW t, hN t ht.1] with ω h2 h4
    simp only [Pi.zero_apply] at h2 h4
    rw [h2, h4, hI]
    ring

/-- The constant value `y_T = 2√T / (1 + T)` of the backward component of the solution. -/
noncomputable def singularY (T : ℝ) : ℝ := 2 * Real.sqrt T / (1 + T)

/-- `y_T` is the fixed point `2√T − y_T T = y_T`, for `T ≥ 0`. -/
theorem singularY_fixed (hT : 0 ≤ T) : 2 * Real.sqrt T - singularY T * T = singularY T := by
  unfold singularY
  have : (1 + T) ≠ 0 := by positivity
  field_simp
  ring

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The path `t ↦ 2√t − y t` has finite energy on `[0, T]`. -/
theorem energy_singularX_ne_top (y : ℝ) :
    Brownian.Ito.energy P T (fun (_ : Ω) s => 2 * Real.sqrt s - y * s) ≠ ⊤ := by
  set K := 2 * Real.sqrt T + |y| * T
  have hle : ∀ s ∈ Icc (0 : ℝ) T,
      (‖2 * Real.sqrt s - y * s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖K‖₊ : ℝ≥0∞) ^ 2 := by
    intro s hs
    have h1 : Real.sqrt s ≤ Real.sqrt T := Real.sqrt_le_sqrt hs.2
    have h2 : |y * s| ≤ |y| * T := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact mul_le_mul_of_nonneg_left hs.2 (abs_nonneg y)
    have h3 : |2 * Real.sqrt s - y * s| ≤ K := by
      have := abs_sub (2 * Real.sqrt s) (y * s)
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt s)] at this
      linarith
    gcongr
    rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs, Real.norm_eq_abs]
    exact h3.trans (le_abs_self K)
  unfold Brownian.Ito.energy
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun _ =>
    setLIntegral_mono_ae (g := fun _ => (‖K‖₊ : ℝ≥0∞) ^ 2) (by fun_prop) (ae_of_all _ hle))
  simp [Real.volume_Icc, ENNReal.mul_eq_top]

/-- **The solution of `SolvesInt`**: for `T > 0`, `X_t = 2√t − y_T t`, `Y ≡ y_T`, `Z = U = 0`
solves `singularCoeffs` from `ξ₀ = 0` in the sense of `SolvesInt` over `augJoint D`, with
`γ = 0`. -/
theorem solvesIntAug_singularCoeffs (hT : 0 < T) :
    SolvesIntAug D T (singularCoeffs (ν := ν) (d := d)) 0
      (fun _ t _ => 2 * Real.sqrt t - singularY T * t) (fun _ _ _ => singularY T) 0 0 0 where
  forcing := Forcing.zero
  jump_rep := Eventually.of_forall fun s => Eventually.of_forall fun ω => by
    filter_upwards [Lp.coeFn_zero (EuclideanSpace ℝ (Fin 1)) 2 ν] with e he
    simp only [singularCoeffs, Coeffs.addDrift, affineCoeffs, tupleAt, Pi.zero_apply,
      uLift_zero, smul_zero, sub_zero]
    rw [he]
    rfl
  fwd i := by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    convert linearFSDEJInt_singularDrift D (augJoint D) D.isBrownianFiltration_aug
      D.isPoissonFiltration_aug (singularY T) using 1
    · rfl
    · funext ω s
      by_cases hs : s ∈ Icc (0 : ℝ) T
      · simp only [driftProc_singularCoeffs _ _ _ _ ω hs, indicator_of_mem hs, one_mul,
          Pi.zero_apply, add_zero]
      · simp [driftProc, hs]
    · funext s ω j
      simp [diffusionProc, singularCoeffs, Coeffs.addDrift, affineCoeffs, tupleAt]
    · funext s ω e
      simp [jumpProc]
  bwd k := by
    convert (linearBSDEJAug_const D hT (singularY T)).toInt using 1
    · funext ω
      simp [terminalVal, singularCoeffs, Coeffs.addDrift, affineCoeffs]
      exact singularY_fixed hT.le
    · funext ω s
      simp [driverProc, singularCoeffs, Coeffs.addDrift, affineCoeffs]
    · rfl
    · rfl
  X_sq _ := energy_singularX_ne_top (singularY T)
  Y_sq _ := by simp [Brownian.Ito.energy, Real.volume_Icc, ENNReal.mul_eq_top]
  XT_sq _ := memLp_const _

/-- **The solution of `PaperWeakSolutionInt`**: for `T > 0`, `X_t = 2√t − y_T t`, `Y ≡ y_T`,
`Z = U = 0` solves `singularCoeffs` from `ξ₀ = 0` in `ℍ²_weak` with pathwise drift and driver
integrals, in the sense of `PaperWeakSolutionInt` over `augJoint D`, with `γ = 0`. -/
theorem paperWeakSolutionIntAug_singularCoeffs (hT : 0 < T) :
    PaperWeakSolutionIntAug D T (singularCoeffs (ν := ν) (d := d)) 0
      (fun _ t _ => 2 * Real.sqrt t - singularY T * t) (fun _ _ _ => singularY T) 0 0 0 :=
  SolvesInt.paperWeakSolutionInt (solvesIntAug_singularCoeffs D hT)
    (fun _ _ => stronglyMeasurable_const) (fun _ => measurable_const) hT.le

end Dissertation.WellPosedness.System
