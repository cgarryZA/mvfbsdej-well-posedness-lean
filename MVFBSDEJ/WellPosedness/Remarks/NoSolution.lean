/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Remarks.HarmonicBVP
import MVFBSDEJ.WellPosedness.Remarks.LinearMean
import MVFBSDEJ.WellPosedness.Remarks.LiMinSystem
import MVFBSDEJ.WellPosedness.System.SolvesIntPaper
import MVFBSDEJ.WellPosedness.Existence.GlobalLipschitzH

/-!
# A Lipschitz system with no solution

The preamble of Section 5 of the paper: the dissipativity of Assumption 2.5 cannot be traded for
Lipschitz continuity alone. The linear mean-field system of Example 3.2 of Li and Min
(`liMinCoeffs`), with `n = m = d = 1`,

`dX_t = 𝔼[Y_t] dt + dW_t + ∫_E U_t(e) Ñ(dt, de)`,
`−dY_t = 𝔼[X_t] dt − Z_t dW_t − ∫_E U_t(e) Ñ(dt, de)`,
`X_0 = ξ₀`, `Y_T = −𝔼[X_T]`,

satisfies Assumptions 2.2 and 2.3 and (2.3), and has no solution in `ℍ²` on the horizon
`T = 3π/4` when `𝔼 ξ₀ ≠ 0`.

Along a solution the drift `𝔼[Y_s]`, the driver `𝔼[X_s]` and the terminal value `−𝔼[X_T]` are
deterministic, and the Brownian and compensated Poisson integrals have mean zero. Taking
expectations in the two equations of (1.1), the means `x(t) = 𝔼 X_t`, `y(t) = 𝔼 Y_t` satisfy

`x(t) = 𝔼 ξ₀ + ∫_0^t y`, `y(t) = −x(T) + ∫_t^T x`, `t ∈ [0, T]`,

the drift and the driver being `y` and `x` at almost every time of `[0, T]`, at which the tuple
is square integrable. The harmonic invariant of this two-point problem gives
`x(T) (cos T + sin T) = 𝔼 ξ₀` (`mul_cos_add_sin_eq_of_integral`), and `cos T + sin T = 0` at
`T = 3π/4`.

The argument uses only the expectations of the two identities of (1.1), so it holds over any
filtration carrying the driver, for the solutions in `ℍ²` of `SolvesInt` and of
`PaperWeakSolutionInt`.

## Main statements

* `tupleMean_lawP2_fst_apply`, `tupleMean_lawP2_snd_fst_apply` — along a square-integrable tuple
  the marginal means are the expectations of the coordinates.
* `driftProc_liMin`, `driverProc_liMin`, `terminalVal_liMin` — the drift, the driver and the
  terminal value along a tuple are deterministic.
* `SolvesInt.integral_mul_cos_add_sin_liMin`,
  `PaperWeakSolutionInt.integral_mul_cos_add_sin_liMin` — along a solution,
  `𝔼 X_T (cos T + sin T) = 𝔼 ξ₀`.
* `not_paperWeakSolutionInt_liMin` — no solution in `ℍ²` at `T = 3π/4` when `𝔼 ξ₀ ≠ 0`,
  over any filtration carrying the driver.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Existence LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

/-! ### The system of Li and Min along a tuple -/

section Along

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℝ} {X Y : Fin 1 → ℝ → Ω → ℝ} {Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ} {U : Fin 1 → ℝ → Ω → E → ℝ}

/-- Along a square-integrable random tuple, the `X`-channel of the mean of its law is the
expectation of the `X`-coordinate. -/
theorem tupleMean_lawP2_fst_apply {Θ : Ω → TupleH ν 1 1 1} (hΘ : MemLp Θ 2 P) :
    (tupleMean (lawP2 P Θ)).1 0 = ∫ ω, (Θ ω).1 0 ∂P := by
  have hi := hΘ.integrable one_le_two
  rw [tupleMean_lawP2 hΘ, fst_integral hi]
  exact ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).integral_comp_comm hi.fst).symm

/-- Along a square-integrable random tuple, the `Y`-channel of the mean of its law is the
expectation of the `Y`-coordinate. -/
theorem tupleMean_lawP2_snd_fst_apply {Θ : Ω → TupleH ν 1 1 1} (hΘ : MemLp Θ 2 P) :
    (tupleMean (lawP2 P Θ)).2.1 0 = ∫ ω, (Θ ω).2.1 0 ∂P := by
  have hi := hΘ.integrable one_le_two
  rw [tupleMean_lawP2 hΘ, snd_integral hi, fst_integral hi.snd]
  exact ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).integral_comp_comm hi.snd.fst).symm

/-- **The drift of Example 3.2 of Li and Min along a tuple is deterministic**:
`b(s, Θ_s(ω), μ_s) = m_Y(μ_s)` for `s ∈ [0, T]`, independently of `ω`. -/
theorem driftProc_liMin (ω : Ω) (s : ℝ) :
    driftProc P T (liMinCoeffs ν) X Y Z U 0 ω s
      = (Set.Icc (0 : ℝ) T).indicator
          (fun s => (tupleMean (lawP2 P (tupleAt ν X Y Z U s))).2.1 0) s :=
  rfl

/-- **The driver of Example 3.2 of Li and Min along a tuple is deterministic**:
`f(s, Θ_s(ω), μ_s) = m_X(μ_s)` for `s ∈ [0, T]`, independently of `ω`. -/
theorem driverProc_liMin (ω : Ω) (s : ℝ) :
    driverProc P T (liMinCoeffs ν) X Y Z U 0 ω s
      = (Set.Icc (0 : ℝ) T).indicator
          (fun s => (tupleMean (lawP2 P (tupleAt ν X Y Z U s))).1 0) s :=
  rfl

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The terminal value of Example 3.2 of Li and Min** is `g(X_T, Law X_T) = −𝔼 X_T` when `X_T`
is square integrable. -/
theorem terminalVal_liMin (hX : ∀ i, MemLp (X i T) 2 P) (ω : Ω) :
    terminalVal P T (liMinCoeffs ν) X 0 ω = -∫ ω', X 0 T ω' ∂P := by
  have hv : MemLp (fun ω' => (WithLp.toLp 2 fun i => X i T ω' : EuclideanSpace ℝ (Fin 1))) 2 P :=
    memLp_toLp_of_forall (u := fun ω' i => X i T ω') hX
  simp only [terminalVal, liMinCoeffs, PiLp.neg_apply]
  rw [barycentre_lawP2 hv]
  congr 1
  exact ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).integral_comp_comm
    (hv.integrable one_le_two)).symm

end Along

/-! ### The harmonic invariant along a solution -/

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {ξ₀ : Fin 1 → Ω → ℝ}
  {X Y : Fin 1 → ℝ → Ω → ℝ} {Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ} {U : Fin 1 → ℝ → Ω → E → ℝ}
  {γ : Fin 1 → ℝ → Ω → E → ℝ}

/-- **The harmonic invariant along a solution in `ℍ²` of `SolvesInt`.** For `T > 0` and a
solution of the system of Example 3.2 of Li and Min with initial datum `ξ₀`, over any filtration
carrying the driver, `𝔼 X_T (cos T + sin T) = 𝔼 ξ₀`. -/
theorem SolvesInt.integral_mul_cos_add_sin_liMin
    (h : SolvesInt D ℱ hℱW hℱN T (liMinCoeffs ν) ξ₀ X Y Z U γ) (hT : 0 < T) :
    (∫ ω, X 0 T ω ∂P) * (Real.cos T + Real.sin T) = ∫ ω, ξ₀ 0 ω ∂P := by
  have hf := h.linearFSDEJInt 0
  have hb := h.linearBSDEJInt 0
  have hbβ := driftProc_liMin (P := P) (T := T) (ν := ν) (X := X) (Y := Y) (Z := Z) (U := U)
  have hfφ := driverProc_liMin (P := P) (T := T) (ν := ν) (X := X) (Y := Y) (Z := Z) (U := U)
  have hξ : Integrable (ξ₀ 0) P :=
    hf.integrable_initial_of_deterministic ((h.XT_sq 0).integrable one_le_two) hbβ hT.le
  have hβi : IntegrableOn (fun s => (Set.Icc (0 : ℝ) T).indicator
      (fun s => (tupleMean (lawP2 P (tupleAt ν X Y Z U s))).2.1 0) s) (Set.Icc 0 T) := by
    obtain ⟨ω, hω⟩ := hf.b_int.exists
    exact hω
  have hφi : IntegrableOn (fun s => (Set.Icc (0 : ℝ) T).indicator
      (fun s => (tupleMean (lawP2 P (tupleAt ν X Y Z U s))).1 0) s) (Set.Icc 0 T) := by
    obtain ⟨ω, hω⟩ := hb.φ_int.exists
    exact hω
  refine mul_cos_add_sin_eq_of_integral (x := fun t => ∫ ω, X 0 t ω ∂P)
    (y := fun t => ∫ ω, Y 0 t ω ∂P) hT hβi hφi (fun t ht => ?_) (fun t ht => ?_) ?_ ?_
  · exact hf.integral_eq_of_deterministic hξ hbβ ht
  · have hterm : terminalVal P T (liMinCoeffs ν) X 0 = fun _ => -∫ ω', X 0 T ω' ∂P :=
      funext (terminalVal_liMin h.XT_sq)
    rw [hb.integral_eq_of_deterministic (hterm ▸ integrable_const _) hfφ ht, hterm]
    simp
  · filter_upwards [h.ae_memLp_tupleAt, ae_restrict_mem measurableSet_Icc] with s hs hsI
    simp only [Set.indicator_of_mem hsI]
    exact tupleMean_lawP2_snd_fst_apply hs
  · filter_upwards [h.ae_memLp_tupleAt, ae_restrict_mem measurableSet_Icc] with s hs hsI
    simp only [Set.indicator_of_mem hsI]
    exact tupleMean_lawP2_fst_apply hs

/-- **The harmonic invariant along a solution in `ℍ²`.** For `T > 0` and a solution of the
system of Example 3.2 of Li and Min with initial datum `ξ₀` in the sense of
`PaperWeakSolutionInt`, over any filtration carrying the driver,
`𝔼 X_T (cos T + sin T) = 𝔼 ξ₀`. -/
theorem PaperWeakSolutionInt.integral_mul_cos_add_sin_liMin
    (h : PaperWeakSolutionInt D ℱ hℱW hℱN T (liMinCoeffs ν) ξ₀ X Y Z U γ) (hT : 0 < T) :
    (∫ ω, X 0 T ω ∂P) * (Real.cos T + Real.sin T) = ∫ ω, ξ₀ 0 ω ∂P := by
  obtain ⟨X', Y', hXe, -, hs⟩ := h.exists_solvesInt hT.le
  rw [← hXe 0 T ⟨hT.le, le_rfl⟩]
  exact hs.integral_mul_cos_add_sin_liMin hT

/-! ### No solution at `T = 3π/4` -/

/-- **No solution in `ℍ²` at `T = 3π/4`.** Over any filtration carrying the driver, the
system of Example 3.2 of Li and Min has no solution in the sense of `PaperWeakSolutionInt` on the
horizon `T = 3π/4` from an initial datum `ξ₀` with `𝔼 ξ₀ ≠ 0`. -/
theorem not_paperWeakSolutionInt_liMin (hξ : ∫ ω, ξ₀ 0 ω ∂P ≠ 0) :
    ¬ PaperWeakSolutionInt D ℱ hℱW hℱN (3 * Real.pi / 4) (liMinCoeffs ν) ξ₀ X Y Z U γ :=
  fun h => by
    have e := h.integral_mul_cos_add_sin_liMin (by positivity)
    rw [cos_add_sin_three_pi_div_four, mul_zero] at e
    exact hξ e.symm

end MVFBSDEJ.WellPosedness.System
