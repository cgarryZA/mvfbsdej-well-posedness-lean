/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Spec.Examples
import Dissertation.WellPosedness.System.PaperSolutionForcedSolves
import Dissertation.WellPosedness.System.BackwardYoung
import Dissertation.WellPosedness.Stability.LinearCongr
import Dissertation.WellPosedness.Examples.Dealer.ZeroSolution
import Dissertation.WellPosedness.Enlarged.CrossWitness
import Dissertation.WellPosedness.System.PredictableForcing

/-!
# A system and two forced solutions at which the Young bound (4.25) fails for large `ε`

The affine system, for `n = m` and any `d`,

`b = x − y`, `σ = −z`, `h = −u`, `f = x + y`, `g(x, ρ) = x`,

is law-free and satisfies (2.3), Assumption 2.3 with `L = 2`, Assumption 2.4 with `G = 1` and
Assumption 2.5 with `G = 1` and `α = β₁ = β₂ = 1`: its interior pairing is
`−|δx|² − |δy|² − |δz|² − ‖δu‖²`. At `λ = 1`, for `a ∈ ℝ` and `T ≥ 0`, the deterministic tuple
`X = 0`, `Y_t = a e^{−t}`, `Z = 0`, `U = 0` solves the forced system (4.1) with initial datum `0`
and the forcing `q^b_t = a e^{−t}` on `[0, T]`, `q^g_T = a e^{−T}`, `q^σ = q^h = q^f = 0`: the
forward drift `x − y + q^b` vanishes, and `a e^{−t} = a e^{−T} + ∫_t^T a e^{−s} ds`.

For the solutions at `a = 1` and `a = 0`, the driver difference is `δf_s = e^{−s}` and
`δY_s = e^{−s}`, while `δX`, `δZ`, `δU` and `δq^f` vanish; so the left side of (4.25) is
`2 e^{−2s}` and its right side `(C/ε) e^{−2s}`, which is smaller once `ε > C/2`.

## Main definitions

* `skewCoeffs` — the system `b = x − y`, `σ = −z`, `h = −u`, `f = x + y`, `g(x, ρ) = x`.
* `skewY`, `skewQb`, `skewQg` — the backward component `a e^{−t}` and the forcings of the
  solution with parameter `a`.

## Main statements

* `multidimStochasticIntegral_ae_zero`, `compensatedIntegral_ae_zero` — the stochastic
  integrals of a zero integrand.
* `linearFSDEJ_zero`, `linearBSDEJ_of_deterministic` — the linear equations with deterministic
  data and zero martingale integrands.
* `skew_assumptions` — (2.3) and Assumptions 2.3–2.5 for the system.
* `skew_predForcing`, `skew_solvesForced`, `skew_paperSolutionForced` — the forcing and the
  solution with parameter `a`.
* `supSize_skew_lt_top` — the difference of two such solutions lies in `ℍ`.
* `integral_pairing_skew`, `lintegral_esq_skewY_sub` — the pairing and `𝔼|δY_s|²` of two such
  solutions.
-/

open MeasureTheory Filter Topology Dissertation.Law Matrix
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Spec

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Stability Dissertation.WellPosedness.BrownianPoisson
  Dissertation.WellPosedness.Enlarged LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

/-! ### Stochastic integrals of a zero integrand -/

section ZeroIntegrals

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The multidimensional Itô integral of an integrand that vanishes identically vanishes almost
surely at each time. -/
theorem multidimStochasticIntegral_ae_zero {d : ℕ}
    (W : Brownian.Multidim.MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : ∀ j : Fin d, Brownian.IsBrownianFiltration (W.W j) ℱ) {Z : ℝ → Ω → (Fin d → ℝ)}
    (hZ : ∀ s ω, Z s ω = 0)
    (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω j)
    (hq : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ) :
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z hm hp hq t =ᵐ[P] 0 := by
  obtain rfl : Z = 0 := funext fun s => funext fun ω => hZ s ω
  have h : ∀ j : Fin d, ∀ᵐ ω ∂P,
      Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hℱ j)
        (fun ω' s => (0 : ℝ → Ω → (Fin d → ℝ)) s ω' j) (hm j) (hp j) (hq j) t ω = 0 := fun j =>
    Brownian.Ito.stochasticIntegralBrownian_ae_zero (W.W j) ℱ (hℱ j) (hm j) (hp j) (hq j) t
  filter_upwards [ae_all_iff.2 h] with ω hω
  simp only [Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral,
    Brownian.Ito.stochasticIntegral, Pi.zero_apply]
  exact Finset.sum_eq_zero fun j _ => hω j

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

/-- The compensated Poisson integral of an integrand that vanishes identically vanishes almost
surely at each time `t ≥ 0`. -/
theorem compensatedIntegral_ae_zero (N : Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : Poisson.IsPoissonFiltration N ℱ)
    {φ : Ω → ℝ → E → ℝ} (hφ : ∀ ω s e, φ ω s e = 0)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) {t : ℝ} (ht : 0 ≤ t) :
    Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t =ᵐ[P] 0 :=
  Poisson.Compensated.stochasticIntegral_ae_zero_of_vanishing N hℱ φ hm hp hq ht
    fun ω s e _ => hφ ω s e

end ZeroIntegrals

/-! ### The linear equations with deterministic data -/

section Linear

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

/-- The energy on `[0, T]` of a deterministic integrand bounded on `[0, T]` is finite. -/
theorem energy_ne_top_of_bound {g : ℝ → ℝ} {M : ℝ} (hg : ∀ s ∈ Set.Icc (0 : ℝ) T, |g s| ≤ M) :
    Brownian.Ito.energy P T (fun _ s => g s) ≠ ⊤ := by
  have hle : ∀ s ∈ Set.Icc (0 : ℝ) T, (‖g s‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (M ^ 2) := by
    intro s hs
    rw [sq_nnnorm_eq_ofReal]
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 := abs_nonneg (g s)
    nlinarith [hg s hs, abs_mul_abs_self (g s)]
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun _ =>
    setLIntegral_mono measurable_const hle) ?_)
  simp only [lintegral_const, measure_univ, mul_one, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Icc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The zero process solves the linear forward equation from `0` with zero integrands. -/
theorem linearFSDEJ_zero :
    LinearFSDEJ D ℱ hℱW hℱN T 0 0 0 0 0 where
  σ_meas _ := measurable_const
  σ_prog _ := Brownian.Ito.progressivelyMeasurable_zero ℱ
  σ_vanish _ _ _ := rfl
  σ_sq _ := by simp [Brownian.Ito.energy]
  γ_meas := measurable_const
  γ_prog := Poisson.Compensated.markedProgressivelyMeasurable_zero ℱ
  γ_vanish _ _ _ _ := rfl
  γ_sq := by simp [Poisson.Compensated.markedEnergy]
  b_meas := measurable_const
  b_prog := Brownian.Ito.progressivelyMeasurable_zero ℱ
  b_vanish _ _ _ := rfl
  b_sq := by simp [Brownian.Ito.energy]
  ξ₀_sq := MemLp.zero
  X_adapted _ := measurable_const
  X_rightCont _ _ := tendsto_const_nhds
  eqn t ht := by
    filter_upwards [multidimStochasticIntegral_ae_zero D.W ℱ hℱW (Z := 0) (fun _ _ => rfl) _ _ _ t,
      compensatedIntegral_ae_zero D.N ℱ hℱN (φ := fun ω' s e => (0 : ℝ → Ω → E → ℝ) s ω' e)
        (fun _ _ _ => rfl) _ _ _ ht.1] with ω h1 h2
    rw [h1, h2]
    simp

/-- **The linear backward equation with deterministic data and zero martingale integrands.** If
`g` is measurable, vanishes off `[0, T]` and is bounded on it, and `y` is continuous with
`y_t = c + ∫_t^T g` for `t ∈ [0, T]`, then `(y, 0, 0)` solves the linear backward equation with
terminal value `c` and drift `g`. -/
theorem linearBSDEJ_of_deterministic {c M : ℝ} {g y : ℝ → ℝ} (hg : Measurable g)
    (hgv : ∀ s, s ∉ Set.Icc (0 : ℝ) T → g s = 0) (hgb : ∀ s ∈ Set.Icc (0 : ℝ) T, |g s| ≤ M)
    (hy : Continuous y) (hyc : ∀ t ∈ Set.Icc (0 : ℝ) T, y t = c + ∫ s in Set.Icc t T, g s) :
    LinearBSDEJ D ℱ hℱW hℱN T (fun _ => c) (fun _ s => g s) (fun t _ => y t) 0 0 where
  Z_meas _ := measurable_const
  Z_prog _ := Brownian.Ito.progressivelyMeasurable_zero ℱ
  Z_vanish _ _ _ := rfl
  Z_sq _ := by simp [Brownian.Ito.energy]
  U_meas := measurable_const
  U_prog := Poisson.Compensated.markedProgressivelyMeasurable_zero ℱ
  U_vanish _ _ _ _ := rfl
  U_sq := by simp [Poisson.Compensated.markedEnergy]
  φ_meas := hg.comp measurable_snd
  φ_prog := progressivelyMeasurable_of_measurable_time hg
  φ_vanish _ s hs := hgv s hs
  φ_sq := energy_ne_top_of_bound hgb
  ξ_sq := memLp_const c
  Y_adapted _ := measurable_const
  Y_rightCont _ t := (hy.tendsto t).mono_left nhdsWithin_le_nhds
  eqn t ht := by
    have hT : 0 ≤ T := ht.1.trans ht.2
    filter_upwards [multidimStochasticIntegral_ae_zero D.W ℱ hℱW (Z := 0) (fun _ _ => rfl) _ _ _ T,
      multidimStochasticIntegral_ae_zero D.W ℱ hℱW (Z := 0) (fun _ _ => rfl) _ _ _ t,
      compensatedIntegral_ae_zero D.N ℱ hℱN (φ := fun ω' s e => (0 : ℝ → Ω → E → ℝ) s ω' e)
        (fun _ _ _ => rfl) _ _ _ hT,
      compensatedIntegral_ae_zero D.N ℱ hℱN (φ := fun ω' s e => (0 : ℝ → Ω → E → ℝ) s ω' e)
        (fun _ _ _ => rfl) _ _ _ ht.1] with ω h1 h2 h3 h4
    rw [h1, h2, h3, h4, hyc t ht]
    simp

end Linear

/-! ### The system -/

section Coefficients

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n d : ℕ}

/-- The affine system `b = x − y`, `σ = −z`, `h = −u`, `f = x + y`, `g(x, ρ) = x` on
`H = ℝⁿ × ℝⁿ × ℝ^{n×d} × L²(ν; ℝⁿ)`. -/
noncomputable def skewCoeffs : Coeffs ν n n d where
  b _ θ _ := θ.1 - θ.2.1
  σ _ θ _ := -θ.2.2.1
  h _ θ _ := -θ.2.2.2
  f _ θ _ := θ.1 + θ.2.1
  g x _ := x

/-- **The interior pairing of `skewCoeffs`** at `G = 1` is
`−|δx|² − |δy|² − |δz|²_F − ‖δu‖²_{L²(ν)}`: (2.7) with `β₁ = β₂ = 1`, with equality. -/
theorem interiorPairing_skew (t : ℝ) (θ θ' : TupleH ν n n d) (μ μ' : P2 (TupleH ν n n d)) :
    interiorPairing (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν)
        (diagDiff (skewCoeffs (ν := ν)) t θ θ' μ μ')
      = dissipation (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν) 1 1
        (diagDiff (skewCoeffs (ν := ν)) t θ θ' μ μ') := by
  have e₁ : θ.1 - θ.2.1 - (θ'.1 - θ'.2.1) = (θ.1 - θ'.1) - (θ.2.1 - θ'.2.1) := by abel
  have e₂ : -θ.2.2.1 - -θ'.2.2.1 = -(θ.2.2.1 - θ'.2.2.1) := by abel
  have e₃ : -θ.2.2.2 - -θ'.2.2.2 = -(θ.2.2.2 - θ'.2.2.2) := by abel
  have e₄ : θ.1 + θ.2.1 - (θ'.1 + θ'.2.1) = (θ.1 - θ'.1) + (θ.2.1 - θ'.2.1) := by abel
  simp only [interiorPairing, dissipation, diagDiff, skewCoeffs, e₁, e₂, e₃, e₄, GX_one, GZ_one,
    GU_one, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]
  generalize θ.1 - θ'.1 = x
  generalize θ.2.1 - θ'.2.1 = y
  generalize θ.2.2.1 - θ'.2.2.1 = z
  generalize θ.2.2.2 - θ'.2.2.2 = u
  simp only [inner_neg_left, inner_sub_left, inner_add_left, real_inner_self_eq_norm_sq]
  rw [real_inner_comm y x]
  ring

/-- **Assumption 2.3, interior, pointwise, for `skewCoeffs`**, with `L = 2`. -/
theorem lipschitzCoefficientsP2_skew :
    LipschitzCoefficientsP2 2 (skewCoeffs (ν := ν) (n := n) (d := d)).b
      (skewCoeffs (ν := ν) (n := n) (d := d)).σ (skewCoeffs (ν := ν) (n := n) (d := d)).h
      (skewCoeffs (ν := ν) (n := n) (d := d)).f := by
  intro t θ θ' μ μ'
  have e₁ : θ.1 - θ.2.1 - (θ'.1 - θ'.2.1) = (θ.1 - θ'.1) - (θ.2.1 - θ'.2.1) := by abel
  have e₂ : -θ.2.2.1 - -θ'.2.2.1 = -(θ.2.2.1 - θ'.2.2.1) := by abel
  have e₃ : -θ.2.2.2 - -θ'.2.2.2 = -(θ.2.2.2 - θ'.2.2.2) := by abel
  have e₄ : θ.1 + θ.2.1 - (θ'.1 + θ'.2.1) = (θ.1 - θ'.1) + (θ.2.1 - θ'.2.1) := by abel
  simp only [skewCoeffs, e₁, e₂, e₃, e₄, norm_neg]
  have htn : tupleNorm (θ - θ')
      = ‖θ.1 - θ'.1‖ + ‖θ.2.1 - θ'.2.1‖ + ‖θ.2.2.1 - θ'.2.2.1‖ + ‖θ.2.2.2 - θ'.2.2.2‖ := rfl
  rw [htn]
  have h₁ := norm_sub_le (θ.1 - θ'.1) (θ.2.1 - θ'.2.1)
  have h₂ := norm_add_le (θ.1 - θ'.1) (θ.2.1 - θ'.2.1)
  have hw := w2P_nonneg μ μ'
  linarith [norm_nonneg (θ.1 - θ'.1), norm_nonneg (θ.2.1 - θ'.2.1),
    norm_nonneg (θ.2.2.1 - θ'.2.2.1), norm_nonneg (θ.2.2.2 - θ'.2.2.2)]

/-- **Assumption 2.3, terminal, pointwise, for `skewCoeffs`**, with `L = 2`. -/
theorem lipschitzTerminalP2_skew :
    LipschitzTerminalP2 2 (skewCoeffs (ν := ν) (n := n) (d := d)).g := by
  intro x x' ρ ρ'
  simp only [skewCoeffs]
  have hw := w2P_nonneg ρ ρ'
  have hn := norm_nonneg (x - x')
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **Assumption 2.5, terminal, along the diagonal, for `skewCoeffs`**, with `G = 1` and
`α = 1`. -/
theorem terminalMonotone_skew :
    TerminalMonotone ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) 1
      (skewCoeffs (ν := ν) (n := n) (d := d)).g := by
  intro ξ ξ' _ _ _ _
  refine le_of_eq ?_
  simp only [skewCoeffs, GX_one, ContinuousLinearMap.id_apply, one_mul,
    real_inner_self_eq_norm_sq]

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **Assumption 2.5, interior, along the diagonal, for `skewCoeffs`**, with `G = 1` and
`β₁ = β₂ = 1`, with equality. -/
theorem diagonalMonotone_skew :
    DiagonalMonotone ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) 1 1
      (skewCoeffs (ν := ν) (n := n) (d := d)) :=
  Eventually.of_forall fun t Θ Θ' _ _ _ _ => le_of_eq (integral_congr_ae
    (Eventually.of_forall fun ω => interiorPairing_skew t (Θ ω) (Θ' ω) _ _))

/-- **(2.3) for `skewCoeffs`, with the Hilbert-norm `W₂` on `P₂(H)`**: the coefficients are
continuous in the tuple and independent of the time and the law. -/
theorem coeffBorelW2_skew (T : ℝ) : CoeffBorelW2 T (skewCoeffs (ν := ν) (n := n) (d := d)) where
  b_meas := measurable_borelW2_of_measurable (ψ := (skewCoeffs (ν := ν) (n := n) (d := d)).b)
    (by simp only [skewCoeffs]; fun_prop)
  σ_meas := measurable_borelW2_of_measurable (ψ := (skewCoeffs (ν := ν) (n := n) (d := d)).σ)
    (by simp only [skewCoeffs]; fun_prop)
  h_meas := measurable_borelW2_of_measurable (ψ := (skewCoeffs (ν := ν) (n := n) (d := d)).h)
    (by simp only [skewCoeffs]; fun_prop)
  f_meas := measurable_borelW2_of_measurable (ψ := (skewCoeffs (ν := ν) (n := n) (d := d)).f)
    (by simp only [skewCoeffs]; fun_prop)

/-- **`skewCoeffs` satisfies the hypotheses of Lemma 4.3**: (2.3), Assumption 2.3 with `L = 2`,
Assumption 2.4 with `G = 1`, and Assumption 2.5 with `G = 1` and `α = β₁ = β₂ = 1`. -/
theorem skew_assumptions :
    JointBorel T (skewCoeffs (ν := ν) (n := n) (d := d))
      ∧ Assumption23 ℱ P T 2 (skewCoeffs (ν := ν) (n := n) (d := d))
      ∧ (1 : Matrix (Fin n) (Fin n) ℝ).rank = min n n
      ∧ Assumption25 ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) 1 1 1
          (skewCoeffs (ν := ν) (n := n) (d := d)) := by
  have hJ : JointBorel T (skewCoeffs (ν := ν) (n := n) (d := d)) :=
    jointBorel_iff.mpr ⟨coeffBorelW2_skew T, continuous_fst.borel_measurable⟩
  have h23 : Assumption23 ℱ P T 2 (skewCoeffs (ν := ν) (n := n) (d := d)) :=
    ⟨zero_le_two, LipInterior.of_diagonalLipschitz
        (diagonalLipschitz_of_lipschitzCoefficientsP2 lipschitzCoefficientsP2_skew),
      terminalLipschitz_of_lipschitzTerminalP2 lipschitzTerminalP2_skew⟩
  exact ⟨hJ, h23, rank_one_eq_min, Assumption25.of_monotone hJ h23
    (constants_affine one_pos one_pos) diagonalMonotone_skew terminalMonotone_skew⟩

end Coefficients

/-! ### The deterministic solutions -/

section Solutions

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {n d : ℕ}

/-- The backward component `Y_t = a e^{−t}` of the solution with parameter `a`. -/
noncomputable def skewY (a : ℝ) : Fin n → ℝ → Ω → ℝ := fun _ t _ => a * Real.exp (-t)

/-- The drift forcing `q^b_t = a e^{−t}` on `[0, T]`, `0` off it, of the solution with parameter
`a`. -/
noncomputable def skewQb (a T : ℝ) : Fin n → Ω → ℝ → ℝ :=
  fun _ _ s => (Set.Icc (0 : ℝ) T).indicator (fun s => a * Real.exp (-s)) s

/-- The terminal forcing `q^g_T = a e^{−T}` of the solution with parameter `a`. -/
noncomputable def skewQg (a T : ℝ) : Fin n → Ω → ℝ := fun _ _ => a * Real.exp (-T)

variable {T : ℝ}

/-- The cut-off `s ↦ 1_{[0, T]}(s) a e^{−s}` is measurable. -/
theorem measurable_indicator_exp (a : ℝ) :
    Measurable ((Set.Icc (0 : ℝ) T).indicator fun s => a * Real.exp (-s)) :=
  (by fun_prop : Measurable fun s : ℝ => a * Real.exp (-s)).indicator measurableSet_Icc

/-- On `[0, T]`, `|1_{[0, T]}(s) a e^{−s}| ≤ |a|`. -/
theorem abs_indicator_exp_le (a : ℝ) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      |(Set.Icc (0 : ℝ) T).indicator (fun s => a * Real.exp (-s)) s| ≤ |a| := by
  intro s hs
  rw [Set.indicator_of_mem hs, abs_mul, Real.abs_exp]
  exact mul_le_of_le_one_right (abs_nonneg a) (Real.exp_le_one_iff.mpr (by linarith [hs.1]))

/-- `a e^{−t} = a e^{−T} + ∫_t^T a e^{−s} ds` for `t ∈ [0, T]`, the integrand cut to `[0, T]`. -/
theorem exp_eq_add_integral (a : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    a * Real.exp (-t) = a * Real.exp (-T)
      + ∫ s in Set.Icc t T, (Set.Icc (0 : ℝ) T).indicator (fun s => a * Real.exp (-s)) s := by
  rw [setIntegral_congr_fun measurableSet_Icc (g := fun s => a * Real.exp (-s))
    fun s hs => Set.indicator_of_mem (show s ∈ Set.Icc (0 : ℝ) T from ⟨ht.1.trans hs.1, hs.2⟩) _,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_neg (fun s => Real.exp s),
    integral_exp]
  ring

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The forcing of the solution with parameter `a` is a forcing of (4.1). -/
theorem skew_forcing {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (a : ℝ) :
    Forcing ℱ P ν T (skewQb (n := n) a T) (0 : Fin n → ℝ → Ω → Fin d → ℝ)
      (0 : Fin n → ℝ → Ω → E → ℝ) (0 : Fin n → Ω → ℝ → ℝ) (skewQg (n := n) a T) where
  qb_meas _ := (measurable_indicator_exp a).comp measurable_snd
  qb_prog _ := progressivelyMeasurable_of_measurable_time (measurable_indicator_exp a)
  qb_vanish _ _ _ hs := Set.indicator_of_notMem hs _
  qb_sq _ := energy_ne_top_of_bound (abs_indicator_exp_le a)
  qσ_meas _ _ := measurable_const
  qσ_prog _ _ := Brownian.Ito.progressivelyMeasurable_zero ℱ
  qσ_vanish _ _ _ _ := rfl
  qσ_sq _ _ := by simp [Brownian.Ito.energy]
  qh_meas _ := measurable_const
  qh_prog _ := Poisson.Compensated.markedProgressivelyMeasurable_zero ℱ
  qh_vanish _ _ _ _ _ := rfl
  qh_sq _ := by simp [Poisson.Compensated.markedEnergy]
  qf_meas _ := measurable_const
  qf_prog _ := Brownian.Ito.progressivelyMeasurable_zero ℱ
  qf_vanish _ _ _ _ := rfl
  qf_sq _ := by simp [Brownian.Ito.energy]
  qg_meas _ := stronglyMeasurable_const
  qg_sq _ := memLp_const _

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The forcing of the solution with parameter `a` is in the class of the paper. -/
theorem skew_predForcing {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (a : ℝ) :
    PredForcing ℱ P ν T (skewQb (n := n) a T) (0 : Fin n → ℝ → Ω → Fin d → ℝ)
      (0 : Fin n → ℝ → Ω → E → ℝ) (0 : Fin n → Ω → ℝ → ℝ) (skewQg (n := n) a T) :=
  { toForcing := skew_forcing a, qh_pred := fun _ => measurable_const }

/-- The drift process of `skewCoeffs` along `(0, a e^{−t}, 0, 0)` is `−a e^{−s}` on `[0, T]`. -/
theorem driftProc_skew (a : ℝ) (i : Fin n) (ω : Ω) (s : ℝ) :
    driftProc P T (skewCoeffs (ν := ν) (d := d)) 0 (skewY a) 0 0 i ω s
      = (Set.Icc (0 : ℝ) T).indicator (fun s => -(a * Real.exp (-s))) s := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · simp [driftProc, hs, skewCoeffs, tupleAt, skewY]
  · simp [driftProc, hs]

/-- The diffusion process of `skewCoeffs` along `(0, a e^{−t}, 0, 0)` vanishes. -/
theorem diffusionProc_skew (a : ℝ) (i : Fin n) (s : ℝ) (ω : Ω) (j : Fin d) :
    diffusionProc P T (skewCoeffs (ν := ν) (d := d)) 0 (skewY a) 0 0 i s ω j = 0 := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · simp [diffusionProc, hs, skewCoeffs, tupleAt]
  · simp [diffusionProc, hs]

/-- The driver process of `skewCoeffs` along `(0, a e^{−t}, 0, 0)` is `a e^{−s}` on `[0, T]`. -/
theorem driverProc_skew (a : ℝ) (k : Fin n) (ω : Ω) (s : ℝ) :
    driverProc P T (skewCoeffs (ν := ν) (d := d)) 0 (skewY a) 0 0 k ω s
      = (Set.Icc (0 : ℝ) T).indicator (fun s => a * Real.exp (-s)) s := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · simp [driverProc, hs, skewCoeffs, tupleAt, skewY]
  · simp [driverProc, hs]

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The terminal value of `skewCoeffs` along `X = 0` vanishes. -/
theorem terminalVal_skew (k : Fin n) (ω : Ω) :
    terminalVal P T (skewCoeffs (ν := ν) (d := d)) 0 k ω = 0 := by
  simp [terminalVal, skewCoeffs]

/-- The jump coefficient `h = −u` of `skewCoeffs` along `(0, a e^{−t}, 0, 0)` is represented by
the zero function of the marks. -/
theorem jumpRep_skew (a s : ℝ) (ω : Ω) :
    (fun e => (WithLp.toLp 2 fun i => (0 : Fin n → ℝ → Ω → E → ℝ) i s ω e :
        EuclideanSpace ℝ (Fin n)))
      =ᵐ[ν] (skewCoeffs (ν := ν) (d := d)).h s (tupleAt ν 0 (skewY a) 0 0 s ω)
        (lawP2 P (tupleAt ν 0 (skewY a) 0 0 s)) := by
  have hu := System.coeFn_uLift (ν := ν)
    (u := fun e (k : Fin n) => (0 : Fin n → ℝ → Ω → E → ℝ) k s ω e) fun _ => MemLp.zero
  filter_upwards [Lp.coeFn_neg (uLift ν fun e (k : Fin n) => (0 : Fin n → ℝ → Ω → E → ℝ) k s ω e),
    hu] with e h1 h2
  change _ = ((-(uLift ν fun e (k : Fin n) => (0 : Fin n → ℝ → Ω → E → ℝ) k s ω e) :
    Lp (EuclideanSpace ℝ (Fin n)) 2 ν) : E → EuclideanSpace ℝ (Fin n)) e
  rw [h1, Pi.neg_apply, h2]
  have h0 : (WithLp.toLp 2 fun _ : Fin n => (0 : ℝ) : EuclideanSpace ℝ (Fin n)) = 0 :=
    WithLp.toLp_zero 2
  simp only [Pi.zero_apply, h0, neg_zero]

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}

/-- **The deterministic solution with parameter `a`.** For `T ≥ 0` and `a ∈ ℝ`, over a filtration
carrying the driver, `(0, a e^{−t}, 0, 0)` solves the `λ`-forced system (4.1) at `λ = 1` for
`skewCoeffs`, with initial datum `0`, the forcing `q^b_t = a e^{−t}` on `[0, T]`,
`q^g_T = a e^{−T}`, `q^σ = q^h = q^f = 0`, and the representative `γ = 0` of the jump
coefficient. -/
theorem skew_solvesForced {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
    {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} (a : ℝ) :
    SolvesForced D ℱ hℱW hℱN T 1 (skewCoeffs (ν := ν) (d := d)) 0 (skewQb (n := n) a T) 0 0 0
      (skewQg a T) 0 (skewY a) 0 0 0 where
  forcing := skew_forcing a
  jump_rep := Eventually.of_forall fun s => Eventually.of_forall fun ω => jumpRep_skew a s ω
  fwd i := linearFSDEJ_zero.of_eq rfl
    (funext fun ω => funext fun s => by
      simp only [driftProc_skew, skewQb, Pi.zero_apply]
      by_cases hs : s ∈ Set.Icc (0 : ℝ) T <;> simp [hs])
    rfl (funext fun s => funext fun ω => funext fun j => by simp [diffusionProc_skew])
    (funext fun s => funext fun ω => funext fun e => by simp [jumpProc])
  bwd k := (linearBSDEJ_of_deterministic (c := a * Real.exp (-T)) (y := fun t => a * Real.exp (-t))
      (measurable_indicator_exp a) (fun s hs => Set.indicator_of_notMem hs _)
      (abs_indicator_exp_le a) (by fun_prop) fun t ht => exp_eq_add_integral a ht).of_eq
    (funext fun ω => by simp [terminalVal_skew, skewQg])
    (funext fun ω => funext fun s => by simp [driverProc_skew]) rfl rfl rfl

/-- **The deterministic solution with parameter `a`, in the sense of the paper.** Over a
filtration carrying the driver, whose null sets lie in its time-`0` field, whose
right-continuation is constant before `0` and which admits a cross witness, for `T > 0`,
`(0, a e^{−t}, 0, 0)` solves (4.1) at `λ = 1` for `skewCoeffs` in the sense of
`PaperSolutionForced`, with the data of `skew_solvesForced`. -/
theorem skew_paperSolutionForced {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
    {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (a : ℝ) :
    PaperSolutionForced D ℱ hℱW hℱN T 1 (skewCoeffs (ν := ν) (d := d)) 0 (skewQb (n := n) a T) 0
      0 0 (skewQg a T) 0 (skewY a) 0 0 0 :=
  (skew_solvesForced a).paperSolutionForced
    (fun _ _ => predictable_of_measurable_time (g := fun _ => 0) measurable_const)
    (fun _ => measurable_const) 𝒲 hℱ0 hnull hT

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] in
/-- On `[0, T]`, `|a e^{−t} − b e^{−t}|² ≤ |a − b|²` coordinatewise. -/
theorem esq_skewY_sub_le (a b : ℝ) {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    esq (fun k : Fin n => skewY a k t ω - skewY b k t ω)
      ≤ ENNReal.ofReal (∑ _k : Fin n, (a - b) ^ 2) := by
  rw [esq_eq_ofReal_sum_sq]
  refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun k _ => ?_)
  have he : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  simp only [skewY]
  rw [show a * Real.exp (-t) - b * Real.exp (-t) = (a - b) * Real.exp (-t) by ring, mul_pow]
  exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ he he1)

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The difference of the solutions with parameters `a` and `b` lies in `ℍ`: its size `supSize`
is finite. -/
theorem supSize_skew_lt_top (a b : ℝ) :
    supSize P ν T (fun i t ω => (0 : Fin n → ℝ → Ω → ℝ) i t ω - (0 : Fin n → ℝ → Ω → ℝ) i t ω)
        (fun k t ω => skewY (n := n) a k t ω - skewY b k t ω)
        (fun k t ω j => (0 : Fin n → ℝ → Ω → Fin d → ℝ) k t ω j
          - (0 : Fin n → ℝ → Ω → Fin d → ℝ) k t ω j)
        (fun k t ω e => (0 : Fin n → ℝ → Ω → E → ℝ) k t ω e
          - (0 : Fin n → ℝ → Ω → E → ℝ) k t ω e) < ⊤ := by
  unfold supSize
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨by simp [esq], ?_⟩,
    by simp [Brownian.Ito.energy]⟩, by simp [Poisson.Compensated.markedEnergy]⟩
  refine lt_of_le_of_lt (lintegral_mono fun ω => iSup₂_le fun t ht =>
    esq_skewY_sub_le a b ht.1 ω) ?_
  simp only [lintegral_const, measure_univ, mul_one]
  exact ENNReal.ofReal_lt_top

/-- **The left side of (4.25) at the solutions with parameters `a` and `b`**: at `s ∈ [0, T]`,
`𝔼⟨δY_s, δf_s⟩ = n ((a − b) e^{−s})²`. -/
theorem integral_pairing_skew (a b : ℝ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ∫ ω, ∑ k : Fin n, (skewY a k s ω - skewY b k s ω)
        * (1 * (driverProc P T (skewCoeffs (ν := ν) (d := d)) 0 (skewY a) 0 0 k ω s
            - driverProc P T (skewCoeffs (ν := ν) (d := d)) 0 (skewY b) 0 0 k ω s)
          + ((0 : Fin n → Ω → ℝ → ℝ) k ω s - (0 : Fin n → Ω → ℝ → ℝ) k ω s)) ∂P
      = n * ((a - b) * Real.exp (-s)) ^ 2 := by
  simp only [driverProc_skew, Set.indicator_of_mem hs, skewY, Pi.zero_apply, sub_self, add_zero,
    one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, integral_const,
    probReal_univ, one_smul]
  ring

/-- **`𝔼|δY_s|²` at the solutions with parameters `a` and `b`** is `n ((a − b) e^{−s})²`. -/
theorem lintegral_esq_skewY_sub (a b s : ℝ) :
    ∫⁻ ω, esq (fun k : Fin n => skewY a k s ω - skewY b k s ω) ∂P
      = ENNReal.ofReal (n * ((a - b) * Real.exp (-s)) ^ 2) := by
  simp only [esq_eq_ofReal_sum_sq, skewY, lintegral_const, measure_univ, mul_one]
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Solutions

end Dissertation.WellPosedness.Spec
