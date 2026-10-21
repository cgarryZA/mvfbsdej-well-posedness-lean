/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.ForcingAlgebra
import Dissertation.WellPosedness.Existence.SizeCompare
import Dissertation.WellPosedness.Existence.WPZero

/-!
# The contraction of the continuation map on forcings

In the continuation step of the existence proof of the well-posedness paper, a solution `Θ` of
the `λ₀`-forced system (4.1) generates the forcing

`Ψ(Θ) = (b(s, Θ_s, μ_s), σ(s, Θ_s, μ_s), h(s, Θ_s, ·, μ_s), f(s, Θ_s, μ_s), g(X_T, Law X_T))`,

and the continuation map sends a forcing `F` to `ζ Ψ(Θ)`, `Θ` the `λ₀`-solution with forcing
`q + F`. For two `λ₀`-solutions `Θ¹, Θ²` with the same coefficients, satisfying Assumption 2.3
along the diagonal with constant `L`, the expected Lipschitz bound (3.2), integrated over
`[0, T]`, and the terminal bound (2.6) with (2.9) bound the data size of `Ψ(Θ¹) − Ψ(Θ²)` by the
energies and the terminal moment of `δΘ = Θ¹ − Θ²`, hence by its size with running suprema:

`dataSize(Ψ(Θ¹) − Ψ(Θ²)) ≤ K_L supSize(δΘ)`,   `K_L = 10 L² max(T, 1) + 4 L²`.

If the `λ₀`-system is stable with constant `C_s`, `supSize(δΘ) ≤ C_s Δ` for a data size `Δ` of
the difference of the data of `Θ¹` and `Θ²`, then, since the data size is quadratic,

`dataSize(ζ Ψ(Θ¹) − ζ Ψ(Θ²)) ≤ ζ² K_L C_s Δ`.

The stability constant is `C₀(T)` at `λ₀ = 0` and the constant of (4.14) at `λ₀ ≥ λ̲ > 0`; both
enter as the hypothesis on `Dissertation.WellPosedness.Stability.supSize`.

## Main definitions

* `lipConst` — the constant `K_L = 10 L² max(T, 1) + 4 L²`.

## Main statements

* `PairLipschitz.sum_energy_le` — (3.2) integrated over the horizon.
* `PairLipschitz.dataSize_le` — the data size of the coefficient differences by the size with
  running suprema.
* `SolvesForced.dataSize_coeff_sub_le` — `dataSize(Ψ(Θ¹) − Ψ(Θ²)) ≤ K_L C_s Δ`.
* `SolvesForced.dataSize_smul_coeff_sub_le` — `dataSize(ζ Ψ(Θ¹) − ζ Ψ(Θ²)) ≤ ζ² K_L C_s Δ`.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System LevyStochCalc

universe u v w

/-- The constant `K_L = 10 L² max(T, 1) + 4 L²` of the bound of the data size of the coefficient
differences along two solutions by their size with running suprema. -/
noncomputable def lipConst (T L : ℝ) : ℝ := 10 * L ^ 2 * max T 1 + 4 * L ^ 2

/-- The constant `K_L` is nonnegative. -/
theorem lipConst_nonneg (T L : ℝ) : 0 ≤ lipConst T L :=
  add_nonneg (mul_nonneg (by positivity) (le_max_of_le_right zero_le_one)) (by positivity)

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

/-! ### The expected Lipschitz bounds over the horizon -/

section PairLipschitz

variable {K KT : ℝ} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {b : Fin n → Ω → ℝ → ℝ}
  {σ : Fin n → ℝ → Ω → Fin d → ℝ} {h : Fin n → ℝ → Ω → E → ℝ} {f : Fin m → Ω → ℝ → ℝ}
  {g : Fin m → Ω → ℝ}

/-- **(3.2) over the horizon.** If the coefficient differences `(δb, δσ, δh, δf)` are jointly
measurable, obey (3.2) with constant `K` at almost every time of `[0, T]` along a progressive
difference `(δX, δY, δZ, δU)`, then
`𝔼 ∫_0^T (|δb|² + |δσ|²_F + ‖δh‖² + |δf|²) ≤ K 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²)`. -/
theorem _root_.Dissertation.WellPosedness.System.PairLipschitz.sum_energy_le
    (hL : PairLipschitz P ν T K KT X Y Z U b σ h f g) (hΘ : ProgTuple ℱ P ν T X Y Z U)
    (hb : ∀ i, Measurable (Function.uncurry (b i)))
    (hσ : ∀ i j, Measurable (Function.uncurry fun ω s => σ i s ω j))
    (hh : ∀ i, Measurable fun p : Ω × ℝ × E => h i p.2.1 p.1 p.2.2)
    (hf : ∀ k, Measurable (Function.uncurry (f k))) :
    ∑ i, Brownian.Ito.energy P T (b i)
        + ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => σ i s ω j)
        + ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => h i s ω e)
        + ∑ k, Brownian.Ito.energy P T (f k)
      ≤ ENNReal.ofReal K * (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
          + ∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
          + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)) := by
  have hL1 : ∫⁻ s in Set.Icc (0 : ℝ) T, (sampleEnergy P b s
        + ∑ i, sampleEnergy P (fun j ω s => σ i s ω j) s
        + markedSampleEnergy P ν (fun i ω s e => h i s ω e) s + sampleEnergy P f s)
      = ∑ i, Brownian.Ito.energy P T (b i)
        + ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => σ i s ω j)
        + ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => h i s ω e)
        + ∑ k, Brownian.Ito.energy P T (f k) := by
    rw [lintegral_add_left (measurable_sampleEnergy_add (x := b)
        (z := fun i j ω s => σ i s ω j) (u := fun i ω s e => h i s ω e) hb hσ hh),
      lintegral_sampleEnergy_add (x := b) (z := fun i j ω s => σ i s ω j)
        (u := fun i ω s e => h i s ω e) hb hσ hh T, lintegral_sampleEnergy hf T]
  have hR1 : ∫⁻ s in Set.Icc (0 : ℝ) T, (sampleEnergy P (fun i ω s => X i s ω) s
        + (sampleEnergy P (fun k ω s => Y k s ω) s
          + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
          + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s))
      = ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
        + (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
          + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)) := by
    have hXm : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω) := fun i =>
      (Probability.measurable_uncurry_of_rightContinuous (hΘ.X_adapted i)
        (hΘ.X_rightCont i)).comp measurable_swap
    have hYm : ∀ k, Measurable (Function.uncurry fun ω s => Y k s ω) := fun k =>
      (Probability.measurable_uncurry_of_rightContinuous (hΘ.Y_adapted k)
        (hΘ.Y_rightCont k)).comp measurable_swap
    rw [lintegral_add_left (measurable_sampleEnergy (x := fun i ω s => X i s ω) hXm),
      lintegral_sampleEnergy (x := fun i ω s => X i s ω) hXm T,
      lintegral_sampleEnergy_add (x := fun k ω s => Y k s ω) (z := fun k j ω s => Z k s ω j)
        (u := fun k ω s e => U k s ω e) hYm hΘ.Z_meas hΘ.U_meas T]
  rw [← hL1, add_assoc _ (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)),
    add_assoc (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)), ← hR1,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hL.lip] with s hs
  refine le_trans ?_ (hs.trans (le_of_eq ?_))
  · simp only [sampleEnergy, markedSampleEnergy, esq]
    exact le_trans (add_le_add (add_le_add (add_le_add (sum_lintegral_le _ _)
      ((Finset.sum_le_sum fun i _ => sum_lintegral_le _ _).trans (sum_lintegral_le _ _)))
      (sum_lintegral_le _ _)) (sum_lintegral_le _ _)) (lintegral_add_four_le _ _ _ _)
  · have hsq : ∀ {u : Ω → ℝ}, Measurable u → Measurable fun ω => (‖u ω‖₊ : ℝ≥0∞) ^ 2 :=
      fun hu => hu.nnnorm.coe_nnreal_ennreal.pow_const 2
    have hX : ∀ i, Measurable (X i s) := fun i => (hΘ.X_adapted i s).mono (ℱ.le s) le_rfl
    have hY : ∀ k, Measurable (Y k s) := fun k => (hΘ.Y_adapted k s).mono (ℱ.le s) le_rfl
    have hZ : ∀ k j, Measurable fun ω => Z k s ω j := fun k j =>
      (hΘ.Z_meas k j).comp (measurable_id.prodMk measurable_const)
    have hU : ∀ k, Measurable fun ω => ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := fun k =>
      (measurable_uncurry_lintegral_sq_mark (ν := ν) (φ := fun ω s e => U k s ω e)
        (hΘ.U_meas k)).comp (measurable_id.prodMk measurable_const)
    simp only [sampleEnergy, markedSampleEnergy, esq]
    rw [lintegral_add_four (Finset.measurable_sum _ fun i _ => hsq (hX i))
        (Finset.measurable_sum _ fun k _ => hsq (hY k))
        (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun j _ => hsq (hZ k j)),
      lintegral_finsetSum' _ fun i _ => (hsq (hX i)).aemeasurable,
      lintegral_finsetSum' _ fun k _ => (hsq (hY k)).aemeasurable,
      lintegral_finsetSum' _ fun k _ =>
        (Finset.measurable_sum _ fun j _ => hsq (hZ k j)).aemeasurable,
      lintegral_finsetSum' _ fun k _ => (hU k).aemeasurable]
    simp only [lintegral_finsetSum' _ fun j _ => (hsq (hZ _ j)).aemeasurable, add_assoc]

/-- **The data size of the coefficient differences by the size with running suprema.** Under the
hypotheses of `PairLipschitz.sum_energy_le`, with `K, K_T, T ≥ 0`,
`𝔼|δg|² + 𝔼 ∫_0^T (|δb|² + |δσ|²_F + ‖δh‖² + |δf|²) ≤ (K max(T, 1) + K_T) N`, `N` the size of
`(δX, δY, δZ, δU)` with running suprema. -/
theorem _root_.Dissertation.WellPosedness.System.PairLipschitz.dataSize_le
    (hL : PairLipschitz P ν T K KT X Y Z U b σ h f g) (hΘ : ProgTuple ℱ P ν T X Y Z U)
    (hb : ∀ i, Measurable (Function.uncurry (b i)))
    (hσ : ∀ i j, Measurable (Function.uncurry fun ω s => σ i s ω j))
    (hh : ∀ i, Measurable fun p : Ω × ℝ × E => h i p.2.1 p.1 p.2.2)
    (hf : ∀ k, Measurable (Function.uncurry (f k))) (hK : 0 ≤ K) (hKT : 0 ≤ KT) (hT : 0 ≤ T) :
    dataSize P ν T 0 b σ h f g ≤ ENNReal.ofReal (K * max T 1 + KT) * supSize P ν T X Y Z U := by
  have h0 : ∫⁻ ω, esq (fun i => (0 : Fin n → Ω → ℝ) i ω) ∂P = 0 := by simp [esq]
  calc dataSize P ν T 0 b σ h f g
      = ∫⁻ ω, esq (fun k => g k ω) ∂P + (∑ i, Brownian.Ito.energy P T (b i)
          + ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => σ i s ω j)
          + ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => h i s ω e)
          + ∑ k, Brownian.Ito.energy P T (f k)) := by
        unfold dataSize
        rw [h0, zero_add]
        ring
    _ ≤ ENNReal.ofReal KT * ∫⁻ ω, esq (fun i => X i T ω) ∂P
          + ENNReal.ofReal K * (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
            + ∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
            + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
            + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)) :=
        add_le_add hL.lipT (hL.sum_energy_le hΘ hb hσ hh hf)
    _ ≤ _ := by
        rw [add_comm]
        exact energies_add_terminal_le_supSize hK hKT hT X Y Z U

end PairLipschitz

/-! ### Along two solutions -/

section Solutions

variable [MeasurableSpace.CountablyGenerated E]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {lam L Cs : ℝ} {C : Coeffs ν n m d}
  {ξ₁ ξ₂ : Fin n → Ω → ℝ} {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ : Fin m → Ω → ℝ}
  {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {Δ : ℝ≥0∞}

/-- **The coefficient processes along two solutions differ by at most `K_L C_s Δ`.** Let
`Θ¹, Θ²` solve the `λ`-forced system (4.1) with the same coefficients, satisfying Assumption 2.3
along the diagonal with constant `L`, over a filtration whose null sets lie in its time-`0`
field, whose right-continuation is constant before `0` and which admits a cross witness; let
the coefficient processes `Ψ(Θ¹), Ψ(Θ²)` along them be forcings, and let
`supSize(Θ¹ − Θ²) ≤ C_s Δ`. Then `dataSize(Ψ(Θ¹) − Ψ(Θ²)) ≤ K_L C_s Δ`, with zero initial
datum. -/
theorem _root_.Dissertation.WellPosedness.System.SolvesForced.dataSize_coeff_sub_le
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hΨ₁ : Forcing ℱ P ν T (driftProc P T C X₁ Y₁ Z₁ U₁) (diffusionProc P T C X₁ Y₁ Z₁ U₁)
      (jumpProc T γ₁) (driverProc P T C X₁ Y₁ Z₁ U₁) (terminalVal P T C X₁))
    (hΨ₂ : Forcing ℱ P ν T (driftProc P T C X₂ Y₂ Z₂ U₂) (diffusionProc P T C X₂ Y₂ Z₂ U₂)
      (jumpProc T γ₂) (driverProc P T C X₂ Y₂ Z₂ U₂) (terminalVal P T C X₂))
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g)
    (hstab : supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      ≤ ENNReal.ofReal Cs * Δ) :
    dataSize P ν T 0
        (fun i ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
        (fun i s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
          - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
        (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
        (fun k ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
        (fun k ω => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
      ≤ ENNReal.ofReal (lipConst T L * Cs) * Δ := by
  have hΨ := hΨ₁.sub hΨ₂
  have hΘ : ProgTuple ℱ P ν T (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e) :=
    ProgTuple.of_legs (fun i => h₁.fwd_sub h₂ hT.le i) (fun k => h₁.bwd_sub h₂ k)
  calc _ ≤ ENNReal.ofReal (lipConst T L) * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω)
        (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
        (fun k t ω e => U₁ k t ω e - U₂ k t ω e) :=
      (h₁.pairLipschitz h₂ 𝒲 hℱ0 hnull hT hL hLT).dataSize_le hΘ hΨ.qb_meas hΨ.qσ_meas
        hΨ.qh_meas hΨ.qf_meas (by positivity) (by positivity) hT.le
    _ ≤ ENNReal.ofReal (lipConst T L) * (ENNReal.ofReal Cs * Δ) := by gcongr
    _ = ENNReal.ofReal (lipConst T L * Cs) * Δ := by
        rw [ENNReal.ofReal_mul (lipConst_nonneg T L), mul_assoc]

/-- **The contraction of the continuation map.** Under the hypotheses of
`SolvesForced.dataSize_coeff_sub_le`, for every real `ζ`,
`dataSize(ζ Ψ(Θ¹) − ζ Ψ(Θ²)) ≤ ζ² K_L C_s Δ`, with zero initial datum. -/
theorem _root_.Dissertation.WellPosedness.System.SolvesForced.dataSize_smul_coeff_sub_le
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hΨ₁ : Forcing ℱ P ν T (driftProc P T C X₁ Y₁ Z₁ U₁) (diffusionProc P T C X₁ Y₁ Z₁ U₁)
      (jumpProc T γ₁) (driverProc P T C X₁ Y₁ Z₁ U₁) (terminalVal P T C X₁))
    (hΨ₂ : Forcing ℱ P ν T (driftProc P T C X₂ Y₂ Z₂ U₂) (diffusionProc P T C X₂ Y₂ Z₂ U₂)
      (jumpProc T γ₂) (driverProc P T C X₂ Y₂ Z₂ U₂) (terminalVal P T C X₂))
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g)
    (hstab : supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      ≤ ENNReal.ofReal Cs * Δ) (ζ : ℝ) :
    dataSize P ν T 0
        (fun i ω s => ζ * driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
          - ζ * driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
        (fun i s ω j => ζ * diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
          - ζ * diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
        (fun i s ω e => ζ * jumpProc T γ₁ i s ω e - ζ * jumpProc T γ₂ i s ω e)
        (fun k ω s => ζ * driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
          - ζ * driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
        (fun k ω => ζ * terminalVal P T C X₁ k ω - ζ * terminalVal P T C X₂ k ω)
      ≤ ENNReal.ofReal (ζ ^ 2 * lipConst T L * Cs) * Δ := by
  have e := dataSize_smul (P := P) (ν := ν) (T := T) ζ 0
    (fun i ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
    (fun i s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
      - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
    (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
    (fun k ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
    (fun k ω => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
  simp only [Pi.zero_apply, mul_zero, mul_sub] at e
  calc _ = ENNReal.ofReal (ζ ^ 2) * dataSize P ν T 0
          (fun i ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
          (fun i s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
          (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
          (fun k ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
            - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
          (fun k ω => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) := e
    _ ≤ ENNReal.ofReal (ζ ^ 2) * (ENNReal.ofReal (lipConst T L * Cs) * Δ) := by
        gcongr
        exact h₁.dataSize_coeff_sub_le h₂ hΨ₁ hΨ₂ 𝒲 hℱ0 hnull hT hL hLT hstab
    _ = ENNReal.ofReal (ζ ^ 2 * lipConst T L * Cs) * Δ := by
        rw [mul_assoc (ζ ^ 2), ENNReal.ofReal_mul (sq_nonneg ζ), mul_assoc]

end Solutions

end Dissertation.WellPosedness.Existence
