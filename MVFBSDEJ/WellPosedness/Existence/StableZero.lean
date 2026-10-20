/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.Apriori
import MVFBSDEJ.WellPosedness.System.BridgeDiff

/-!
# Stability of the `λ = 0` system

At `λ = 0` the `λ`-forced system (4.1) does not see its coefficients: the forward equation is
the Itô process `X_t = ξ₀ + ∫_0^t q^b + ∫_0^t q^σ dW + ∫_0^t ∫_E q^h dÑ` and the backward
equation is the linear backward equation with terminal value `q^g_T` and drift `q^f`. Two
solutions, for coefficients `C¹, C²`, initial data `ξ₀¹, ξ₀²` and forcings `q¹, q²`, therefore
differ by a solution of the difference system `PairDiff` of the zero coefficients, with
Lipschitz constants `K = K_T = 0` and Assumption 2.5 holding with `G = 0` and
`α = β₁ = β₂ = 0`. The bounds of Lemma 4.3 then close without the rank case:

* the weighted forward bound at rate `c = 0` gives `𝔼|δX_T|² + 𝔼 ∫_0^T |δX|² ≤ e^{2T} P`, with
  `P` the data size of the differences;
* the backward estimate gives `𝔼|δY_0|² + 𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²)
  ≤ 4 e^{2T} (𝔼|δX_T|² + 𝔼 ∫_0^T |δX|² + P)`;
* the supremum upgrade gives `N ≤ 6 (T + 4) (N' + P)`.

Hence the stability estimate at `λ = 0`,

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²) ≤ C₀(T) P`,

`C₀(T) = 6 (T + 4) (1 + e^{2T}) (1 + 4 e^{2T})`, which depends on the horizon only. This is the
estimate that starts the continuation from `λ = 0` (Lemma 4.2 of the paper), where the constant
of Lemma 4.3 is not available.

## Main definitions

* `zeroConst` — the constant `C₀(T) = 6 (T + 4) (1 + e^{2T}) (1 + 4 e^{2T})`.

## Main statements

* `SolvesForced.fwd_sub_zero`, `SolvesForced.bwd_sub_zero` — the difference equations at
  `λ = 0`.
* `SolvesForced.pairDiff_zero` — the difference of two `λ = 0` solutions is a `PairDiff` of the
  zero coefficients.
* `SolvesForced.supSize_sub_le_zero` — the stability estimate at `λ = 0`.
-/

open MeasureTheory Filter Matrix
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.System LevyStochCalc

universe u v w

/-- The constant `C₀(T) = 6 (T + 4) (1 + e^{2T}) (1 + 4 e^{2T})` of the stability estimate at
`λ = 0`. -/
noncomputable def zeroConst (T : ℝ) : ℝ :=
  6 * (T + 4) * (1 + Real.exp (2 * T)) * (1 + 4 * Real.exp (2 * T))

/-- The constant of the stability estimate at `λ = 0` is positive for `T ≥ 0`. -/
theorem zeroConst_pos {T : ℝ} (hT : 0 ≤ T) : 0 < zeroConst T := by
  unfold zeroConst
  positivity

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {C₁ C₂ : Coeffs ν n m d}
  {ξ₁ ξ₂ : Fin n → Ω → ℝ}
  {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ : Fin m → Ω → ℝ}
  {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ}

/-- **The forward difference equation at `λ = 0`**: coordinate `i` of `δX` solves the linear
forward equation from `δξ₀` with drift `δq^b`, diffusion `δq^σ` and jump integrand `δq^h`. -/
theorem _root_.MVFBSDEJ.WellPosedness.System.SolvesForced.fwd_sub_zero
    (h₁ : SolvesForced D ℱ hℱW hℱN T 0 C₁ ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T 0 C₂ ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hT : 0 ≤ T) (i : Fin n) :
    LinearFSDEJ D ℱ hℱW hℱN T (fun ω => ξ₁ i ω - ξ₂ i ω) (fun ω s => qb₁ i ω s - qb₂ i ω s)
      (fun t ω => X₁ i t ω - X₂ i t ω) (fun s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
      (fun s ω e => qh₁ i s ω e - qh₂ i s ω e) := by
  simpa only [zero_mul, zero_add] using h₁.fwd_sub h₂ hT i

/-- **The backward difference equation at `λ = 0`**: coordinate `k` of `(δY, δZ, δU)` solves the
linear backward equation with terminal value `δq^g` and drift `δq^f`. -/
theorem _root_.MVFBSDEJ.WellPosedness.System.SolvesForced.bwd_sub_zero
    (h₁ : SolvesForced D ℱ hℱW hℱN T 0 C₁ ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T 0 C₂ ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂) (k : Fin m) :
    LinearBSDEJ D ℱ hℱW hℱN T (fun ω => qg₁ k ω - qg₂ k ω) (fun ω s => qf₁ k ω s - qf₂ k ω s)
      (fun t ω => Y₁ k t ω - Y₂ k t ω) (fun s ω j => Z₁ k s ω j - Z₂ k s ω j)
      (fun s ω e => U₁ k s ω e - U₂ k s ω e) := by
  simpa only [zero_mul, zero_add] using h₁.bwd_sub h₂ k

/-- **The difference of two `λ = 0` solutions is a difference system of the zero
coefficients**: a `PairDiff` at `λ = 0` with zero coefficient differences, Lipschitz constants
`K = K_T = 0`, coupling matrix `G = 0` and `α = β₁ = β₂ = 0`, whose forcing is the difference of
the forcings. -/
theorem _root_.MVFBSDEJ.WellPosedness.System.SolvesForced.pairDiff_zero
    (h₁ : SolvesForced D ℱ hℱW hℱN T 0 C₁ ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T 0 C₂ ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hT : 0 ≤ T) :
    PairDiff D ℱ hℱW hℱN T 0 0 0 0 0 0 (0 : Matrix (Fin m) (Fin n) ℝ)
      (fun i ω => ξ₁ i ω - ξ₂ i ω)
      (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
      (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun _ _ _ => 0) (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0)
      (fun i ω s => qb₁ i ω s - qb₂ i ω s) (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
      (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
      (fun k ω => qg₁ k ω - qg₂ k ω) :=
  pairDiff_of_legs (fun i => by simpa only [mul_zero, zero_add] using h₁.fwd_sub_zero h₂ hT i)
    (fun k => by simpa only [mul_zero, zero_add] using h₁.bwd_sub_zero h₂ k)
    (h₁.forcing.sub h₂.forcing)
    { lip := Eventually.of_forall fun s => by simp [esq]
      lipT := by simp [esq] }
    { mono := Eventually.of_forall fun s => by simp [dotProduct]
      monoT := by simp [dotProduct] }

/-- **The stability estimate at `λ = 0`.** Two solutions of the `λ = 0` forced system, for
coefficients `C¹, C²`, initial data `ξ₀¹, ξ₀²` and forcings `q¹, q²`, satisfy

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)
  ≤ C₀(T) (𝔼|δξ₀|² + 𝔼|δq^g_T|² + 𝔼 ∫_0^T (|δq^b|² + |δq^σ|²_F + ‖δq^h‖² + |δq^f|²))`,

`C₀(T) = 6 (T + 4) (1 + e^{2T}) (1 + 4 e^{2T})`, over a filtration whose null sets lie in its
time-`0` field, whose right-continuation is constant before `0`, and which admits a cross
witness. -/
theorem _root_.MVFBSDEJ.WellPosedness.System.SolvesForced.supSize_sub_le_zero
    (h₁ : SolvesForced D ℱ hℱW hℱN T 0 C₁ ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T 0 C₂ ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      ≤ ENNReal.ofReal (zeroConst T)
        * dataSize P ν T (fun i ω => ξ₁ i ω - ξ₂ i ω) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
          (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
          (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω) := by
  set Pd := dataSize P ν T (fun i ω => ξ₁ i ω - ξ₂ i ω) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
    (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
    (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω) with hPd
  by_cases hP : Pd = ⊤
  · rw [hP, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (zeroConst_pos hT.le)).ne']
    exact le_top
  have hq := h₁.forcing.sub h₂.forcing
  have hD := h₁.pairDiff_zero h₂ hT.le
  obtain ⟨-, -, hqb, hqσ, hqh, -⟩ := lt_top_of_dataSize_ne_top hP
  -- the forward bound at rate `0`
  set G : ℝ → ℝ≥0∞ := fun s => sampleEnergy P (fun i ω s => qb₁ i ω s - qb₂ i ω s) s
    + ∑ i, sampleEnergy P (fun j ω s => qσ₁ i s ω j - qσ₂ i s ω j) s
    + markedSampleEnergy P ν (fun i ω s e => qh₁ i s ω e - qh₂ i s ω e) s with hG
  have hGw : ∫⁻ s in Set.Icc (0 : ℝ) T, G s
      = ∑ i, Brownian.Ito.energy P T (fun ω s => qb₁ i ω s - qb₂ i ω s)
        + ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ₁ i s ω j - qσ₂ i s ω j)
        + ∑ i, Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => qh₁ i s ω e - qh₂ i s ω e) :=
    lintegral_sampleEnergy_add hq.qb_meas hq.qσ_meas hq.qh_meas T
  have hbf : ∑ i, Brownian.Ito.energy P T (fun ω s => qb₁ i ω s - qb₂ i ω s) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => (hqb i).ne
  have hσf : ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ₁ i s ω j - qσ₂ i s ω j) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => ENNReal.sum_ne_top.mpr fun j _ => (hqσ i j).ne
  have hhf : ∑ i, Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => qh₁ i s ω e - qh₂ i s ω e) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => (hqh i).ne
  have hGf : ∫⁻ s in Set.Icc (0 : ℝ) T, G s ≠ ⊤ := by
    rw [hGw]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hbf, hσf⟩, hhf⟩
  have hF := forward_energy_le (fun i => h₁.fwd_sub_zero h₂ hT.le i) 𝒲 hT le_rfl
    (measurable_sampleEnergy_add hq.qb_meas hq.qσ_meas hq.qh_meas) hGf
    (Eventually.of_forall fun s => by simp only [ENNReal.ofReal_zero, zero_mul, zero_add, hG,
      le_refl])
  rw [add_zero, hGw, ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hbf, hσf⟩) hhf,
    ENNReal.toReal_add hbf hσf] at hF
  -- the backward estimate
  have hB := hD.backward_le 𝒲 hT le_rfl zero_le_one le_rfl le_rfl hP
  have hkB : backwardConst T 0 0 = 4 * Real.exp (2 * T) := by
    unfold backwardConst
    norm_num
  rw [hkB] at hB
  -- the time-integrated size
  have hN := hD.diffSize_lt_top 𝒲 hℱ0 hnull hT
  have hPr := toReal_dataSize hP
  set e := Real.exp (2 * T) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hN' : diffSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω)
      (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
      (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      ≤ ENNReal.ofReal (e + 4 * e * (e + 1)) * Pd := by
    rw [← ENNReal.ofReal_toReal hN.ne, ← ENNReal.ofReal_toReal hP,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [toReal_diffSize hN.ne]
    rw [← hPd] at hPr
    set A := (∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P).toReal
    set IX := (∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)).toReal
    set Y0 := (∫⁻ ω, esq (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P).toReal
    set J := (∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω)
      + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
      + ∑ k, Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => U₁ k s ω e - U₂ k s ω e)).toReal
    have hA : 0 ≤ A := ENNReal.toReal_nonneg
    have hIX : 0 ≤ IX := ENNReal.toReal_nonneg
    have hPr0 : 0 ≤ Pd.toReal := ENNReal.toReal_nonneg
    have hfw : A + IX ≤ e * Pd.toReal := by
      refine hF.trans (mul_le_mul_of_nonneg_left ?_ he0)
      rw [hPr]
      have := (ENNReal.toReal_nonneg : 0 ≤ (∫⁻ ω, esq (fun k => qg₁ k ω - qg₂ k ω) ∂P).toReal)
      have := (ENNReal.toReal_nonneg :
        0 ≤ (∑ k, Brownian.Ito.energy P T (fun ω s => qf₁ k ω s - qf₂ k ω s)).toReal)
      linarith
    have hbw : Y0 + J ≤ 4 * e * (A + IX + Pd.toReal) := hB
    nlinarith
  calc supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      ≤ ENNReal.ofReal (supConst T 0) * (diffSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω)
          (fun k t ω => Y₁ k t ω - Y₂ k t ω) (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j)
          (fun k t ω e => U₁ k t ω e - U₂ k t ω e) + Pd) :=
        hD.supSize_le 𝒲 hℱ0 hnull hT le_rfl zero_le_one le_rfl
    _ ≤ ENNReal.ofReal (supConst T 0) * (ENNReal.ofReal (e + 4 * e * (e + 1)) * Pd + Pd) := by
        gcongr
    _ = ENNReal.ofReal (zeroConst T) * Pd := by
        have hz : zeroConst T = supConst T 0 * ((e + 4 * e * (e + 1)) + 1) := by
          rw [he]
          unfold zeroConst supConst
          ring
        rw [hz, ENNReal.ofReal_mul (supConst_nonneg hT.le le_rfl),
          ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_one]
        ring

end MVFBSDEJ.WellPosedness.Existence
