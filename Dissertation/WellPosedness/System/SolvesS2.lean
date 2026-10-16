/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.Estimate
import Dissertation.WellPosedness.Stability.Sub
import Dissertation.WellPosedness.Stability.SupUpgrade
import Dissertation.WellPosedness.System.Solves

/-!
# The `𝕊`-norm of solutions and of their differences

The solution space of the well-posedness paper is
`𝕊 = S²(0, T; ℝⁿ) × S²(0, T; ℝᵐ) × H²_W × H²_N`, with squared norm

`‖Θ‖²_𝕊 = 𝔼 sup_{t ≤ T} |X_t|² + 𝔼 sup_{t ≤ T} |Y_t|² + 𝔼 ∫_0^T (|Z_t|²_F + ‖U_t‖²_{L²(ν)}) dt`,

the quantity `supSize`. Along a solution of the `λ`-forced system (4.1) each coordinate of `X`
solves a linear forward equation, which is a linear backward equation with its own terminal
value, and each coordinate of `(Y, Z, U)` solves a linear backward equation with
square-integrable data, so Lemma 4.1 gives `𝔼 sup_{t ≤ T} |X_{i,t}|² < ∞` and
`𝔼 sup_{t ≤ T} |Y_{k,t}|² < ∞`; the integrands `Z, U` have finite energy by the solution
predicate. The difference of two solutions of (4.1), at any two parameters, with any two sets of
coefficients, initial data and forcings, has finite `𝕊`-norm, since the difference of two
solutions of a linear equation solves the differenced linear equation. This is the finiteness of
the left-hand side of (4.14) that the a-priori estimate absorbs, as in Remark 3.2 and in the proof
of Theorem 3.3. The path and measurability conditions of `𝕊` are those of the solution predicate:
`X, Y` adapted with right-continuous paths, `Z, U` progressively measurable.

The filtration is one on which Lemma 4.1 applies: its null sets lie in its time-`0` field, its
right-continuation is constant before `0`, and it admits a cross witness.

## Main statements

* `SolvesForced.lintegral_biSup_X_lt_top`, `SolvesForced.lintegral_biSup_Y_lt_top` —
  `𝔼 sup_{t ≤ T} |X_t|² < ∞` and `𝔼 sup_{t ≤ T} |Y_t|² < ∞`.
* `supSize_lt_top_of_linear` — a tuple solving linear forward and backward equations has finite
  `𝕊`-norm.
* `SolvesForced.supSize_sub_lt_top` — the difference of two solutions has finite `𝕊`-norm.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam lam₁ lam₂ : ℝ}
  {C C₁ C₂ : Coeffs ν n m d} {ξ₀ ξ₁ ξ₂ : Fin n → Ω → ℝ}
  {qb qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf qf₁ qf₂ : Fin m → Ω → ℝ → ℝ}
  {qg qg₁ qg₂ : Fin m → Ω → ℝ}
  {X X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ}

/-! ### Coordinatewise `S²` bounds -/

/-- The squared running supremum over `[0, T]` of a finite family of solutions of linear forward
equations has finite expectation. -/
theorem lintegral_biSup_esq_lt_top_of_linearFSDEJ {ι : Type*} [Fintype ι] {x₀ : ι → Ω → ℝ}
    {b : ι → Ω → ℝ → ℝ} {x : ι → ℝ → Ω → ℝ} {σ : ι → ℝ → Ω → Fin d → ℝ}
    {γ' : ι → ℝ → Ω → E → ℝ} (h : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (x₀ i) (b i) (x i) (σ i) (γ' i))
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂P < ⊤ :=
  (lintegral_biSup_esq_le hT.le (fun i t => ((h i).X_adapted t).mono (ℱ.le t) le_rfl)
    fun i => (h i).X_rightCont).trans_lt (ENNReal.sum_lt_top.mpr fun i _ =>
      ((h i).linearBSDEJ hT.le).lintegral_biSup_sq_lt_top 𝒲 hℱ0 hnull hT)

/-- The squared running supremum over `[0, T]` of a finite family of solutions of linear backward
equations has finite expectation. -/
theorem lintegral_biSup_esq_lt_top_of_linearBSDEJ {ι : Type*} [Fintype ι] {ξ : ι → Ω → ℝ}
    {φ : ι → Ω → ℝ → ℝ} {y : ι → ℝ → Ω → ℝ} {z : ι → ℝ → Ω → Fin d → ℝ}
    {u : ι → ℝ → Ω → E → ℝ} (h : ∀ k, LinearBSDEJ D ℱ hℱW hℱN T (ξ k) (φ k) (y k) (z k) (u k))
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => y k t ω)) ∂P < ⊤ :=
  (lintegral_biSup_esq_le hT.le (fun k t => ((h k).Y_adapted t).mono (ℱ.le t) le_rfl)
    fun k => (h k).Y_rightCont).trans_lt (ENNReal.sum_lt_top.mpr fun k _ =>
      (h k).lintegral_biSup_sq_lt_top 𝒲 hℱ0 hnull hT)

/-- The `𝕊`-size of a tuple whose forward coordinates solve linear forward equations and whose
backward coordinates solve linear backward equations is finite. -/
theorem supSize_lt_top_of_linear {x₀ : Fin n → Ω → ℝ} {b : Fin n → Ω → ℝ → ℝ}
    {x : Fin n → ℝ → Ω → ℝ} {σ : Fin n → ℝ → Ω → Fin d → ℝ} {γ' : Fin n → ℝ → Ω → E → ℝ}
    {ξ : Fin m → Ω → ℝ} {φ : Fin m → Ω → ℝ → ℝ} {y : Fin m → ℝ → Ω → ℝ}
    {z : Fin m → ℝ → Ω → Fin d → ℝ} {u : Fin m → ℝ → Ω → E → ℝ}
    (hx : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (x₀ i) (b i) (x i) (σ i) (γ' i))
    (hy : ∀ k, LinearBSDEJ D ℱ hℱW hℱN T (ξ k) (φ k) (y k) (z k) (u k))
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    supSize P ν T x y (fun k t ω j => z k t ω j) (fun k t ω e => u k t ω e) < ⊤ := by
  unfold supSize
  refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨lintegral_biSup_esq_lt_top_of_linearFSDEJ hx 𝒲 hℱ0 hnull hT,
      lintegral_biSup_esq_lt_top_of_linearBSDEJ hy 𝒲 hℱ0 hnull hT⟩, ?_⟩, ?_⟩
  · exact ENNReal.sum_lt_top.mpr fun k _ => ENNReal.sum_lt_top.mpr fun j _ =>
      lt_top_iff_ne_top.mpr ((hy k).Z_sq j)
  · exact ENNReal.sum_lt_top.mpr fun k _ => lt_top_iff_ne_top.mpr (hy k).U_sq

/-! ### Solutions and their differences -/

variable [MeasurableSpace.CountablyGenerated E]

/-- **`X ∈ S²(0, T; ℝⁿ)`**: the forward component of a solution of the `λ`-forced system (4.1)
satisfies `𝔼 sup_{t ≤ T} |X_t|² < ∞`. -/
theorem SolvesForced.lintegral_biSup_X_lt_top
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P < ⊤ :=
  lintegral_biSup_esq_lt_top_of_linearFSDEJ h.fwd 𝒲 hℱ0 hnull hT

/-- **`Y ∈ S²(0, T; ℝᵐ)`**: the backward component of a solution of the `λ`-forced system (4.1)
satisfies `𝔼 sup_{t ≤ T} |Y_t|² < ∞`. -/
theorem SolvesForced.lintegral_biSup_Y_lt_top
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y k t ω)) ∂P < ⊤ :=
  lintegral_biSup_esq_lt_top_of_linearBSDEJ h.bwd 𝒲 hℱ0 hnull hT

/-- **The difference of two solutions has finite `𝕊`-norm**: for solutions `Θ¹, Θ²` of the
forced system (4.1) at parameters `λ₁, λ₂`, with coefficients `C¹, C²`, initial data
`ξ₀¹, ξ₀²` and forcings `q¹, q²`, `δΘ = Θ¹ − Θ²` satisfies
`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ_t|²_F + ‖δU_t‖²_{L²(ν)}) dt < ∞`. -/
theorem SolvesForced.supSize_sub_lt_top
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam₁ C₁ ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam₂ C₂ ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
      (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤ :=
  supSize_lt_top_of_linear (fun i => (h₁.fwd i).sub (h₂.fwd i) hT.le)
    (fun k => (h₁.bwd k).sub (h₂.bwd k)) 𝒲 hℱ0 hnull hT

end Dissertation.WellPosedness.System
