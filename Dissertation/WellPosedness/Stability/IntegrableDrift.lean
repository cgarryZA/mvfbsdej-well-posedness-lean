/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.Sub

/-!
# The linear equations with jumps with an integrable drift

The drift integral `∫_0^t b_s ds` of the linear forward equation

`X_t = ξ₀ + ∫_0^t b_s ds + ∫_0^t σ_s dW_s + ∫_0^t ∫_E γ_s(e) Ñ(ds, de)`

is a pathwise Lebesgue integral: it needs only that almost every path of `b` be integrable on
`[0, T]`. The two stochastic integrals are the `L²` ones, so they need `σ` and `γ` of finite energy
on `[0, T]`. `LinearFSDEJInt` records the forward equation with these hypotheses: it is
`LinearFSDEJ` with the finite energy of the drift replaced by almost sure integrability of its
paths on `[0, T]`, and with no integrability condition on the initial value. `LinearBSDEJInt` is
`LinearBSDEJ` with the same change for its drift and no integrability condition on its terminal
value.

The equations stay linear in their data. The difference of two solutions solves the equation with
the differenced data, and when that difference has a drift of finite energy and a square-integrable
initial (respectively terminal) value, it solves the equation of `LinearFSDEJ` (respectively
`LinearBSDEJ`). For the forward equation the initial difference is square integrable as soon as the
difference at the horizon and the drift difference are, by the equation at `T`.

## Main definitions

* `LinearFSDEJInt` — the linear forward equation with an almost surely integrable drift.
* `LinearBSDEJInt` — the linear backward equation with an almost surely integrable drift.

## Main statements

* `LinearBSDEJ.toInt` — a drift of finite energy is almost surely integrable.
* `LinearFSDEJInt.linComb`, `LinearFSDEJInt.sub` — linear combinations and differences of forward
  solutions, given a drift of finite energy and a square-integrable initial value.
* `LinearFSDEJInt.memLp_initial_sub` — the initial difference is square integrable when the drift
  difference and the difference at the horizon are.
* `LinearBSDEJInt.linComb`, `LinearBSDEJInt.sub` — the same for backward solutions, given a
  square-integrable terminal value.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc Dissertation.WellPosedness.BrownianPoisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- `X` solves the linear forward equation with jumps

`X_t = ξ₀ + ∫_0^t b_s ds + ∫_0^t σ_s dW_s + ∫_0^t ∫_E γ_s(e) Ñ(ds, de)`

driven by `D` over the filtration `ℱ`, almost surely at each `t ∈ [0, T]`, with the two
stochastic integrals the canonical ones for `ℱ`; `σ` and `γ` are progressive, of finite energy on
`[0, T]` and vanish off it, `b` is progressive, vanishes off `[0, T]` and almost every path of `b`
is integrable on `[0, T]`, and `X` is adapted with right-continuous paths. -/
structure LinearFSDEJInt (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ)
    (T : ℝ) (ξ₀ : Ω → ℝ) (b : Ω → ℝ → ℝ)
    (X : ℝ → Ω → ℝ) (σ : ℝ → Ω → (Fin d → ℝ)) (γ : ℝ → Ω → E → ℝ) : Prop where
  /-- Each coordinate of `σ` is jointly measurable. -/
  σ_meas : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ s ω j)
  /-- Each coordinate of `σ` is progressively measurable. -/
  σ_prog : ∀ j : Fin d, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => σ s ω j
  /-- `σ` vanishes off the horizon. -/
  σ_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → σ s ω = 0
  /-- Each coordinate of `σ` has finite energy on the horizon. -/
  σ_sq : ∀ j : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => σ s ω j) ≠ ⊤
  /-- `γ` is jointly measurable in the sample point, the time and the mark. -/
  γ_meas : Measurable fun p : Ω × ℝ × E => γ p.2.1 p.1 p.2.2
  /-- `γ` is marked progressively measurable. -/
  γ_prog : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => γ s ω e
  /-- `γ` vanishes off the horizon. -/
  γ_vanish : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → γ s ω e = 0
  /-- `γ` has finite marked energy on the horizon. -/
  γ_sq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => γ s ω e) ≠ ⊤
  /-- The drift is jointly measurable. -/
  b_meas : Measurable (Function.uncurry b)
  /-- The drift is progressively measurable. -/
  b_prog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ b
  /-- The drift vanishes off the horizon. -/
  b_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0
  /-- Almost every path of the drift is integrable on the horizon. -/
  b_int : ∀ᵐ ω ∂P, IntegrableOn (b ω) (Set.Icc (0 : ℝ) T)
  /-- `X` is adapted. -/
  X_adapted : MeasureTheory.Adapted ℱ X
  /-- Every path of `X` is right-continuous. -/
  X_rightCont : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
  /-- The forward equation, almost surely at each time of the horizon. -/
  eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
    X t ω = ξ₀ ω + (∫ s in Set.Icc (0 : ℝ) t, b ω s)
      + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW σ
          σ_meas σ_prog (sq_int_global_of_vanishing σ_vanish σ_sq) t ω
      + LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
          (fun ω' s e => γ s ω' e) γ_meas γ_prog (marked_sq_int_global_of_vanishing γ_vanish γ_sq)
          t ω

/-- `(Y, Z, U)` solves the linear backward equation with jumps

`Y_t = ξ + ∫_t^T φ_s ds − ∫_t^T Z_s dW_s − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`

driven by `D` over the filtration `ℱ`, almost surely at each `t ∈ [0, T]`, with the two
stochastic integrals the canonical ones for `ℱ`; `Z` and `U` are progressive, of finite energy on
`[0, T]` and vanish off it, `φ` is progressive, vanishes off `[0, T]` and almost every path of `φ`
is integrable on `[0, T]`, and `Y` is adapted with right-continuous paths. -/
structure LinearBSDEJInt (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ)
    (T : ℝ) (ξ : Ω → ℝ) (φ : Ω → ℝ → ℝ)
    (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) : Prop where
  /-- Each coordinate of `Z` is jointly measurable. -/
  Z_meas : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i)
  /-- Each coordinate of `Z` is progressively measurable. -/
  Z_prog : ∀ i : Fin d, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i
  /-- `Z` vanishes off the horizon. -/
  Z_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0
  /-- Each coordinate of `Z` has finite energy on the horizon. -/
  Z_sq : ∀ i : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤
  /-- `U` is jointly measurable in the sample point, the time and the mark. -/
  U_meas : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2
  /-- `U` is marked progressively measurable. -/
  U_prog : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U s ω e
  /-- `U` vanishes off the horizon. -/
  U_vanish : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0
  /-- `U` has finite marked energy on the horizon. -/
  U_sq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤
  /-- The drift is jointly measurable. -/
  φ_meas : Measurable (Function.uncurry φ)
  /-- The drift is progressively measurable. -/
  φ_prog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ φ
  /-- The drift vanishes off the horizon. -/
  φ_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ ω s = 0
  /-- Almost every path of the drift is integrable on the horizon. -/
  φ_int : ∀ᵐ ω ∂P, IntegrableOn (φ ω) (Set.Icc (0 : ℝ) T)
  /-- `Y` is adapted. -/
  Y_adapted : MeasureTheory.Adapted ℱ Y
  /-- Every path of `Y` is right-continuous. -/
  Y_rightCont : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω))
  /-- The backward equation, almost surely at each time of the horizon. -/
  eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
    Y t ω = ξ ω + (∫ s in Set.Icc t T, φ ω s)
      - (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z
            Z_meas Z_prog (sq_int_global_of_vanishing Z_vanish Z_sq) T ω
          - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z
            Z_meas Z_prog (sq_int_global_of_vanishing Z_vanish Z_sq) t ω)
      - (LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
            (fun ω' s e => U s ω' e) U_meas U_prog (marked_sq_int_global_of_vanishing U_vanish U_sq)
            T ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
            (fun ω' s e => U s ω' e) U_meas U_prog (marked_sq_int_global_of_vanishing U_vanish U_sq)
            t ω)

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

/-! ### From finite energy to integrable paths -/

/-- **A solution of the linear backward equation with a drift of finite energy has an almost
surely integrable drift.** -/
theorem _root_.Dissertation.WellPosedness.BrownianPoisson.LinearBSDEJ.toInt {ξ : Ω → ℝ}
    {φ : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) : LinearBSDEJInt D ℱ hℱW hℱN T ξ φ Y Z U where
  Z_meas := h.Z_meas
  Z_prog := h.Z_prog
  Z_vanish := h.Z_vanish
  Z_sq := h.Z_sq
  U_meas := h.U_meas
  U_prog := h.U_prog
  U_vanish := h.U_vanish
  U_sq := h.U_sq
  φ_meas := h.φ_meas
  φ_prog := h.φ_prog
  φ_vanish := h.φ_vanish
  φ_int := ae_mem_integrablePaths h.φ_meas h.φ_sq
  Y_adapted := h.Y_adapted
  Y_rightCont := h.Y_rightCont
  eqn := h.eqn

/-! ### The forward equation -/

namespace LinearFSDEJInt

variable {ξ₀ ξ₀₁ ξ₀₂ : Ω → ℝ} {b b₁ b₂ : Ω → ℝ → ℝ} {X X₁ X₂ : ℝ → Ω → ℝ}
  {σ σ₁ σ₂ : ℝ → Ω → (Fin d → ℝ)} {γ γ₁ γ₂ : ℝ → Ω → E → ℝ}

/-- A solution of the linear forward equation is jointly measurable in time and sample point. -/
theorem measurable_uncurry (h : LinearFSDEJInt D ℱ hℱW hℱN T ξ₀ b X σ γ) :
    Measurable (Function.uncurry X) :=
  Probability.measurable_uncurry_of_rightContinuous h.X_adapted h.X_rightCont

/-- **Linear combinations of solutions of the linear forward equation**: for real `a, c`,
`aX¹ + cX²` solves the linear forward equation of `LinearFSDEJ` with initial value
`aξ₀¹ + cξ₀²`, drift `ab¹ + cb²`, diffusion vector `aσ¹ + cσ²` and jump integrand `aγ¹ + cγ²`,
when that drift has finite energy on `[0, T]` and that initial value is square integrable. -/
theorem linComb (h₁ : LinearFSDEJInt D ℱ hℱW hℱN T ξ₀₁ b₁ X₁ σ₁ γ₁)
    (h₂ : LinearFSDEJInt D ℱ hℱW hℱN T ξ₀₂ b₂ X₂ σ₂ γ₂) (a c : ℝ)
    (hb : Brownian.Ito.energy P T (fun ω s => a * b₁ ω s + c * b₂ ω s) ≠ ⊤)
    (hξ : MemLp (fun ω => a * ξ₀₁ ω + c * ξ₀₂ ω) 2 P) :
    LinearFSDEJ D ℱ hℱW hℱN T (fun ω => a * ξ₀₁ ω + c * ξ₀₂ ω)
      (fun ω s => a * b₁ ω s + c * b₂ ω s) (fun t ω => a * X₁ t ω + c * X₂ t ω)
      (fun s ω j => a * σ₁ s ω j + c * σ₂ s ω j) (fun s ω e => a * γ₁ s ω e + c * γ₂ s ω e) := by
  have hσm : ∀ j : Fin d,
      Measurable (Function.uncurry fun ω s => a * σ₁ s ω j + c * σ₂ s ω j) := fun j =>
    ((h₁.σ_meas j).const_mul a).add ((h₂.σ_meas j).const_mul c)
  have hσp : ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ fun ω s => a * σ₁ s ω j + c * σ₂ s ω j := fun j =>
    ((continuous_const_mul a).comp_progressivelyMeasurable (mul_zero a) (h₁.σ_prog j)).add
      ((continuous_const_mul c).comp_progressivelyMeasurable (mul_zero c) (h₂.σ_prog j))
  have hσv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → (fun j => a * σ₁ s ω j + c * σ₂ s ω j) = 0 :=
    fun ω s hs => by
      funext j
      simp [h₁.σ_vanish ω s hs, h₂.σ_vanish ω s hs]
  have hσq : ∀ j : Fin d, Brownian.Ito.energy P T
      (fun ω s => a * σ₁ s ω j + c * σ₂ s ω j) ≠ ⊤ := fun j =>
    Brownian.Ito.energy_add_ne_top ((h₁.σ_meas j).const_mul a) ((h₂.σ_meas j).const_mul c)
      (Brownian.Ito.energy_const_mul_ne_top (h₁.σ_meas j) (h₁.σ_sq j) a)
      (Brownian.Ito.energy_const_mul_ne_top (h₂.σ_meas j) (h₂.σ_sq j) c)
  have hγm : Measurable fun p : Ω × ℝ × E => a * γ₁ p.2.1 p.1 p.2.2 + c * γ₂ p.2.1 p.1 p.2.2 :=
    (h₁.γ_meas.const_mul a).add (h₂.γ_meas.const_mul c)
  have hγp : Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => a * γ₁ s ω e + c * γ₂ s ω e :=
    Poisson.Compensated.markedProgressivelyMeasurable_add
      (Poisson.Compensated.markedProgressivelyMeasurable_const_mul h₁.γ_prog a)
      (Poisson.Compensated.markedProgressivelyMeasurable_const_mul h₂.γ_prog c)
  have hγv : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → a * γ₁ s ω e + c * γ₂ s ω e = 0 :=
    fun ω s e hs => by simp [h₁.γ_vanish ω s e hs, h₂.γ_vanish ω s e hs]
  have hγq : Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => a * γ₁ s ω e + c * γ₂ s ω e) ≠ ⊤ :=
    Poisson.Compensated.markedEnergy_add_ne_top (h₁.γ_meas.const_mul a)
      (h₂.γ_meas.const_mul c)
      (Poisson.Compensated.markedEnergy_const_mul_ne_top h₁.γ_meas h₁.γ_sq a)
      (Poisson.Compensated.markedEnergy_const_mul_ne_top h₂.γ_meas h₂.γ_sq c)
  refine
    { σ_meas := hσm
      σ_prog := hσp
      σ_vanish := hσv
      σ_sq := hσq
      γ_meas := hγm
      γ_prog := hγp
      γ_vanish := hγv
      γ_sq := hγq
      b_meas := (h₁.b_meas.const_mul a).add (h₂.b_meas.const_mul c)
      b_prog := ((continuous_const_mul a).comp_progressivelyMeasurable (mul_zero a)
        h₁.b_prog).add ((continuous_const_mul c).comp_progressivelyMeasurable (mul_zero c)
        h₂.b_prog)
      b_vanish := fun ω s hs => by simp [h₁.b_vanish ω s hs, h₂.b_vanish ω s hs]
      b_sq := hb
      ξ₀_sq := hξ
      X_adapted := fun t => ((h₁.X_adapted t).const_mul a).add ((h₂.X_adapted t).const_mul c)
      X_rightCont := fun ω t =>
        ((h₁.X_rightCont ω t).const_mul a).add ((h₂.X_rightCont ω t).const_mul c)
      eqn := ?_ }
  intro t ht
  have hW := multidimStochasticIntegral_linComb_ae D.W hℱW a c h₁.σ_meas h₂.σ_meas
    h₁.σ_prog h₂.σ_prog (sq_int_global_of_vanishing h₁.σ_vanish h₁.σ_sq)
    (sq_int_global_of_vanishing h₂.σ_vanish h₂.σ_sq) hσm hσp
    (sq_int_global_of_vanishing hσv hσq) t
  have hN := compensatedIntegral_linComb_ae D.N hℱN (φ₁ := fun ω s e => γ₁ s ω e)
    (φ₂ := fun ω s e => γ₂ s ω e) a c h₁.γ_meas h₂.γ_meas h₁.γ_prog h₂.γ_prog
    (marked_sq_int_global_of_vanishing h₁.γ_vanish h₁.γ_sq)
    (marked_sq_int_global_of_vanishing h₂.γ_vanish h₂.γ_sq) hγm hγp
    (marked_sq_int_global_of_vanishing hγv hγq) t
  filter_upwards [h₁.eqn t ht, h₂.eqn t ht, hW, hN,
    ae_setIntegral_linComb_of_integrableOn a c h₁.b_int h₂.b_int
      (Set.Icc_subset_Icc le_rfl ht.2)] with ω e₁ e₂ eW eN eb
  rw [e₁, e₂, eb, eW, eN]
  ring

/-- **The difference of two solutions of the linear forward equation** solves the linear forward
equation of `LinearFSDEJ` with the differenced initial value, drift, diffusion vector and jump
integrand, when the drift difference has finite energy on `[0, T]` and the initial difference is
square integrable. -/
theorem sub (h₁ : LinearFSDEJInt D ℱ hℱW hℱN T ξ₀₁ b₁ X₁ σ₁ γ₁)
    (h₂ : LinearFSDEJInt D ℱ hℱW hℱN T ξ₀₂ b₂ X₂ σ₂ γ₂)
    (hb : Brownian.Ito.energy P T (fun ω s => b₁ ω s - b₂ ω s) ≠ ⊤)
    (hξ : MemLp (fun ω => ξ₀₁ ω - ξ₀₂ ω) 2 P) :
    LinearFSDEJ D ℱ hℱW hℱN T (fun ω => ξ₀₁ ω - ξ₀₂ ω) (fun ω s => b₁ ω s - b₂ ω s)
      (fun t ω => X₁ t ω - X₂ t ω) (fun s ω j => σ₁ s ω j - σ₂ s ω j)
      (fun s ω e => γ₁ s ω e - γ₂ s ω e) := by
  simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg] using
    h₁.linComb h₂ 1 (-1) (by simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg] using hb)
      (by simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg] using hξ)

/-- **The initial difference of two solutions of the linear forward equation is square
integrable** when the drift difference has finite energy on `[0, T]` and the difference at the
horizon is square integrable: by the equation at `T`,
`δξ₀ = δX_T − ∫_0^T δb_s ds − ∫_0^T δσ_s dW_s − ∫_0^T ∫_E δγ_s(e) Ñ(ds, de)`. -/
theorem memLp_initial_sub (h₁ : LinearFSDEJInt D ℱ hℱW hℱN T ξ₀₁ b₁ X₁ σ₁ γ₁)
    (h₂ : LinearFSDEJInt D ℱ hℱW hℱN T ξ₀₂ b₂ X₂ σ₂ γ₂) (hT : 0 ≤ T)
    (hb : Brownian.Ito.energy P T (fun ω s => b₁ ω s - b₂ ω s) ≠ ⊤)
    (hX : MemLp (fun ω => X₁ T ω - X₂ T ω) 2 P) :
    MemLp (fun ω => ξ₀₁ ω - ξ₀₂ ω) 2 P := by
  have hA : MemLp (fun ω => ∫ s in Set.Icc (0 : ℝ) T, (b₁ ω s - b₂ ω s)) 2 P :=
    Ito.SecondMoment.memLp_two_setIntegral (h₁.b_meas.sub h₂.b_meas) hT hb.lt_top
  have hW : ∀ {σ : ℝ → Ω → (Fin d → ℝ)}
      (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ s ω j))
      (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => σ s ω j)
      (hq : ∀ (j : Fin d) (T' : ℝ), 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      MemLp (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW σ hm hp hq
        T) 2 P := fun hm hp hq =>
    memLp_finsetSum Finset.univ fun i _ =>
      Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W i) ℱ (hℱW i) _ (hm i) (hp i) (hq i) T
  have hN : ∀ {γ : ℝ → Ω → E → ℝ} (hm : Measurable fun p : Ω × ℝ × E => γ p.2.1 p.1 p.2.2)
      (hp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => γ s ω e)
      (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖γ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
      MemLp (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => γ s ω' e) hm hp hq
        T) 2 P := fun hm hp hq =>
    Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN _ hm hp hq T
  refine ((((hX.sub hA).sub ((hW h₁.σ_meas h₁.σ_prog
    (sq_int_global_of_vanishing h₁.σ_vanish h₁.σ_sq)).sub (hW h₂.σ_meas h₂.σ_prog
    (sq_int_global_of_vanishing h₂.σ_vanish h₂.σ_sq)))).sub ((hN h₁.γ_meas h₁.γ_prog
    (marked_sq_int_global_of_vanishing h₁.γ_vanish h₁.γ_sq)).sub (hN h₂.γ_meas h₂.γ_prog
    (marked_sq_int_global_of_vanishing h₂.γ_vanish h₂.γ_sq))))).ae_eq ?_
  have hI := ae_setIntegral_linComb_of_integrableOn 1 (-1) h₁.b_int h₂.b_int
    (subset_refl (Set.Icc (0 : ℝ) T))
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hI
  filter_upwards [h₁.eqn T ⟨hT, le_rfl⟩, h₂.eqn T ⟨hT, le_rfl⟩, hI] with ω e₁ e₂ eI
  simp only [Pi.sub_apply]
  rw [eI]
  linarith

end LinearFSDEJInt

/-! ### The backward equation -/

namespace LinearBSDEJInt

variable {ξ ξ₁ ξ₂ : Ω → ℝ} {φ φ₁ φ₂ : Ω → ℝ → ℝ} {Y Y₁ Y₂ : ℝ → Ω → ℝ}
  {Z Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U U₁ U₂ : ℝ → Ω → E → ℝ}

/-- A solution of the linear backward equation is jointly measurable in time and sample point. -/
theorem measurable_uncurry (h : LinearBSDEJInt D ℱ hℱW hℱN T ξ φ Y Z U) :
    Measurable (Function.uncurry Y) :=
  Probability.measurable_uncurry_of_rightContinuous h.Y_adapted h.Y_rightCont

/-- The value of a solution of the linear backward equation at the horizon is its terminal value,
almost surely. -/
theorem ae_eq_terminal (h : LinearBSDEJInt D ℱ hℱW hℱN T ξ φ Y Z U) (hT : 0 ≤ T) :
    Y T =ᵐ[P] ξ := by
  filter_upwards [h.eqn T ⟨hT, le_rfl⟩] with ω hω
  rw [hω, integral_Icc_eq_integral_Ioc, Set.Ioc_self, setIntegral_empty]
  ring

/-- **Linear combinations of solutions of the linear backward equation**: for real `a, c`,
`(aY¹ + cY², aZ¹ + cZ², aU¹ + cU²)` solves the linear backward equation of `LinearBSDEJ` with
terminal value `aξ¹ + cξ²` and drift `aφ¹ + cφ²`, when that drift has finite energy on `[0, T]`
and that terminal value is square integrable. -/
theorem linComb (h₁ : LinearBSDEJInt D ℱ hℱW hℱN T ξ₁ φ₁ Y₁ Z₁ U₁)
    (h₂ : LinearBSDEJInt D ℱ hℱW hℱN T ξ₂ φ₂ Y₂ Z₂ U₂) (a c : ℝ)
    (hφ : Brownian.Ito.energy P T (fun ω s => a * φ₁ ω s + c * φ₂ ω s) ≠ ⊤)
    (hξ : MemLp (fun ω => a * ξ₁ ω + c * ξ₂ ω) 2 P) :
    LinearBSDEJ D ℱ hℱW hℱN T (fun ω => a * ξ₁ ω + c * ξ₂ ω)
      (fun ω s => a * φ₁ ω s + c * φ₂ ω s) (fun t ω => a * Y₁ t ω + c * Y₂ t ω)
      (fun s ω j => a * Z₁ s ω j + c * Z₂ s ω j) (fun s ω e => a * U₁ s ω e + c * U₂ s ω e) := by
  have hZm : ∀ j : Fin d,
      Measurable (Function.uncurry fun ω s => a * Z₁ s ω j + c * Z₂ s ω j) := fun j =>
    ((h₁.Z_meas j).const_mul a).add ((h₂.Z_meas j).const_mul c)
  have hZp : ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ fun ω s => a * Z₁ s ω j + c * Z₂ s ω j := fun j =>
    ((continuous_const_mul a).comp_progressivelyMeasurable (mul_zero a) (h₁.Z_prog j)).add
      ((continuous_const_mul c).comp_progressivelyMeasurable (mul_zero c) (h₂.Z_prog j))
  have hZv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → (fun j => a * Z₁ s ω j + c * Z₂ s ω j) = 0 :=
    fun ω s hs => by
      funext j
      simp [h₁.Z_vanish ω s hs, h₂.Z_vanish ω s hs]
  have hZq : ∀ j : Fin d, Brownian.Ito.energy P T
      (fun ω s => a * Z₁ s ω j + c * Z₂ s ω j) ≠ ⊤ := fun j =>
    Brownian.Ito.energy_add_ne_top ((h₁.Z_meas j).const_mul a) ((h₂.Z_meas j).const_mul c)
      (Brownian.Ito.energy_const_mul_ne_top (h₁.Z_meas j) (h₁.Z_sq j) a)
      (Brownian.Ito.energy_const_mul_ne_top (h₂.Z_meas j) (h₂.Z_sq j) c)
  have hUm : Measurable fun p : Ω × ℝ × E => a * U₁ p.2.1 p.1 p.2.2 + c * U₂ p.2.1 p.1 p.2.2 :=
    (h₁.U_meas.const_mul a).add (h₂.U_meas.const_mul c)
  have hUp : Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => a * U₁ s ω e + c * U₂ s ω e :=
    Poisson.Compensated.markedProgressivelyMeasurable_add
      (Poisson.Compensated.markedProgressivelyMeasurable_const_mul h₁.U_prog a)
      (Poisson.Compensated.markedProgressivelyMeasurable_const_mul h₂.U_prog c)
  have hUv : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → a * U₁ s ω e + c * U₂ s ω e = 0 :=
    fun ω s e hs => by simp [h₁.U_vanish ω s e hs, h₂.U_vanish ω s e hs]
  have hUq : Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => a * U₁ s ω e + c * U₂ s ω e) ≠ ⊤ :=
    Poisson.Compensated.markedEnergy_add_ne_top (h₁.U_meas.const_mul a)
      (h₂.U_meas.const_mul c)
      (Poisson.Compensated.markedEnergy_const_mul_ne_top h₁.U_meas h₁.U_sq a)
      (Poisson.Compensated.markedEnergy_const_mul_ne_top h₂.U_meas h₂.U_sq c)
  refine
    { Z_meas := hZm
      Z_prog := hZp
      Z_vanish := hZv
      Z_sq := hZq
      U_meas := hUm
      U_prog := hUp
      U_vanish := hUv
      U_sq := hUq
      φ_meas := (h₁.φ_meas.const_mul a).add (h₂.φ_meas.const_mul c)
      φ_prog := ((continuous_const_mul a).comp_progressivelyMeasurable (mul_zero a)
        h₁.φ_prog).add ((continuous_const_mul c).comp_progressivelyMeasurable (mul_zero c)
        h₂.φ_prog)
      φ_vanish := fun ω s hs => by simp [h₁.φ_vanish ω s hs, h₂.φ_vanish ω s hs]
      φ_sq := hφ
      ξ_sq := hξ
      Y_adapted := fun t => ((h₁.Y_adapted t).const_mul a).add ((h₂.Y_adapted t).const_mul c)
      Y_rightCont := fun ω t =>
        ((h₁.Y_rightCont ω t).const_mul a).add ((h₂.Y_rightCont ω t).const_mul c)
      eqn := ?_ }
  intro t ht
  have hW := fun r => multidimStochasticIntegral_linComb_ae D.W hℱW a c h₁.Z_meas h₂.Z_meas
    h₁.Z_prog h₂.Z_prog (sq_int_global_of_vanishing h₁.Z_vanish h₁.Z_sq)
    (sq_int_global_of_vanishing h₂.Z_vanish h₂.Z_sq) hZm hZp
    (sq_int_global_of_vanishing hZv hZq) r
  have hN := fun r => compensatedIntegral_linComb_ae D.N hℱN (φ₁ := fun ω s e => U₁ s ω e)
    (φ₂ := fun ω s e => U₂ s ω e) a c h₁.U_meas h₂.U_meas h₁.U_prog h₂.U_prog
    (marked_sq_int_global_of_vanishing h₁.U_vanish h₁.U_sq)
    (marked_sq_int_global_of_vanishing h₂.U_vanish h₂.U_sq) hUm hUp
    (marked_sq_int_global_of_vanishing hUv hUq) r
  filter_upwards [h₁.eqn t ht, h₂.eqn t ht, hW T, hW t, hN T, hN t,
    ae_setIntegral_linComb_of_integrableOn a c h₁.φ_int h₂.φ_int
      (Set.Icc_subset_Icc ht.1 le_rfl)] with ω e₁ e₂ eWT eWt eNT eNt eφ
  rw [e₁, e₂, eφ, eWT, eWt, eNT, eNt]
  ring

/-- **The difference of two solutions of the linear backward equation** solves the linear
backward equation of `LinearBSDEJ` with the differenced terminal value and drift, when the drift
difference has finite energy on `[0, T]` and the terminal difference is square integrable. -/
theorem sub (h₁ : LinearBSDEJInt D ℱ hℱW hℱN T ξ₁ φ₁ Y₁ Z₁ U₁)
    (h₂ : LinearBSDEJInt D ℱ hℱW hℱN T ξ₂ φ₂ Y₂ Z₂ U₂)
    (hφ : Brownian.Ito.energy P T (fun ω s => φ₁ ω s - φ₂ ω s) ≠ ⊤)
    (hξ : MemLp (fun ω => ξ₁ ω - ξ₂ ω) 2 P) :
    LinearBSDEJ D ℱ hℱW hℱN T (fun ω => ξ₁ ω - ξ₂ ω) (fun ω s => φ₁ ω s - φ₂ ω s)
      (fun t ω => Y₁ t ω - Y₂ t ω) (fun s ω j => Z₁ s ω j - Z₂ s ω j)
      (fun s ω e => U₁ s ω e - U₂ s ω e) := by
  simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg] using
    h₁.linComb h₂ 1 (-1) (by simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg] using hφ)
      (by simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg] using hξ)

end LinearBSDEJInt

end Dissertation.WellPosedness.Stability
