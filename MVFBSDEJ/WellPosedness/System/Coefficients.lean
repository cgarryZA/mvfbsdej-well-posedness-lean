/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Law.Assumptions
import MVFBSDEJ.WellPosedness.BrownianPoisson.Hypotheses
import MVFBSDEJ.WellPosedness.System.Operators
import MVFBSDEJ.WellPosedness.System.TupleLaw

/-!
# The coefficients of the well-posedness paper and their diagonal assumptions

The system (1.1) of the well-posedness paper has deterministic coefficients

`b : [0, T] × H × P₂(H) → ℝⁿ`, `σ : [0, T] × H × P₂(H) → ℝ^{n×d}`,
`h : [0, T] × H × P₂(H) → L²(ν; ℝⁿ)`, `f : [0, T] × H × P₂(H) → ℝᵐ`, `g : ℝⁿ × P₂(ℝⁿ) → ℝᵐ`

on the tuple space `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)`. `Coeffs` records them, with `ℝ^{n×d}`
the Euclidean space on the pairs `(i, j)`, whose norm is the Frobenius norm, and with time ranging
over `ℝ`, of which only `[0, T]` enters. The joint Borel measurability of the coefficients is not
part of `Coeffs`: it serves only to make the coefficient processes along a solution measurable,
(2.5), and that measurability is a condition of the solution predicate instead.

Assumptions 2.3 and 2.5 are imposed along the diagonal `D_t = {(Θ, Law Θ) : Θ ∈ L²(Ω, ℱ_t; H)}`
of Definition 2.1. Over a probability space with a filtration `ℱ`, the diagonal inputs at time `t`
are the pairs `(Θ, lawP2 P Θ)` with `Θ : Ω → H` strongly `ℱ_t`-measurable and square integrable.
For two of them, `δψ = ψ(t, Θ, μ) − ψ(t, Θ', μ')`, and the four predicates are:

* `DiagonalLipschitz`, Assumption 2.3, interior: for almost every `t ∈ [0, T]`, almost surely,
  `|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ L (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + W₂(μ, μ'))`;
* `TerminalLipschitz`, (2.6): for `X_T, X'_T ∈ L²(Ω, ℱ_T; ℝⁿ)`, almost surely,
  `|δg_T| ≤ L (|X_T − X'_T| + W₂(ρ, ρ'))`, with `ρ, ρ'` the laws of `X_T, X'_T`;
* `DiagonalMonotone`, Assumption 2.5, interior: (2.7) for almost every `t ∈ [0, T]`;
* `TerminalMonotone`, Assumption 2.5, terminal: `𝔼⟨δg_T, G δX_T⟩ ≥ α 𝔼|G δX_T|²`.

`G` acts through `GX`, `GZ`, `GU`, and `W₂` is `w2P` on the laws of finite second moment. `H`
carries the maximum of its four channel norms, which lies between one half of the paper's Hilbert
norm and that norm; so `W₂` here lies between one half of the paper's `W₂` and it, and
`DiagonalLipschitz` at `L` implies the paper's interior bound at `L`, which in turn implies
`DiagonalLipschitz` at `2L`. The pointwise conditions `LipschitzCoefficientsP2` and
`LipschitzTerminalP2`, imposed at every pair of points and laws, imply the diagonal ones.

A forcing of the `λ`-system (4.1) is `q = (q^b, q^σ, q^h, q^f, q^g_T)` with `q^b, q^σ, q^f`
progressively measurable, `q^h` measurable in the predictable-times-mark sense, each square
integrable over `Ω × [0, T]` (and `ν`), and `q^g_T ∈ L²(Ω, ℱ_T; ℝᵐ)`. `Forcing` records this in
coordinates, with two conventions: each process is represented by its extension by `0` off `[0, T]`,
as the integrands of `BrownianPoisson.LinearBSDEJ` are, and `q^h` is marked progressively measurable
rather than predictable.

## Main definitions

* `Coeffs` — the coefficients `(b, σ, h, f, g)`.
* `diagDiff` — the channel differences of two diagonal inputs.
* `DiagonalLipschitz`, `TerminalLipschitz` — Assumption 2.3 along the diagonal.
* `DiagonalMonotone`, `TerminalMonotone` — Assumption 2.5 along the diagonal.
* `Forcing` — a square-integrable forcing of (4.1).

## Main statements

* `diagonalLipschitz_of_lipschitzCoefficientsP2`, `terminalLipschitz_of_lipschitzTerminalP2` —
  the pointwise Lipschitz conditions imply the diagonal ones.
* `Forcing.zero` — the zero forcing.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

variable {E : Type*} [MeasurableSpace E]

/-- The coefficients of the system (1.1) on the tuple space `H = TupleH ν n m d`: the drift `b`,
the diffusion `σ` with values in `ℝ^{n×d}`, the jump coefficient `h` with values in
`L²(ν; ℝⁿ)` and the backward driver `f`, functions of time, a point of `H` and a law of finite
second moment on `H`; and the terminal function `g` of a point of `ℝⁿ` and a law on `ℝⁿ`. -/
structure Coeffs (ν : Measure E) (n m d : ℕ) where
  /-- The drift `b(t, θ, μ) ∈ ℝⁿ`. -/
  b : ℝ → TupleH ν n m d → P2 (TupleH ν n m d) → EuclideanSpace ℝ (Fin n)
  /-- The diffusion `σ(t, θ, μ) ∈ ℝ^{n×d}`. -/
  σ : ℝ → TupleH ν n m d → P2 (TupleH ν n m d) → EuclideanSpace ℝ (Fin n × Fin d)
  /-- The jump coefficient `h(t, θ, ·, μ) ∈ L²(ν; ℝⁿ)`. -/
  h : ℝ → TupleH ν n m d → P2 (TupleH ν n m d) → Lp (EuclideanSpace ℝ (Fin n)) 2 ν
  /-- The backward driver `f(t, θ, μ) ∈ ℝᵐ`. -/
  f : ℝ → TupleH ν n m d → P2 (TupleH ν n m d) → EuclideanSpace ℝ (Fin m)
  /-- The terminal function `g(x, ρ) ∈ ℝᵐ`. -/
  g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)

variable {ν : Measure E} {n m d : ℕ}

/-- The channel differences of two inputs `(θ, μ)`, `(θ', μ')` at time `t`: the tuple
differences `δX, δY, δZ, δU` and the coefficient differences
`δψ = ψ(t, θ, μ) − ψ(t, θ', μ')`, `ψ ∈ {b, σ, h, f}`. -/
noncomputable def diagDiff (C : Coeffs ν n m d) (t : ℝ) (θ θ' : TupleH ν n m d)
    (μ μ' : P2 (TupleH ν n m d)) :
    ChannelDiff (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin n × Fin d)) (EuclideanSpace ℝ (Fin m × Fin d))
      (Lp (EuclideanSpace ℝ (Fin n)) 2 ν) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν) where
  δX := θ.1 - θ'.1
  δY := θ.2.1 - θ'.2.1
  δZ := θ.2.2.1 - θ'.2.2.1
  δU := θ.2.2.2 - θ'.2.2.2
  δb := C.b t θ μ - C.b t θ' μ'
  δσ := C.σ t θ μ - C.σ t θ' μ'
  δh := C.h t θ μ - C.h t θ' μ'
  δf := C.f t θ μ - C.f t θ' μ'

section Diagonal

variable {Ω : Type*} [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **Assumption 2.3, interior, along the diagonal**: for almost every `t ∈ [0, T]` and any two
strongly `ℱ_t`-measurable square-integrable tuples `Θ, Θ'` with laws `μ, μ'`, almost surely
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ L (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + W₂(μ, μ'))`. -/
def DiagonalLipschitz (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T L : ℝ) (C : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ Θ Θ' : Ω → TupleH ν n m d,
    StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
    ∀ᵐ ω ∂P, ‖C.b t (Θ ω) (lawP2 P Θ) - C.b t (Θ' ω) (lawP2 P Θ')‖
        + ‖C.σ t (Θ ω) (lawP2 P Θ) - C.σ t (Θ' ω) (lawP2 P Θ')‖
        + ‖C.h t (Θ ω) (lawP2 P Θ) - C.h t (Θ' ω) (lawP2 P Θ')‖
        + ‖C.f t (Θ ω) (lawP2 P Θ) - C.f t (Θ' ω) (lawP2 P Θ')‖
      ≤ L * (tupleNorm (Θ ω - Θ' ω) + w2P (lawP2 P Θ) (lawP2 P Θ'))

/-- **Assumption 2.5, interior, along the diagonal** (2.7): for almost every `t ∈ [0, T]` and any
two strongly `ℱ_t`-measurable square-integrable tuples with laws `μ, μ'`,
`𝔼[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F − ⟨δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)]
  ≤ −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}] − β₂ 𝔼|G δX|²`. -/
def DiagonalMonotone (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (β₁ β₂ : ℝ)
    (C : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ Θ Θ' : Ω → TupleH ν n m d,
    StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
    ∫ ω, interiorPairing (GX G) (GZ G) (GU G ν)
        (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P
      ≤ ∫ ω, dissipation (GX G) (GZ G) (GU G ν) β₁ β₂
        (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P

/-- The pointwise interior Lipschitz condition, at every time, pair of points and pair of laws,
implies the diagonal one. -/
theorem diagonalLipschitz_of_lipschitzCoefficientsP2 {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {P : Measure Ω} [IsProbabilityMeasure P] {T L : ℝ} {C : Coeffs ν n m d}
    (hC : LipschitzCoefficientsP2 L C.b C.σ C.h C.f) : DiagonalLipschitz ℱ P T L C :=
  Eventually.of_forall fun t Θ Θ' _ _ _ _ => Eventually.of_forall fun ω =>
    hC t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')

end Diagonal

section Terminal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Assumption 2.3, terminal (2.6), along the diagonal**: for any two strongly
`ℱ_T`-measurable square-integrable `X_T, X'_T` with laws `ρ, ρ'`, almost surely
`|g(X_T, ρ) − g(X'_T, ρ')| ≤ L (|X_T − X'_T| + W₂(ρ, ρ'))`. -/
def TerminalLipschitz (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T L : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)) :
    Prop :=
  ∀ ξ ξ' : Ω → EuclideanSpace ℝ (Fin n), StronglyMeasurable[ℱ T] ξ →
    StronglyMeasurable[ℱ T] ξ' → MemLp ξ 2 P → MemLp ξ' 2 P →
    ∀ᵐ ω ∂P, ‖g (ξ ω) (lawP2 P ξ) - g (ξ' ω) (lawP2 P ξ')‖
      ≤ L * (‖ξ ω - ξ' ω‖ + w2P (lawP2 P ξ) (lawP2 P ξ'))

/-- **Assumption 2.5, terminal, along the diagonal**: for any two strongly `ℱ_T`-measurable
square-integrable `X_T, X'_T` with laws `ρ, ρ'`,
`α 𝔼|G (X_T − X'_T)|² ≤ 𝔼⟨g(X_T, ρ) − g(X'_T, ρ'), G (X_T − X'_T)⟩`. -/
def TerminalMonotone (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (α : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)) :
    Prop :=
  ∀ ξ ξ' : Ω → EuclideanSpace ℝ (Fin n), StronglyMeasurable[ℱ T] ξ →
    StronglyMeasurable[ℱ T] ξ' → MemLp ξ 2 P → MemLp ξ' 2 P →
    α * ∫ ω, ‖GX G (ξ ω - ξ' ω)‖ ^ 2 ∂P
      ≤ ∫ ω, inner ℝ (g (ξ ω) (lawP2 P ξ) - g (ξ' ω) (lawP2 P ξ')) (GX G (ξ ω - ξ' ω)) ∂P

/-- The pointwise terminal Lipschitz condition, at every pair of points and pair of laws, implies
the diagonal one. -/
theorem terminalLipschitz_of_lipschitzTerminalP2 {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {P : Measure Ω} [IsProbabilityMeasure P] {T L : ℝ}
    {g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)}
    (hg : LipschitzTerminalP2 L g) : TerminalLipschitz ℱ P T L g :=
  fun ξ ξ' _ _ _ _ => Eventually.of_forall fun ω => hg (ξ ω) (ξ' ω) (lawP2 P ξ) (lawP2 P ξ')

end Terminal

/-! ### Forcings -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A forcing of the `λ`-system (4.1)**, in coordinates, over the filtration `ℱ`: `q^b`, `q^σ`
and `q^f` are jointly measurable, progressively measurable, vanish off `[0, T]` and have finite
energy on it; `q^h` is jointly measurable in the sample point, the time and the mark, marked
progressively measurable, vanishes off `[0, T]` and has finite marked energy on it; and
`q^g_T` is strongly `ℱ_T`-measurable and square integrable. -/
structure Forcing (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) (ν : Measure E) (T : ℝ)
    (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
    (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ) : Prop where
  /-- `q^b` is jointly measurable. -/
  qb_meas : ∀ i, Measurable (Function.uncurry (qb i))
  /-- `q^b` is progressively measurable. -/
  qb_prog : ∀ i, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (qb i)
  /-- `q^b` vanishes off the horizon. -/
  qb_vanish : ∀ i ω s, s ∉ Set.Icc (0 : ℝ) T → qb i ω s = 0
  /-- `q^b` has finite energy on the horizon. -/
  qb_sq : ∀ i, LevyStochCalc.Brownian.Ito.energy P T (qb i) ≠ ⊤
  /-- `q^σ` is jointly measurable. -/
  qσ_meas : ∀ i j, Measurable (Function.uncurry fun ω s => qσ i s ω j)
  /-- `q^σ` is progressively measurable. -/
  qσ_prog : ∀ i j, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => qσ i s ω j
  /-- `q^σ` vanishes off the horizon. -/
  qσ_vanish : ∀ i ω s, s ∉ Set.Icc (0 : ℝ) T → qσ i s ω = 0
  /-- `q^σ` has finite energy on the horizon. -/
  qσ_sq : ∀ i j, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => qσ i s ω j) ≠ ⊤
  /-- `q^h` is jointly measurable in the sample point, the time and the mark. -/
  qh_meas : ∀ i, Measurable fun p : Ω × ℝ × E => qh i p.2.1 p.1 p.2.2
  /-- `q^h` is marked progressively measurable. -/
  qh_prog : ∀ i,
    LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => qh i s ω e
  /-- `q^h` vanishes off the horizon. -/
  qh_vanish : ∀ i ω s e, s ∉ Set.Icc (0 : ℝ) T → qh i s ω e = 0
  /-- `q^h` has finite marked energy on the horizon. -/
  qh_sq : ∀ i,
    LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e) ≠ ⊤
  /-- `q^f` is jointly measurable. -/
  qf_meas : ∀ k, Measurable (Function.uncurry (qf k))
  /-- `q^f` is progressively measurable. -/
  qf_prog : ∀ k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (qf k)
  /-- `q^f` vanishes off the horizon. -/
  qf_vanish : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) T → qf k ω s = 0
  /-- `q^f` has finite energy on the horizon. -/
  qf_sq : ∀ k, LevyStochCalc.Brownian.Ito.energy P T (qf k) ≠ ⊤
  /-- `q^g_T` is strongly `ℱ_T`-measurable. -/
  qg_meas : ∀ k, StronglyMeasurable[ℱ T] (qg k)
  /-- `q^g_T` is square integrable. -/
  qg_sq : ∀ k, MemLp (qg k) 2 P

/-- The zero forcing is a forcing. -/
theorem Forcing.zero {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} {T : ℝ} :
    Forcing ℱ P ν T (0 : Fin n → Ω → ℝ → ℝ) (0 : Fin n → ℝ → Ω → Fin d → ℝ)
      (0 : Fin n → ℝ → Ω → E → ℝ) (0 : Fin m → Ω → ℝ → ℝ) (0 : Fin m → Ω → ℝ) where
  qb_meas _ := measurable_const
  qb_prog _ := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_zero ℱ
  qb_vanish _ _ _ _ := rfl
  qb_sq _ := by simp [LevyStochCalc.Brownian.Ito.energy]
  qσ_meas _ _ := measurable_const
  qσ_prog _ _ := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_zero ℱ
  qσ_vanish _ _ _ _ := rfl
  qσ_sq _ _ := by simp [LevyStochCalc.Brownian.Ito.energy]
  qh_meas _ := measurable_const
  qh_prog _ := LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_zero ℱ
  qh_vanish _ _ _ _ _ := rfl
  qh_sq _ := by simp [LevyStochCalc.Poisson.Compensated.markedEnergy]
  qf_meas _ := measurable_const
  qf_prog _ := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_zero ℱ
  qf_vanish _ _ _ _ := rfl
  qf_sq _ := by simp [LevyStochCalc.Brownian.Ito.energy]
  qg_meas _ := stronglyMeasurable_const
  qg_sq _ := MemLp.zero

end MVFBSDEJ.WellPosedness.System
