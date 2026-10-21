/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.DiagonalInputs
import Dissertation.WellPosedness.Existence.CoeffBorelW2
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Assumptions 2.2, 2.3 and 2.5 of the well-posedness paper, as printed

This file states the standing measurability (2.3) and Assumptions 2.2, 2.3 and 2.5 of the
well-posedness paper in the form in which the paper prints them, over a filtered probability
space `(Ω, ℱ, P)`, a horizon `T` and coefficients `C = (b, σ, h, f, g)` on the tuple space
`H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)`.

* **(2.3)** The coefficients `b, σ, h, f` are Borel measurable on `[0, T] × H × P₂(H)`, `h` as a
  map into `L²(ν; ℝⁿ)`, and `g` is Borel measurable on `ℝⁿ × P₂(ℝⁿ)`; `P₂(H)` and `P₂(ℝⁿ)` carry
  the 2-Wasserstein distances of the Hilbert norm of `H` and of the Euclidean norm.
* **Assumption 2.2** `ξ₀ ∈ L²(Ω, ℱ₀; ℝⁿ)`, and with `δ₀` the Dirac mass at the origin of `H`,
  `b(·, 0, δ₀) ∈ L²(0, T; ℝⁿ)`, `σ(·, 0, δ₀) ∈ L²(0, T; ℝ^{n×d})`,
  `h(·, 0, ·, δ₀) ∈ L²(0, T; L²(ν; ℝⁿ))`, `f(·, 0, δ₀) ∈ L²(0, T; ℝᵐ)`.
* **Assumption 2.3** There is `L ≥ 0` such that, for almost every `t ∈ [0, T]` and all
  `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, almost surely
  `|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ L (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + W₂(μ, μ'))`;
  and for all `X_T, X'_T ∈ L²(Ω, ℱ_T; ℝⁿ)`, almost surely `|δg_T| ≤ L (|X_T − X'_T| + W₂(ρ, ρ'))`,
  (2.6).
* **Assumption 2.5** For all `X_T, X'_T ∈ L²(Ω, ℱ_T; ℝⁿ)`, `𝔼⟨δg_T, G δX_T⟩ ≥ α 𝔼|G δX_T|²`;
  for almost every `t ∈ [0, T]` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, (2.7),
  `𝔼[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F + ⟨−δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)]
    ≤ −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}] − β₂ 𝔼|G δX|²`;
  and `α, β₁, β₂` are admissible.

Here `𝒟_t` is the diagonal of Definition 2.1, `Dissertation.WellPosedness.System.diagonalInputs`,
whose elements are pairs of a strongly `ℱ_t`-measurable square-integrable `Θ : Ω → H` and its law.
An element of an `L²` space is represented by a strongly measurable square-integrable map. The
expectations of Assumption 2.5 are Bochner integrals; the two expectations of pairings are required
to exist, as integrability of the integrands, and the others exist for square-integrable inputs. The
interior conditions of Assumptions 2.3 and 2.5 at a fixed time `t`, `LipInteriorAt` and `Mono27At`,
are the conditions the two assumptions impose for almost every `t ∈ [0, T]`.

## Main definitions

* `JointBorel` — the joint Borel measurability (2.3).
* `OriginValues`, `Assumption22` — Assumption 2.2.
* `LipInteriorAt`, `LipInterior`, `LipTerminal`, `Assumption23` — the interior bound of
  Assumption 2.3 at a fixed time, and Assumption 2.3.
* `pairing27`, `Mono27At`, `Assumption25` — the integrand of the left-hand side of (2.7), the
  interior inequality (2.7) at a fixed time, and Assumption 2.5.
-/

open MeasureTheory Filter Dissertation.Law Matrix

namespace Dissertation.WellPosedness.Spec

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-! ### The joint Borel measurability (2.3) -/

/-- **The joint Borel measurability (2.3)**: each of `(t, θ, μ) ↦ ψ(t, θ, μ)`,
`ψ ∈ {b, σ, h, f}`, is Borel measurable on `[0, T] × H × P₂(H)`, the jump coefficient as a map into
`L²(ν; ℝⁿ)`, and `(x, ρ) ↦ g(x, ρ)` is Borel measurable on `ℝⁿ × P₂(ℝⁿ)`, with `P₂(H)` and `P₂(ℝⁿ)`
carrying the 2-Wasserstein distances of the Hilbert norm of `H` and of the Euclidean norm. -/
structure JointBorel (T : ℝ) (C : Coeffs ν n m d) : Prop where
  /-- The drift is Borel measurable on `[0, T] × H × P₂(H)`. -/
  b_meas : Measurable[borel (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d),
    borel (EuclideanSpace ℝ (Fin n))] fun p => C.b p.1 p.2.1 p.2.2.toP2
  /-- The diffusion is Borel measurable on `[0, T] × H × P₂(H)`. -/
  σ_meas : Measurable[borel (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d),
    borel (EuclideanSpace ℝ (Fin n × Fin d))] fun p => C.σ p.1 p.2.1 p.2.2.toP2
  /-- The jump coefficient is Borel measurable on `[0, T] × H × P₂(H)` into `L²(ν; ℝⁿ)`. -/
  h_meas : Measurable[borel (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d),
    borel (Lp (EuclideanSpace ℝ (Fin n)) 2 ν)] fun p => C.h p.1 p.2.1 p.2.2.toP2
  /-- The driver is Borel measurable on `[0, T] × H × P₂(H)`. -/
  f_meas : Measurable[borel (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d),
    borel (EuclideanSpace ℝ (Fin m))] fun p => C.f p.1 p.2.1 p.2.2.toP2
  /-- The terminal function is Borel measurable on `ℝⁿ × P₂(ℝⁿ)`. -/
  g_meas : Measurable[borel (EuclideanSpace ℝ (Fin n) × P2W (EuclideanSpace ℝ (Fin n))),
    borel (EuclideanSpace ℝ (Fin m))] fun p => C.g p.1 p.2.toP2

/-! ### Assumption 2.2 -/

/-- **The origin values of Assumption 2.2**: with `δ₀` the Dirac mass at the origin of `H`,
`b(·, 0, δ₀) ∈ L²(0, T; ℝⁿ)`, `σ(·, 0, δ₀) ∈ L²(0, T; ℝ^{n×d})`,
`h(·, 0, ·, δ₀) ∈ L²(0, T; L²(ν; ℝⁿ))` and `f(·, 0, δ₀) ∈ L²(0, T; ℝᵐ)`. -/
structure OriginValues (T : ℝ) (C : Coeffs ν n m d) : Prop where
  /-- `b(·, 0, δ₀) ∈ L²(0, T; ℝⁿ)`. -/
  b_memLp : MemLp (fun t => C.b t 0 (P2.dirac 0)) 2 (volume.restrict (Set.Ioo 0 T))
  /-- `σ(·, 0, δ₀) ∈ L²(0, T; ℝ^{n×d})`. -/
  σ_memLp : MemLp (fun t => C.σ t 0 (P2.dirac 0)) 2 (volume.restrict (Set.Ioo 0 T))
  /-- `h(·, 0, ·, δ₀) ∈ L²(0, T; L²(ν; ℝⁿ))`. -/
  h_memLp : MemLp (fun t => C.h t 0 (P2.dirac 0)) 2 (volume.restrict (Set.Ioo 0 T))
  /-- `f(·, 0, δ₀) ∈ L²(0, T; ℝᵐ)`. -/
  f_memLp : MemLp (fun t => C.f t 0 (P2.dirac 0)) 2 (volume.restrict (Set.Ioo 0 T))

/-- **Assumption 2.2**: the initial datum lies in `L²(Ω, ℱ₀; ℝⁿ)`, and the origin values of the
coefficients lie in `L²(0, T)`. -/
structure Assumption22 (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) (T : ℝ)
    (C : Coeffs ν n m d) (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)) : Prop where
  /-- `ξ₀` is strongly `ℱ₀`-measurable. -/
  initial_meas : StronglyMeasurable[ℱ 0] ξ₀
  /-- `ξ₀` is square integrable. -/
  initial_memLp : MemLp ξ₀ 2 P
  /-- The origin values lie in `L²(0, T)`. -/
  origin : OriginValues T C

/-! ### Assumption 2.3 -/

/-- **The interior bound of Assumption 2.3 at the time `t`**: for all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`,
almost surely
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ L (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + W₂(μ, μ'))`,
the coefficients evaluated at `t` and `W₂` the 2-Wasserstein distance on `P₂(H)` of the Hilbert
norm of `H`. -/
def LipInteriorAt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (t L : ℝ) (C : Coeffs ν n m d) : Prop :=
  ∀ p ∈ diagonalInputs ν n m d ℱ P t, ∀ p' ∈ diagonalInputs ν n m d ℱ P t, ∀ᵐ ω ∂P,
    ‖C.b t (p.1 ω) p.2 - C.b t (p'.1 ω) p'.2‖ + ‖C.σ t (p.1 ω) p.2 - C.σ t (p'.1 ω) p'.2‖
        + ‖C.h t (p.1 ω) p.2 - C.h t (p'.1 ω) p'.2‖
        + ‖C.f t (p.1 ω) p.2 - C.f t (p'.1 ω) p'.2‖
      ≤ L * (‖(p.1 ω).1 - (p'.1 ω).1‖ + ‖(p.1 ω).2.1 - (p'.1 ω).2.1‖
        + ‖(p.1 ω).2.2.1 - (p'.1 ω).2.2.1‖ + ‖(p.1 ω).2.2.2 - (p'.1 ω).2.2.2‖
        + w2H p.2 p'.2)

/-- **Assumption 2.3, interior**: for almost every `t ∈ [0, T]` and all
`(Θ, μ), (Θ', μ') ∈ 𝒟_t`, almost surely
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ L (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + W₂(μ, μ'))`,
with `W₂` the 2-Wasserstein distance on `P₂(H)` of the Hilbert norm of `H`. -/
def LipInterior (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) [IsProbabilityMeasure P]
    (T L : ℝ) (C : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), LipInteriorAt ℱ P t L C

/-- **Assumption 2.3, terminal (2.6)**: for all `X_T, X'_T ∈ L²(Ω, ℱ_T; ℝⁿ)` with laws `ρ, ρ'`,
almost surely `|g(X_T, ρ) − g(X'_T, ρ')| ≤ L (|X_T − X'_T| + W₂(ρ, ρ'))`, with `W₂` the
2-Wasserstein distance on `P₂(ℝⁿ)`. -/
def LipTerminal (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) [IsProbabilityMeasure P]
    (T L : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)) :
    Prop :=
  ∀ XT XT' : Ω → EuclideanSpace ℝ (Fin n), StronglyMeasurable[ℱ T] XT →
    StronglyMeasurable[ℱ T] XT' → MemLp XT 2 P → MemLp XT' 2 P →
    ∀ᵐ ω ∂P, ‖g (XT ω) (lawP2 P XT) - g (XT' ω) (lawP2 P XT')‖
      ≤ L * (‖XT ω - XT' ω‖ + w2P (lawP2 P XT) (lawP2 P XT'))

/-- **Assumption 2.3** with the constant `L`: `L ≥ 0`, and the interior and terminal Lipschitz
bounds hold with `L`. -/
structure Assumption23 (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T L : ℝ) (C : Coeffs ν n m d) : Prop where
  /-- `L ≥ 0`. -/
  nonneg : 0 ≤ L
  /-- The interior Lipschitz bound. -/
  interior : LipInterior ℱ P T L C
  /-- The terminal Lipschitz bound (2.6). -/
  terminal : LipTerminal ℱ P T L C.g

/-! ### Assumption 2.5 -/

/-- **The integrand of the left-hand side of (2.7)** at two points `θ, θ'` of `H` and two laws
`μ, μ'` at the time `t`:
`⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F + ⟨−δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)`, with
`δψ = ψ(t, θ, μ) − ψ(t, θ', μ')` and `δX, δY, δZ, δU` the channels of `θ − θ'`. -/
noncomputable def pairing27 (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d) (t : ℝ)
    (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)) : ℝ :=
  inner ℝ (C.b t θ μ - C.b t θ' μ') (GX Gᵀ (θ.2.1 - θ'.2.1))
    + inner ℝ (C.σ t θ μ - C.σ t θ' μ') (GZ Gᵀ (θ.2.2.1 - θ'.2.2.1))
    + inner ℝ (-(C.f t θ μ - C.f t θ' μ')) (GX G (θ.1 - θ'.1))
    + ∫ e, inner ℝ (C.h t θ μ e - C.h t θ' μ' e) (GX Gᵀ (θ.2.2.2 e - θ'.2.2.2 e)) ∂ν

/-- **The interior inequality (2.7) at the time `t`**, with the coupling matrix `G` and the
constants `β₁, β₂`: for all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, the expectation of the pairing exists and
`𝔼[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F + ⟨−δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)]
  ≤ −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}] − β₂ 𝔼|G δX|²`,
the coefficients evaluated at `t`. -/
def Mono27At (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) [IsProbabilityMeasure P]
    (t : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (β₁ β₂ : ℝ) (C : Coeffs ν n m d) : Prop :=
  ∀ p ∈ diagonalInputs ν n m d ℱ P t, ∀ p' ∈ diagonalInputs ν n m d ℱ P t,
    Integrable (fun ω => pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2) P
      ∧ ∫ ω, pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2 ∂P
        ≤ -β₁ * ∫ ω, (‖GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)‖ ^ 2
            + ‖GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)‖ ^ 2
            + ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2) ∂P
          - β₂ * ∫ ω, ‖GX G ((p.1 ω).1 - (p'.1 ω).1)‖ ^ 2 ∂P

/-- **Assumption 2.5** with the coupling matrix `G` and the constants `α, β₁, β₂`: the terminal
inequality `𝔼⟨δg_T, G δX_T⟩ ≥ α 𝔼|G δX_T|²` for all `X_T, X'_T ∈ L²(Ω, ℱ_T; ℝⁿ)`; the interior
inequality (2.7) for almost every `t ∈ [0, T]` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`; each with the
expectation of its pairing existing; and the admissible constants. -/
structure Assumption25 (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (α β₁ β₂ : ℝ)
    (C : Coeffs ν n m d) : Prop where
  /-- The terminal inequality. -/
  terminal : ∀ XT XT' : Ω → EuclideanSpace ℝ (Fin n), StronglyMeasurable[ℱ T] XT →
    StronglyMeasurable[ℱ T] XT' → MemLp XT 2 P → MemLp XT' 2 P →
    Integrable (fun ω => inner ℝ (C.g (XT ω) (lawP2 P XT) - C.g (XT' ω) (lawP2 P XT'))
        (GX G (XT ω - XT' ω))) P
      ∧ ∫ ω, inner ℝ (C.g (XT ω) (lawP2 P XT) - C.g (XT' ω) (lawP2 P XT'))
          (GX G (XT ω - XT' ω)) ∂P
        ≥ α * ∫ ω, ‖GX G (XT ω - XT' ω)‖ ^ 2 ∂P
  /-- The interior inequality (2.7). -/
  interior : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Mono27At ℱ P t G β₁ β₂ C
  /-- The constants are admissible. -/
  constants : Constants n m α β₁ β₂

end Dissertation.WellPosedness.Spec
