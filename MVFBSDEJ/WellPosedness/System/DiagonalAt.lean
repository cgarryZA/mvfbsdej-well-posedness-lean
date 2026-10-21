/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.DiagonalLipschitzH
/-!
# The interior hypotheses at a fixed time

Assumptions 2.3 and 2.5 impose their interior conditions for almost every `t ∈ [0, T]`. At a fixed
time `t` the two conditions are:

* `DiagonalLipschitzHAt ℱ P t L C` — for any two strongly `ℱ_t`-measurable square-integrable
  tuples `Θ, Θ'` with laws `μ, μ'`, almost surely
  `|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ L (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + W₂(μ, μ'))`,
  with `W₂` the 2-Wasserstein distance of the Hilbert norm of `H`;
* `DiagonalMonotoneAt ℱ P t G β₁ β₂ C` — for any two such tuples, the interior inequality (2.7)
  `𝔼[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F − ⟨δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)]
    ≤ −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}] − β₂ 𝔼|G δX|²`.

## Main definitions

* `DiagonalLipschitzHAt` — Assumption 2.3, interior, at a fixed time.
* `DiagonalMonotoneAt` — Assumption 2.5, interior, at a fixed time.
-/

open MeasureTheory Filter MVFBSDEJ.Law MVFBSDEJ.WellPosedness
  MVFBSDEJ.WellPosedness.System

namespace MVFBSDEJ.WellPosedness

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}
  {Ω : Type*} [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **Assumption 2.3, interior, at the time `t`**: for any two strongly `ℱ_t`-measurable
square-integrable tuples `Θ, Θ'` with laws `μ, μ'`, almost surely
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ L (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + W₂(μ, μ'))`,
the coefficients evaluated at `t` and `W₂` the 2-Wasserstein distance of the Hilbert norm of
`H`. -/
def DiagonalLipschitzHAt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (t L : ℝ) (C : Coeffs ν n m d) : Prop :=
  ∀ Θ Θ' : Ω → TupleH ν n m d,
    StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
    ∀ᵐ ω ∂P, ‖C.b t (Θ ω) (lawP2 P Θ) - C.b t (Θ' ω) (lawP2 P Θ')‖
        + ‖C.σ t (Θ ω) (lawP2 P Θ) - C.σ t (Θ' ω) (lawP2 P Θ')‖
        + ‖C.h t (Θ ω) (lawP2 P Θ) - C.h t (Θ' ω) (lawP2 P Θ')‖
        + ‖C.f t (Θ ω) (lawP2 P Θ) - C.f t (Θ' ω) (lawP2 P Θ')‖
      ≤ L * (tupleNorm (Θ ω - Θ' ω) + w2H (lawP2 P Θ) (lawP2 P Θ'))

/-- **Assumption 2.5, interior, at the time `t`** (2.7): for any two strongly `ℱ_t`-measurable
square-integrable tuples with laws `μ, μ'`, the coefficients evaluated at `t`,
`𝔼[⟨δb, Gᵀ δY⟩ + ⟨δσ, Gᵀ δZ⟩_F − ⟨δf, G δX⟩ + ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de)]
  ≤ −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}] − β₂ 𝔼|G δX|²`. -/
def DiagonalMonotoneAt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (t : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (β₁ β₂ : ℝ)
    (C : Coeffs ν n m d) : Prop :=
  ∀ Θ Θ' : Ω → TupleH ν n m d,
    StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
    ∫ ω, interiorPairing (GX G) (GZ G) (GU G ν)
        (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P
      ≤ ∫ ω, dissipation (GX G) (GZ G) (GU G ν) β₁ β₂
        (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P

end MVFBSDEJ.WellPosedness
