/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.HilbertW2
import Dissertation.WellPosedness.System.FullRank
import Dissertation.WellPosedness.System.HilbertLipschitz
import Dissertation.Law.TupleMarginal

/-!
# Section 2 of the well-posedness paper: the coupling matrix and the Wasserstein bounds

Statement and equation numbers refer to the well-posedness paper at `e939294`.

## Main definitions

* `Dissertation.PaperSpec.A.eq_coupling` — the coupling bound (2.8).
* `Dissertation.PaperSpec.A.eq_couplingT` — its terminal form (2.9).
* `Dissertation.PaperSpec.A.eq_lipfun` — Lipschitz law functionals, (2.10).
* `Dissertation.PaperSpec.A.eq_margproj` — the `U`-marginal projection, (2.11).
* `Dissertation.PaperSpec.A.ass_G` — the bounds asserted in Assumption 2.4.
-/

open MeasureTheory Dissertation.Law

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System

universe u v w

/-- Lipschitz law functionals (2.10): for a separable Hilbert space `K` and a map `φ̄ : H → K`
that is `L`-Lipschitz for the Hilbert norm of `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)`,
`|∫_H φ̄ dμ − ∫_H φ̄ dμ'|_K ≤ L W₂(μ, μ')` for all `μ, μ' ∈ P₂(H)`, with `W₂` that of the Hilbert
norm. -/
def eq_lipfun : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d : ℕ) {K : Type w} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] [TopologicalSpace.SeparableSpace K]
    (φ : TupleH ν n m d → K) (L : ℝ), 0 ≤ L →
    (∀ θ θ' : TupleH ν n m d, ‖φ θ - φ θ'‖ ≤ L * ‖toL2 θ - toL2 θ'‖) →
    ∀ μ μ' : P2 (TupleH ν n m d), ‖(∫ θ, φ θ ∂μ.law) - ∫ θ, φ θ ∂μ'.law‖ ≤ L * w2H μ μ'

/-- The `U`-marginal projection (2.11): for all `μ, μ' ∈ P₂(H)`, the `U`-marginals
`μ^U, μ'^U ∈ P₂(L²(ν; ℝᵐ))` satisfy `W₂(μ^U, μ'^U) ≤ W₂(μ, μ')`, with `W₂` of the norm of
`L²(ν; ℝᵐ)` on the left and of the Hilbert norm of `H` on the right. -/
def eq_margproj : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d : ℕ) (μ μ' : P2 (TupleH ν n m d)),
    w2P μ.margU μ'.margU ≤ w2H μ μ'

/-- The bounds asserted in Assumption 2.4 (coupling matrix). For `m, n ≥ 1` and
`G ∈ ℝ^{m×n}` of full rank, `s_min(G) > 0`; with `‖G‖` the operator norm,
`|G v| ≤ ‖G‖ |v|` and `|Gᵀ v| ≤ ‖G‖ |v|`; with `c_G = s_min(G)⁻²`, `|x|² ≤ c_G |G x|²` when
`m ≥ n` and `|y|² ≤ c_G |Gᵀ y|²` when `n ≥ m`; and when `Gᵀ` is injective,
`|Z|²_F ≤ c_G |Gᵀ Z|²_F` for `Z ∈ ℝ^{m×d}` and `‖U‖²_{L²(ν)} ≤ c_G ‖Gᵀ U‖²_{L²(ν)}` for
`U ∈ L²(ν; ℝᵐ)`. -/
def ass_G : Prop :=
  ∀ (m n : ℕ), 0 < m → 0 < n → ∀ G : Matrix (Fin m) (Fin n) ℝ, G.rank = min m n →
    0 < sMin G
    ∧ (∀ v : EuclideanSpace ℝ (Fin n), ‖GX G v‖ ≤ ‖GX G‖ * ‖v‖)
    ∧ (∀ v : EuclideanSpace ℝ (Fin m), ‖ContinuousLinearMap.adjoint (GX G) v‖ ≤ ‖GX G‖ * ‖v‖)
    ∧ (n ≤ m → ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 ≤ (sMin G ^ 2)⁻¹ * ‖GX G x‖ ^ 2)
    ∧ (m ≤ n → ∀ y : EuclideanSpace ℝ (Fin m),
        ‖y‖ ^ 2 ≤ (sMin G ^ 2)⁻¹ * ‖ContinuousLinearMap.adjoint (GX G) y‖ ^ 2)
    ∧ (Function.Injective (ContinuousLinearMap.adjoint (GX G)) →
        (∀ (d : ℕ) (Z : EuclideanSpace ℝ (Fin m × Fin d)),
          ‖Z‖ ^ 2 ≤ (sMin G ^ 2)⁻¹ * ‖ContinuousLinearMap.adjoint (GZ (d := d) G) Z‖ ^ 2)
        ∧ ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E)
          (U : Lp (EuclideanSpace ℝ (Fin m)) 2 ν),
          ‖U‖ ^ 2 ≤ (sMin G ^ 2)⁻¹ * ‖ContinuousLinearMap.adjoint (GU G ν) U‖ ^ 2)

/-- The coupling bound (2.8): for square-integrable random tuples `Θ, Θ'` of
`H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)` on one probability space,
`W₂(Law Θ, Law Θ')² ≤ 𝔼[|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}]`, with `W₂` the
2-Wasserstein distance of the Hilbert norm of `H`. -/
def eq_coupling : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (Θ Θ' : Ω → TupleH ν n m d), MemLp Θ 2 P → MemLp Θ' 2 P →
    w2H (lawP2 P Θ) (lawP2 P Θ') ^ 2
      ≤ ∫ ω, (‖(Θ ω).1 - (Θ' ω).1‖ ^ 2 + ‖(Θ ω).2.1 - (Θ' ω).2.1‖ ^ 2
          + ‖(Θ ω).2.2.1 - (Θ' ω).2.2.1‖ ^ 2 + ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2) ∂P

/-- The terminal coupling bound (2.9): for square-integrable random vectors `X, X'` of `ℝⁿ` on
one probability space, `W₂(Law X, Law X')² ≤ 𝔼|X − X'|²`. -/
def eq_couplingT : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ)
    (X X' : Ω → EuclideanSpace ℝ (Fin n)), MemLp X 2 P → MemLp X' 2 P →
    w2P (lawP2 P X) (lawP2 P X') ^ 2 ≤ ∫ ω, ‖X ω - X' ω‖ ^ 2 ∂P

end Dissertation.PaperSpec.A
