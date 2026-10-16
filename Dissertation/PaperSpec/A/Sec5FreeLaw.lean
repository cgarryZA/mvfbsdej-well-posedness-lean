/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec2Remarks

/-!
# Remark 5.6 of the well-posedness paper: the scope of the measure argument

Statement numbers refer to arXiv 2608.23203v1, in the standing setting of §2.
Remark 5.6: the proofs consume the tuple law only through the `W₂` term of Assumption 2.3,
dominated by the coupling bound (2.8); the right-hand side carries `𝔼‖δU‖²` whether or not the
measure argument reads the `U`-marginal, because the coefficients depend on `u` pointwise, a
dependence Remark 2.10 makes unavoidable when `β₁ > 0` and `ν ≠ 0`.

## Main definitions

* `Dissertation.PaperSpec.A.rem_freelaw` — under Assumption 2.5 with `β₁ > 0` and `ν ≠ 0`, the
  jump coefficient differs at two inputs with one law and the same `(X, Y, Z)`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Matrix

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.Law

universe u v w

/-- Remark 5.6, the measure argument. In the standing setting with `n, m, d ≥ 1`, `T > 0`, a
nonzero intensity `ν` and `G ∈ ℝ^{m×n}` of full rank, let the coefficients satisfy Assumption 2.5
with `G` and `β₁ > 0`. Then for almost every `t ∈ [0, T]` there are `(Θ, μ), (Θ', μ') ∈ 𝒟_t` with
one and the same law, `μ = μ'`, and the same `(X, Y, Z)`, at which the jump coefficient differs,
`h(t, Θ, μ) ≠ h(t, Θ', μ')` with positive probability: the coefficients depend on `u` pointwise,
and that dependence is not seen by any measure argument, every law term vanishing at such a
pair. -/
def rem_freelaw : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → 0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T → ν ≠ 0 →
    ∀ (G : Matrix (Fin m) (Fin n) ℝ), G.rank = min m n →
    ∀ (α β₁ β₂ : ℝ) (C : Coeffs ν n m d),
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C → 0 < β₁ →
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∃ p ∈ diagonalInputs ν n m d (enlJoint 𝒢₀ D h𝒢₀) P t,
      ∃ p' ∈ diagonalInputs ν n m d (enlJoint 𝒢₀ D h𝒢₀) P t,
        p.2 = p'.2
        ∧ (∀ ω, (p.1 ω).1 = (p'.1 ω).1 ∧ (p.1 ω).2.1 = (p'.1 ω).2.1
          ∧ (p.1 ω).2.2.1 = (p'.1 ω).2.2.1)
        ∧ ¬ ∀ᵐ ω ∂P, C.h t (p.1 ω) p.2 = C.h t (p'.1 ω) p'.2

end Dissertation.PaperSpec.A
