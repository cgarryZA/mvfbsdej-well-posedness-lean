/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec2Basics
import Dissertation.PaperSpec.A.Sec5

/-!
# Example 5.2 of the well-posedness paper: the representation warning and the branch `m > n`

Statement numbers refer to the well-posedness paper at `f598204`, in the standing setting of §2.
Example 5.2 removes the Poisson channel from the stochastic basis; it warns that setting `h ≡ 0`
on a Brownian–Poisson basis is not a reduction, since the Poisson integral and its integrand
persist in the representation, and it states that both rank branches of Assumption 2.5 are
available without a jump channel. The branch `m < n` is the last clause of `ex_brownian`.

## Main definitions

* `Dissertation.PaperSpec.A.ex_brownian_not_h0` — at a nonzero intensity, a square-integrable
  martingale with no representation in which `U = 0`.
* `Dissertation.PaperSpec.A.ex_brownian_rank_gt` — at `ν = 0`, the branch `m > n` of
  Assumption 2.5.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Enlarged
  Dissertation.WellPosedness.Spec

universe u v w

/-- Example 5.2, setting `h ≡ 0` is not a reduction. In the standing setting with `d ≥ 1` and a
nonzero intensity `ν`, on every horizon `T > 0` there is a square-integrable martingale of the
filtration of §2 with no representation `(Z, U)` on `[0, T]` in which `U = 0`: the Poisson
integral and its integrand persist in the representation property, whatever the coefficients. -/
def ex_brownian_not_h0 : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] (ν : Measure E) [SigmaFinite ν]
    (d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), 0 < d → ν ≠ 0 → ∀ T : ℝ, 0 < T →
    ∃ M : ℝ → Ω → ℝ, Martingale M (enlJoint 𝒢₀ D h𝒢₀) P ∧ (∀ t, MemLp (M t) 2 P)
      ∧ ¬ ∃ Z : ℝ → Ω → Fin d → ℝ, RepresentsMart D h𝒢₀ hind₀ T M Z fun _ _ _ => 0

/-- Example 5.2, the branch `m > n`. In the standing setting with the intensity `ν = 0`, for
`1 ≤ n < m`, `d ≥ 1`, `T > 0` and `ξ₀ ∈ L²(Ω, ℱ₀)` there are a coupling matrix `G` of full rank
and coefficients satisfying (2.3) and Assumptions 2.2–2.5 with `β₂ > 0`. -/
def ex_brownian_rank_gt : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] (d : ℕ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d (0 : Measure E)) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P →
    ∀ n m : ℕ, 0 < n → n < m → 0 < d → ∀ T : ℝ, 0 < T →
      ∀ ξ₀ : Ω → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₀ → MemLp ξ₀ 2 P →
      ∃ (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs (0 : Measure E) n m d) (L α β₁ β₂ : ℝ),
        JointBorel T C ∧ Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀
        ∧ Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C ∧ G.rank = min m n
        ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C ∧ 0 < β₂

end Dissertation.PaperSpec.A
