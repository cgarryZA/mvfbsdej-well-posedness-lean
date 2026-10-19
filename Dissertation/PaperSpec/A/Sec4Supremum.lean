/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.LocalProperty

/-!
# The supremum criterion of Section 4 of the well-posedness paper

Statement numbers refer to the well-posedness paper at `1f67672`. The preamble of §4 states that, by
localisation and dominated convergence, a càdlàg local martingale whose running supremum is
integrable has zero-mean increments; the proofs of Lemmas 4.1 and 4.3 apply it on `[0, T]`.

A local martingale is read through Mathlib's `ProbabilityTheory.Locally`: there are stopping
times `τ_k`, almost surely nondecreasing and tending to `∞`, such that every stopped process
`M^{τ_k} 1_{τ_k > 0}` is a martingale.

## Main definitions

* `Dissertation.PaperSpec.A.sec4_supremum_criterion` — the supremum criterion.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace Dissertation.PaperSpec.A

universe u

/-- The supremum criterion of §4. On a filtered probability space with time `[0, ∞)`, let `M` be
a real adapted process whose paths are almost surely càdlàg and which is a local martingale, and
let `T ≥ 0` with `𝔼 sup_{u ≤ T} |M_u| < ∞`; then `M_t` is integrable for `t ≤ T` and
`𝔼[M_t - M_s] = 0` for `s ≤ t ≤ T`. -/
def sec4_supremum_criterion : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0),
    Adapted 𝓕 M →
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, ContinuousWithinAt (fun u => M u ω) (Set.Ici t) t
      ∧ ∃ l : ℝ, Tendsto (fun u => M u ω) (𝓝[<] t) (𝓝 l)) →
    Locally (fun X => Martingale X 𝓕 P) 𝓕 M P →
    ∫⁻ ω, ⨆ u ≤ T, ‖M u ω‖ₑ ∂P < ∞ →
    (∀ t ≤ T, Integrable (M t) P) ∧ ∀ s t : ℝ≥0, s ≤ t → t ≤ T → ∫ ω, M t ω - M s ω ∂P = 0

end Dissertation.PaperSpec.A
