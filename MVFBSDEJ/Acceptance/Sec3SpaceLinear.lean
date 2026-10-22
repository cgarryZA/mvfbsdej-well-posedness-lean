/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec3SpaceNorm
import MVFBSDEJ.WellPosedness.System.WeakTupleLinear

/-!
# The linear structure of the solution space of §3: proofs

Statement numbers refer to the well-posedness paper at `1f67672`. Each condition of `ℍ²` passes
to coordinatewise sums and multiples
(`MVFBSDEJ.WellPosedness.System.PaperWeakTuple.add`,
`MVFBSDEJ.WellPosedness.System.PaperWeakTuple.const_mul`): adaptedness, right-continuity and
left limits coordinatewise, predictability as measurability for the predictable σ-algebras, and
finite energy by `|a + b|² ≤ 2 (|a|² + |b|²)`, with `X` and `Y` replaced on `[0, T]` by jointly
measurable processes.

## Main statements

* `MVFBSDEJ.Acceptance.sec3_HH_linear`.
-/

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System

universe u v w

/-- §3, the solution space is a linear space. -/
theorem sec3_HH_linear : PaperSpec.sec3_HH_linear.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ T X X' Y Y' Z Z' U U' hΘ hΘ'
  exact ⟨hΘ.add hΘ', fun c => hΘ.const_mul c⟩

end MVFBSDEJ.Acceptance
