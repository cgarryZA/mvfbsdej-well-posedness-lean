/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Acceptance.Sec3SpaceNorm
import MVFBSDEJ.WellPosedness.System.WeakTupleLinear

/-!
# The linear structure of the solution space of §3: proofs

Statement numbers refer to the well-posedness paper at `1f67672`. Each condition of `ℍ²` passes
to coordinatewise sums and multiples
(`MVFBSDEJ.WellPosedness.System.PaperWeakTuple.add`,
`MVFBSDEJ.WellPosedness.System.PaperWeakTuple.const_mul`): adaptedness, right-continuity and
left limits coordinatewise, predictability as measurability for the predictable σ-algebras, and
finite energy by `|a + b|² ≤ 2 (|a|² + |b|²)`, with `X` and `Y` replaced on `[0, T]` by jointly
measurable processes. The finiteness of `‖·‖_𝕊` passes to sums and multiples by the triangle
inequality and the homogeneity of `sec3_HH_norm`.

## Main statements

* `MVFBSDEJ.Acceptance.sec3_HH_linear`.
-/

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System

universe u v w

/-- §3, the solution space is a linear space. -/
theorem sec3_HH_linear : PaperSpec.sec3_HH_linear.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ T X X' Y Y' Z Z' U U' hΘ hΘ'
  obtain ⟨htri, hhom⟩ := sec3_HH_norm 𝒢₀ ν n m d P D h𝒢₀ T X X' Y Y' Z Z' U U' hΘ hΘ'
  have hhalf : (0 : ℝ) < 1 / 2 := one_half_pos
  refine ⟨hΘ.add hΘ', fun c => hΘ.const_mul c, fun h h' => ?_, fun h c => ?_⟩
  · refine ((ENNReal.rpow_lt_top_iff_of_pos hhalf).mp (htri.trans_lt ?_)).ne
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.rpow_lt_top_of_nonneg hhalf.le h,
      ENNReal.rpow_lt_top_of_nonneg hhalf.le h'⟩
  · refine ((ENNReal.rpow_lt_top_iff_of_pos hhalf).mp ?_).ne
    rw [hhom c]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.rpow_lt_top_of_nonneg hhalf.le h)

end MVFBSDEJ.Acceptance
