/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec4ProofSteps
import MVFBSDEJ.WellPosedness.Spec.Bridge22
import MVFBSDEJ.WellPosedness.System.FrozenDifference
import MVFBSDEJ.WellPosedness.System.WeakTupleJumpLeft

/-!
# The coefficient processes along a tuple of `𝕊`: proofs

Statement numbers refer to the well-posedness paper at `1f67672`. Under (2.3) and Assumptions
2.2–2.3, along a tuple `Θ` of `ℍ²` the drift, diffusion and driver processes and the canonical
representative `MVFBSDEJ.WellPosedness.Existence.coeffJump` of the jump coefficient at the tuple
have finite energy on `[0, T]`
(`MVFBSDEJ.WellPosedness.System.PaperWeakTuple.paperAdmissible_coeffJump`). Along a tuple of `𝕊`
every path of `X` and `Y` has left limits on `(0, T]`, and `coeffJump` at the predictable tuple
`Θ⁻` has the energy of `coeffJump` at `Θ`
(`MVFBSDEJ.WellPosedness.System.PaperWeakTuple.markedEnergy_coeffJump_leftLim_eq`).

## Main statements

* `MVFBSDEJ.Acceptance.sec4_coeff_sq`.
-/

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Spec

universe u v w

/-- §4, the coefficient processes (2.5) along a tuple of `𝕊` are square integrable. -/
theorem sec4_coeff_sq : PaperSpec.sec4_coeff_sq.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ _ _ _ _ T hT L C ξ₀ hJ h22 h23 X Y Z U hH
  obtain ⟨hΘ, hXl, hYl, -, -⟩ := hH
  have hB : CoeffBorel T C := (jointBorel_iff.mp hJ).1.toCoeffBorel
  have hA := hΘ.paperAdmissible_coeffJump hT.le hB
    (originValues_iff_coeffOrigin.mp h22.origin) h23.interior.diagonalLipschitz_two_mul
  refine ⟨hA.b_sq, hA.σ_sq, fun i => ?_, hA.f_sq⟩
  rw [hΘ.markedEnergy_coeffJump_leftLim_eq hT.le hXl hYl hB i]
  exact hA.γ_sq i

end MVFBSDEJ.Acceptance
