/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4BackwardYoung
import Dissertation.WellPosedness.System.BackwardYoung
import Dissertation.Acceptance.A.Sec4

/-!
# The Young bound (4.25) of the proof of Lemma 4.3

Statement and equation numbers refer to the well-posedness paper at `1f67672`. For
`ε ∈ (0, 1]` the bound (4.25) holds with `C = 2 (10 (2L)²) + 3`. Its hypotheses are those of
Lemma 4.3, an instance of which is `Dissertation.Acceptance.A.lem_pert_data_forcing_hypotheses`.

## Main statements

* `Dissertation.Acceptance.A.eq_bwdyoung` — (4.25).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.PaperSpec.A LevyStochCalc

universe u v w

/-- (4.25), with `C = 2 (10 (2L)²) + 3`. -/
theorem eq_bwdyoung : PaperSpec.A.eq_bwdyoung.{u, v, w} := by
  refine ⟨fun _ L _ _ _ _ _ => 2 * (10 * (2 * L) ^ 2) + 3, ?_⟩
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow _ hlam hlam1 ξ₁ ξ₂ _ _ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ _ _
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩ _ ε hε hε1
  exact PaperWeakSolutionForcedInt.ae_backwardYoung_le h₁ h₂ hT.le (hlow.le.trans hlam) hlam1 hε
    hε1 h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone

end Dissertation.Acceptance.A
