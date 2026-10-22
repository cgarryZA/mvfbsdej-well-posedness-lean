/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.AppA
import MVFBSDEJ.PaperSpec.AppASteps
import MVFBSDEJ.PaperSpec.Sec2
import MVFBSDEJ.PaperSpec.Sec2Basics
import MVFBSDEJ.PaperSpec.Sec2Measurability
import MVFBSDEJ.PaperSpec.Sec2Remarks
import MVFBSDEJ.PaperSpec.Sec3
import MVFBSDEJ.PaperSpec.Sec3GeneralRank
import MVFBSDEJ.PaperSpec.Sec3Margin
import MVFBSDEJ.PaperSpec.Sec3Rem34
import MVFBSDEJ.PaperSpec.Sec3Remarks
import MVFBSDEJ.PaperSpec.Sec3Space
import MVFBSDEJ.PaperSpec.Sec3SpaceNorm
import MVFBSDEJ.PaperSpec.Sec3Stability
import MVFBSDEJ.PaperSpec.Sec3Uniqueness
import MVFBSDEJ.PaperSpec.Sec3UniquenessLip
import MVFBSDEJ.PaperSpec.Sec4
import MVFBSDEJ.PaperSpec.Sec4BDG
import MVFBSDEJ.PaperSpec.Sec4BackwardYoung
import MVFBSDEJ.PaperSpec.Sec4BrownianPoisson
import MVFBSDEJ.PaperSpec.Sec4Coeff
import MVFBSDEJ.PaperSpec.Sec4Continuation
import MVFBSDEJ.PaperSpec.Sec4Contraction
import MVFBSDEJ.PaperSpec.Sec4Difference
import MVFBSDEJ.PaperSpec.Sec4Estimates
import MVFBSDEJ.PaperSpec.Sec4Frozen
import MVFBSDEJ.PaperSpec.Sec4Horizon
import MVFBSDEJ.PaperSpec.Sec4LocalMartingales
import MVFBSDEJ.PaperSpec.Sec4ProofSteps
import MVFBSDEJ.PaperSpec.Sec4Small
import MVFBSDEJ.PaperSpec.Sec4Supremum
import MVFBSDEJ.PaperSpec.Sec5
import MVFBSDEJ.PaperSpec.Sec5Brownian
import MVFBSDEJ.PaperSpec.Sec5BrownianReduction
import MVFBSDEJ.PaperSpec.Sec5Dealer
import MVFBSDEJ.PaperSpec.Sec5DealerActive
import MVFBSDEJ.PaperSpec.Sec5FreeLaw
import MVFBSDEJ.PaperSpec.Sec5Preamble
import MVFBSDEJ.PaperSpec.Sec5Sharp
import MVFBSDEJ.PaperSpec.Setting

/-!
# The statements of the paper

Each result of the well-posedness paper at `1f67672` as a proposition written from its text.
`MVFBSDEJ.Acceptance` holds their proofs, and `acceptance/claims.json` maps each claim of the
manuscript to its proposition.
-/
