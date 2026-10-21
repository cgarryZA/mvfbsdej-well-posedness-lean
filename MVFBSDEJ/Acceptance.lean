/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Acceptance.AppA
import MVFBSDEJ.Acceptance.AppASteps
import MVFBSDEJ.Acceptance.Dealer
import MVFBSDEJ.Acceptance.Sec2
import MVFBSDEJ.Acceptance.Sec2Basics
import MVFBSDEJ.Acceptance.Sec2Remarks
import MVFBSDEJ.Acceptance.Sec3
import MVFBSDEJ.Acceptance.Sec3Complete
import MVFBSDEJ.Acceptance.Sec3GeneralRank
import MVFBSDEJ.Acceptance.Sec3Margin
import MVFBSDEJ.Acceptance.Sec3MarginContinuous
import MVFBSDEJ.Acceptance.Sec3Rem34
import MVFBSDEJ.Acceptance.Sec3Rem34Translation
import MVFBSDEJ.Acceptance.Sec3Remarks
import MVFBSDEJ.Acceptance.Sec3Space
import MVFBSDEJ.Acceptance.Sec3SpaceNorm
import MVFBSDEJ.Acceptance.Sec3Stability
import MVFBSDEJ.Acceptance.Sec3Uniqueness
import MVFBSDEJ.Acceptance.Sec3UniquenessLip
import MVFBSDEJ.Acceptance.Sec4
import MVFBSDEJ.Acceptance.Sec4BDG
import MVFBSDEJ.Acceptance.Sec4BackwardYoung
import MVFBSDEJ.Acceptance.Sec4BrownianPoisson
import MVFBSDEJ.Acceptance.Sec4Coeff
import MVFBSDEJ.Acceptance.Sec4Continuation
import MVFBSDEJ.Acceptance.Sec4Contraction
import MVFBSDEJ.Acceptance.Sec4Difference
import MVFBSDEJ.Acceptance.Sec4Estimates
import MVFBSDEJ.Acceptance.Sec4Frozen
import MVFBSDEJ.Acceptance.Sec4Horizon
import MVFBSDEJ.Acceptance.Sec4LocalMartingales
import MVFBSDEJ.Acceptance.Sec4ProofSteps
import MVFBSDEJ.Acceptance.Sec4Small
import MVFBSDEJ.Acceptance.Sec4Supremum
import MVFBSDEJ.Acceptance.Sec5
import MVFBSDEJ.Acceptance.Sec5Brownian
import MVFBSDEJ.Acceptance.Sec5BrownianReduction
import MVFBSDEJ.Acceptance.Sec5Dealer
import MVFBSDEJ.Acceptance.Sec5DealerActive
import MVFBSDEJ.Acceptance.Sec5FreeLaw
import MVFBSDEJ.Acceptance.Sec5Preamble
import MVFBSDEJ.Acceptance.Sec5Sharp
import MVFBSDEJ.Acceptance.Solution
import MVFBSDEJ.Acceptance.Witness
import MVFBSDEJ.Acceptance.WitnessContraction
import MVFBSDEJ.Acceptance.WitnessForced
import MVFBSDEJ.Acceptance.WitnessFrozen
import MVFBSDEJ.Acceptance.WitnessFrozenLam
import MVFBSDEJ.Acceptance.WitnessFrozenPair
import MVFBSDEJ.Acceptance.WitnessFullLaw
import MVFBSDEJ.Acceptance.WitnessHyp
import MVFBSDEJ.Acceptance.WitnessInfinite
import MVFBSDEJ.Acceptance.WitnessLocal
import MVFBSDEJ.Acceptance.WitnessNonzero
import MVFBSDEJ.Acceptance.WitnessPert
import MVFBSDEJ.Acceptance.WitnessRotation
import MVFBSDEJ.Acceptance.WitnessSec4

/-!
# Proofs of the statements of the paper

For each proposition `MVFBSDEJ.PaperSpec.<label>` that is proved, a theorem
`MVFBSDEJ.Acceptance.<label>` whose type is that proposition.
-/
