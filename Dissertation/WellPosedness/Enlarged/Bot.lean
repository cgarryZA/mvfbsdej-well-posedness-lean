/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Enlarged.Driver
import Dissertation.WellPosedness.Existence.TerminalRep

/-!
# The trivial initial enlargement

For `𝒢₀ = ⊥` the initially enlarged joint filtration of a Lévy driver is its joint natural
filtration `ℱ`, and the enlarged filtration is the augmented joint filtration `augJoint D`: at a
time `t ≥ 0` the germ field `ℱ₊_t` lies in the augmentation of `ℱ_t`
(`LevyStochCalc.Driver.LevyDriver.filtration_rightCont_le_aug`), so augmenting `ℱ₊_t` and
augmenting `ℱ_t` give the same σ-algebra, and before time `0` both filtrations are frozen at
their time-`0` fields.

## Main statements

* `initJoint_bot` — `initJoint ⊥ D bot_le = D.filtration`.
* `enlJoint_bot` — `enlJoint ⊥ D bot_le = augJoint D`.
-/

open MeasureTheory ProbabilityTheory

namespace Dissertation.WellPosedness.Enlarged

open LevyStochCalc LevyStochCalc.Probability

universe u v w

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)

/-- The joint filtration enlarged by the trivial σ-algebra is the joint filtration. -/
theorem initJoint_bot : initJoint ⊥ D bot_le = D.filtration :=
  MeasureTheory.Filtration.ext (funext fun t => sup_bot_eq (D.filtration t))

/-- The enlarged filtration for the trivial σ-algebra is the augmented joint filtration. -/
theorem enlJoint_bot : enlJoint ⊥ D bot_le = BSDEJ.Solves.augJoint D := by
  change Brownian.augFiltration (initJoint ⊥ D bot_le).rightCont P
    = Brownian.augFiltration D.filtration P
  rw [initJoint_bot]
  refine MeasureTheory.Filtration.ext (funext fun t => ?_)
  change aug (D.filtration.rightCont (max t 0)) mΩ P = aug (D.filtration (max t 0)) mΩ P
  exact le_antisymm (aug_le_of_le_aug (D.filtration_rightCont_le_aug (le_max_right t 0)))
    (aug_mono (D.filtration.le_rightCont (max t 0)))

end Dissertation.WellPosedness.Enlarged
