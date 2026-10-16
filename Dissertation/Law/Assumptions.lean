/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.P2
import Dissertation.Law.Wasserstein
import Dissertation.WellPosedness.Assumptions

/-!
# The Lipschitz assumptions with the law distance taken to be `w2`

The interior and terminal Lipschitz conditions on the coefficients of a mean-field
forward–backward system are stated over an abstract law type carrying a real-valued distance
function. Taking that type to be the laws of finite second moment `P2 H` on a normed space `H`
and that function to be the 2-Wasserstein distance `w2P`, the square root of a finite squared
distance on `P2 H`, gives the two conditions below.

## Main definitions

* `Dissertation.Law.LipschitzCoefficientsP2`: the interior Lipschitz condition on the four
  coefficient functions, with law argument a law of finite second moment on `H` and law distance
  `w2`.
* `Dissertation.Law.LipschitzTerminalP2`: the terminal Lipschitz condition, with terminal law
  argument a law of finite second moment on `H` and law distance `w2`.
-/

namespace Dissertation.Law

open MeasureTheory

variable {H HX HY HZX HZY HUX HUY : Type*} [NormedAddCommGroup H] [MeasurableSpace H]
  [NormedAddCommGroup HX] [InnerProductSpace ℝ HX] [CompleteSpace HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [CompleteSpace HY]
  [NormedAddCommGroup HZX] [InnerProductSpace ℝ HZX] [CompleteSpace HZX]
  [NormedAddCommGroup HZY] [InnerProductSpace ℝ HZY] [CompleteSpace HZY]
  [NormedAddCommGroup HUX] [InnerProductSpace ℝ HUX] [CompleteSpace HUX]
  [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY] [CompleteSpace HUY]

/-- The interior Lipschitz condition on the four coefficient functions, with law argument a law
of finite second moment on `H` and law distance `w2`. -/
abbrev LipschitzCoefficientsP2 (L : ℝ)
    (b : ℝ → WellPosedness.Tuple HX HY HZY HUY → P2 H → HX)
    (σ : ℝ → WellPosedness.Tuple HX HY HZY HUY → P2 H → HZX)
    (h : ℝ → WellPosedness.Tuple HX HY HZY HUY → P2 H → HUX)
    (f : ℝ → WellPosedness.Tuple HX HY HZY HUY → P2 H → HY) : Prop :=
  WellPosedness.LipschitzCoefficients L (w2P (E := H)) b σ h f

/-- The terminal Lipschitz condition, with terminal law argument a law of finite second moment on
`H` and law distance `w2`. -/
abbrev LipschitzTerminalP2 (L : ℝ) (g : HX → P2 H → HY) : Prop :=
  WellPosedness.LipschitzTerminal L (w2P (E := H)) g

end Dissertation.Law
