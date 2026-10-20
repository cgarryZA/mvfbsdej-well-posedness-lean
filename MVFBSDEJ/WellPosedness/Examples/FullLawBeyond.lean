/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Law.Mixture
import MVFBSDEJ.Law.TupleMarginal

/-!
# Mixtures and Dirac masses on the tuple space

Laws of finite second moment on the tuple space `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)`: the
`U`-marginal of a mixture is the mixture of the `U`-marginals, the `U`-marginal of a Dirac mass is
the Dirac mass at the `U`-channel, and the 2-Wasserstein distance of two Dirac masses, for the
Hilbert norm of `H`, is the Hilbert norm of the difference of their points.

## Main statements

* `margU_mix`, `margU_dirac` — the `U`-marginal of a mixture and of a Dirac mass.
* `w2H_dirac_dirac` — the Hilbert-norm distance of two Dirac masses.
-/

open MeasureTheory MVFBSDEJ.Law

namespace MVFBSDEJ.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The `U`-marginal of a mixture is the mixture of the `U`-marginals. -/
theorem margU_mix (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (μ μ' : P2 (TupleH ν n m d)) :
    (P2.mix t ht μ μ').margU = P2.mix t ht μ.margU μ'.margU := by
  refine P2.ext_law ?_
  rw [margU_law, P2.mix_law, P2.mix_law, Measure.map_add _ _ measurable_projUH, Measure.map_smul,
    Measure.map_smul, margU_law, margU_law]

/-- The `U`-marginal of a Dirac mass is the Dirac mass at the `U`-channel. -/
theorem margU_dirac (θ : TupleH ν n m d) : (P2.dirac θ).margU = P2.dirac θ.2.2.2 :=
  P2.ext_law (Measure.map_dirac' measurable_projUH θ)

/-- The Hilbert-norm distance of two Dirac masses is the Hilbert norm of the difference of their
points. -/
theorem w2H_dirac_dirac (θ θ' : TupleH ν n m d) :
    w2H (P2.dirac θ) (P2.dirac θ') = ‖toL2 (θ - θ')‖ := by
  rw [w2H, P2.dirac, P2.dirac]
  simp only
  rw [Measure.map_dirac' measurable_toL2, Measure.map_dirac' measurable_toL2, toL2_sub]
  exact w2_dirac_dirac (toL2 θ) (toL2 θ')

end MVFBSDEJ.WellPosedness.System
