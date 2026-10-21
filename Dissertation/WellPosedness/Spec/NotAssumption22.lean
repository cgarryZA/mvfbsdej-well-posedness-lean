/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Spec.Bridge22
import Dissertation.WellPosedness.Spec.Bridge25
import Dissertation.WellPosedness.Examples.SingularDrift
import Dissertation.WellPosedness.Examples.MeanFieldMonotone
import Dissertation.WellPosedness.Existence.GlobalEnl
import LevyStochCalc.Driver.GaussianInitial

/-!
# A system failing Assumption 2.2: the singular drift

The system `Dissertation.WellPosedness.System.singularCoeffs`, with `n = m = 1` and any `d`,

`b(t, x, y, z, u) = t^{-1/2} − y`, `σ = −z`, `h = −u`, `f = 0`, `g(x, ρ) = x`,

is the affine system of Example 5.1(i) with `β₁ = 1`, `β₂ = 0`, `σ_c = 0`, `h_c = 0` and the
deterministic drift `t ↦ t^{-1/2}` added. Over any filtered probability space and at every horizon
`T > 0` it satisfies the measurability (2.3), Assumption 2.3 with `L = 1` and Assumption 2.5 with
`G = 1`, `α = 1`, `β₁ = 1`, `β₂ = 0`, and it fails Assumption 2.2 for every initial datum: the
origin value `b(t, 0, δ₀) = t^{-1/2}` is not square integrable on `(0, T)`.

A deterministic drift measurable in time keeps (2.3), since it adds a measurable function of the
time to the drift, and it cancels in every difference of coefficients, which keeps Assumptions 2.3
and 2.5.

## Main statements

* `measurable_singularDrift` — the drift `t ↦ t^{-1/2}` is measurable.
* `coeffBorelW2_addDrift` — a measurable deterministic drift keeps
  `Dissertation.WellPosedness.Existence.CoeffBorelW2`.
* `jointBorel_singularCoeffs`, `assumption23_singularCoeffs`, `assumption25_singularCoeffs` —
  (2.3), Assumption 2.3 and Assumption 2.5.
* `not_assumption22_singularCoeffs` — Assumption 2.2 fails for every initial datum.
-/

open MeasureTheory Filter Dissertation.Law Matrix

namespace Dissertation.WellPosedness.Spec

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-- The drift `t ↦ t^{-1/2}` is measurable. -/
theorem measurable_singularDrift : Measurable singularDrift :=
  measurable_toLp_of_forall (x := fun (_ : Fin 1) (t : ℝ) => (Real.sqrt t)⁻¹)
    fun _ => Real.continuous_sqrt.measurable.inv

/-- **A measurable deterministic drift keeps `CoeffBorelW2`**: `(t, θ, μ) ↦ c(t) + b(t, θ, μ)` is
Borel measurable on `[0, T] × H × P₂(H)` when `b` is and `c` is measurable. -/
theorem coeffBorelW2_addDrift {T : ℝ} {C : Coeffs ν n m d} (hC : CoeffBorelW2 T C)
    {c : ℝ → EuclideanSpace ℝ (Fin n)} (hc : Measurable c) :
    CoeffBorelW2 T (C.addDrift c) where
  b_meas := by
    have hb := hC.b_meas
    rw [← BorelSpace.measurable_eq (α := EuclideanSpace ℝ (Fin n)),
      ← BorelSpace.measurable_eq
        (α := Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d)] at hb ⊢
    exact (hc.comp (measurable_subtype_coe.comp measurable_fst)).add hb
  σ_meas := hC.σ_meas
  h_meas := hC.h_meas
  f_meas := hC.f_meas

/-- **(2.3) for the singular drift.** -/
theorem jointBorel_singularCoeffs (T : ℝ) : JointBorel T (singularCoeffs (ν := ν) (d := d)) :=
  jointBorel_iff.mpr ⟨coeffBorelW2_addDrift (coeffBorelW2_affine T) measurable_singularDrift,
    continuous_fst.borel_measurable⟩

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **Assumption 2.3 for the singular drift**, with `L = 1`. -/
theorem assumption23_singularCoeffs : Assumption23 ℱ P T 1 (singularCoeffs (ν := ν) (d := d)) :=
  ⟨zero_le_one, LipInterior.of_diagonalLipschitz diagonalLipschitz_singularCoeffs,
    terminalLipschitz_singularCoeffs⟩

/-- **Assumption 2.5 for the singular drift**, with `G = 1`, `α = 1`, `β₁ = 1`, `β₂ = 0`. -/
theorem assumption25_singularCoeffs :
    Assumption25 ℱ P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 0 (singularCoeffs (ν := ν) (d := d)) :=
  Assumption25.of_monotone (jointBorel_singularCoeffs T) assumption23_singularCoeffs
    constants_singularCoeffs diagonalMonotone_singularCoeffs terminalMonotone_singularCoeffs

omit [IsProbabilityMeasure P] in
/-- **Assumption 2.2 fails for the singular drift**, for every initial datum and every horizon
`T > 0`: the origin value `b(t, 0, δ₀) = t^{-1/2}` is not square integrable on `(0, T)`. -/
theorem not_assumption22_singularCoeffs (hT : 0 < T) (ξ₀ : Ω → EuclideanSpace ℝ (Fin 1)) :
    ¬ Assumption22 ℱ P T (singularCoeffs (ν := ν) (d := d)) ξ₀ := fun h =>
  not_coeffOrigin_singularCoeffs hT (originValues_iff_coeffOrigin.mp h.origin)

end Dissertation.WellPosedness.Spec
