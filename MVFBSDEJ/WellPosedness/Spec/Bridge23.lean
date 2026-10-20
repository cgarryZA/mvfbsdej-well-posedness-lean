/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Spec.Assumptions

/-!
# Assumption 2.3 and the measurability (2.3) in the forms the proofs consume

The interior half of Assumption 2.3, quantified over pairs of elements of the diagonal `𝒟_t`, is
`DiagonalLipschitzH` with the same constant, and the terminal half (2.6) is `TerminalLipschitz`.
The contraction steps of the proofs use `DiagonalLipschitz`, the interior bound with the
2-Wasserstein distance of the maximum of the four channel norms of `H`. As
`w2P ≤ w2H ≤ 2 w2P`, the interior bound with the constant `L` gives `DiagonalLipschitz` with the
constant `2L`, and `DiagonalLipschitz` with the constant `L` gives the interior bound with `L`.

The measurability (2.3) is `CoeffBorelW2` for `b, σ, h, f` together with the Borel measurability
of `g` on `ℝⁿ × P₂(ℝⁿ)`. It gives the Borel measurability of every section `x ↦ g(x, ρ)`, since
`ℝⁿ` and `P₂(ℝⁿ)` are second countable, and `CoeffBorel`.

## Main statements

* `lipInterior_iff_diagonalLipschitzH`, `lipTerminal_iff_terminalLipschitz` — the two halves of
  Assumption 2.3 with the same constant.
* `assumption23_iff` — Assumption 2.3 as `0 ≤ L`, `DiagonalLipschitzH` and `TerminalLipschitz`.
* `LipInterior.diagonalLipschitz_two_mul` — the interior bound with `L` gives
  `DiagonalLipschitz` with `2L`.
* `LipInterior.of_diagonalLipschitz` — `DiagonalLipschitz` with `L` gives the interior bound
  with `L`.
* `jointBorel_iff` — (2.3) as `CoeffBorelW2` and the Borel measurability of `g`.
* `JointBorel.measurable_g_section` — every section `x ↦ g(x, ρ)` is Borel measurable.
-/

open MeasureTheory Filter MVFBSDEJ.Law

namespace MVFBSDEJ.WellPosedness.Spec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-! ### Assumption 2.3 -/

section Lipschitz

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T L : ℝ} {C : Coeffs ν n m d}

/-- **The interior half of Assumption 2.3 is `DiagonalLipschitzH`**, with the same constant. -/
theorem lipInterior_iff_diagonalLipschitzH :
    LipInterior ℱ P T L C ↔ DiagonalLipschitzH ℱ P T L C :=
  diagonalLipschitzH_iff_diagonalInputs.symm

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The terminal half (2.6) of Assumption 2.3 is `TerminalLipschitz`**, with the same
constant. -/
theorem lipTerminal_iff_terminalLipschitz
    {g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)} :
    LipTerminal ℱ P T L g ↔ TerminalLipschitz ℱ P T L g :=
  Iff.rfl

/-- **Assumption 2.3 in the consumed form**: `L ≥ 0`, `DiagonalLipschitzH` and
`TerminalLipschitz`, with the same constant. -/
theorem assumption23_iff :
    Assumption23 ℱ P T L C
      ↔ 0 ≤ L ∧ DiagonalLipschitzH ℱ P T L C ∧ TerminalLipschitz ℱ P T L C.g :=
  ⟨fun h => ⟨h.nonneg, lipInterior_iff_diagonalLipschitzH.mp h.interior, h.terminal⟩,
    fun h => ⟨h.1, lipInterior_iff_diagonalLipschitzH.mpr h.2.1, h.2.2⟩⟩

/-- **The interior bound with the constant `L` gives `DiagonalLipschitz` with `2L`**, since
`w2H ≤ 2 w2P`. -/
theorem LipInterior.diagonalLipschitz_two_mul (h : LipInterior ℱ P T L C) :
    DiagonalLipschitz ℱ P T (2 * L) C :=
  (lipInterior_iff_diagonalLipschitzH.mp h).diagonalLipschitz

/-- **`DiagonalLipschitz` with the constant `L` gives the interior bound with `L`**, since
`w2P ≤ w2H`. -/
theorem LipInterior.of_diagonalLipschitz (h : DiagonalLipschitz ℱ P T L C) :
    LipInterior ℱ P T L C :=
  lipInterior_iff_diagonalLipschitzH.mpr h.diagonalLipschitzH

end Lipschitz

/-! ### The measurability (2.3) -/

section Borel

variable {T : ℝ} {C : Coeffs ν n m d}

/-- **(2.3) is `CoeffBorelW2` together with the Borel measurability of `g`** on
`ℝⁿ × P₂(ℝⁿ)`. -/
theorem jointBorel_iff :
    JointBorel T C ↔ CoeffBorelW2 T C
      ∧ Measurable[borel (EuclideanSpace ℝ (Fin n) × P2W (EuclideanSpace ℝ (Fin n))),
          borel (EuclideanSpace ℝ (Fin m))] fun p => C.g p.1 p.2.toP2 :=
  ⟨fun h => ⟨⟨h.b_meas, h.σ_meas, h.h_meas, h.f_meas⟩, h.g_meas⟩,
    fun h => ⟨h.1.b_meas, h.1.σ_meas, h.1.h_meas, h.1.f_meas, h.2⟩⟩

namespace JointBorel

/-- **Under (2.3) every section `x ↦ g(x, ρ)` is Borel measurable**, the Borel σ-algebra of
`ℝⁿ × P₂(ℝⁿ)` being the product of those of the factors. -/
theorem measurable_g_section (h : JointBorel T C) (ρ : P2 (EuclideanSpace ℝ (Fin n))) :
    Measurable fun x => C.g x ρ := by
  have hg := h.g_meas
  rw [← BorelSpace.measurable_eq (α := EuclideanSpace ℝ (Fin m)),
    ← BorelSpace.measurable_eq
      (α := EuclideanSpace ℝ (Fin n) × P2W (EuclideanSpace ℝ (Fin n)))] at hg
  exact hg.comp (measurable_id.prodMk (measurable_const (a := ρ.toP2W)))

end JointBorel

end Borel

end MVFBSDEJ.WellPosedness.Spec
