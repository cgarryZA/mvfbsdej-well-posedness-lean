/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Existence.GlobalEnl
import MVFBSDEJ.WellPosedness.Robustness.Corollary
import MVFBSDEJ.WellPosedness.Spec.Bridge22
import MVFBSDEJ.WellPosedness.Spec.CorollaryHyps
import MVFBSDEJ.WellPosedness.Spec.Thm31
import MVFBSDEJ.WellPosedness.Spec.Thm33

/-!
# Corollary 3.6: the assumptions of the perturbed system

Corollary 3.6 of the well-posedness paper: let `m = n`, let the baseline system `C` with initial
datum `ξ₀` satisfy Assumptions 2.2–2.5 with the margin `c_diss > 0` in the unweighted form
(2.13), and let the perturbation `p` satisfy the origin integrability and the interior diagonal
Lipschitz condition of Assumptions 2.2–2.3 and the pairing bound (3.4) with `c_pert ≥ 0`. If
`c_pert < c_diss`, the perturbed system `C.perturb p`, with the same initial datum `ξ₀`,
satisfies Assumptions 2.2–2.5 with the same `G, α, β₁, β₂` and margin `c_diss − c_pert`, and by
Theorems 3.1, 3.3 and 3.5 it is well posed.

This file states the first of these conclusions over a general filtration, with the hypotheses
of the paper and the measurability (2.3) of the perturbed system. The Lipschitz constant of the
perturbed system is `L₀ + L_p`.

## Main statements

* `perturb_assumptions_of_assumptions` — the perturbed system satisfies Assumptions 2.2, 2.3
  (constant `L₀ + L_p`), 2.5 (same `G, α, β₁, β₂`) and (2.13) with margin `c_diss − c_pert`.
-/

open MeasureTheory Filter ProbabilityTheory Matrix
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.Spec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability LevyStochCalc

section Assumptions

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n d : ℕ} {P : Measure Ω}
  [IsProbabilityMeasure P] {T L₀ Lₚ α β₁ β₂ cdiss cpert : ℝ} {G : Matrix (Fin n) (Fin n) ℝ}
  {C p : Coeffs ν n n d} {ξ₀ : Ω → EuclideanSpace ℝ (Fin n)}

/-- **Corollary 3.6, the assumptions of the perturbed system.** Let `m = n`; let the baseline `C`
with initial datum `ξ₀` satisfy Assumption 2.2, Assumption 2.3 with a constant `L₀`, Assumption
2.5 with `G` and constants `α, β₁, β₂`, and (2.13) with a margin `c_diss > 0`; let the
perturbation `p` satisfy the origin values of Assumption 2.2, the interior bound of Assumption 2.3
with a constant `L_p ≥ 0` and (3.4) with a constant `c_pert < c_diss`; and let the perturbed system
satisfy the measurability (2.3). Then `C.perturb p` with initial datum `ξ₀` satisfies Assumption
2.2, Assumption 2.3 with the constant `L₀ + L_p`, Assumption 2.5 with the same `G, α, β₁, β₂`, and
(2.13) with the margin `c_diss − c_pert > 0`. -/
theorem perturb_assumptions_of_assumptions {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (h22 : Assumption22 ℱ P T C ξ₀) (h23 : Assumption23 ℱ P T L₀ C)
    (h25 : Assumption25 ℱ P T G α β₁ β₂ C) (h213 : Margin213 ℱ P T G β₁ β₂ cdiss C)
    (hcdiss : 0 < cdiss) (hJp : JointBorel T (C.perturb p)) (horigp : OriginValues T p)
    (hLp : LipInterior ℱ P T Lₚ p) (hLp0 : 0 ≤ Lₚ) (h34 : PairingBound34 ℱ P T G cpert p)
    (hc : cpert < cdiss) :
    Assumption22 ℱ P T (C.perturb p) ξ₀ ∧ Assumption23 ℱ P T (L₀ + Lₚ) (C.perturb p)
      ∧ Assumption25 ℱ P T G α β₁ β₂ (C.perturb p)
      ∧ Margin213 ℱ P T G β₁ β₂ (cdiss - cpert) (C.perturb p) ∧ 0 < cdiss - cpert := by
  obtain ⟨horig', hLH, hLT', hMm, hpos, hM, hMT⟩ := perturb_assumptions
    (originValues_iff_coeffOrigin.mp h22.origin)
    (lipInterior_iff_diagonalLipschitzH.mp h23.interior)
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal) h25.constants
    h213.diagonalMonotoneMargin hcdiss h25.terminalMonotone
    (originValues_iff_coeffOrigin.mp horigp) (lipInterior_iff_diagonalLipschitzH.mp hLp)
    h34.diagonalPairingBound hc
  have h23' : Assumption23 ℱ P T (L₀ + Lₚ) (C.perturb p) :=
    ⟨add_nonneg h23.nonneg hLp0, lipInterior_iff_diagonalLipschitzH.mpr hLH,
      lipTerminal_iff_terminalLipschitz.mpr (hLT'.mono (le_add_of_nonneg_right hLp0))⟩
  exact ⟨⟨h22.initial_meas, h22.initial_memLp, originValues_iff_coeffOrigin.mpr horig'⟩, h23',
    Assumption25.of_monotone hJp h23' h25.constants hM hMT,
    (margin213_iff hpos h25.constants.β₁_nonneg h25.constants.β₂_nonneg).mpr hMm, hpos⟩

end Assumptions

end MVFBSDEJ.WellPosedness.Spec
