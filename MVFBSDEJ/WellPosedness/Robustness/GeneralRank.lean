/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Robustness.MarginPerturb
import MVFBSDEJ.WellPosedness.Robustness.Regular
import MVFBSDEJ.WellPosedness.Existence.GlobalLipschitzH

/-!
# Remark 3.7: robustness of well-posedness at general rank

Remark 3.7: the restriction `m = n` of Corollary 3.6 reflects only the unweighted bookkeeping of
(2.13). Run in the weighted quantity `Q = |Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)} + |G δX|²` of
(2.12), the same splitting of the interior pairing into a baseline and a perturbation bracket
works for arbitrary `m, n`, when the margin of the baseline and the bound (3.4) of the
perturbation are both recorded in `Q`: the perturbed system satisfies Assumptions 2.2–2.5 with
the same `G, α, β₁, β₂` and margin `c_diss − c_pert` in (2.12).

## Main statements

* `perturb_assumptions_weighted` — the perturbed system satisfies Assumptions 2.2–2.5 with margin
  `c_diss − c_pert` in (2.12).
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.System LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T L₀ Lₚ α β₁ β₂ cdiss cpert : ℝ}
  {G : Matrix (Fin m) (Fin n) ℝ} {C p : Coeffs ν n m d} {ξ₀ : Fin n → Ω → ℝ}

/-- **Remark 3.7, the assumptions.** Let the baseline `C` satisfy Assumption 2.2, Assumption 2.3
along the diagonal with constant `L₀` and the Hilbert-norm `W₂`, and Assumption 2.5 with
admissible constants `α, β₁, β₂`, the interior inequality with a margin `c_diss > 0` in the
weighted form (2.12). Let the perturbation `p` satisfy Assumption 2.2, Assumption 2.3 along the
diagonal with constant `L_p`, and (3.4) in the weighted quantity of (2.12) with a constant
`c_pert < c_diss`. Then the perturbed system satisfies Assumption 2.2; Assumption 2.3 with the
constant `L₀ + L_p` in the interior and `L₀` at the terminal time; and Assumption 2.5 with the
same `G, α, β₁, β₂`, the interior inequality with the margin `c_diss − c_pert > 0` in (2.12). -/
theorem perturb_assumptions_weighted {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (horig : CoeffOrigin T C) (hL : DiagonalLipschitzH ℱ P T L₀ C)
    (hLT : TerminalLipschitz ℱ P T L₀ C.g) (hconst : Constants n m α β₁ β₂)
    (hM : DiagonalMonotoneWeightedMargin ℱ P T G β₁ β₂ cdiss C) (hcdiss : 0 < cdiss)
    (hMT : TerminalMonotone ℱ P T G α C.g) (horigp : CoeffOrigin T p)
    (hLp : DiagonalLipschitzH ℱ P T Lₚ p) (hpair : DiagonalWeightedPairingBound ℱ P T G cpert p)
    (hc : cpert < cdiss) :
    CoeffOrigin T (C.perturb p) ∧ DiagonalLipschitzH ℱ P T (L₀ + Lₚ) (C.perturb p)
      ∧ TerminalLipschitz ℱ P T L₀ (C.perturb p).g
      ∧ DiagonalMonotoneWeightedMargin ℱ P T G β₁ β₂ (cdiss - cpert) (C.perturb p)
      ∧ 0 < cdiss - cpert ∧ DiagonalMonotone ℱ P T G β₁ β₂ (C.perturb p)
      ∧ TerminalMonotone ℱ P T G α (C.perturb p).g :=
  ⟨coeffOrigin_perturb horig horigp, hL.perturb hLp, hLT.perturb,
    hM.perturb hcdiss hconst.β₁_nonneg hconst.β₂_nonneg hpair, sub_pos.mpr hc,
    hM.diagonalMonotone_perturb hcdiss hconst.β₁_nonneg hconst.β₂_nonneg hpair hc.le,
    hMT.perturb⟩

end MVFBSDEJ.WellPosedness.Existence
