/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Robustness.MarginPerturb
import MVFBSDEJ.WellPosedness.Robustness.LawPerturb
import MVFBSDEJ.WellPosedness.Robustness.Regular
import MVFBSDEJ.WellPosedness.Existence.GlobalLipschitzH

/-!
# Corollary 3.6: robustness of the assumptions

Let `m = n`, and let the baseline system `C = (b₀, σ₀, h₀, f₀, g)` satisfy Assumption 2.2,
Assumption 2.3 along the diagonal with the Hilbert-norm `W₂`, and Assumption 2.5 with a coupling
matrix `G` and a margin `c_diss > 0` in the unweighted form (2.13). Let the perturbation
`p = (p_b, p_σ, p_h, p_f)` satisfy the origin integrability of Assumption 2.2, the diagonal
Lipschitz bound of Assumption 2.3 and (3.4) with a constant `c_pert < c_diss`. Then the perturbed
system `C.perturb p = (b₀ + p_b, σ₀ + p_σ, h₀ + p_h, f₀ + p_f, g)` satisfies Assumptions 2.2,
2.3 and 2.5 with the same `G, α, β₁, β₂`, the interior Lipschitz constants adding, and margin
`c_diss − c_pert` in (2.13).

## Main statements

* `perturb_assumptions` — the perturbed system satisfies Assumptions 2.2, 2.3 and 2.5 with margin
  `c_diss − c_pert`.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.System LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T L₀ Lₚ α β₁ β₂ cdiss cpert : ℝ}
  {G : Matrix (Fin n) (Fin n) ℝ} {C p : Coeffs ν n n d} {ξ₀ : Fin n → Ω → ℝ}

/-- **Corollary 3.6, the assumptions.** Let `m = n`, let the baseline `C` satisfy Assumption 2.2,
Assumption 2.3 along the diagonal with constant `L₀` and the Hilbert-norm `W₂`, and Assumption
2.5 with admissible constants `α, β₁, β₂`, the interior inequality with a margin `c_diss > 0` in
the unweighted form (2.13). Let the perturbation `p` satisfy Assumption 2.2, Assumption 2.3 along
the diagonal with constant `L_p`, and (3.4) with a constant `c_pert < c_diss`. Then the perturbed
system satisfies Assumption 2.2; Assumption 2.3 with the constant `L₀ + L_p` in the interior and
`L₀` at the terminal time; and Assumption 2.5 with the same `G, α, β₁, β₂`, the interior
inequality with the margin `c_diss − c_pert > 0` in (2.13). -/
theorem perturb_assumptions {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (horig : CoeffOrigin T C) (hL : DiagonalLipschitzH ℱ P T L₀ C)
    (hLT : TerminalLipschitz ℱ P T L₀ C.g) (hconst : Constants n n α β₁ β₂)
    (hM : DiagonalMonotoneMargin ℱ P T G β₁ β₂ cdiss C) (hcdiss : 0 < cdiss)
    (hMT : TerminalMonotone ℱ P T G α C.g) (horigp : CoeffOrigin T p)
    (hLp : DiagonalLipschitzH ℱ P T Lₚ p) (hpair : DiagonalPairingBound ℱ P T G cpert p)
    (hc : cpert < cdiss) :
    CoeffOrigin T (C.perturb p) ∧ DiagonalLipschitzH ℱ P T (L₀ + Lₚ) (C.perturb p)
      ∧ TerminalLipschitz ℱ P T L₀ (C.perturb p).g
      ∧ DiagonalMonotoneMargin ℱ P T G β₁ β₂ (cdiss - cpert) (C.perturb p)
      ∧ 0 < cdiss - cpert ∧ DiagonalMonotone ℱ P T G β₁ β₂ (C.perturb p)
      ∧ TerminalMonotone ℱ P T G α (C.perturb p).g :=
  ⟨coeffOrigin_perturb horig horigp, hL.perturb hLp, hLT.perturb,
    hM.perturb hcdiss hconst.β₁_nonneg hconst.β₂_nonneg hpair, sub_pos.mpr hc,
    hM.diagonalMonotone_perturb hcdiss hconst.β₁_nonneg hconst.β₂_nonneg hpair hc.le,
    hMT.perturb⟩

end MVFBSDEJ.WellPosedness.Existence
