/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Robustness.Perturb
import MVFBSDEJ.WellPosedness.Robustness.Margin

/-!
# A dissipativity margin survives a perturbation of smaller pairing

Let the baseline `C` satisfy the interior inequality (2.7) with a margin `c_diss > 0`, in the
unweighted form (2.13) or the weighted form (2.12), and let the perturbation `p` satisfy (3.4)
with constant `c_pert` in the same quantity. Along any two diagonal inputs the pairing of the
perturbed system `C.perturb p` splits into the baseline bracket and the perturbation bracket,
both integrable (the baseline one by its positive margin), and the right-hand side of (2.7) and
the quantity of the margin are shared. So, off the union of the two null sets of times, with
`I_C` the pairing of the system `C`,

`𝔼 I_{C.perturb p} = 𝔼 I_C + 𝔼 I_p`
`  ≤ −β₁ 𝔼[…] − β₂ 𝔼|G δX|² − c_diss 𝔼 Q + c_pert 𝔼 Q`,

which is the same inequality with margin `c_diss − c_pert`. For `c_pert ≤ c_diss` this margin is
nonnegative and the perturbed system satisfies Assumption 2.5, interior, with the baseline's
`G, β₁, β₂`. The terminal half of Assumption 2.5 concerns only `G` and `g`, both unchanged.

## Main statements

* `integral_le_sub_mul_of_add` — the integral bookkeeping of the splitting.
* `DiagonalMonotoneMargin.perturb`, `DiagonalMonotoneMargin.diagonalMonotone_perturb` — the
  unweighted margin (2.13) survives, with margin `c_diss − c_pert`, and gives Assumption 2.5,
  interior.
* `DiagonalMonotoneWeightedMargin.perturb`,
  `DiagonalMonotoneWeightedMargin.diagonalMonotone_perturb` — the same for the weighted margin
  (2.12).
* `TerminalMonotone.perturb` — the terminal half of Assumption 2.5 is unchanged.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

/-- **The integral bookkeeping of the splitting.** If `pair = pair₀ + pairₚ` with both summands
integrable, `∫ pair₀ ≤ ∫ diss − c₀ ∫ Q` and `∫ pairₚ ≤ cₚ ∫ Q`, then
`∫ pair ≤ ∫ diss − (c₀ − cₚ) ∫ Q`. -/
theorem integral_le_sub_mul_of_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {pair pair₀ pairₚ diss Q : Ω → ℝ} {c₀ cₚ : ℝ} (hsplit : ∀ ω, pair ω = pair₀ ω + pairₚ ω)
    (h₀ : Integrable pair₀ P) (hₚ : Integrable pairₚ P)
    (hb : ∫ ω, pair₀ ω ∂P ≤ ∫ ω, diss ω ∂P - c₀ * ∫ ω, Q ω ∂P)
    (hp : ∫ ω, pairₚ ω ∂P ≤ cₚ * ∫ ω, Q ω ∂P) :
    ∫ ω, pair ω ∂P ≤ ∫ ω, diss ω ∂P - (c₀ - cₚ) * ∫ ω, Q ω ∂P := by
  have e : ∫ ω, pair ω ∂P = ∫ ω, pair₀ ω ∂P + ∫ ω, pairₚ ω ∂P := by
    rw [← integral_add h₀ hₚ]
    exact integral_congr_ae (ae_of_all _ hsplit)
  rw [e]
  linarith

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}
  {Ω : Type*} [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T α β₁ β₂ cdiss cpert : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C p : Coeffs ν n m d}

/-- **The unweighted margin survives a perturbation** (Corollary 3.6): if the baseline satisfies
(2.13) with margin `c_diss > 0` and constants `β₁, β₂ ≥ 0`, and the perturbation satisfies (3.4)
with constant `c_pert`, the perturbed system satisfies (2.13) with the same `G, β₁, β₂` and margin
`c_diss − c_pert`. -/
theorem DiagonalMonotoneMargin.perturb (hC : DiagonalMonotoneMargin ℱ P T G β₁ β₂ cdiss C)
    (hcdiss : 0 < cdiss) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hp : DiagonalPairingBound ℱ P T G cpert p) :
    DiagonalMonotoneMargin ℱ P T G β₁ β₂ (cdiss - cpert) (C.perturb p) := by
  filter_upwards [hC, hC.integrable hcdiss hβ₁ hβ₂, hp] with t ht hi hpt Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  obtain ⟨hpi, hpb⟩ := hpt Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  exact integral_le_sub_mul_of_add
    (fun ω => interiorPairing_diagDiff_perturb _ _ _ C p t _ _ _ _)
    (hi Θ Θ' hΘ hΘ' hΘ2 hΘ2') hpi (ht Θ Θ' hΘ hΘ' hΘ2 hΘ2') hpb

/-- **A perturbation of smaller pairing keeps Assumption 2.5, interior** (Corollary 3.6): under
the hypotheses of `DiagonalMonotoneMargin.perturb` with `c_pert ≤ c_diss`, the perturbed system
satisfies (2.7) with the baseline's `G, β₁, β₂`. -/
theorem DiagonalMonotoneMargin.diagonalMonotone_perturb
    (hC : DiagonalMonotoneMargin ℱ P T G β₁ β₂ cdiss C) (hcdiss : 0 < cdiss) (hβ₁ : 0 ≤ β₁)
    (hβ₂ : 0 ≤ β₂) (hp : DiagonalPairingBound ℱ P T G cpert p) (hc : cpert ≤ cdiss) :
    DiagonalMonotone ℱ P T G β₁ β₂ (C.perturb p) :=
  (hC.perturb hcdiss hβ₁ hβ₂ hp).diagonalMonotone (sub_nonneg.mpr hc)

/-- **The weighted margin survives a perturbation** (Remark 3.7): if the baseline satisfies (2.12)
with margin `c_diss > 0` and constants `β₁, β₂ ≥ 0`, and the perturbation satisfies (3.4) in the
weighted quantity with constant `c_pert`, the perturbed system satisfies (2.12) with the same
`G, β₁, β₂` and margin `c_diss − c_pert`. -/
theorem DiagonalMonotoneWeightedMargin.perturb
    (hC : DiagonalMonotoneWeightedMargin ℱ P T G β₁ β₂ cdiss C) (hcdiss : 0 < cdiss)
    (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hp : DiagonalWeightedPairingBound ℱ P T G cpert p) :
    DiagonalMonotoneWeightedMargin ℱ P T G β₁ β₂ (cdiss - cpert) (C.perturb p) := by
  filter_upwards [hC, hC.integrable hcdiss hβ₁ hβ₂, hp] with t ht hi hpt Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  obtain ⟨hpi, hpb⟩ := hpt Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  exact integral_le_sub_mul_of_add
    (fun ω => interiorPairing_diagDiff_perturb _ _ _ C p t _ _ _ _)
    (hi Θ Θ' hΘ hΘ' hΘ2 hΘ2') hpi (ht Θ Θ' hΘ hΘ' hΘ2 hΘ2') hpb

/-- **A perturbation of smaller weighted pairing keeps Assumption 2.5, interior**
(Remark 3.7): under the hypotheses of `DiagonalMonotoneWeightedMargin.perturb` with
`c_pert ≤ c_diss`, the perturbed system satisfies (2.7) with the baseline's `G, β₁, β₂`. -/
theorem DiagonalMonotoneWeightedMargin.diagonalMonotone_perturb
    (hC : DiagonalMonotoneWeightedMargin ℱ P T G β₁ β₂ cdiss C) (hcdiss : 0 < cdiss)
    (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hp : DiagonalWeightedPairingBound ℱ P T G cpert p)
    (hc : cpert ≤ cdiss) : DiagonalMonotone ℱ P T G β₁ β₂ (C.perturb p) :=
  (hC.perturb hcdiss hβ₁ hβ₂ hp).diagonalMonotone (sub_nonneg.mpr hc)

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The terminal half of Assumption 2.5 is unchanged by a perturbation**, whose terminal
function is the baseline's. -/
theorem TerminalMonotone.perturb (h : TerminalMonotone ℱ P T G α C.g) :
    TerminalMonotone ℱ P T G α (C.perturb p).g :=
  h

end MVFBSDEJ.WellPosedness.System
