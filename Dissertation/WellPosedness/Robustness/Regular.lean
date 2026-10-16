/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Robustness.Perturb
import Dissertation.WellPosedness.Existence.CoeffBorelW2
import Dissertation.WellPosedness.Existence.OriginBound
import Dissertation.WellPosedness.System.DiagonalLipschitzH

/-!
# Regularity of a perturbed system

The proof of Corollary 3.6 of the well-posedness paper opens with: origin values add in `L²` and
Lipschitz constants add, so the perturbed system `(b₀ + p_b, σ₀ + p_σ, h₀ + p_h, f₀ + p_f, g)`
satisfies Assumptions 2.2–2.3. For Assumption 2.2 the origin values of the perturbed system are
the sums of those of the baseline and of the perturbation. For Assumption 2.3 along the diagonal,
with the Hilbert-norm `W₂`, the triangle inequality in each channel gives the constant `L₀ + L_p`;
the terminal function is the baseline's, with its constant.

The coefficients of the perturbed system are the sums of those of the baseline and of the
perturbation, so the joint Borel measurability (2.3) with the Hilbert-norm `W₂` on `P₂(H)`,
`CoeffBorelW2`, of the baseline and of the perturbation gives that of the perturbed system.

## Main statements

* `coeffOrigin_perturb` — Assumption 2.2 for the perturbed system.
* `DiagonalLipschitzH.perturb` — Assumption 2.3, interior, with the constant `L₀ + L_p`.
* `TerminalLipschitz.perturb` — Assumption 2.3, terminal, with the baseline's constant.
* `TerminalLipschitz.mono` — Assumption 2.3, terminal, at a larger constant.
* `CoeffBorelW2.perturb` — (2.3) for the perturbed system.
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.Existence

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ} {C p : Coeffs ν n m d}

/-! ### Assumption 2.2 -/

/-- **Assumption 2.2 for the perturbed system**: its origin values are the sums of those of the
baseline and of the perturbation, square integrable in time when both are. -/
theorem coeffOrigin_perturb {T : ℝ} (hC : CoeffOrigin T C) (hp : CoeffOrigin T p) :
    CoeffOrigin T (C.perturb p) where
  b_memLp := hC.b_memLp.add hp.b_memLp
  σ_memLp := hC.σ_memLp.add hp.σ_memLp
  h_memLp := hC.h_memLp.add hp.h_memLp
  f_memLp := hC.f_memLp.add hp.f_memLp

/-! ### Assumption 2.3 -/

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T L L' L₀ Lₚ : ℝ}

/-- **Assumption 2.3, interior, for the perturbed system**: Lipschitz constants add, `L₀ + L_p`,
along the diagonal with the Hilbert-norm `W₂`. -/
theorem DiagonalLipschitzH.perturb (hC : DiagonalLipschitzH ℱ P T L₀ C)
    (hp : DiagonalLipschitzH ℱ P T Lₚ p) : DiagonalLipschitzH ℱ P T (L₀ + Lₚ) (C.perturb p) := by
  filter_upwards [hC, hp] with t hCt hpt Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  filter_upwards [hCt Θ Θ' hΘ hΘ' hΘ2 hΘ2', hpt Θ Θ' hΘ hΘ' hΘ2 hΘ2'] with ω h1 h2
  simp only [Coeffs.perturb]
  have eb := dist_add_add_le (C.b t (Θ ω) (lawP2 P Θ)) (p.b t (Θ ω) (lawP2 P Θ))
    (C.b t (Θ' ω) (lawP2 P Θ')) (p.b t (Θ' ω) (lawP2 P Θ'))
  have eσ := dist_add_add_le (C.σ t (Θ ω) (lawP2 P Θ)) (p.σ t (Θ ω) (lawP2 P Θ))
    (C.σ t (Θ' ω) (lawP2 P Θ')) (p.σ t (Θ' ω) (lawP2 P Θ'))
  have eh := dist_add_add_le (C.h t (Θ ω) (lawP2 P Θ)) (p.h t (Θ ω) (lawP2 P Θ))
    (C.h t (Θ' ω) (lawP2 P Θ')) (p.h t (Θ' ω) (lawP2 P Θ'))
  have ef := dist_add_add_le (C.f t (Θ ω) (lawP2 P Θ)) (p.f t (Θ ω) (lawP2 P Θ))
    (C.f t (Θ' ω) (lawP2 P Θ')) (p.f t (Θ' ω) (lawP2 P Θ'))
  simp only [dist_eq_norm] at eb eσ eh ef
  rw [add_mul]
  linarith

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **Assumption 2.3, terminal, for the perturbed system**: the terminal function is the
baseline's. -/
theorem TerminalLipschitz.perturb (hC : TerminalLipschitz ℱ P T L₀ C.g) :
    TerminalLipschitz ℱ P T L₀ (C.perturb p).g :=
  hC

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- Assumption 2.3, terminal, holds at every larger constant. -/
theorem TerminalLipschitz.mono
    {g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)}
    (h : TerminalLipschitz ℱ P T L g) (hL : L ≤ L') : TerminalLipschitz ℱ P T L' g := by
  intro ξ ξ' hξ hξ' hξ2 hξ2'
  filter_upwards [h ξ ξ' hξ hξ' hξ2 hξ2'] with ω hω
  have h0 : 0 ≤ ‖ξ ω - ξ' ω‖ + w2P (lawP2 P ξ) (lawP2 P ξ') := by
    have := w2P_nonneg (lawP2 P ξ) (lawP2 P ξ')
    positivity
  exact hω.trans (mul_le_mul_of_nonneg_right hL h0)

/-! ### (2.3) -/

variable {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ} {γ₀ γp : Fin n → ℝ → Ω → E → ℝ}

/-- The sum of two maps measurable into the Borel σ-algebra of a space with measurable addition is
measurable. -/
private theorem measurable_borel_add {α W : Type*} {mα : MeasurableSpace α} [TopologicalSpace W]
    [MeasurableSpace W] [BorelSpace W] [Add W] [MeasurableAdd₂ W] {f g : α → W}
    (hf : Measurable[mα, borel W] f) (hg : Measurable[mα, borel W] g) :
    Measurable[mα, borel W] fun a => f a + g a := by
  rw [← BorelSpace.measurable_eq (α := W)] at hf hg ⊢
  exact hf.add hg

/-- **(2.3) with the Hilbert-norm `W₂` for the perturbed system**, from (2.3) for the baseline and
for the perturbation. -/
theorem _root_.Dissertation.WellPosedness.Existence.CoeffBorelW2.perturb {T : ℝ}
    (hC : CoeffBorelW2 T C) (hp : CoeffBorelW2 T p) : CoeffBorelW2 T (C.perturb p) where
  b_meas := measurable_borel_add hC.b_meas hp.b_meas
  σ_meas := measurable_borel_add hC.σ_meas hp.σ_meas
  h_meas := measurable_borel_add hC.h_meas hp.h_meas
  f_meas := measurable_borel_add hC.f_meas hp.f_meas

end Dissertation.WellPosedness.System
