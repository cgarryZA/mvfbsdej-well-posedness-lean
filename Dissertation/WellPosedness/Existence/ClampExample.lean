/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.ClampAffine
import Dissertation.WellPosedness.Existence.GlobalEnl
import Dissertation.WellPosedness.System.PaperUniquenessInt
import LevyStochCalc.Driver.GaussianInitial

/-!
# The affine system with the drift (3.6): Assumptions 2.2, 2.3 and (2.3)

Replacing the drift `−β₁ y` of the affine system of Example 5.1(i) at `n = m = 1` by the drift
(3.6) of Proposition 3.8 gives the coefficient system `clampAffineCoeffs` on
`H = ℝ × ℝ × ℝ^{1×d} × L²(ν; ℝ)`,

`b = −β₁ y + ε g₀(y − m_Y(μ))`, `σ = σ_c − β₁ z`, `h = h_c − β₁ u`, `f = β₂ x`, `g(x, ρ) = x`,

with `g₀(r) = max(−1, min(1, r))` and `m_Y(μ) = ∫_H y μ(dθ)` the `Y`-marginal mean. For
`β₁, β₂, ε ≥ 0` it satisfies

* Assumption 2.2, its coefficients being independent of the time;
* Assumption 2.3 at `L = max{β₁ + ε, β₂, 1}`, with the Hilbert-norm `W₂` on `P₂(H)` in the
  interior, since the drift (3.6) is Lipschitz in the state and in the law with constant
  `β₁ + ε`;
* the joint Borel measurability (2.3): the mean `m_Y` is `1`-Lipschitz for `W₂`, so the drift is
  continuous on `[0, T] × H × P₂(H)`, and the other coefficients are continuous in the tuple and
  independent of the time and the law.

Assumption 2.5 along the diagonal, at `G = 1` with the constants `(β₁ − ε, β₂)`, is
`diagonalMonotone_clampAffine`.

## Main statements

* `norm_clampAffine_sub_le` — the interior bound of Assumption 2.3, pointwise.
* `diagonalLipschitzH_and_terminalLipschitz_clampAffine` — Assumption 2.3 at
  `L = max{β₁ + ε, β₂, 1}`.
* `coeffOrigin_clampAffine` — Assumption 2.2.
* `lipschitzWith_meanY`, `continuous_clampVec`, `coeffBorelW2_clampAffine` — (2.3).
-/

open MeasureTheory Filter ProbabilityTheory Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System Dissertation.WellPosedness.Enlarged LevyStochCalc
  LevyStochCalc.BSDEJ.Solves

universe u v w

/-! ### Assumptions 2.2 and 2.3 -/

section Lipschitz

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {d : ℕ} {β₁ β₂ ε : ℝ}
  {σc : EuclideanSpace ℝ (Fin 1 × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν}

/-- **Assumption 2.3, interior, pointwise, for the system with the drift (3.6)**: for
`β₁, β₂, ε ≥ 0`, at every time, pair of points and pair of laws,
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf|
  ≤ max{β₁ + ε, β₂} (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + W₂(μ, μ'))`,
with `W₂` the 2-Wasserstein distance of the Hilbert norm. -/
theorem norm_clampAffine_sub_le (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hε : 0 ≤ ε) (t : ℝ)
    (θ θ' : TupleH ν 1 1 d) (μ μ' : P2 (TupleH ν 1 1 d)) :
    ‖(clampAffineCoeffs β₁ β₂ ε σc hc).b t θ μ - (clampAffineCoeffs β₁ β₂ ε σc hc).b t θ' μ'‖
        + ‖(clampAffineCoeffs β₁ β₂ ε σc hc).σ t θ μ
          - (clampAffineCoeffs β₁ β₂ ε σc hc).σ t θ' μ'‖
        + ‖(clampAffineCoeffs β₁ β₂ ε σc hc).h t θ μ
          - (clampAffineCoeffs β₁ β₂ ε σc hc).h t θ' μ'‖
        + ‖(clampAffineCoeffs β₁ β₂ ε σc hc).f t θ μ
          - (clampAffineCoeffs β₁ β₂ ε σc hc).f t θ' μ'‖
      ≤ max (β₁ + ε) β₂ * (tupleNorm (θ - θ') + w2H μ μ') := by
  have hb := norm_clampDrift_sub_le hβ₁ hε t θ θ' μ μ'
  have e₂ : σc - β₁ • θ.2.2.1 - (σc - β₁ • θ'.2.2.1) = -(β₁ • (θ.2.2.1 - θ'.2.2.1)) := by
    rw [smul_sub]; abel
  have e₃ : hc - β₁ • θ.2.2.2 - (hc - β₁ • θ'.2.2.2) = -(β₁ • (θ.2.2.2 - θ'.2.2.2)) := by
    rw [smul_sub]; abel
  simp only [clampAffineCoeffs, affineCoeffs, e₂, e₃, ← smul_sub, norm_neg, norm_smul,
    Real.norm_of_nonneg hβ₁, Real.norm_of_nonneg hβ₂]
  have htn : tupleNorm (θ - θ')
      = ‖θ.1 - θ'.1‖ + ‖θ.2.1 - θ'.2.1‖ + ‖θ.2.2.1 - θ'.2.2.1‖ + ‖θ.2.2.2 - θ'.2.2.2‖ := rfl
  rw [htn]
  have hM₁ : β₁ + ε ≤ max (β₁ + ε) β₂ := le_max_left _ _
  have hM₀ : β₁ ≤ max (β₁ + ε) β₂ := by linarith
  have hM₂ : β₂ ≤ max (β₁ + ε) β₂ := le_max_right _ _
  have h1 := mul_le_mul_of_nonneg_right hM₁
    (add_nonneg (norm_nonneg (θ.2.1 - θ'.2.1)) (w2H_nonneg μ μ'))
  have h2 := mul_le_mul_of_nonneg_right hM₀ (norm_nonneg (θ.2.2.1 - θ'.2.2.1))
  have h3 := mul_le_mul_of_nonneg_right hM₀ (norm_nonneg (θ.2.2.2 - θ'.2.2.2))
  have h4 := mul_le_mul_of_nonneg_right hM₂ (norm_nonneg (θ.1 - θ'.1))
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Assumption 2.3 for the system with the drift (3.6) at `L = max{β₁ + ε, β₂, 1}`**, for
`β₁, β₂, ε ≥ 0`: the interior bound along the diagonal with the Hilbert-norm `W₂` on `P₂(H)`,
and the terminal bound (2.6). -/
theorem diagonalLipschitzH_and_terminalLipschitz_clampAffine
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hε : 0 ≤ ε) :
    DiagonalLipschitzH ℱ P T (max (max (β₁ + ε) β₂) 1) (clampAffineCoeffs β₁ β₂ ε σc hc)
      ∧ TerminalLipschitz ℱ P T (max (max (β₁ + ε) β₂) 1)
        (clampAffineCoeffs β₁ β₂ ε σc hc).g :=
  ⟨Eventually.of_forall fun t Θ Θ' _ _ _ _ => Eventually.of_forall fun ω =>
    (norm_clampAffine_sub_le hβ₁ hβ₂ hε t (Θ ω) (Θ' ω) _ _).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (add_nonneg (by unfold tupleNorm; positivity) (w2H_nonneg _ _))),
    terminalLipschitz_affine (β₁ := β₁) (β₂ := β₂) (σc := σc) (hc := hc) (le_max_right _ 1)⟩

/-- **Assumption 2.2 for the system with the drift (3.6)**: its coefficients are independent of
the time, so its origin values are constant. -/
theorem coeffOrigin_clampAffine (T : ℝ) : CoeffOrigin T (clampAffineCoeffs β₁ β₂ ε σc hc) :=
  originIntegrable_const T _ _ _ _

end Lipschitz

/-! ### Joint measurability -/

section Measurability

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {d : ℕ} {β₁ β₂ ε : ℝ}
  {σc : EuclideanSpace ℝ (Fin 1 × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν}

/-- The `Y`-marginal mean `m_Y` is `1`-Lipschitz on `P₂(H)` with the Hilbert-norm `W₂`. -/
theorem lipschitzWith_meanY : LipschitzWith 1 fun μ : TupleP2WH ν 1 1 d => meanY μ.toP2 :=
  LipschitzWith.of_dist_le_mul fun μ μ' => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm]
    exact norm_meanY_sub_le_w2H μ.toP2 μ'.toP2

/-- The clamp `g₀` on `ℝ¹` is continuous. -/
theorem continuous_clampVec : Continuous clampVec :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    continuous_clamp01.comp ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)))

/-- **(2.3) for the system with the drift (3.6)**: its coefficients are Borel measurable on
`[0, T] × H × P₂(H)`, with the Hilbert-norm `W₂` on `P₂(H)`. The drift is continuous there, the
`Y`-marginal mean being `1`-Lipschitz; the other coefficients are continuous in the tuple and
independent of the time and the law. -/
theorem coeffBorelW2_clampAffine (T : ℝ) : CoeffBorelW2 T (clampAffineCoeffs β₁ β₂ ε σc hc) where
  b_meas := by
    refine Continuous.borel_measurable ?_
    change Continuous fun p : Set.Icc (0 : ℝ) T × TupleH ν 1 1 d × TupleP2WH ν 1 1 d =>
      -(β₁ • p.2.1.2.1) + ε • clampVec (p.2.1.2.1 - meanY p.2.2.toP2)
    have hy : Continuous fun p : Set.Icc (0 : ℝ) T × TupleH ν 1 1 d × TupleP2WH ν 1 1 d =>
        p.2.1.2.1 :=
      continuous_fst.comp (continuous_snd.comp (continuous_fst.comp continuous_snd))
    have hm : Continuous fun p : Set.Icc (0 : ℝ) T × TupleH ν 1 1 d × TupleP2WH ν 1 1 d =>
        meanY p.2.2.toP2 :=
      lipschitzWith_meanY.continuous.comp (continuous_snd.comp continuous_snd)
    exact (hy.const_smul β₁).neg.add ((continuous_clampVec.comp (hy.sub hm)).const_smul ε)
  σ_meas := measurable_borelW2_of_measurable (ψ := (clampAffineCoeffs β₁ β₂ ε σc hc).σ) (by
    simp only [clampAffineCoeffs, affineCoeffs]; fun_prop)
  h_meas := measurable_borelW2_of_measurable (ψ := (clampAffineCoeffs β₁ β₂ ε σc hc).h) (by
    simp only [clampAffineCoeffs, affineCoeffs]; fun_prop)
  f_meas := measurable_borelW2_of_measurable (ψ := (clampAffineCoeffs β₁ β₂ ε σc hc).f) (by
    simp only [clampAffineCoeffs, affineCoeffs]; fun_prop)

end Measurability

end Dissertation.WellPosedness.Existence
