/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Robustness.Corollary
import Dissertation.WellPosedness.Existence.AffineExample

/-!
# Margins and perturbations of Example 5.1(i)

The affine system of Example 5.1(i) with constants `β₁ + c, β₂ + c`, `c > 0`,

`b = −(β₁ + c) y`, `σ = σ_c − (β₁ + c) z`, `h = h_c − (β₁ + c) u`, `f = (β₂ + c) x`, `g(x, ρ) = x`,

satisfies (2.7) with equality at `G = I` and its own constants, so, as Remark 2.11 records, it
satisfies (2.13) with the constants `β₁, β₂` and margin `c`; it is a baseline for Corollary 3.6.
Equivalently, Example 5.1(i) with constants `β₁, β₂` carries every margin `c` with the reduced
constants `β₁ − c, β₂ − c` in the unweighted form (2.13).
Two perturbations are treated:

* the feedback `p_b = ε y`, `p_σ = ε z`, `p_h = ε u`, `p_f = 0` for `ε ≥ 0`, which raises the
  interior pairing by `ε (|δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)})` and so satisfies (3.4) with
  `c_pert = ε`; it is the affine system with constants `−ε, 0` and origin values `0`;
* a constant perturbation of the diffusion and jump coefficients, `p_σ = σ'`, `p_h = h'`, which
  is independent of the tuple and satisfies (3.5) with every `L_p ≥ 0`.

## Main statements

* `dissipation_affine_add` — the right-hand side of (2.7) at `G = I` with the constants raised by
  `c`.
* `diagonalMonotoneMargin_affine` — (2.13) for Example 5.1(i) with margin `c`.
* `diagonalMonotoneMargin_affine_sub` — Example 5.1(i) with constants `β₁, β₂` carries every
  margin `c` in (2.13), with the reduced constants `β₁ − c, β₂ − c`.
* `lipschitzCoefficientsP2_affine_feedback`, `diagonalPairingBound_affine_feedback` — the
  feedback perturbation satisfies Assumption 2.3 and (3.4) with `c_pert = ε`.
* `tupleIndep_affine_const`, `diagonalLawLipschitzH_affine_const` — the constant perturbation is
  independent of the tuple and satisfies (3.5).
-/

open MeasureTheory Filter WithLp Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

section Margin

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n d : ℕ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}

/-- **The right-hand side of (2.7) at `G = I` with the constants raised by `c`** is that at
`β₁, β₂` minus `c (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)})`. -/
theorem dissipation_affine_add (β₁ β₂ c : ℝ) (C : Coeffs ν n n d) (t : ℝ)
    (θ θ' : TupleH ν n n d) (μ μ' : P2 (TupleH ν n n d)) :
    dissipation (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν) (β₁ + c) (β₂ + c)
        (diagDiff C t θ θ' μ μ')
      = dissipation (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν) β₁ β₂
          (diagDiff C t θ θ' μ μ') - c * channelSq (θ - θ') := by
  simp only [dissipation, diagDiff, GX_one, GZ_one, GU_one, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_apply, channelSq, Prod.fst_sub, Prod.snd_sub]
  ring

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **(2.13) for Example 5.1(i)**: the affine system with constants `β₁ + c, β₂ + c` satisfies
the interior inequality at `G = I` with the constants `β₁, β₂` and margin `c`, with equality. -/
theorem diagonalMonotoneMargin_affine (β₁ β₂ c : ℝ) :
    DiagonalMonotoneMargin ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) β₁ β₂ c
      (affineCoeffs (β₁ + c) (β₂ + c) σc hc) := by
  refine Eventually.of_forall fun t Θ Θ' _ _ hΘ hΘ' => le_of_eq ?_
  rw [← integral_const_mul, ← integral_sub
    (integrable_dissipation_diagDiff _ _ _ _ _ _ t _ _ hΘ hΘ')
    ((integrable_channelSq_sub hΘ hΘ').const_mul c)]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  dsimp only
  rw [interiorPairing_affine, dissipation_affine_add]

/-- **Every margin of Example 5.1(i), unweighted (2.13).** For every `c`, the affine system with
constants `β₁, β₂` satisfies the interior inequality at `G = I` with the reduced constants
`β₁ − c, β₂ − c` and margin `c`, with equality. -/
theorem diagonalMonotoneMargin_affine_sub (β₁ β₂ c : ℝ) :
    DiagonalMonotoneMargin ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) (β₁ - c) (β₂ - c) c
      (affineCoeffs β₁ β₂ σc hc) := by
  simpa only [sub_add_cancel] using
    diagonalMonotoneMargin_affine (ℱ := ℱ) (P := P) (T := T) (σc := σc) (hc := hc)
      (β₁ - c) (β₂ - c) c

end Margin

section Feedback

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n d : ℕ} {ε : ℝ}

/-- **Assumption 2.3, interior, pointwise, for the feedback perturbation** `p_b = ε y`,
`p_σ = ε z`, `p_h = ε u`, `p_f = 0`, with constant `ε ≥ 0`. -/
theorem lipschitzCoefficientsP2_affine_feedback (hε : 0 ≤ ε) :
    LipschitzCoefficientsP2 ε (affineCoeffs (ν := ν) (n := n) (d := d) (-ε) 0 0 0).b
      (affineCoeffs (ν := ν) (-ε) 0 0 0).σ (affineCoeffs (ν := ν) (-ε) 0 0 0).h
      (affineCoeffs (ν := ν) (-ε) 0 0 0).f := by
  intro t θ θ' μ μ'
  have e₁ : -((-ε) • θ.2.1) - -((-ε) • θ'.2.1) = ε • (θ.2.1 - θ'.2.1) := by
    rw [smul_sub, neg_smul, neg_smul]; abel
  have e₂ : (0 : EuclideanSpace ℝ (Fin n × Fin d)) - (-ε) • θ.2.2.1
      - (0 - (-ε) • θ'.2.2.1) = ε • (θ.2.2.1 - θ'.2.2.1) := by
    rw [smul_sub, neg_smul, neg_smul]; abel
  have e₃ : (0 : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) - (-ε) • θ.2.2.2
      - (0 - (-ε) • θ'.2.2.2) = ε • (θ.2.2.2 - θ'.2.2.2) := by
    rw [smul_sub, neg_smul, neg_smul]; abel
  simp only [affineCoeffs, e₁, e₂, e₃, zero_smul, sub_self, norm_zero, add_zero, norm_smul,
    Real.norm_of_nonneg hε]
  have htn : tupleNorm (θ - θ')
      = ‖θ.1 - θ'.1‖ + ‖θ.2.1 - θ'.2.1‖ + ‖θ.2.2.1 - θ'.2.2.1‖ + ‖θ.2.2.2 - θ'.2.2.2‖ := rfl
  rw [htn]
  have hw := w2P_nonneg μ μ'
  nlinarith [norm_nonneg (θ.1 - θ'.1), norm_nonneg (θ.2.1 - θ'.2.1),
    norm_nonneg (θ.2.2.1 - θ'.2.2.1), norm_nonneg (θ.2.2.2 - θ'.2.2.2)]

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **(3.4) for the feedback perturbation** `p_b = ε y`, `p_σ = ε z`, `p_h = ε u`, `p_f = 0` at
`G = I`, with `c_pert = ε ≥ 0`: its pairing is `ε (|δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)})`. -/
theorem diagonalPairingBound_affine_feedback (hε : 0 ≤ ε) :
    DiagonalPairingBound ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) ε
      (affineCoeffs (ν := ν) (d := d) (-ε) 0 0 0) := by
  refine Eventually.of_forall fun t Θ Θ' _ _ hΘ hΘ' => ?_
  have hi := integrable_dissipation_diagDiff (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1)
    (GU 1 ν) (-ε) 0 (affineCoeffs (-ε) 0 0 0) t (lawP2 P Θ) (lawP2 P Θ') hΘ hΘ'
  have e : (fun ω => interiorPairing (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν)
      (diagDiff (affineCoeffs (-ε) 0 0 0) t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')))
      = fun ω => dissipation (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν) (-ε) 0
        (diagDiff (affineCoeffs (-ε) 0 0 0) t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) :=
    funext fun ω => interiorPairing_affine t _ _ _ _
  rw [e]
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  refine integral_mono hi ((integrable_channelSq_sub hΘ hΘ').const_mul ε) fun ω => ?_
  simp only [dissipation, diagDiff, GX_one, GZ_one, GU_one, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_apply, channelSq, Prod.fst_sub, Prod.snd_sub]
  nlinarith [sq_nonneg ‖(Θ ω).1 - (Θ' ω).1‖]

end Feedback

section Const

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n d : ℕ}
  {σ' : EuclideanSpace ℝ (Fin n × Fin d)} {h' : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}

/-- The constant perturbation `p_b = 0`, `p_σ = σ'`, `p_h = h'`, `p_f = 0` is independent of the
tuple. -/
theorem tupleIndep_affine_const : (affineCoeffs (ν := ν) 0 0 σ' h').TupleIndep :=
  ⟨fun _ _ _ _ => by simp [affineCoeffs], fun _ _ _ _ => by simp [affineCoeffs],
    fun _ _ _ _ => by simp [affineCoeffs], fun _ _ _ _ => by simp [affineCoeffs]⟩

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **(3.5) for the constant perturbation**, with every constant `L_p ≥ 0`: its differences
vanish. -/
theorem diagonalLawLipschitzH_affine_const {Lₚ : ℝ} (hLp : 0 ≤ Lₚ) :
    DiagonalLawLipschitzH ℱ P T Lₚ (affineCoeffs (ν := ν) 0 0 σ' h') := by
  refine Eventually.of_forall fun t Θ Θ' _ _ _ _ => Eventually.of_forall fun ω => ?_
  simp only [affineCoeffs, zero_smul, neg_zero, sub_zero, sub_self, norm_zero, add_zero]
  exact mul_nonneg hLp (w2H_nonneg _ _)

end Const

end Dissertation.WellPosedness.Existence
