/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.ExpectedVsPointwiseModel
import Dissertation.WellPosedness.Existence.AffineExample

/-!
# The drift (3.6) in the affine system: Assumption 2.5 along the diagonal

Replacing the drift `−β₁ y` of the affine system of Example 5.1(i) at `n = m = 1` by the drift
(3.6) of Proposition 3.8 gives the coefficient system

`b = −β₁ y + ε g₀(y − m_Y(μ))`, `σ = σ_c − β₁ z`, `h = h_c − β₁ u`, `f = β₂ x`, `g(x, ρ) = x`

on `H = ℝ × ℝ × ℝ^{1×d} × L²(ν; ℝ)`. With `G = 1` its interior pairing is
`⟨δb, δY⟩ − β₁ |δZ|²_F − β₂ |δX|² − β₁ ‖δU‖²_{L²(ν)}`, so (3.7) gives the interior inequality
(2.7) of Assumption 2.5 along the diagonal with the constants `(β₁ − ε, β₂)`, for every
`ε ≥ 0`, from square integrability of the two tuples alone.

## Main definitions

* `clampAffineCoeffs` — the affine system of Example 5.1(i) with the drift (3.6).

## Main statements

* `interiorPairing_clampAffine` — the interior pairing at `G = 1`.
* `integrable_norm_sub_sq_of_lipschitz` — a channel difference of two square-integrable tuples
  has integrable squared norm.
* `diagonalMonotone_clampAffine` — Assumption 2.5, interior, along the diagonal, with
  `G = 1` and the constants `(β₁ − ε, β₂)`.
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {d : ℕ}

/-- The affine system of Example 5.1(i) at `n = m = 1` with the drift (3.6): for
`θ = (x, y, z, u)`, `b = −β₁ y + ε g₀(y − m_Y(μ))`, `σ = σ_c − β₁ z`, `h = h_c − β₁ u`,
`f = β₂ x`, and `g(x, ρ) = x`. -/
noncomputable def clampAffineCoeffs (β₁ β₂ ε : ℝ) (σc : EuclideanSpace ℝ (Fin 1 × Fin d))
    (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) : Coeffs ν 1 1 d :=
  { affineCoeffs β₁ β₂ σc hc with b := clampDrift β₁ ε }

variable {β₁ β₂ ε : ℝ} {σc : EuclideanSpace ℝ (Fin 1 × Fin d)}
  {hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν}

/-- **The interior pairing of the system with the drift (3.6)** at `G = 1`:
`⟨δb, δY⟩ − β₁ |δZ|²_F − β₂ |δX|² − β₁ ‖δU‖²_{L²(ν)}`. -/
theorem interiorPairing_clampAffine (t : ℝ) (θ θ' : TupleH ν 1 1 d)
    (μ μ' : P2 (TupleH ν 1 1 d)) :
    interiorPairing (GX (1 : Matrix (Fin 1) (Fin 1) ℝ)) (GZ 1) (GU 1 ν)
        (diagDiff (clampAffineCoeffs β₁ β₂ ε σc hc) t θ θ' μ μ')
      = inner ℝ (clampDrift β₁ ε t θ μ - clampDrift β₁ ε t θ' μ') (θ.2.1 - θ'.2.1)
        - β₁ * ‖θ.2.2.1 - θ'.2.2.1‖ ^ 2 - β₂ * ‖θ.1 - θ'.1‖ ^ 2
        - β₁ * ‖θ.2.2.2 - θ'.2.2.2‖ ^ 2 := by
  have e₂ : σc - β₁ • θ.2.2.1 - (σc - β₁ • θ'.2.2.1) = -(β₁ • (θ.2.2.1 - θ'.2.2.1)) := by
    rw [smul_sub]; abel
  have e₃ : hc - β₁ • θ.2.2.2 - (hc - β₁ • θ'.2.2.2) = -(β₁ • (θ.2.2.2 - θ'.2.2.2)) := by
    rw [smul_sub]; abel
  simp only [interiorPairing, diagDiff, clampAffineCoeffs, affineCoeffs, e₂, e₃, ← smul_sub,
    GX_one, GZ_one, GU_one, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply,
    inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

/-- The dissipation of (2.7) at `G = 1` and the constants `(β₁ − ε, β₂)`. -/
theorem dissipation_clampAffine (t : ℝ) (θ θ' : TupleH ν 1 1 d)
    (μ μ' : P2 (TupleH ν 1 1 d)) :
    dissipation (GX (1 : Matrix (Fin 1) (Fin 1) ℝ)) (GZ 1) (GU 1 ν) (β₁ - ε) β₂
        (diagDiff (clampAffineCoeffs β₁ β₂ ε σc hc) t θ θ' μ μ')
      = -(β₁ - ε) * ‖θ.2.1 - θ'.2.1‖ ^ 2
        + (-(β₁ - ε) * (‖θ.2.2.1 - θ'.2.2.1‖ ^ 2 + ‖θ.2.2.2 - θ'.2.2.2‖ ^ 2)
          - β₂ * ‖θ.1 - θ'.1‖ ^ 2) := by
  simp only [dissipation, diagDiff, GX_one, GZ_one, GU_one, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_apply]
  ring

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A continuous map of the tuple space that does not increase distances sends two
square-integrable tuples to maps whose difference has integrable squared norm. -/
theorem integrable_norm_sub_sq_of_lipschitz {F : Type*} [NormedAddCommGroup F]
    {π : TupleH ν 1 1 d → F} (hπc : Continuous π) (hπ : ∀ θ θ', ‖π θ - π θ'‖ ≤ ‖θ - θ'‖)
    {Θ Θ' : Ω → TupleH ν 1 1 d} (hΘ : MemLp Θ 2 P) (hΘ' : MemLp Θ' 2 P) :
    Integrable (fun ω => ‖π (Θ ω) - π (Θ' ω)‖ ^ 2) P := by
  have h : MemLp (fun ω => π (Θ ω) - π (Θ' ω)) 2 P :=
    (hΘ.sub hΘ').of_le ((hπc.comp_aestronglyMeasurable hΘ.aestronglyMeasurable).sub
      (hπc.comp_aestronglyMeasurable hΘ'.aestronglyMeasurable))
      (ae_of_all _ fun ω => by simpa using hπ (Θ ω) (Θ' ω))
  exact h.integrable_norm_pow two_ne_zero

/-- **Assumption 2.5, interior, along the diagonal, for the affine system with the drift
(3.6)**, with `G = 1` and the constants `(β₁ − ε, β₂)`, for every `ε ≥ 0`. -/
theorem diagonalMonotone_clampAffine (hε : 0 ≤ ε) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {T : ℝ} :
    DiagonalMonotone ℱ P T (1 : Matrix (Fin 1) (Fin 1) ℝ) (β₁ - ε) β₂
      (clampAffineCoeffs β₁ β₂ ε σc hc) := by
  refine Eventually.of_forall fun t Θ Θ' _ _ hΘ hΘ' => ?_
  have iX := integrable_norm_sub_sq_of_lipschitz (π := fun θ : TupleH ν 1 1 d => θ.1)
    continuous_fst (fun θ θ' => norm_fst_le (θ - θ')) hΘ hΘ'
  have iY := integrable_norm_sub_sq_of_lipschitz (π := fun θ : TupleH ν 1 1 d => θ.2.1)
    (continuous_fst.comp continuous_snd)
    (fun θ θ' => (norm_fst_le (θ - θ').2).trans (norm_snd_le (θ - θ'))) hΘ hΘ'
  have iZ := integrable_norm_sub_sq_of_lipschitz (π := fun θ : TupleH ν 1 1 d => θ.2.2.1)
    (continuous_fst.comp (continuous_snd.comp continuous_snd))
    (fun θ θ' => ((norm_fst_le (θ - θ').2.2).trans (norm_snd_le (θ - θ').2)).trans
      (norm_snd_le (θ - θ'))) hΘ hΘ'
  have iU := integrable_norm_sub_sq_of_lipschitz (π := fun θ : TupleH ν 1 1 d => θ.2.2.2)
    (continuous_snd.comp (continuous_snd.comp continuous_snd))
    (fun θ θ' => ((norm_snd_le (θ - θ').2.2).trans (norm_snd_le (θ - θ').2)).trans
      (norm_snd_le (θ - θ'))) hΘ hΘ'
  have iI := integrable_inner_clampDrift (β₁ := β₁) (ε := ε) hΘ hΘ' t
  have iR₁ : Integrable (fun ω => -β₁ * ‖(Θ ω).2.2.1 - (Θ' ω).2.2.1‖ ^ 2
      - β₂ * ‖(Θ ω).1 - (Θ' ω).1‖ ^ 2 - β₁ * ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2) P :=
    ((iZ.const_mul _).sub (iX.const_mul _)).sub (iU.const_mul _)
  have iR₂ : Integrable (fun ω => -(β₁ - ε) * (‖(Θ ω).2.2.1 - (Θ' ω).2.2.1‖ ^ 2
      + ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2) - β₂ * ‖(Θ ω).1 - (Θ' ω).1‖ ^ 2) P :=
    ((iZ.add iU).const_mul _).sub (iX.const_mul _)
  have hpair : ∀ ω, interiorPairing (GX (1 : Matrix (Fin 1) (Fin 1) ℝ)) (GZ 1) (GU 1 ν)
      (diagDiff (clampAffineCoeffs β₁ β₂ ε σc hc) t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ'))
      = inner ℝ (clampDrift β₁ ε t (Θ ω) (lawP2 P Θ) - clampDrift β₁ ε t (Θ' ω) (lawP2 P Θ'))
          ((Θ ω).2.1 - (Θ' ω).2.1)
        + (-β₁ * ‖(Θ ω).2.2.1 - (Θ' ω).2.2.1‖ ^ 2 - β₂ * ‖(Θ ω).1 - (Θ' ω).1‖ ^ 2
          - β₁ * ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2) := fun ω => by
    rw [interiorPairing_clampAffine]; ring
  simp_rw [hpair, dissipation_clampAffine]
  rw [integral_add iI iR₁, integral_add ((iY.const_mul _)) iR₂, integral_const_mul]
  have h37 := integral_inner_clampDrift_le (β₁ := β₁) hε hΘ hΘ' t
  have hR : ∫ ω, (-β₁ * ‖(Θ ω).2.2.1 - (Θ' ω).2.2.1‖ ^ 2 - β₂ * ‖(Θ ω).1 - (Θ' ω).1‖ ^ 2
        - β₁ * ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2) ∂P
      ≤ ∫ ω, (-(β₁ - ε) * (‖(Θ ω).2.2.1 - (Θ' ω).2.2.1‖ ^ 2
        + ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖ ^ 2) - β₂ * ‖(Θ ω).1 - (Θ' ω).1‖ ^ 2) ∂P :=
    integral_mono iR₁ iR₂ fun ω => by
      nlinarith [sq_nonneg ‖(Θ ω).2.2.1 - (Θ' ω).2.2.1‖,
        sq_nonneg ‖(Θ ω).2.2.2 - (Θ' ω).2.2.2‖]
  linarith

end Dissertation.WellPosedness.Existence
