/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.MeanField

/-!
# Example 5.1(ii): Assumption 2.5 for the mean-field coefficients

For the coefficients `b = −2y − m_Y(μ)`, `σ = −2z − m_Z(μ)`, `h = −2u − m_U(μ)`,
`f = 2x + m_X(μ)`, `g(x, ρ) = 2x + 𝔟(ρ)` of Example 5.1(ii), with `G = 1`, the interior pairing
of (2.7) at two points `θ, θ'` and two laws `μ, μ'` is

`⟨δb, δY⟩ + ⟨δσ, δZ⟩_F − ⟨δf, δX⟩ + ⟨δh, δU⟩_{L²(ν)} = −2 |δθ|²_H − ⟨δm, δθ⟩_H`,

with `δm = ∫_H θ dμ − ∫_H θ dμ'` and `|·|_H` the Hilbert norm. Along two diagonal inputs
`(Θ, Law Θ)`, `(Θ', Law Θ')` with `Θ, Θ'` square integrable the mean difference is the
deterministic `δm = 𝔼 δΘ`, so `𝔼⟨δm, δΘ⟩_H = |𝔼 δΘ|²_H` and

`𝔼[⟨δb, δY⟩ + ⟨δσ, δZ⟩_F − ⟨δf, δX⟩ + ⟨δh, δU⟩_{L²(ν)}]
  = −2 𝔼[|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}]
    − (|𝔼 δX|² + |𝔼 δY|² + |𝔼 δZ|²_F + ‖𝔼 δU‖²_{L²(ν)})`:

each channel contributes its own mean square, so (2.7) holds with `β₁ = β₂ = 2`. In the same way
`𝔼⟨δg_T, δX_T⟩ = 2 𝔼|δX_T|² + |𝔼 δX_T|²`, and the terminal half of Assumption 2.5 holds with
`α = 2`. Only `U ∈ L²(ν)` enters, so the constants do not depend on `ν`.

## Main statements

* `interiorPairing_meanField`, `dissipation_meanField` — the pointwise pairing and dissipation.
* `integral_interiorPairing_meanField` — the expected interior pairing along the diagonal.
* `diagonalMonotone_meanField` — Assumption 2.5, interior, with `G = 1` and `β₁ = β₂ = 2`.
* `integral_inner_meanField_g` — the expected terminal pairing along the diagonal.
* `terminalMonotone_meanField` — Assumption 2.5, terminal, with `G = 1` and `α = 2`.
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n d : ℕ}

/-- The dissipation of (2.7) for Example 5.1(ii) at `G = 1` and `β₁ = β₂ = 2` is
`−2 |θ − θ'|²_H`. -/
theorem dissipation_meanField (t : ℝ) (θ θ' : TupleH ν n n d) (μ μ' : P2 (TupleH ν n n d)) :
    dissipation (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν) 2 2
        (diagDiff (meanFieldCoeffs ν n d) t θ θ' μ μ')
      = -2 * ‖toL2 (θ - θ')‖ ^ 2 := by
  rw [norm_toL2_sq]
  simp only [dissipation, diagDiff, GX_one, GZ_one, GU_one, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_apply, channelSq, Prod.fst_sub, Prod.snd_sub]
  ring

/-- **The interior pairing of Example 5.1(ii)** at `G = 1`: pointwise,
`⟨δb, δY⟩ + ⟨δσ, δZ⟩_F − ⟨δf, δX⟩ + ⟨δh, δU⟩_{L²(ν)} = −2 |δθ|²_H − ⟨δm, δθ⟩_H`, the dissipation
at `β₁ = β₂ = 2` less the Hilbert pairing of the mean difference `δm = ∫_H θ dμ − ∫_H θ dμ'` with
`δθ = θ − θ'`. -/
theorem interiorPairing_meanField (t : ℝ) (θ θ' : TupleH ν n n d) (μ μ' : P2 (TupleH ν n n d)) :
    interiorPairing (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν)
        (diagDiff (meanFieldCoeffs ν n d) t θ θ' μ μ')
      = dissipation (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν) 2 2
          (diagDiff (meanFieldCoeffs ν n d) t θ θ' μ μ')
        - inner ℝ (toL2 (tupleMean μ - tupleMean μ')) (toL2 (θ - θ')) := by
  have eb : -((2 : ℝ) • θ.2.1) - (tupleMean μ).2.1 - (-((2 : ℝ) • θ'.2.1) - (tupleMean μ').2.1)
      = -((2 : ℝ) • (θ.2.1 - θ'.2.1)) - ((tupleMean μ).2.1 - (tupleMean μ').2.1) := by
    rw [smul_sub]; abel
  have eσ : -((2 : ℝ) • θ.2.2.1) - (tupleMean μ).2.2.1
        - (-((2 : ℝ) • θ'.2.2.1) - (tupleMean μ').2.2.1)
      = -((2 : ℝ) • (θ.2.2.1 - θ'.2.2.1)) - ((tupleMean μ).2.2.1 - (tupleMean μ').2.2.1) := by
    rw [smul_sub]; abel
  have eh : -((2 : ℝ) • θ.2.2.2) - (tupleMean μ).2.2.2
        - (-((2 : ℝ) • θ'.2.2.2) - (tupleMean μ').2.2.2)
      = -((2 : ℝ) • (θ.2.2.2 - θ'.2.2.2)) - ((tupleMean μ).2.2.2 - (tupleMean μ').2.2.2) := by
    rw [smul_sub]; abel
  have ef : (2 : ℝ) • θ.1 + (tupleMean μ).1 - ((2 : ℝ) • θ'.1 + (tupleMean μ').1)
      = (2 : ℝ) • (θ.1 - θ'.1) + ((tupleMean μ).1 - (tupleMean μ').1) := by
    rw [smul_sub]; abel
  rw [dissipation_meanField, inner_toL2, norm_toL2_sq]
  simp only [interiorPairing, diagDiff, meanFieldCoeffs, eb, eσ, eh, ef, GX_one, GZ_one, GU_one,
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply, channelSq, Prod.fst_sub,
    Prod.snd_sub]
  generalize θ.1 - θ'.1 = a₁
  generalize θ.2.1 - θ'.2.1 = a₂
  generalize θ.2.2.1 - θ'.2.2.1 = a₃
  generalize θ.2.2.2 - θ'.2.2.2 = a₄
  generalize (tupleMean μ).1 - (tupleMean μ').1 = c₁
  generalize (tupleMean μ).2.1 - (tupleMean μ').2.1 = c₂
  generalize (tupleMean μ).2.2.1 - (tupleMean μ').2.2.1 = c₃
  generalize (tupleMean μ).2.2.2 - (tupleMean μ').2.2.2 = c₄
  simp only [inner_sub_left, inner_add_left, inner_neg_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  ring

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] [IsProbabilityMeasure P] in
/-- A square-integrable random tuple has a square-integrable Hilbert-norm realisation. -/
theorem memLp_toL2 {V : Ω → TupleH ν n n d} (hV : MemLp V 2 P) :
    MemLp (fun ω => toL2 (V ω)) 2 P :=
  hV.of_le_mul (c := 2) (continuous_toL2.comp_aestronglyMeasurable hV.aestronglyMeasurable)
    (ae_of_all _ fun _ => norm_toL2_le _)

/-- **The expected interior pairing of Example 5.1(ii) along the diagonal.** For
square-integrable random tuples `Θ, Θ'` with laws `μ, μ'`, at `G = 1`,
`𝔼[⟨δb, δY⟩ + ⟨δσ, δZ⟩_F − ⟨δf, δX⟩ + ⟨δh, δU⟩_{L²(ν)}]` is the expected dissipation at
`β₁ = β₂ = 2` less `|𝔼 δX|² + |𝔼 δY|² + |𝔼 δZ|²_F + ‖𝔼 δU‖²_{L²(ν)}`, the sum of the squared
channel norms of `𝔼 δΘ`. -/
theorem integral_interiorPairing_meanField {Θ Θ' : Ω → TupleH ν n n d} (hΘ : MemLp Θ 2 P)
    (hΘ' : MemLp Θ' 2 P) (t : ℝ) :
    ∫ ω, interiorPairing (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν)
        (diagDiff (meanFieldCoeffs ν n d) t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P
      = ∫ ω, dissipation (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν) 2 2
          (diagDiff (meanFieldCoeffs ν n d) t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ')) ∂P
        - channelSq (∫ ω, (Θ ω - Θ' ω) ∂P) := by
  have hd : MemLp (fun ω => Θ ω - Θ' ω) 2 P := hΘ.sub hΘ'
  have hL : MemLp (fun ω => toL2 (Θ ω - Θ' ω)) 2 P := memLp_toL2 hd
  have hmean : tupleMean (lawP2 P Θ) - tupleMean (lawP2 P Θ') = ∫ ω, (Θ ω - Θ' ω) ∂P := by
    rw [tupleMean_lawP2 hΘ, tupleMean_lawP2 hΘ',
      integral_sub (hΘ.integrable one_le_two) (hΘ'.integrable one_le_two)]
  have iD : Integrable (fun ω => dissipation (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1)
      (GU 1 ν) 2 2
      (diagDiff (meanFieldCoeffs ν n d) t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ'))) P := by
    simp_rw [dissipation_meanField]
    exact (hL.integrable_norm_pow two_ne_zero).const_mul _
  have iI : Integrable (fun ω => inner ℝ (toL2 (∫ ω, (Θ ω - Θ' ω) ∂P))
      (toL2 (Θ ω - Θ' ω))) P :=
    (hL.integrable one_le_two).const_inner _
  simp_rw [interiorPairing_meanField, hmean]
  rw [integral_sub iD iI, integral_inner (hL.integrable one_le_two),
    integral_toL2 (hd.integrable one_le_two), real_inner_self_eq_norm_sq, norm_toL2_sq]

/-- **Assumption 2.5, interior, along the diagonal, for Example 5.1(ii)**, with `G = 1` and
`β₁ = β₂ = 2`. -/
theorem diagonalMonotone_meanField {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ} :
    DiagonalMonotone ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) 2 2 (meanFieldCoeffs ν n d) :=
  Eventually.of_forall fun t Θ Θ' _ _ hΘ hΘ' => by
    rw [integral_interiorPairing_meanField hΘ hΘ' t]
    linarith [channelSq_nonneg (∫ ω, (Θ ω - Θ' ω) ∂P)]

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The expected terminal pairing of Example 5.1(ii) along the diagonal.** For square-integrable
random vectors `ξ, ξ'` with laws `ρ, ρ'`,
`𝔼⟨g(ξ, ρ) − g(ξ', ρ'), ξ − ξ'⟩ = 2 𝔼|ξ − ξ'|² + |𝔼(ξ − ξ')|²`. -/
theorem integral_inner_meanField_g {ξ ξ' : Ω → EuclideanSpace ℝ (Fin n)} (hξ : MemLp ξ 2 P)
    (hξ' : MemLp ξ' 2 P) :
    ∫ ω, inner ℝ ((meanFieldCoeffs ν n d).g (ξ ω) (lawP2 P ξ)
        - (meanFieldCoeffs ν n d).g (ξ' ω) (lawP2 P ξ')) (ξ ω - ξ' ω) ∂P
      = 2 * ∫ ω, ‖ξ ω - ξ' ω‖ ^ 2 ∂P + ‖∫ ω, (ξ ω - ξ' ω) ∂P‖ ^ 2 := by
  have hd : MemLp (fun ω => ξ ω - ξ' ω) 2 P := hξ.sub hξ'
  have hmean : barycentre (lawP2 P ξ) - barycentre (lawP2 P ξ') = ∫ ω, (ξ ω - ξ' ω) ∂P := by
    rw [barycentre_lawP2 hξ, barycentre_lawP2 hξ',
      integral_sub (hξ.integrable one_le_two) (hξ'.integrable one_le_two)]
  have hpt : ∀ ω, inner ℝ ((meanFieldCoeffs ν n d).g (ξ ω) (lawP2 P ξ)
        - (meanFieldCoeffs ν n d).g (ξ' ω) (lawP2 P ξ')) (ξ ω - ξ' ω)
      = 2 * ‖ξ ω - ξ' ω‖ ^ 2 + inner ℝ (∫ ω, (ξ ω - ξ' ω) ∂P) (ξ ω - ξ' ω) := fun ω => by
    have e : (2 : ℝ) • ξ ω + barycentre (lawP2 P ξ) - ((2 : ℝ) • ξ' ω + barycentre (lawP2 P ξ'))
        = (2 : ℝ) • (ξ ω - ξ' ω) + (barycentre (lawP2 P ξ) - barycentre (lawP2 P ξ')) := by
      rw [smul_sub]; abel
    simp only [meanFieldCoeffs, e, hmean, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
  simp_rw [hpt]
  rw [integral_add ((hd.integrable_norm_pow two_ne_zero).const_mul _)
      ((hd.integrable one_le_two).const_inner _), integral_const_mul,
    integral_inner (hd.integrable one_le_two), real_inner_self_eq_norm_sq]

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **Assumption 2.5, terminal, along the diagonal, for Example 5.1(ii)**, with `G = 1` and
`α = 2`: `2 𝔼|δX_T|² ≤ 𝔼⟨δg_T, δX_T⟩`. -/
theorem terminalMonotone_meanField {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ} :
    TerminalMonotone ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) 2 (meanFieldCoeffs ν n d).g := by
  intro ξ ξ' _ _ hξ hξ'
  simp only [GX_one, ContinuousLinearMap.id_apply]
  rw [integral_inner_meanField_g hξ hξ']
  exact le_add_of_nonneg_right (sq_nonneg _)

end Dissertation.WellPosedness.Existence
