/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.CoeffBorelW2
import Dissertation.WellPosedness.Existence.Global
import Dissertation.WellPosedness.System.Stability
import Dissertation.WellPosedness.System.Example

/-!
# Example 5.1(i): a fully coupled affine system

For `n = m`, any `d`, `β₁, β₂ > 0`, `σ_c ∈ ℝ^{n×d}` and `h_c ∈ L²(ν; ℝⁿ)`, the affine system of
Example 5.1(i), which the paper obtains from a linear-quadratic control problem through the
stochastic maximum principle,

`b = −β₁ y`, `σ = σ_c − β₁ z`, `h = h_c − β₁ u`, `f = β₂ x`, `g(x, ρ) = x`,

is law-free and fully coupled: the drift, the diffusion and the jump coefficient of the forward
equation are functions of the backward components `(Y, Z, U)`. It satisfies Assumption 2.2, with
the constant origin values `0, σ_c, h_c, 0`; Assumption 2.3 pointwise, hence along the diagonal,
with `L = max{β₁, β₂, 1}`; Assumption 2.4 for `G = I` with `c_G = 1`; and Assumption 2.5 along
the diagonal with `α = 1` and its own `β₁, β₂`, the interior inequality (2.7) and the terminal
inequality holding with equality. The jump coefficient is `U`-dissipative with equality,
`∫_E ⟨δh(e), δU(e)⟩ ν(de) = −β₁ ‖δU‖²_{L²(ν)}`, and the constants are sharp: for `n > 0` and
`T > 0`, (2.7) fails for any `β₁' > β₁` or `β₂' > β₂`, at a pair of deterministic tuples. Its
coefficients are continuous in the tuple and independent of the time and the law, so Borel
measurable on `[0, T] × H × P₂(H)` for the Hilbert-norm `W₂`, (2.3). The paper's case is
`n = d = 1`.

## Main definitions

* `affineCoeffs` — the affine coefficient system.

## Main statements

* `GZ_one`, `GU_one` — the coupling operators of `G = I` on the `Z` and `U` channels are the
  identity.
* `interiorPairing_affine` — the interior inequality (2.7) with equality, pointwise.
* `jumpPairing_affine` — the jump coefficient is `U`-dissipative with equality.
* `lipschitzCoefficientsP2_affine`, `lipschitzTerminalP2_affine`, `diagonalLipschitz_affine`,
  `terminalLipschitz_affine` — Assumption 2.3.
* `coeffOrigin_affine` — Assumption 2.2.
* `constants_affine`, `diagonalMonotone_affine`, `terminalMonotone_affine` — Assumption 2.5.
* `not_diagonalMonotone_affine_of_lt` — the constants `β₁, β₂` of (2.7) cannot be raised.
* `coeffBorelW2_affine` — (2.3), with the Hilbert-norm `W₂` on `P₂(H)`.
-/

open MeasureTheory Filter WithLp Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

/-! ### The coefficients -/

section Coefficients

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n d : ℕ}

/-- The affine coefficient system of Example 5.1(i) on
`H = ℝⁿ × ℝⁿ × ℝ^{n×d} × L²(ν; ℝⁿ)`: for `θ = (x, y, z, u)`, `b = −β₁ y`, `σ = σ_c − β₁ z`,
`h = h_c − β₁ u`, `f = β₂ x`, and `g(x, ρ) = x`. -/
noncomputable def affineCoeffs (β₁ β₂ : ℝ) (σc : EuclideanSpace ℝ (Fin n × Fin d))
    (hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) : Coeffs ν n n d where
  b _ θ _ := -(β₁ • θ.2.1)
  σ _ θ _ := σc - β₁ • θ.2.2.1
  h _ θ _ := hc - β₁ • θ.2.2.2
  f _ θ _ := β₂ • θ.1
  g x _ := x

/-- The coupling operator of the identity matrix on `n × d` matrices is the identity. -/
theorem _root_.Dissertation.WellPosedness.System.GZ_one :
    GZ (d := d) (1 : Matrix (Fin n) (Fin n) ℝ) = ContinuousLinearMap.id ℝ _ := by
  ext z : 1
  refine PiLp.ext fun p => ?_
  rw [← toLp_ofLp 2 z, GZ_toLp_apply, Matrix.one_mulVec]
  rfl

variable (ν) in
/-- The coupling operator of the identity matrix on `L²(ν; ℝⁿ)` is the identity. -/
theorem _root_.Dissertation.WellPosedness.System.GU_one :
    GU (1 : Matrix (Fin n) (Fin n) ℝ) ν = ContinuousLinearMap.id ℝ _ := by
  ext u : 1
  refine Lp.ext ?_
  filter_upwards [coeFn_GU (1 : Matrix (Fin n) (Fin n) ℝ) ν u] with e he
  rw [he, GX_one]
  rfl

variable {β₁ β₂ : ℝ} {σc : EuclideanSpace ℝ (Fin n × Fin d)}
  {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}

/-- **The interior pairing of Example 5.1(i)** equals the dissipation, (2.7) with equality, at
`G = I` and the system's own `β₁, β₂`: pointwise,
`⟨δb, δY⟩ + ⟨δσ, δZ⟩_F − ⟨δf, δX⟩ + ⟨δh, δU⟩_{L²(ν)}
  = −β₁ (|δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}) − β₂ |δX|²`. -/
theorem interiorPairing_affine (t : ℝ) (θ θ' : TupleH ν n n d) (μ μ' : P2 (TupleH ν n n d)) :
    interiorPairing (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν)
        (diagDiff (affineCoeffs β₁ β₂ σc hc) t θ θ' μ μ')
      = dissipation (GX (1 : Matrix (Fin n) (Fin n) ℝ)) (GZ 1) (GU 1 ν) β₁ β₂
        (diagDiff (affineCoeffs β₁ β₂ σc hc) t θ θ' μ μ') := by
  have e₁ : -(β₁ • θ.2.1) - -(β₁ • θ'.2.1) = -(β₁ • (θ.2.1 - θ'.2.1)) := by
    rw [smul_sub]; abel
  have e₂ : σc - β₁ • θ.2.2.1 - (σc - β₁ • θ'.2.2.1) = -(β₁ • (θ.2.2.1 - θ'.2.2.1)) := by
    rw [smul_sub]; abel
  have e₃ : hc - β₁ • θ.2.2.2 - (hc - β₁ • θ'.2.2.2) = -(β₁ • (θ.2.2.2 - θ'.2.2.2)) := by
    rw [smul_sub]; abel
  simp only [interiorPairing, dissipation, diagDiff, affineCoeffs, e₁, e₂, e₃, ← smul_sub,
    GX_one, GZ_one, GU_one, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply,
    inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

/-- **The jump pairing of Example 5.1(i)**: the jump coefficient `h = h_c − β₁ u` is
`U`-dissipative with equality, `∫_E ⟨δh(e), δU(e)⟩ ν(de) = −β₁ ‖δU‖²_{L²(ν)}`, pointwise. -/
theorem jumpPairing_affine (t : ℝ) (θ θ' : TupleH ν n n d) (μ μ' : P2 (TupleH ν n n d)) :
    ∫ e, inner ℝ (((affineCoeffs β₁ β₂ σc hc).h t θ μ - (affineCoeffs β₁ β₂ σc hc).h t θ' μ' :
        Lp (EuclideanSpace ℝ (Fin n)) 2 ν) e) ((θ.2.2.2 - θ'.2.2.2 :
        Lp (EuclideanSpace ℝ (Fin n)) 2 ν) e) ∂ν
      = -β₁ * ‖θ.2.2.2 - θ'.2.2.2‖ ^ 2 := by
  have e₃ : hc - β₁ • θ.2.2.2 - (hc - β₁ • θ'.2.2.2) = -(β₁ • (θ.2.2.2 - θ'.2.2.2)) := by
    rw [smul_sub]; abel
  rw [← L2.inner_def]
  simp only [affineCoeffs, e₃, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

/-- **Assumption 2.3, interior, pointwise, for Example 5.1(i)**, with any constant
`L ≥ max β₁ β₂`, `β₁, β₂ ≥ 0`. -/
theorem lipschitzCoefficientsP2_affine (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) {L : ℝ}
    (hL : max β₁ β₂ ≤ L) :
    LipschitzCoefficientsP2 L (affineCoeffs β₁ β₂ σc hc).b (affineCoeffs β₁ β₂ σc hc).σ
      (affineCoeffs β₁ β₂ σc hc).h (affineCoeffs β₁ β₂ σc hc).f := by
  intro t θ θ' μ μ'
  have e₁ : -(β₁ • θ.2.1) - -(β₁ • θ'.2.1) = -(β₁ • (θ.2.1 - θ'.2.1)) := by
    rw [smul_sub]; abel
  have e₂ : σc - β₁ • θ.2.2.1 - (σc - β₁ • θ'.2.2.1) = -(β₁ • (θ.2.2.1 - θ'.2.2.1)) := by
    rw [smul_sub]; abel
  have e₃ : hc - β₁ • θ.2.2.2 - (hc - β₁ • θ'.2.2.2) = -(β₁ • (θ.2.2.2 - θ'.2.2.2)) := by
    rw [smul_sub]; abel
  simp only [affineCoeffs, e₁, e₂, e₃, ← smul_sub, norm_neg, norm_smul, Real.norm_of_nonneg hβ₁,
    Real.norm_of_nonneg hβ₂]
  have htn : tupleNorm (θ - θ')
      = ‖θ.1 - θ'.1‖ + ‖θ.2.1 - θ'.2.1‖ + ‖θ.2.2.1 - θ'.2.2.1‖ + ‖θ.2.2.2 - θ'.2.2.2‖ := rfl
  rw [htn]
  have hL₁ : β₁ ≤ L := (le_max_left _ _).trans hL
  have hL₂ : β₂ ≤ L := (le_max_right _ _).trans hL
  have hw := w2P_nonneg μ μ'
  nlinarith [norm_nonneg (θ.1 - θ'.1), norm_nonneg (θ.2.1 - θ'.2.1),
    norm_nonneg (θ.2.2.1 - θ'.2.2.1), norm_nonneg (θ.2.2.2 - θ'.2.2.2)]

/-- **Assumption 2.3, terminal, pointwise, for Example 5.1(i)**, with any constant `L ≥ 1`. -/
theorem lipschitzTerminalP2_affine {L : ℝ} (hL : 1 ≤ L) :
    LipschitzTerminalP2 L (affineCoeffs β₁ β₂ σc hc).g := by
  intro x x' ρ ρ'
  simp only [affineCoeffs]
  have hw := w2P_nonneg ρ ρ'
  have hn := norm_nonneg (x - x')
  nlinarith

/-- The constants `α = 1`, `β₁, β₂ > 0` are admissible in the square case. -/
theorem constants_affine (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂) : Constants n n 1 β₁ β₂ :=
  Constants.square zero_le_one hβ₁.le hβ₂.le (by linarith) (by linarith)

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- Assumption 2.3, terminal, along the diagonal, for Example 5.1(i) with `L ≥ 1`. -/
theorem terminalLipschitz_affine {L : ℝ} (hL : 1 ≤ L) :
    TerminalLipschitz ℱ P T L (affineCoeffs β₁ β₂ σc hc).g :=
  terminalLipschitz_of_lipschitzTerminalP2 (lipschitzTerminalP2_affine hL)

/-- **Assumption 2.5, terminal, along the diagonal, for Example 5.1(i)**, with `G = I` and
`α = 1`: `𝔼|δX_T|² = 𝔼⟨δg_T, δX_T⟩`. -/
theorem terminalMonotone_affine :
    TerminalMonotone ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) 1 (affineCoeffs β₁ β₂ σc hc).g := by
  intro ξ ξ' _ _ _ _
  refine le_of_eq ?_
  simp only [affineCoeffs, GX_one, ContinuousLinearMap.id_apply, one_mul,
    real_inner_self_eq_norm_sq]

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **Assumption 2.2 for Example 5.1(i)**: the origin values are the constants `0`, `σ_c`, `h_c`,
`0`. -/
theorem coeffOrigin_affine (T : ℝ) : CoeffOrigin T (affineCoeffs β₁ β₂ σc hc) :=
  originIntegrable_const T _ _ _ _

/-- Assumption 2.3, interior, along the diagonal, for Example 5.1(i) with `L ≥ max β₁ β₂`,
`β₁, β₂ ≥ 0`. -/
theorem diagonalLipschitz_affine (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) {L : ℝ} (hL : max β₁ β₂ ≤ L) :
    DiagonalLipschitz ℱ P T L (affineCoeffs β₁ β₂ σc hc) :=
  diagonalLipschitz_of_lipschitzCoefficientsP2 (lipschitzCoefficientsP2_affine hβ₁ hβ₂ hL)

/-- **Assumption 2.5, interior, along the diagonal, for Example 5.1(i)**, with `G = I` and the
system's own `β₁, β₂`, with equality. -/
theorem diagonalMonotone_affine :
    DiagonalMonotone ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) β₁ β₂ (affineCoeffs β₁ β₂ σc hc) :=
  Eventually.of_forall fun t Θ Θ' _ _ _ _ => le_of_eq (integral_congr_ae
    (Eventually.of_forall fun ω => interiorPairing_affine t (Θ ω) (Θ' ω) _ _))

/-- **The constants of Example 5.1(i) are sharp.** For `n > 0` and `T > 0`, if `β₁ < β₁'` or
`β₂ < β₂'` then Assumption 2.5, interior, along the diagonal, with `G = I`, fails for the
constants `β₁', β₂'`: it fails at a pair of deterministic tuples. -/
theorem not_diagonalMonotone_affine_of_lt (hn : 0 < n) (hT : 0 < T) {β₁' β₂' : ℝ}
    (h : β₁ < β₁' ∨ β₂ < β₂') :
    ¬ DiagonalMonotone ℱ P T (1 : Matrix (Fin n) (Fin n) ℝ) β₁' β₂'
      (affineCoeffs β₁ β₂ σc hc) := by
  intro hM
  haveI : (ae (volume.restrict (Set.Icc (0 : ℝ) T))).NeBot := by
    rw [ae_restrict_neBot, Real.volume_Icc, sub_zero]
    exact ENNReal.ofReal_ne_zero_iff.mpr hT
  obtain ⟨t, ht⟩ := hM.exists
  have key : ∀ x y : EuclideanSpace ℝ (Fin n),
      -β₁ * ‖y‖ ^ 2 - β₂ * ‖x‖ ^ 2 ≤ -β₁' * ‖y‖ ^ 2 - β₂' * ‖x‖ ^ 2 := fun x y => by
    have hxy := ht (fun _ => ((x, y, 0, 0) : TupleH ν n n d)) (fun _ => 0)
      stronglyMeasurable_const stronglyMeasurable_const (memLp_const _) (memLp_const _)
    simp only [integral_const, probReal_univ, one_smul, interiorPairing_affine] at hxy
    simpa [dissipation, diagDiff, GX_one, GZ_one, GU_one] using hxy
  have hv : ‖(EuclideanSpace.single ⟨0, hn⟩ 1 : EuclideanSpace ℝ (Fin n))‖ = 1 := by simp
  rcases h with h | h
  · have := key 0 (EuclideanSpace.single ⟨0, hn⟩ 1)
    rw [hv, norm_zero] at this
    linarith
  · have := key (EuclideanSpace.single ⟨0, hn⟩ 1) 0
    rw [hv, norm_zero] at this
    linarith

end Coefficients

/-! ### Joint measurability -/

section Measurability

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n d : ℕ} {β₁ β₂ : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **(2.3) for Example 5.1(i), with the Hilbert-norm `W₂` on `P₂(H)`**: the coefficients are
continuous in the tuple and independent of the time and the law, so Borel measurable on
`[0, T] × H × P₂(H)`. -/
theorem coeffBorelW2_affine (T : ℝ) : CoeffBorelW2 T (affineCoeffs β₁ β₂ σc hc) where
  b_meas := measurable_borelW2_of_measurable (ψ := (affineCoeffs β₁ β₂ σc hc).b) (by
    simp only [affineCoeffs]; fun_prop)
  σ_meas := measurable_borelW2_of_measurable (ψ := (affineCoeffs β₁ β₂ σc hc).σ) (by
    simp only [affineCoeffs]; fun_prop)
  h_meas := measurable_borelW2_of_measurable (ψ := (affineCoeffs β₁ β₂ σc hc).h) (by
    simp only [affineCoeffs]; fun_prop)
  f_meas := measurable_borelW2_of_measurable (ψ := (affineCoeffs β₁ β₂ σc hc).f) (by
    simp only [affineCoeffs]; fun_prop)

end Measurability

end Dissertation.WellPosedness.Existence
