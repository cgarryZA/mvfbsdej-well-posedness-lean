/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.AffineExample
import Dissertation.WellPosedness.Examples.MarkKernel
import Dissertation.WellPosedness.System.DiagonalLipschitzH

/-!
# Example 5.1(ii): the mean-field coefficients

Write `θ = (x, y, z, u)` for a point of the tuple space `H = ℝⁿ × ℝⁿ × ℝ^{n×d} × L²(ν; ℝⁿ)`. The
mean of a law `μ` of finite second moment on `H` is the Bochner integral `∫_H θ μ(dθ) ∈ H`, whose
four channels are the marginal means `m_X(μ), m_Y(μ), m_Z(μ), m_U(μ)`, and the barycentre of a law
`ρ` of finite second moment on `ℝⁿ` is `𝔟(ρ) = ∫ x ρ(dx)`. The mean-field coefficients of
Example 5.1(ii) of the well-posedness paper are

`b = −2y − m_Y(μ)`, `σ = −2z − m_Z(μ)`, `h = −2u − m_U(μ)`, `f = 2x + m_X(μ)`,
`g(x, ρ) = 2x + 𝔟(ρ)`.

The paper's case is `n = d = 1`; the coefficients make sense for every `n` and `d`.

Along a diagonal input `(Θ, Law Θ)` with `Θ` square integrable the mean is the expectation,
`∫_H θ Law(Θ)(dθ) = 𝔼 Θ`. The identity map is `1`-Lipschitz, so by (2.10) the mean is `1`-Lipschitz
for the 2-Wasserstein distance of the Hilbert norm, `|∫θ dμ − ∫θ dμ'|_H ≤ W₂(μ, μ')`, and the
barycentre is `1`-Lipschitz for `W₂` on `P₂(ℝⁿ)`. The sum of the four channel norms is at most
twice the Hilbert norm, so the coefficients satisfy Assumption 2.3 with the constant `L = 2`, at
every pair of points and laws, for the Hilbert-norm `W₂` on `P₂(H)`. The coefficients
`b, σ, h, f` vanish at `(0, δ₀)`, which gives Assumption 2.2, and they are continuous on
`[0, T] × H × P₂(H)`, which gives (2.3).

## Main definitions

* `toL2CLM` — the identification of the tuple space with its Hilbert-norm realisation, as a
  continuous linear map.
* `tupleMean` — the mean `∫_H θ μ(dθ)` of a law of finite second moment on `H`.
* `barycentre` — the barycentre `𝔟(ρ) = ∫ x ρ(dx)` of a law of finite second moment on `ℝⁿ`.
* `meanFieldCoeffs` — the coefficients of Example 5.1(ii).

## Main statements

* `integral_id_lawP2`, `tupleMean_lawP2`, `barycentre_lawP2` — along a square-integrable random
  element the mean of its law is its expectation.
* `tupleMean_eq` — the four channels of the mean are the marginal means.
* `norm_toL2_tupleMean_sub_le`, `tupleNorm_tupleMean_sub_le`, `norm_barycentre_sub_le` — the
  Lipschitz bounds of the mean and the barycentre for `W₂`.
* `lipschitzCoefficients_meanField`, `lipschitzTerminalP2_meanField` — Assumption 2.3,
  pointwise.
* `diagonalLipschitzH_meanField`, `terminalLipschitz_meanField` — Assumption 2.3 along the
  diagonal.
* `meanField_origin`, `coeffOrigin_meanField` — Assumption 2.2.
* `coeffBorelW2_meanField` — (2.3).
-/

open MeasureTheory Filter Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

/-! ### The Hilbert norm of the tuple space -/

section ToL2

variable {HX HY HZY HUY : Type*} [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [NormedAddCommGroup HZY]
  [InnerProductSpace ℝ HZY] [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY]

/-- The identification `toL2` of the tuple space, with the maximum of its channel norms, with the
tuple space with the Hilbert norm, as a continuous linear map. -/
noncomputable def toL2CLM : Tuple HX HY HZY HUY →L[ℝ] TupleL2 HX HY HZY HUY :=
  LinearMap.mkContinuous
    { toFun := toL2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    2 norm_toL2_le

/-- The Hilbert inner product of two tuples is the sum of the inner products of their channels. -/
theorem inner_toL2 (θ θ' : Tuple HX HY HZY HUY) :
    inner ℝ (toL2 θ) (toL2 θ') = inner ℝ θ.1 θ'.1 + inner ℝ θ.2.1 θ'.2.1
      + inner ℝ θ.2.2.1 θ'.2.2.1 + inner ℝ θ.2.2.2 θ'.2.2.2 := by
  simp only [toL2, WithLp.prod_inner_apply]
  ring

variable [CompleteSpace HX] [CompleteSpace HY] [CompleteSpace HZY] [CompleteSpace HUY]

/-- `toL2` commutes with the Bochner integral of an integrable random tuple. -/
theorem integral_toL2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {V : Ω → Tuple HX HY HZY HUY} (hV : Integrable V P) :
    ∫ ω, toL2 (V ω) ∂P = toL2 (∫ ω, V ω ∂P) :=
  toL2CLM.integral_comp_comm hV

end ToL2

/-! ### Means of laws of finite second moment -/

section Mean

/-- A law of finite second moment on a second-countable Borel normed space integrates the
identity. -/
theorem _root_.Dissertation.Law.P2.integrable_id {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (μ : P2 F) :
    Integrable (fun x : F => x) μ.law :=
  integrable_of_norm_sub_le (φ := fun x : F => x) stronglyMeasurable_id (K := 1)
    (fun _ _ => (one_mul _).ge) μ.secondMoment_ne_top

/-- **The mean of the law of a random element is its expectation**: for `Θ` square integrable,
`∫ x Law(Θ)(dx) = 𝔼 Θ`. -/
theorem integral_id_lawP2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Θ : Ω → F}
    (hΘ : MemLp Θ 2 P) : ∫ x, x ∂(lawP2 P Θ).law = ∫ ω, Θ ω ∂P := by
  rw [lawP2_law hΘ]
  exact integral_map hΘ.aestronglyMeasurable.aemeasurable aestronglyMeasurable_id

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}

/-- The mean `∫_H θ μ(dθ)` of a law of finite second moment on the tuple space
`H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)`. -/
noncomputable def tupleMean (μ : P2 (TupleH ν n m d)) : TupleH ν n m d :=
  ∫ θ, θ ∂μ.law

/-- The barycentre `𝔟(ρ) = ∫ x ρ(dx)` of a law of finite second moment on `ℝⁿ`. -/
noncomputable def barycentre (ρ : P2 (EuclideanSpace ℝ (Fin n))) : EuclideanSpace ℝ (Fin n) :=
  ∫ x, x ∂ρ.law

/-- The barycentre of the law of a square-integrable random vector is its expectation. -/
theorem barycentre_lawP2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : Ω → EuclideanSpace ℝ (Fin n)} (hξ : MemLp ξ 2 P) :
    barycentre (lawP2 P ξ) = ∫ ω, ξ ω ∂P :=
  integral_id_lawP2 hξ

/-- The barycentre is `1`-Lipschitz for `W₂` on `P₂(ℝⁿ)`: `|𝔟(ρ) − 𝔟(ρ')| ≤ W₂(ρ, ρ')`. -/
theorem norm_barycentre_sub_le (ρ ρ' : P2 (EuclideanSpace ℝ (Fin n))) :
    ‖barycentre ρ - barycentre ρ'‖ ≤ w2P ρ ρ' := by
  simpa only [one_mul, barycentre, w2P] using norm_integral_sub_le_w2_of_nonneg
    (φ := fun x : EuclideanSpace ℝ (Fin n) => x) stronglyMeasurable_id zero_le_one
    (fun _ _ => (one_mul _).ge) ρ.integrable_id ρ'.integrable_id (w2sq_ne_top ρ ρ')

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- The mean of the law of a square-integrable random tuple is its expectation. -/
theorem tupleMean_lawP2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Ω → TupleH ν n m d} (hΘ : MemLp Θ 2 P) :
    tupleMean (lawP2 P Θ) = ∫ ω, Θ ω ∂P :=
  integral_id_lawP2 hΘ

/-- **The channels of the mean are the marginal means**:
`∫_H θ μ(dθ) = (m_X(μ), m_Y(μ), m_Z(μ), m_U(μ))`, with `m_Ψ(μ) = ∫_H π_Ψ(θ) μ(dθ)`. -/
theorem tupleMean_eq (μ : P2 (TupleH ν n m d)) :
    tupleMean μ = (∫ θ, θ.1 ∂μ.law, ∫ θ, θ.2.1 ∂μ.law, ∫ θ, θ.2.2.1 ∂μ.law,
      ∫ θ, θ.2.2.2 ∂μ.law) := by
  have h := μ.integrable_id
  refine Prod.ext (fst_integral h) (Prod.ext ?_ (Prod.ext ?_ ?_))
  · change (∫ θ, θ ∂μ.law).2.1 = _
    rw [snd_integral h, fst_integral h.snd]
  · change (∫ θ, θ ∂μ.law).2.2.1 = _
    rw [snd_integral h, snd_integral h.snd, fst_integral h.snd.snd]
  · change (∫ θ, θ ∂μ.law).2.2.2 = _
    rw [snd_integral h, snd_integral h.snd, snd_integral h.snd.snd]

/-- The mean of the Dirac mass at a tuple is that tuple. -/
theorem tupleMean_dirac (a : TupleH ν n m d) : tupleMean (P2.dirac a) = a := by
  simp [tupleMean, P2.dirac]

/-- **The mean is `1`-Lipschitz for the Hilbert-norm `W₂`**, (2.10) for the identity map:
`|∫_H θ dμ − ∫_H θ dμ'|_H ≤ W₂(μ, μ')`. -/
theorem norm_toL2_tupleMean_sub_le (μ μ' : P2 (TupleH ν n m d)) :
    ‖toL2 (tupleMean μ - tupleMean μ')‖ ≤ w2H μ μ' := by
  have h := norm_integral_sub_le_w2H (φ := fun θ : TupleH ν n m d => toL2 θ) zero_le_one
    (fun θ θ' => (one_mul _).ge) μ μ'
  rw [one_mul, integral_toL2 μ.integrable_id, integral_toL2 μ'.integrable_id, ← toL2_sub] at h
  exact h

/-- **The channel means are jointly Lipschitz for the Hilbert-norm `W₂`**:
`|δm_X| + |δm_Y| + |δm_Z|_F + ‖δm_U‖_{L²(ν)} ≤ 2 |δm|_H ≤ 2 W₂(μ, μ')`. -/
theorem tupleNorm_tupleMean_sub_le (μ μ' : P2 (TupleH ν n m d)) :
    tupleNorm (tupleMean μ - tupleMean μ') ≤ 2 * w2H μ μ' :=
  (tupleNorm_le_two_mul_norm_toL2 _).trans
    (mul_le_mul_of_nonneg_left (norm_toL2_tupleMean_sub_le μ μ') zero_le_two)

/-- The mean is `1`-Lipschitz from `P₂(H)` with the Hilbert-norm `W₂` to the tuple space. -/
theorem lipschitzWith_tupleMean :
    LipschitzWith 1 fun μ : TupleP2WH ν n m d => tupleMean μ.toP2 :=
  LipschitzWith.of_dist_le_mul fun μ μ' => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm]
    exact (norm_le_norm_toL2 _).trans (norm_toL2_tupleMean_sub_le μ.toP2 μ'.toP2)

end Mean

end Dissertation.WellPosedness.System

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.System

/-! ### The coefficients -/

section Coefficients

variable {E : Type*} [MeasurableSpace E]

variable (ν : Measure E) (n d : ℕ) in
/-- The mean-field coefficients of Example 5.1(ii) on `H = ℝⁿ × ℝⁿ × ℝ^{n×d} × L²(ν; ℝⁿ)`: for
`θ = (x, y, z, u)`, `b = −2y − m_Y(μ)`, `σ = −2z − m_Z(μ)`, `h = −2u − m_U(μ)`,
`f = 2x + m_X(μ)`, with `m_Ψ(μ)` the channels of the mean `∫_H θ μ(dθ)`, and
`g(x, ρ) = 2x + 𝔟(ρ)`, with `𝔟(ρ)` the barycentre of `ρ`. -/
noncomputable def meanFieldCoeffs : Coeffs ν n n d where
  b _ θ μ := -((2 : ℝ) • θ.2.1) - (tupleMean μ).2.1
  σ _ θ μ := -((2 : ℝ) • θ.2.2.1) - (tupleMean μ).2.2.1
  h _ θ μ := -((2 : ℝ) • θ.2.2.2) - (tupleMean μ).2.2.2
  f _ θ μ := (2 : ℝ) • θ.1 + (tupleMean μ).1
  g x ρ := (2 : ℝ) • x + barycentre ρ

variable {ν : Measure E} {n d : ℕ}

/-- The constants `α = β₁ = β₂ = 2` are admissible in the square case. -/
theorem constants_meanField : Constants n n 2 2 2 :=
  Constants.square zero_le_two zero_le_two zero_le_two (by norm_num) (by norm_num)

/-- A difference `(−2a − c) − (−2a' − c')` has norm at most `2 |a − a'| + |c − c'|`. -/
theorem norm_neg_two_smul_sub_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a a' c c' : V) :
    ‖-((2 : ℝ) • a) - c - (-((2 : ℝ) • a') - c')‖ ≤ 2 * ‖a - a'‖ + ‖c - c'‖ := by
  have e : -((2 : ℝ) • a) - c - (-((2 : ℝ) • a') - c') = -((2 : ℝ) • (a - a')) - (c - c') := by
    rw [smul_sub]; abel
  rw [e]
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [norm_neg, norm_smul, Real.norm_two]

/-- A difference `(2a + c) − (2a' + c')` has norm at most `2 |a − a'| + |c − c'|`. -/
theorem norm_two_smul_add_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a a' c c' : V) :
    ‖(2 : ℝ) • a + c - ((2 : ℝ) • a' + c')‖ ≤ 2 * ‖a - a'‖ + ‖c - c'‖ := by
  have e : (2 : ℝ) • a + c - ((2 : ℝ) • a' + c') = (2 : ℝ) • (a - a') + (c - c') := by
    rw [smul_sub]; abel
  rw [e]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_smul, Real.norm_two]

/-- **Assumption 2.3, terminal, pointwise, for Example 5.1(ii)**, with any constant `L ≥ 2`:
`|g(x, ρ) − g(x', ρ')| ≤ L (|x − x'| + W₂(ρ, ρ'))`. -/
theorem lipschitzTerminalP2_meanField {L : ℝ} (hL : 2 ≤ L) :
    LipschitzTerminalP2 L (meanFieldCoeffs ν n d).g := by
  intro x x' ρ ρ'
  have h1 := norm_two_smul_add_sub_le x x' (barycentre ρ) (barycentre ρ')
  have h2 := norm_barycentre_sub_le ρ ρ'
  have h3 := norm_nonneg (x - x')
  have h4 := w2P_nonneg ρ ρ'
  simp only [meanFieldCoeffs]
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- Assumption 2.3, terminal, along the diagonal, for Example 5.1(ii), with any constant
`L ≥ 2`. -/
theorem terminalLipschitz_meanField {L : ℝ} (hL : 2 ≤ L) :
    TerminalLipschitz ℱ P T L (meanFieldCoeffs ν n d).g :=
  terminalLipschitz_of_lipschitzTerminalP2 (lipschitzTerminalP2_meanField hL)

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **Assumption 2.3, interior, pointwise, for Example 5.1(ii), at `L = 2`**, with `W₂` the
2-Wasserstein distance of the Hilbert norm: at every time, pair of points and pair of laws,
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ 2 (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + W₂(μ, μ'))`. -/
theorem lipschitzCoefficients_meanField :
    LipschitzCoefficients 2 (w2H (HX := EuclideanSpace ℝ (Fin n))
        (HY := EuclideanSpace ℝ (Fin n)) (HZY := EuclideanSpace ℝ (Fin n × Fin d))
        (HUY := Lp (EuclideanSpace ℝ (Fin n)) 2 ν))
      (meanFieldCoeffs ν n d).b (meanFieldCoeffs ν n d).σ (meanFieldCoeffs ν n d).h
      (meanFieldCoeffs ν n d).f := by
  intro t θ θ' μ μ'
  have hb := norm_neg_two_smul_sub_sub_le θ.2.1 θ'.2.1 (tupleMean μ).2.1 (tupleMean μ').2.1
  have hσ := norm_neg_two_smul_sub_sub_le θ.2.2.1 θ'.2.2.1 (tupleMean μ).2.2.1
    (tupleMean μ').2.2.1
  have hh := norm_neg_two_smul_sub_sub_le θ.2.2.2 θ'.2.2.2 (tupleMean μ).2.2.2
    (tupleMean μ').2.2.2
  have hf := norm_two_smul_add_sub_le θ.1 θ'.1 (tupleMean μ).1 (tupleMean μ').1
  have hm := tupleNorm_tupleMean_sub_le μ μ'
  have htn : tupleNorm (θ - θ')
      = ‖θ.1 - θ'.1‖ + ‖θ.2.1 - θ'.2.1‖ + ‖θ.2.2.1 - θ'.2.2.1‖ + ‖θ.2.2.2 - θ'.2.2.2‖ := rfl
  have hmn : tupleNorm (tupleMean μ - tupleMean μ')
      = ‖(tupleMean μ).1 - (tupleMean μ').1‖ + ‖(tupleMean μ).2.1 - (tupleMean μ').2.1‖
        + ‖(tupleMean μ).2.2.1 - (tupleMean μ').2.2.1‖
        + ‖(tupleMean μ).2.2.2 - (tupleMean μ').2.2.2‖ := rfl
  simp only [meanFieldCoeffs]
  rw [htn]
  linarith

/-- **Assumption 2.3, interior, along the diagonal, for Example 5.1(ii), at `L = 2`**, with the
Hilbert-norm `W₂` on `P₂(H)`. -/
theorem diagonalLipschitzH_meanField : DiagonalLipschitzH ℱ P T 2 (meanFieldCoeffs ν n d) :=
  Eventually.of_forall fun t Θ Θ' _ _ _ _ => Eventually.of_forall fun ω =>
    lipschitzCoefficients_meanField t (Θ ω) (Θ' ω) _ _

/-- **The coefficients of Example 5.1(ii) vanish at the origin**: `b, σ, h, f` at `(t, 0, δ₀)`
are `0`. -/
theorem meanField_origin (t : ℝ) :
    (meanFieldCoeffs ν n d).b t 0 (P2.dirac 0) = 0 ∧ (meanFieldCoeffs ν n d).σ t 0 (P2.dirac 0) = 0
      ∧ (meanFieldCoeffs ν n d).h t 0 (P2.dirac 0) = 0
      ∧ (meanFieldCoeffs ν n d).f t 0 (P2.dirac 0) = 0 := by
  simp [meanFieldCoeffs, tupleMean_dirac]

/-- **Assumption 2.2 for Example 5.1(ii)**: the origin values are independent of the time, hence
square integrable over `[0, T]`. -/
theorem coeffOrigin_meanField (T : ℝ) : CoeffOrigin T (meanFieldCoeffs ν n d) :=
  originIntegrable_const T _ _ _ _

end Coefficients

/-! ### Joint measurability -/

section Measurability

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {n d : ℕ}

/-- **(2.3) for Example 5.1(ii)**: the coefficients are Borel measurable on
`[0, T] × H × P₂(H)`, with the Hilbert-norm `W₂` on `P₂(H)`. They are continuous there, the mean
being `1`-Lipschitz. -/
theorem coeffBorelW2_meanField (T : ℝ) : CoeffBorelW2 T (meanFieldCoeffs ν n d) := by
  have hθ : Continuous fun p : Set.Icc (0 : ℝ) T × TupleH ν n n d × TupleP2WH ν n n d => p.2.1 :=
    continuous_fst.comp continuous_snd
  have hm : Continuous fun p : Set.Icc (0 : ℝ) T × TupleH ν n n d × TupleP2WH ν n n d =>
      tupleMean p.2.2.toP2 :=
    lipschitzWith_tupleMean.continuous.comp (continuous_snd.comp continuous_snd)
  exact
    { b_meas := Continuous.borel_measurable ((hθ.snd.fst.const_smul (2 : ℝ)).neg.sub hm.snd.fst)
      σ_meas := Continuous.borel_measurable
        ((hθ.snd.snd.fst.const_smul (2 : ℝ)).neg.sub hm.snd.snd.fst)
      h_meas := Continuous.borel_measurable
        ((hθ.snd.snd.snd.const_smul (2 : ℝ)).neg.sub hm.snd.snd.snd)
      f_meas := Continuous.borel_measurable ((hθ.fst.const_smul (2 : ℝ)).add hm.fst) }

end Measurability

end Dissertation.WellPosedness.Existence
