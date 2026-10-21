/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.TupleMarginal
import Dissertation.Law.Cylindrical
import Dissertation.WellPosedness.Robustness.LawPerturb
import Dissertation.WellPosedness.Robustness.Regular

/-!
# Example 5.4: nonlinear law functionals as a perturbation

Fix a reference law `μ₀ ∈ P₂(H)` on the tuple space `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)`, a
reference law `Λ₀ ∈ P₂(L²(ν; ℝᵐ))`, a size `ε ≥ 0`, Lipschitz profiles `𝔮, 𝔮̃, 𝔮̂ : ℝ → ℝ`, a
Lipschitz outer function `Q : ℝ^J → ℝ`, Lipschitz features `φ_1, …, φ_J : L²(ν; ℝᵐ) → ℝ`, and
directions `w₀, w₁ ∈ ℝᵐ`, `v₀ ∈ ℝⁿ`, `ĥ ∈ L²(ν; ℝⁿ)`. With `μ^U` the `U`-marginal of `μ` and
`W₂` the 2-Wasserstein distance of the Hilbert norm of `H`, the perturbation of Example 5.4 of
the paper is

`p_f(t, θ, μ) = ε 𝔮(W₂(μ, μ₀)) w₀ + ε Q(∫ φ_1 dμ^U, …, ∫ φ_J dμ^U) w₁`,
`p_b(t, θ, μ) = ε 𝔮̃(W₂(μ^U, Λ₀)) v₀`, `p_h(t, θ, μ) = ε 𝔮̂(W₂(μ^U, Λ₀)) ĥ`, `p_σ = 0`.

It is independent of the time and of the tuple. Each law statistic is `W₂`-Lipschitz: the radial
statistic of the full law with constant `Lip(𝔮)`, by the triangle inequality for `W₂`; the
radial statistics of the `U`-marginal with constants `Lip(𝔮̃)`, `Lip(𝔮̂)`, marginal projection
being `1`-Lipschitz, (2.11); and the cylindrical statistic with constant
`L_Q = Lip(Q) (∑_j Lip(φ_j)²)^{1/2}`, by (2.10) for the feature map. So the perturbation satisfies
(3.5), pointwise in the two laws, with

`L_p = ε (|w₀| Lip(𝔮) + |v₀| Lip(𝔮̃) + |w₁| L_Q + ‖ĥ‖ Lip(𝔮̂))`,

hence Assumption 2.3 along the diagonal with the constant `L_p`, and (3.4) with
`c_pert = ‖G‖ L_p`. Its origin values are constant in time, so Assumption 2.2 holds, and its
coefficients are Lipschitz, hence continuous, on `[0, T] × H × P₂(H)`, which gives (2.3) with
the Hilbert-norm `W₂` on `P₂(H)`. The bounds on the profiles, on `Q` and on the features play no
role in these conclusions.

## Main definitions

* `FullLawData` — the data of Example 5.4.
* `FullLawData.Lip` — the Lipschitz bounds of the profiles, of `Q` and of the features.
* `FullLawData.lipConst` — the constant `L_p` of (3.5).
* `fullLawPert` — the perturbation of Example 5.4.

## Main statements

* `abs_radial_w2H_sub_le`, `abs_radial_margU_sub_le`, `abs_cylindrical_margU_sub_le` — the
  Lipschitz bounds of the three law statistics for the Hilbert-norm `W₂`.
* `norm_fullLawPert_sub_le` — (3.5) at every pair of points and laws.
* `tupleIndep_fullLaw` — the perturbation is independent of the tuple.
* `diagonalLawLipschitzH_fullLaw`, `diagonalLipschitzH_fullLaw`,
  `diagonalPairingBound_fullLaw` — (3.5), Assumption 2.3 and (3.4) along the diagonal.
* `coeffOrigin_fullLaw` — Assumption 2.2.
* `coeffBorelW2_fullLaw` — (2.3).
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.Existence

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d J : ℕ}

/-- The data of Example 5.4: the size `ε`, the radial profiles `𝔮` (full law, driver), `𝔮̃`
(`U`-marginal, drift) and `𝔮̂` (`U`-marginal, jump coefficient), the outer function `Q` and the
features `φ_1, …, φ_J` of the cylindrical statistic, the reference laws `μ₀ ∈ P₂(H)` and
`Λ₀ ∈ P₂(L²(ν; ℝᵐ))`, and the directions `w₀, w₁ ∈ ℝᵐ`, `v₀ ∈ ℝⁿ`, `ĥ ∈ L²(ν; ℝⁿ)`. -/
structure FullLawData (ν : Measure E) (n m d J : ℕ) where
  /-- The size `ε` of the perturbation. -/
  ε : ℝ
  /-- The radial profile `𝔮` of the full tuple law, entering the driver. -/
  q : ℝ → ℝ
  /-- The radial profile `𝔮̃` of the `U`-marginal, entering the drift. -/
  qb : ℝ → ℝ
  /-- The radial profile `𝔮̂` of the `U`-marginal, entering the jump coefficient. -/
  qh : ℝ → ℝ
  /-- The outer function `Q` of the cylindrical statistic. -/
  Q : EuclideanSpace ℝ (Fin J) → ℝ
  /-- The features `φ_1, …, φ_J` of the cylindrical statistic. -/
  φ : Fin J → Lp (EuclideanSpace ℝ (Fin m)) 2 ν → ℝ
  /-- The reference law `μ₀` of the full tuple. -/
  μ₀ : P2 (TupleH ν n m d)
  /-- The reference law `Λ₀` of the `U`-marginal. -/
  Λ₀ : P2 (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)
  /-- The direction `w₀` of the radial term of the driver. -/
  w₀ : EuclideanSpace ℝ (Fin m)
  /-- The direction `w₁` of the cylindrical term of the driver. -/
  w₁ : EuclideanSpace ℝ (Fin m)
  /-- The direction `v₀` of the drift. -/
  v₀ : EuclideanSpace ℝ (Fin n)
  /-- The direction `ĥ` of the jump coefficient. -/
  hhat : Lp (EuclideanSpace ℝ (Fin n)) 2 ν

/-- The Lipschitz bounds of Example 5.4: `ε ≥ 0`; `𝔮, 𝔮̃, 𝔮̂` Lipschitz with constants
`Lq, Lqb, Lqh ≥ 0`; `Q` Lipschitz for the Euclidean norm with constant `LQ ≥ 0`; and each feature
`φ_j` Lipschitz with constant `K_j`. -/
structure FullLawData.Lip (D : FullLawData ν n m d J) (Lq Lqb Lqh LQ : ℝ) (K : Fin J → ℝ) :
    Prop where
  /-- The size is nonnegative. -/
  ε_nonneg : 0 ≤ D.ε
  /-- The constant of `𝔮` is nonnegative. -/
  Lq_nonneg : 0 ≤ Lq
  /-- The constant of `𝔮̃` is nonnegative. -/
  Lqb_nonneg : 0 ≤ Lqb
  /-- The constant of `𝔮̂` is nonnegative. -/
  Lqh_nonneg : 0 ≤ Lqh
  /-- The constant of `Q` is nonnegative. -/
  LQ_nonneg : 0 ≤ LQ
  /-- `𝔮` is Lipschitz. -/
  q_lip : ∀ r r', |D.q r - D.q r'| ≤ Lq * |r - r'|
  /-- `𝔮̃` is Lipschitz. -/
  qb_lip : ∀ r r', |D.qb r - D.qb r'| ≤ Lqb * |r - r'|
  /-- `𝔮̂` is Lipschitz. -/
  qh_lip : ∀ r r', |D.qh r - D.qh r'| ≤ Lqh * |r - r'|
  /-- `Q` is Lipschitz for the Euclidean norm. -/
  Q_lip : ∀ v v', |D.Q v - D.Q v'| ≤ LQ * ‖v - v'‖
  /-- Each feature is Lipschitz. -/
  φ_lip : ∀ j u u', |D.φ j u - D.φ j u'| ≤ K j * ‖u - u'‖

/-- The constant `L_p = ε (|w₀| Lip(𝔮) + |v₀| Lip(𝔮̃) + |w₁| L_Q + ‖ĥ‖ Lip(𝔮̂))` of (3.5), with
`L_Q = Lip(Q) (∑_j Lip(φ_j)²)^{1/2}`. -/
noncomputable def FullLawData.lipConst (D : FullLawData ν n m d J) (Lq Lqb Lqh LQ : ℝ)
    (K : Fin J → ℝ) : ℝ :=
  D.ε * (‖D.w₀‖ * Lq + ‖D.v₀‖ * Lqb + ‖D.w₁‖ * (LQ * Real.sqrt (∑ j, K j ^ 2))
    + ‖D.hhat‖ * Lqh)

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- The perturbation of Example 5.4: `p_b = ε 𝔮̃(W₂(μ^U, Λ₀)) v₀`, `p_σ = 0`,
`p_h = ε 𝔮̂(W₂(μ^U, Λ₀)) ĥ` and
`p_f = ε 𝔮(W₂(μ, μ₀)) w₀ + ε Q(∫ φ_1 dμ^U, …, ∫ φ_J dμ^U) w₁`, with `W₂` on `P₂(H)` for the
Hilbert norm of `H`. -/
noncomputable def fullLawPert (D : FullLawData ν n m d J) : Coeffs ν n m d :=
  Coeffs.ofLaw (fun _ μ => (D.ε * D.qb (w2P μ.margU D.Λ₀)) • D.v₀) (fun _ _ => 0)
    (fun _ μ => (D.ε * D.qh (w2P μ.margU D.Λ₀)) • D.hhat)
    (fun _ μ => (D.ε * D.q (w2H μ D.μ₀)) • D.w₀
      + (D.ε * cylindricalFunctional D.Q D.φ μ.margU) • D.w₁)

variable {D : FullLawData ν n m d J} {Lq Lqb Lqh LQ : ℝ} {K : Fin J → ℝ}

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The constant `L_p` is nonnegative. -/
theorem FullLawData.lipConst_nonneg (hD : D.Lip Lq Lqb Lqh LQ K) :
    0 ≤ D.lipConst Lq Lqb Lqh LQ K := by
  have := hD.ε_nonneg
  have := hD.Lq_nonneg
  have := hD.Lqb_nonneg
  have := hD.Lqh_nonneg
  have := hD.LQ_nonneg
  unfold FullLawData.lipConst
  positivity

/-! ### The three law statistics -/

/-- **The radial statistic of the full law is Lipschitz**:
`|𝔮(W₂(μ, μ₀)) − 𝔮(W₂(μ', μ₀))| ≤ Lip(𝔮) W₂(μ, μ')`, for the Hilbert-norm `W₂`. -/
theorem abs_radial_w2H_sub_le {q : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hq : ∀ r r', |q r - q r'| ≤ L * |r - r'|) (μ₀ μ μ' : P2 (TupleH ν n m d)) :
    |q (w2H μ μ₀) - q (w2H μ' μ₀)| ≤ L * w2H μ μ' :=
  (hq _ _).trans (mul_le_mul_of_nonneg_left
    (abs_dist_sub_le μ.toP2WH μ'.toP2WH μ₀.toP2WH) hL)

/-- **The radial statistic of the `U`-marginal is Lipschitz**:
`|𝔮̃(W₂(μ^U, Λ₀)) − 𝔮̃(W₂(μ'^U, Λ₀))| ≤ Lip(𝔮̃) W₂(μ, μ')`, for the Hilbert-norm `W₂` on the
right. -/
theorem abs_radial_margU_sub_le {q : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hq : ∀ r r', |q r - q r'| ≤ L * |r - r'|) (Λ₀ : P2 (Lp (EuclideanSpace ℝ (Fin m)) 2 ν))
    (μ μ' : P2 (TupleH ν n m d)) :
    |q (w2P μ.margU Λ₀) - q (w2P μ'.margU Λ₀)| ≤ L * w2H μ μ' :=
  (hq _ _).trans (mul_le_mul_of_nonneg_left
    ((abs_w2P_sub_w2P_le μ.margU μ'.margU Λ₀).trans (w2P_margU_le_w2H μ μ')) hL)

/-- A real function with a Lipschitz bound is continuous. -/
theorem continuous_of_abs_sub_le {X : Type*} [PseudoMetricSpace X] {f : X → ℝ} {L : ℝ}
    (hf : ∀ x y, |f x - f y| ≤ L * dist x y) : Continuous f :=
  (LipschitzWith.of_dist_le' fun x y => by rw [Real.dist_eq]; exact hf x y).continuous

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- A feature with a Lipschitz bound is strongly measurable. -/
theorem stronglyMeasurable_of_abs_sub_le {φ : Lp (EuclideanSpace ℝ (Fin m)) 2 ν → ℝ} {L : ℝ}
    (hφ : ∀ u u', |φ u - φ u'| ≤ L * ‖u - u'‖) : StronglyMeasurable φ :=
  (continuous_of_abs_sub_le fun u u' => by rw [dist_eq_norm]; exact hφ u u').stronglyMeasurable

/-- **The cylindrical statistic of the `U`-marginal is Lipschitz**:
`|Q((∫ φ_j dμ^U)_j) − Q((∫ φ_j dμ'^U)_j)| ≤ L_Q W₂(μ, μ')`,
`L_Q = Lip(Q) (∑_j Lip(φ_j)²)^{1/2}`, for the Hilbert-norm `W₂` on the right. -/
theorem abs_cylindrical_margU_sub_le {Q : EuclideanSpace ℝ (Fin J) → ℝ}
    {φ : Fin J → Lp (EuclideanSpace ℝ (Fin m)) 2 ν → ℝ} {LQ : ℝ} (hLQ : 0 ≤ LQ)
    (hQ : ∀ v v', |Q v - Q v'| ≤ LQ * ‖v - v'‖)
    (hφ : ∀ j u u', |φ j u - φ j u'| ≤ K j * ‖u - u'‖) (μ μ' : P2 (TupleH ν n m d)) :
    |cylindricalFunctional Q φ μ.margU - cylindricalFunctional Q φ μ'.margU|
      ≤ LQ * Real.sqrt (∑ j, K j ^ 2) * w2H μ μ' :=
  (norm_cylindricalFunctional_sub_le hLQ hQ (fun j => stronglyMeasurable_of_abs_sub_le (hφ j))
    hφ μ.margU μ'.margU).trans
    (mul_le_mul_of_nonneg_left (w2P_margU_le_w2H μ μ') (by positivity))

/-! ### (3.5) -/

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- A scalar gap `|a − a'| ≤ c W` scaled by `ε ≥ 0` along a direction `w` gives
`‖(ε a) w − (ε a') w‖ ≤ ε ‖w‖ c W`. -/
theorem norm_mul_smul_sub_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (w : F)
    {ε a a' c W : ℝ} (hε : 0 ≤ ε) (h : |a - a'| ≤ c * W) :
    ‖(ε * a) • w - (ε * a') • w‖ ≤ ε * ‖w‖ * c * W := by
  rw [← sub_smul, norm_smul, ← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg hε]
  have hw := norm_nonneg w
  calc ε * |a - a'| * ‖w‖ ≤ ε * (c * W) * ‖w‖ := by gcongr
    _ = ε * ‖w‖ * c * W := by ring

/-- **(3.5) for the perturbation of Example 5.4, pointwise**: at every time, pair of points and
pair of laws, `|δp_b| + |δp_σ|_F + ‖δp_h‖_{L²(ν)} + |δp_f| ≤ L_p W₂(μ, μ')`, with the Hilbert-norm
`W₂` and `L_p = ε (|w₀| Lip(𝔮) + |v₀| Lip(𝔮̃) + |w₁| L_Q + ‖ĥ‖ Lip(𝔮̂))`. -/
theorem norm_fullLawPert_sub_le (hD : D.Lip Lq Lqb Lqh LQ K) (t : ℝ) (θ θ' : TupleH ν n m d)
    (μ μ' : P2 (TupleH ν n m d)) :
    ‖(fullLawPert D).b t θ μ - (fullLawPert D).b t θ' μ'‖
        + ‖(fullLawPert D).σ t θ μ - (fullLawPert D).σ t θ' μ'‖
        + ‖(fullLawPert D).h t θ μ - (fullLawPert D).h t θ' μ'‖
        + ‖(fullLawPert D).f t θ μ - (fullLawPert D).f t θ' μ'‖
      ≤ D.lipConst Lq Lqb Lqh LQ K * w2H μ μ' := by
  set W := w2H μ μ'
  have hb := norm_mul_smul_sub_le D.v₀ hD.ε_nonneg
    (abs_radial_margU_sub_le hD.Lqb_nonneg hD.qb_lip D.Λ₀ μ μ')
  have hh := norm_mul_smul_sub_le D.hhat hD.ε_nonneg
    (abs_radial_margU_sub_le hD.Lqh_nonneg hD.qh_lip D.Λ₀ μ μ')
  have hf₀ := norm_mul_smul_sub_le D.w₀ hD.ε_nonneg
    (abs_radial_w2H_sub_le hD.Lq_nonneg hD.q_lip D.μ₀ μ μ')
  have hf₁ := norm_mul_smul_sub_le D.w₁ hD.ε_nonneg
    (abs_cylindrical_margU_sub_le hD.LQ_nonneg hD.Q_lip hD.φ_lip μ μ')
  have hf : ‖(fullLawPert D).f t θ μ - (fullLawPert D).f t θ' μ'‖
      ≤ D.ε * ‖D.w₀‖ * Lq * W + D.ε * ‖D.w₁‖ * (LQ * Real.sqrt (∑ j, K j ^ 2)) * W := by
    simp only [fullLawPert, Coeffs.ofLaw]
    rw [add_sub_add_comm]
    refine (norm_add_le _ _).trans (add_le_add hf₀ ?_)
    calc _ ≤ D.ε * ‖D.w₁‖ * (LQ * Real.sqrt (∑ j, K j ^ 2)) * W := hf₁
      _ = _ := rfl
  have hσ : ‖(fullLawPert D).σ t θ μ - (fullLawPert D).σ t θ' μ'‖ = 0 := by
    simp [fullLawPert, Coeffs.ofLaw]
  have hb' : ‖(fullLawPert D).b t θ μ - (fullLawPert D).b t θ' μ'‖
      ≤ D.ε * ‖D.v₀‖ * Lqb * W := hb
  have hh' : ‖(fullLawPert D).h t θ μ - (fullLawPert D).h t θ' μ'‖
      ≤ D.ε * ‖D.hhat‖ * Lqh * W := hh
  have e : D.lipConst Lq Lqb Lqh LQ K * W = D.ε * ‖D.v₀‖ * Lqb * W + D.ε * ‖D.hhat‖ * Lqh * W
      + (D.ε * ‖D.w₀‖ * Lq * W + D.ε * ‖D.w₁‖ * (LQ * Real.sqrt (∑ j, K j ^ 2)) * W) := by
    unfold FullLawData.lipConst
    ring
  rw [e, hσ]
  linarith

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The perturbation of Example 5.4 is independent of the tuple.** -/
theorem tupleIndep_fullLaw : (fullLawPert D).TupleIndep :=
  Coeffs.tupleIndep_ofLaw _ _ _ _

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **(3.5) for the perturbation of Example 5.4**, along the diagonal with the Hilbert-norm `W₂`
and the constant `L_p = ε (|w₀| Lip(𝔮) + |v₀| Lip(𝔮̃) + |w₁| L_Q + ‖ĥ‖ Lip(𝔮̂))`. -/
theorem diagonalLawLipschitzH_fullLaw (hD : D.Lip Lq Lqb Lqh LQ K) :
    DiagonalLawLipschitzH ℱ P T (D.lipConst Lq Lqb Lqh LQ K) (fullLawPert D) :=
  Eventually.of_forall fun t Θ Θ' _ _ _ _ => Eventually.of_forall fun ω =>
    norm_fullLawPert_sub_le hD t (Θ ω) (Θ' ω) _ _

/-- **Assumption 2.3, interior, for the perturbation of Example 5.4**, along the diagonal with the
Hilbert-norm `W₂` and the constant `L_p`. -/
theorem diagonalLipschitzH_fullLaw (hD : D.Lip Lq Lqb Lqh LQ K) :
    DiagonalLipschitzH ℱ P T (D.lipConst Lq Lqb Lqh LQ K) (fullLawPert D) :=
  (diagonalLawLipschitzH_fullLaw hD).diagonalLipschitzH (FullLawData.lipConst_nonneg hD)

/-- **(3.4) for the perturbation of Example 5.4** with `c_pert = ‖G‖ L_p`, `‖G‖` the operator
norm of `GX G`. -/
theorem diagonalPairingBound_fullLaw (hD : D.Lip Lq Lqb Lqh LQ K) (G : Matrix (Fin m) (Fin n) ℝ) :
    DiagonalPairingBound ℱ P T G (‖GX G‖ * D.lipConst Lq Lqb Lqh LQ K) (fullLawPert D) :=
  (diagonalLawLipschitzH_fullLaw hD).diagonalPairingBound tupleIndep_fullLaw
    (FullLawData.lipConst_nonneg hD) G

/-! ### Assumption 2.2 and (2.3) -/

/-- **Assumption 2.2 for the perturbation of Example 5.4**: its origin values are constant in
time. -/
theorem coeffOrigin_fullLaw (T : ℝ) : CoeffOrigin T (fullLawPert D) :=
  originIntegrable_const T _ _ _ _

/-- **(2.3) for the perturbation of Example 5.4, with the Hilbert-norm `W₂` on `P₂(H)`**: its
coefficients are Lipschitz in the law for that distance and independent of the time and the
tuple, hence continuous, so Borel measurable on `[0, T] × H × P₂(H)`. -/
theorem coeffBorelW2_fullLaw (hD : D.Lip Lq Lqb Lqh LQ K) (T : ℝ) :
    CoeffBorelW2 T (fullLawPert D) := by
  have hμ : Continuous fun p : Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d =>
      p.2.2 :=
    continuous_snd.comp continuous_snd
  have hc : ∀ {F : P2 (TupleH ν n m d) → ℝ} {L : ℝ}, (∀ μ μ', |F μ - F μ'| ≤ L * w2H μ μ') →
      Continuous fun p : Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d =>
        F p.2.2.toP2 := fun h =>
    (continuous_of_abs_sub_le (X := TupleP2WH ν n m d) fun μ μ' => h μ.toP2 μ'.toP2).comp hμ
  have hb := hc (abs_radial_margU_sub_le hD.Lqb_nonneg hD.qb_lip D.Λ₀)
  have hh := hc (abs_radial_margU_sub_le hD.Lqh_nonneg hD.qh_lip D.Λ₀)
  have hf₀ := hc (abs_radial_w2H_sub_le hD.Lq_nonneg hD.q_lip D.μ₀)
  have hf₁ := hc (abs_cylindrical_margU_sub_le hD.LQ_nonneg hD.Q_lip hD.φ_lip)
  exact
    { b_meas := Continuous.borel_measurable ((continuous_const.mul hb).smul continuous_const)
      σ_meas := Continuous.borel_measurable continuous_const
      h_meas := Continuous.borel_measurable ((continuous_const.mul hh).smul continuous_const)
      f_meas := Continuous.borel_measurable (((continuous_const.mul hf₀).smul continuous_const).add
        ((continuous_const.mul hf₁).smul continuous_const)) }

end Dissertation.WellPosedness.System
