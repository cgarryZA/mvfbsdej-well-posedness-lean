/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec5
import Dissertation.Acceptance.A.Sec3
import Dissertation.WellPosedness.Spec.Examples
import Dissertation.WellPosedness.Spec.LiMin
import Dissertation.WellPosedness.Existence.ClampExample
import Dissertation.WellPosedness.BrownianPoisson.FrozenCell
import LevyStochCalc.Brownian.ItoCellIsometry
import LevyStochCalc.Ito.CompensatedCellIsometry
import Dissertation.WellPosedness.Enlarged.Bot
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Dissertation.WellPosedness.Remarks.LinearMean
import Dissertation.WellPosedness.Examples.LinearGenerator
import Dissertation.WellPosedness.Analysis.DiagMatrix
import Dissertation.WellPosedness.Examples.BrownianFiltration
import Dissertation.WellPosedness.Examples.Nemytskii
import Dissertation.WellPosedness.Examples.FullLawBeyondRef

/-!
# Section 5 of the well-posedness paper: proofs of the examples

## Main statements

* `Dissertation.Acceptance.A.ex_concrete_i_ham`, `ex_concrete_i`, `ex_concrete_i_pairing`,
  `ex_concrete_i_wp`, `ex_concrete_i_clamp`, `ex_concrete_i_clamp_wp` — Example 5.1(i).
* `Dissertation.Acceptance.A.ex_concrete_ii_mean`, `ex_concrete_ii`, `ex_concrete_ii_pairing` —
  Example 5.1(ii).
* `Dissertation.Acceptance.A.ex_brownian` — Example 5.2, with the linear generator
  `(−Gᵀ y, −Gᵀ z, −Gᵀ u, 0)`, `g(x, ρ) = G x` and the diagonal `G`, `α = β₁ = 1`, `β₂ = 0`.
* `Dissertation.Acceptance.A.ex_expfunc`, `ex_expfunc_limin`, `ex_expfunc_jump` — Example 5.3.
* `Dissertation.Acceptance.A.ex_fulllaw_lip`, `ex_fulllaw_pert`, `ex_fulllaw_wp`,
  `ex_fulllaw_affineQ` — Example 5.4.
* `Dissertation.Acceptance.A.ex_fulllaw_beyond_radial`, `ex_fulllaw_beyond_U_corr`,
  `ex_fulllaw_beyond_Q` — Example 5.4, the three law statistics are no expectation functionals.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.Law

universe u v w

section Hamiltonian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For `a + b = 1`, `‖a x + b y‖² = a ‖x‖² + b ‖y‖² − a b ‖x − y‖²`. -/
theorem norm_smul_add_smul_sq (x y : V) {a b : ℝ} (hab : a + b = 1) :
    ‖a • x + b • y‖ ^ 2 = a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 - a * b * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  obtain rfl : b = 1 - a := by linarith
  ring

/-- Completing the square: for `β > 0`,
`⟨a, y⟩ + ‖a‖² / (2β) = −(β/2) ‖y‖² + ‖a + β y‖² / (2β)`. -/
theorem inner_add_norm_sq_div (a y : V) {β : ℝ} (hβ : 0 < β) :
    inner ℝ a y + 1 / (2 * β) * ‖a‖ ^ 2
      = -(β / 2) * ‖y‖ ^ 2 + 1 / (2 * β) * ‖a + β • y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp
  ring

/-- An affine functional plus `q (‖a₁‖² + ‖a₂‖² + ‖a₃‖²)` with `q > 0` is strictly convex on a
product of three inner product spaces. -/
theorem strictConvexOn_inner_add_norm_sq {V₁ V₂ V₃ : Type*} [NormedAddCommGroup V₁]
    [InnerProductSpace ℝ V₁] [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
    [NormedAddCommGroup V₃] [InnerProductSpace ℝ V₃] (w₁ : V₁) (w₂ : V₂) (w₃ : V₃) (k q : ℝ)
    (hq : 0 < q) :
    StrictConvexOn ℝ Set.univ fun a : V₁ × V₂ × V₃ =>
      inner ℝ a.1 w₁ + inner ℝ a.2.1 w₂ + inner ℝ a.2.2 w₃ + k
        + q * (‖a.1‖ ^ 2 + ‖a.2.1‖ ^ 2 + ‖a.2.2‖ ^ 2) := by
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  have hS : 0 < ‖x.1 - y.1‖ ^ 2 + ‖x.2.1 - y.2.1‖ ^ 2 + ‖x.2.2 - y.2.2‖ ^ 2 := by
    by_contra hS
    have h₁ : ‖x.1 - y.1‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖x.1 - y.1‖, sq_nonneg ‖x.2.1 - y.2.1‖, sq_nonneg ‖x.2.2 - y.2.2‖]
    have h₂ : ‖x.2.1 - y.2.1‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖x.1 - y.1‖, sq_nonneg ‖x.2.1 - y.2.1‖, sq_nonneg ‖x.2.2 - y.2.2‖]
    have h₃ : ‖x.2.2 - y.2.2‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖x.1 - y.1‖, sq_nonneg ‖x.2.1 - y.2.1‖, sq_nonneg ‖x.2.2 - y.2.2‖]
    simp only [pow_eq_zero_iff two_ne_zero, norm_eq_zero, sub_eq_zero] at h₁ h₂ h₃
    exact hxy (Prod.ext h₁ (Prod.ext h₂ h₃))
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, inner_add_left,
    real_inner_smul_left, smul_eq_mul, norm_smul_add_smul_sq _ _ hab]
  have hab' : a * b > 0 := mul_pos ha hb
  have k_eq : k = a * k + b * k := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_pos hq (mul_pos hab' hS)]

end Hamiltonian

/-- Example 5.1(i), the Hamiltonian and its minimiser. -/
theorem ex_concrete_i_ham : PaperSpec.A.ex_concrete_i_ham.{v} := by
  intro E _ ν β₁ β₂ hβ₁ σc hc x y z u H
  have hint : ∀ w : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν,
      ∫ e, inner ℝ (hc e + w e) (u e) ∂ν = inner ℝ hc u + inner ℝ w u := fun w => by
    rw [← inner_add_left, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add hc w] with e he
    rw [he, Pi.add_apply]
  have hH : H = fun a => inner ℝ a.1 y + inner ℝ a.2.1 z + inner ℝ a.2.2 u
      + (inner ℝ σc z + inner ℝ hc u + β₂ / 2 * ‖x‖ ^ 2)
      + 1 / (2 * β₁) * (‖a.1‖ ^ 2 + ‖a.2.1‖ ^ 2 + ‖a.2.2‖ ^ 2) := by
    funext a
    simp only [H]
    rw [hint, inner_add_left]
    ring
  rw [hH]
  refine ⟨strictConvexOn_inner_add_norm_sq y z u _ _ (by positivity), fun a => ?_⟩
  dsimp only
  have e₁ := inner_add_norm_sq_div a.1 y hβ₁
  have e₂ := inner_add_norm_sq_div a.2.1 z hβ₁
  have e₃ := inner_add_norm_sq_div a.2.2 u hβ₁
  have f₁ := inner_add_norm_sq_div (-(β₁ • y)) y hβ₁
  have f₂ := inner_add_norm_sq_div (-(β₁ • z)) z hβ₁
  have f₃ := inner_add_norm_sq_div (-(β₁ • u)) u hβ₁
  simp only [neg_add_cancel, norm_zero] at f₁ f₂ f₃
  have hq : 0 ≤ 1 / (2 * β₁) := by positivity
  nlinarith [mul_nonneg hq (sq_nonneg ‖a.1 + β₁ • y‖), mul_nonneg hq (sq_nonneg ‖a.2.1 + β₁ • z‖),
    mul_nonneg hq (sq_nonneg ‖a.2.2 + β₁ • u‖)]

/-- Example 5.1(i), the assumptions. -/
theorem ex_concrete_i : PaperSpec.A.ex_concrete_i.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ _ T _ β₁ β₂ hβ₁ hβ₂ σc hc ξ₀ hξm hξ
  obtain ⟨hJ, -, h23, hG, h25⟩ :=
    affine_assumptions (ν := ν) (ℱ := enlJoint 𝒢₀ D h𝒢₀) (P := P) (T := T) (σc := σc) (hc := hc)
      hβ₁ hβ₂ (0 : EuclideanSpace ℝ (Fin 1))
  refine ⟨hJ, ⟨hξm, hξ, originValues_iff_coeffOrigin.mpr (coeffOrigin_affine T)⟩, h23, hG, ?_,
    h25⟩
  rw [sMin_one]
  norm_num

/-- Example 5.1(i), the pairings. -/
theorem ex_concrete_i_pairing : PaperSpec.A.ex_concrete_i_pairing.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ _ T _ β₁ β₂ hβ₁ hβ₂ σc hc
  refine ⟨fun t p hp p' hp' => ?_, fun XT XT' _ _ _ _ => ?_, fun c hc0 hcm => ?_,
    fun t θ θ' μ μ' => ?_⟩
  · obtain ⟨-, h2, -⟩ := hp
    obtain ⟨-, h2', -⟩ := hp'
    have hpt : ∀ ω, pairing27 (1 : Matrix (Fin 1) (Fin 1) ℝ) (affineCoeffs β₁ β₂ σc hc) t
        (p.1 ω) (p'.1 ω) p.2 p'.2
        = WellPosedness.dissipation (GX (1 : Matrix (Fin 1) (Fin 1) ℝ)) (GZ 1) (GU 1 ν) β₁ β₂
          (diagDiff (affineCoeffs β₁ β₂ σc hc) t (p.1 ω) (p'.1 ω) p.2 p'.2) := fun ω => by
      rw [pairing27_eq, interiorPairing_affine]
    rw [integral_congr_ae (ae_of_all _ hpt), integral_dissipation_eq h2 h2']
    simp only [Matrix.transpose_one, GX_one, GZ_one, GU_one, ContinuousLinearMap.id_apply]
  · simp only [affineCoeffs, real_inner_self_eq_norm_sq]
  · exact (margin213_iff hc0 (by linarith [min_le_left β₁ β₂])
      (by linarith [min_le_right β₁ β₂])).mpr (diagonalMonotoneMargin_affine_sub β₁ β₂ c)
  · rw [← jumpPairing_affine (β₂ := β₂) (σc := σc) (hc := hc) t θ θ' μ μ']
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub ((affineCoeffs β₁ β₂ σc hc).h t θ μ)
        ((affineCoeffs β₁ β₂ σc hc).h t θ' μ'), Lp.coeFn_sub θ.2.2.2 θ'.2.2.2] with e h₁ h₂
    rw [h₁, h₂, Pi.sub_apply, Pi.sub_apply]

/-- Example 5.1(i), well-posedness. -/
theorem ex_concrete_i_wp : PaperSpec.A.ex_concrete_i_wp.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc ξ₀ hξm hξ
  obtain ⟨hJ, h22, h23, hG, -, h25⟩ :=
    ex_concrete_i 𝒢₀ ν P D h𝒢₀ hind₀ T hT β₁ β₂ hβ₁ hβ₂ σc hc ξ₀ hξm hξ
  exact thm_cwp 𝒢₀ ν 1 1 1 P D h𝒢₀ hind₀ one_pos one_pos one_pos T hT _ 1 β₁ β₂ 1 _ ξ₀ hJ h22
    h23 hG h25

/-- Example 5.1(i) with the drift (3.6), the assumptions. -/
theorem ex_concrete_i_clamp : PaperSpec.A.ex_concrete_i_clamp.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ _ T _ β₁ β₂ ε hβ₁ hβ₂ hε hεβ σc hc ξ₀ hξm hξ
  have hJ : JointBorel T (clampAffineCoeffs β₁ β₂ ε σc hc) :=
    jointBorel_iff.mpr ⟨coeffBorelW2_clampAffine T, continuous_fst.borel_measurable⟩
  obtain ⟨hL, hLT⟩ := diagonalLipschitzH_and_terminalLipschitz_clampAffine
    (ℱ := enlJoint 𝒢₀ D h𝒢₀) (P := P) (T := T) (σc := σc) (hc := hc) hβ₁.le hβ₂.le hε.le
  have h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T (max (max (β₁ + ε) β₂) 1)
      (clampAffineCoeffs β₁ β₂ ε σc hc) :=
    ⟨zero_le_one.trans (le_max_right _ _), lipInterior_iff_diagonalLipschitzH.mpr hL,
      lipTerminal_iff_terminalLipschitz.mpr hLT⟩
  refine ⟨hJ, ⟨hξm, hξ, originValues_iff_coeffOrigin.mpr (coeffOrigin_clampAffine T)⟩, ⟨_, h23⟩,
    rank_one_eq_min, Assumption25.of_monotone hJ h23 (constants_affine (sub_pos.mpr hεβ) hβ₂)
      (diagonalMonotone_clampAffine hε.le) ?_⟩
  exact terminalMonotone_affine (β₁ := β₁) (β₂ := β₂) (σc := σc) (hc := hc)

/-- Example 5.1(i) with the drift (3.6), well-posedness. -/
theorem ex_concrete_i_clamp_wp : PaperSpec.A.ex_concrete_i_clamp_wp.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ hind₀ T hT β₁ β₂ ε hβ₁ hβ₂ hε hεβ σc hc ξ₀ hξm hξ
  obtain ⟨hJ, h22, ⟨L, h23⟩, hG, h25⟩ :=
    ex_concrete_i_clamp 𝒢₀ ν P D h𝒢₀ hind₀ T hT β₁ β₂ ε hβ₁ hβ₂ hε hεβ σc hc ξ₀ hξm hξ
  exact thm_cwp 𝒢₀ ν 1 1 1 P D h𝒢₀ hind₀ one_pos one_pos one_pos T hT L 1 (β₁ - ε) β₂ 1 _ ξ₀
    hJ h22 h23 hG h25

/-- Example 5.1(ii), the mean and the barycentre. -/
theorem ex_concrete_ii_mean : PaperSpec.A.ex_concrete_ii_mean.{v} := by
  intro E _ ν _ _
  exact ⟨fun μ μ' => ⟨tupleMean_eq μ, norm_toL2_tupleMean_sub_le μ μ',
    tupleNorm_le_two_mul_norm_toL2 _⟩, norm_barycentre_sub_le⟩

/-- Example 5.1(ii), the assumptions. -/
theorem ex_concrete_ii : PaperSpec.A.ex_concrete_ii.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ _ T _ ξ₀ hξm hξ
  have hJ : JointBorel T (meanFieldCoeffs ν 1 1) :=
    jointBorel_iff.mpr ⟨coeffBorelW2_meanField T,
      ((continuous_fst.const_smul (2 : ℝ)).add
        (lipschitzWith_barycentre_toP2.continuous.comp continuous_snd)).borel_measurable⟩
  have h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T 2 (meanFieldCoeffs ν 1 1) :=
    ⟨zero_le_two, lipInterior_iff_diagonalLipschitzH.mpr diagonalLipschitzH_meanField,
      lipTerminal_iff_terminalLipschitz.mpr (terminalLipschitz_meanField le_rfl)⟩
  exact ⟨hJ, meanField_origin,
    ⟨hξm, hξ, originValues_iff_coeffOrigin.mpr (coeffOrigin_meanField T)⟩, h23, rank_one_eq_min,
    Assumption25.of_monotone hJ h23 constants_meanField diagonalMonotone_meanField
      terminalMonotone_meanField⟩

section MeanSquare

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A channel of a square-integrable random element is square integrable. -/
theorem memLp_comp_of_norm_le {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    {π : V → W} (hπ : Continuous π) (hle : ∀ v, ‖π v‖ ≤ ‖v‖) {f : Ω → V} (hf : MemLp f 2 P) :
    MemLp (fun ω => π (f ω)) 2 P :=
  hf.of_le (hπ.comp_aestronglyMeasurable hf.aestronglyMeasurable) (ae_of_all _ fun ω => hle (f ω))

/-- **Each channel contributes its own mean square**: for `W ∈ L²(Ω; V)`,
`𝔼⟨−2 W − 𝔼 W, W⟩ = −2 𝔼|W|² − |𝔼 W|²`. -/
theorem integral_inner_neg_two_smul_sub_integral [IsFiniteMeasure P] {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] {W : Ω → V}
    (hW : MemLp W 2 P) :
    ∫ ω, inner ℝ (-((2 : ℝ) • W ω) - ∫ ω, W ω ∂P) (W ω) ∂P
      = -2 * ∫ ω, ‖W ω‖ ^ 2 ∂P - ‖∫ ω, W ω ∂P‖ ^ 2 := by
  have hpt : ∀ ω, inner ℝ (-((2 : ℝ) • W ω) - ∫ ω, W ω ∂P) (W ω)
      = -2 * ‖W ω‖ ^ 2 - inner ℝ (∫ ω, W ω ∂P) (W ω) := fun ω => by
    rw [inner_sub_left, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  simp_rw [hpt]
  rw [integral_sub ((hW.integrable_norm_pow two_ne_zero).const_mul _)
      ((hW.integrable one_le_two).const_inner _), integral_const_mul,
    integral_inner (hW.integrable one_le_two), real_inner_self_eq_norm_sq]

end MeanSquare

/-- Example 5.1(ii), the pairings along the diagonal. -/
theorem ex_concrete_ii_pairing : PaperSpec.A.ex_concrete_ii_pairing.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ P _ D h𝒢₀ _ T _
  refine ⟨fun t p hp p' hp' => ?_, fun XT XT' _ _ hX hX' => integral_inner_meanField_g hX hX'⟩
  obtain ⟨-, h2, he⟩ := hp
  obtain ⟨-, h2', he'⟩ := hp'
  have hdm : MemLp (fun ω => p.1 ω - p'.1 ω) 2 P := h2.sub h2'
  have hd : Integrable (fun ω => p.1 ω - p'.1 ω) P := hdm.integrable one_le_two
  have hmean : tupleMean p.2 - tupleMean p'.2 = ∫ ω, (p.1 ω - p'.1 ω) ∂P := by
    rw [he, he', tupleMean_lawP2 h2, tupleMean_lawP2 h2',
      integral_sub (h2.integrable one_le_two) (h2'.integrable one_le_two)]
  have hX : MemLp (fun ω => (p.1 ω).1 - (p'.1 ω).1) 2 P :=
    memLp_comp_of_norm_le (π := fun v : TupleH ν 1 1 1 => v.1) continuous_fst norm_fst_le hdm
  have hY : MemLp (fun ω => (p.1 ω).2.1 - (p'.1 ω).2.1) 2 P :=
    memLp_comp_of_norm_le (π := fun v : TupleH ν 1 1 1 => v.2.1)
      (continuous_fst.comp continuous_snd)
      (fun v => (norm_fst_le v.2).trans (norm_snd_le v)) hdm
  have hZ : MemLp (fun ω => (p.1 ω).2.2.1 - (p'.1 ω).2.2.1) 2 P :=
    memLp_comp_of_norm_le (π := fun v : TupleH ν 1 1 1 => v.2.2.1)
      (continuous_fst.comp (continuous_snd.comp continuous_snd))
      (fun v => ((norm_fst_le v.2.2).trans (norm_snd_le v.2)).trans (norm_snd_le v)) hdm
  have hU : MemLp (fun ω => (p.1 ω).2.2.2 - (p'.1 ω).2.2.2) 2 P :=
    memLp_comp_of_norm_le (π := fun v : TupleH ν 1 1 1 => v.2.2.2)
      (continuous_snd.comp (continuous_snd.comp continuous_snd))
      (fun v => ((norm_snd_le v.2.2).trans (norm_snd_le v.2)).trans (norm_snd_le v)) hdm
  have mX : (tupleMean p.2).1 - (tupleMean p'.2).1 = ∫ ω, ((p.1 ω).1 - (p'.1 ω).1) ∂P := by
    change (tupleMean p.2 - tupleMean p'.2).1 = _
    rw [hmean, fst_integral hd]
    rfl
  have mY : (tupleMean p.2).2.1 - (tupleMean p'.2).2.1
      = ∫ ω, ((p.1 ω).2.1 - (p'.1 ω).2.1) ∂P := by
    change (tupleMean p.2 - tupleMean p'.2).2.1 = _
    rw [hmean, snd_integral hd, fst_integral hd.snd]
    rfl
  have mZ : (tupleMean p.2).2.2.1 - (tupleMean p'.2).2.2.1
      = ∫ ω, ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1) ∂P := by
    change (tupleMean p.2 - tupleMean p'.2).2.2.1 = _
    rw [hmean, snd_integral hd, snd_integral hd.snd, fst_integral hd.snd.snd]
    rfl
  have mU : (tupleMean p.2).2.2.2 - (tupleMean p'.2).2.2.2
      = ∫ ω, ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2) ∂P := by
    change (tupleMean p.2 - tupleMean p'.2).2.2.2 = _
    rw [hmean, snd_integral hd, snd_integral hd.snd, snd_integral hd.snd.snd]
    rfl
  refine ⟨by rw [he]; exact tupleMean_lawP2 h2, ?_, ?_, ?_, ?_, ?_⟩
  · have e : ∀ ω, -((meanFieldCoeffs ν 1 1).f t (p.1 ω) p.2
        - (meanFieldCoeffs ν 1 1).f t (p'.1 ω) p'.2)
        = -((2 : ℝ) • ((p.1 ω).1 - (p'.1 ω).1)) - ∫ ω, ((p.1 ω).1 - (p'.1 ω).1) ∂P :=
      fun ω => by
        rw [← mX]
        simp only [meanFieldCoeffs]
        rw [smul_sub]
        abel
    simp_rw [e]
    exact integral_inner_neg_two_smul_sub_integral hX
  · have e : ∀ ω, (meanFieldCoeffs ν 1 1).b t (p.1 ω) p.2
        - (meanFieldCoeffs ν 1 1).b t (p'.1 ω) p'.2
        = -((2 : ℝ) • ((p.1 ω).2.1 - (p'.1 ω).2.1)) - ∫ ω, ((p.1 ω).2.1 - (p'.1 ω).2.1) ∂P :=
      fun ω => by
        rw [← mY]
        simp only [meanFieldCoeffs]
        rw [smul_sub]
        abel
    simp_rw [e]
    exact integral_inner_neg_two_smul_sub_integral hY
  · have e : ∀ ω, (meanFieldCoeffs ν 1 1).σ t (p.1 ω) p.2
        - (meanFieldCoeffs ν 1 1).σ t (p'.1 ω) p'.2
        = -((2 : ℝ) • ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1))
          - ∫ ω, ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1) ∂P :=
      fun ω => by
        rw [← mZ]
        simp only [meanFieldCoeffs]
        rw [smul_sub]
        abel
    simp_rw [e]
    exact integral_inner_neg_two_smul_sub_integral hZ
  · have e : ∀ ω, (meanFieldCoeffs ν 1 1).h t (p.1 ω) p.2
        - (meanFieldCoeffs ν 1 1).h t (p'.1 ω) p'.2
        = -((2 : ℝ) • ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2))
          - ∫ ω, ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2) ∂P :=
      fun ω => by
        rw [← mU]
        simp only [meanFieldCoeffs]
        rw [smul_sub]
        abel
    have hL2 : ∀ ω, ∫ e, inner ℝ ((meanFieldCoeffs ν 1 1).h t (p.1 ω) p.2 e
          - (meanFieldCoeffs ν 1 1).h t (p'.1 ω) p'.2 e)
          ((p.1 ω).2.2.2 e - (p'.1 ω).2.2.2 e) ∂ν
        = inner ℝ ((meanFieldCoeffs ν 1 1).h t (p.1 ω) p.2
          - (meanFieldCoeffs ν 1 1).h t (p'.1 ω) p'.2) ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2) :=
      fun ω => by
        rw [L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_sub ((meanFieldCoeffs ν 1 1).h t (p.1 ω) p.2)
            ((meanFieldCoeffs ν 1 1).h t (p'.1 ω) p'.2),
          Lp.coeFn_sub (p.1 ω).2.2.2 (p'.1 ω).2.2.2] with e h₁ h₂
        rw [h₁, h₂, Pi.sub_apply, Pi.sub_apply]
    simp_rw [hL2, e]
    exact integral_inner_neg_two_smul_sub_integral hU
  · have key := integral_interiorPairing_meanField h2 h2' t
    rw [← he, ← he'] at key
    simp_rw [pairing27_eq, key, dissipation_meanField, norm_toL2_sq]
    rw [integral_const_mul]
    simp only [channelSq, Prod.fst_sub, Prod.snd_sub]
    rw [fst_integral hd, snd_integral hd, fst_integral hd.snd, snd_integral hd.snd,
      fst_integral hd.snd.snd, snd_integral hd.snd.snd]
    rfl

/-- Example 5.2, the Brownian case `ν = 0`. -/
theorem ex_brownian : PaperSpec.A.ex_brownian.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ _ d P _ D h𝒢₀ _
  refine ⟨enlJoint_nu_zero_eq 𝒢₀ D h𝒢₀, fun m u => Subsingleton.elim u 0,
    fun n m μ μ' => w2P_projP2 μ μ', ?_⟩
  intro n m _ hmn _ T _ ξ₀ hξm hξ
  set G := Dissertation.WellPosedness.diagMatrix m n
  set C : Coeffs (0 : Measure E) n m d := Dissertation.WellPosedness.linearGenerator G 1 0
  have hJ : JointBorel T C :=
    jointBorel_iff.mpr ⟨WellPosedness.coeffBorelW2_linearGenerator T,
      ((GX G).continuous.comp continuous_fst).borel_measurable⟩
  have hL : max (1 * ‖GX G‖) (0 * ‖GX G‖) ≤ ‖GX G‖ := by
    rw [one_mul, zero_mul]
    exact max_le le_rfl (norm_nonneg _)
  have h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T ‖GX G‖ C :=
    ⟨norm_nonneg _, lipInterior_iff_diagonalLipschitzH.mpr (Eventually.of_forall fun t =>
      WellPosedness.diagonalLipschitzHAt_linearGenerator zero_le_one le_rfl hL t),
      lipTerminal_iff_terminalLipschitz.mpr
        (WellPosedness.terminalLipschitz_linearGenerator le_rfl)⟩
  have hconst : WellPosedness.Constants n m 1 1 0 :=
    ⟨zero_le_one, zero_le_one, le_rfl, by norm_num, by norm_num, fun _ => one_pos,
      fun h => (lt_asymm hmn h).elim⟩
  refine ⟨G, C, ‖GX G‖, 1, 1, 0, fun t θ θ' μ μ' _ => Subsingleton.elim _ _, hJ,
    ⟨hξm, hξ, originValues_iff_coeffOrigin.mpr (WellPosedness.coeffOrigin_linearGenerator T)⟩, h23,
    Dissertation.WellPosedness.rank_diagMatrix m n, Assumption25.of_monotone hJ h23 hconst
      (Eventually.of_forall fun t => WellPosedness.diagonalMonotoneAt_linearGenerator t)
      WellPosedness.terminalMonotone_linearGenerator, one_pos⟩

/-- Example 5.3, the class. -/
theorem ex_expfunc : PaperSpec.A.ex_expfunc.{v} := by
  intro E _ ν _ _ n m d k φbar L hL _ hlip t θ
  have hker : ∀ θ₁' θ₂' : TupleH ν n m d,
      ‖φbar t θ θ₁' - φbar t θ θ₂'‖ ≤ L * ‖toL2 θ₁' - toL2 θ₂'‖ := fun θ₁' θ₂' => by
    simpa using hlip t θ θ₁' θ θ₂'
  exact ⟨hker, fun μ μ' => norm_integral_sub_le_w2H hL hker μ μ'⟩

/-- The Hilbert norm of a block difference is the Euclidean norm of the four channel
differences. -/
theorem norm_toL2_sub_eq_sqrt {HX HY HZY HV : Type*} [NormedAddCommGroup HX]
    [InnerProductSpace ℝ HX] [NormedAddCommGroup HY] [InnerProductSpace ℝ HY]
    [NormedAddCommGroup HZY] [InnerProductSpace ℝ HZY] [NormedAddCommGroup HV]
    [InnerProductSpace ℝ HV] (a b : WellPosedness.Tuple HX HY HZY HV) :
    ‖toL2 a - toL2 b‖ = Real.sqrt (‖a.1 - b.1‖ ^ 2 + ‖a.2.1 - b.2.1‖ ^ 2
      + ‖a.2.2.1 - b.2.2.1‖ ^ 2 + ‖a.2.2.2 - b.2.2.2‖ ^ 2) := by
  rw [← toL2_sub, ← Real.sqrt_sq (norm_nonneg _), norm_toL2_sq]
  rfl

/-- Example 5.3, the kernels of independent-copy interactions. -/
theorem ex_expfunc_limin : PaperSpec.A.ex_expfunc_limin.{v} := by
  intro E _ ν _ n m d k ψbar Lip hLip hψ t
  have hψ' : KernelLipschitzH Lip ψbar := fun t a b a' b' => by
    rw [norm_toL2_sub_eq_sqrt, norm_toL2_sub_eq_sqrt]
    exact hψ t a a' b b'
  exact ⟨fun θ θ' => integrable_markIntegrand hLip hψ' t θ θ',
    fun θ₁ θ₁' θ₂ θ₂' => kernelLipschitzH_markKernel hLip hψ' t θ₁ θ₂ θ₁' θ₂',
    fun θ θ' v v' hv hv' => markKernel_congr ψbar t θ θ' hv hv'⟩

/-- Example 5.3, the jump coefficient. -/
theorem ex_expfunc_jump : PaperSpec.A.ex_expfunc_jump.{v} := by
  intro E _ ν _ _ n m d hbar
  refine ⟨fun t θ θ' v v' hv hv' => nemytskiiFun_congr hbar t θ θ' hv hv',
    fun H C hC _ hlip t θ μ μ' => ?_⟩
  have hker : ∀ θ₁' θ₂' : TupleH ν n m d,
      ‖H t θ θ₁' - H t θ θ₂'‖ ≤ C * ‖toL2 θ₁' - toL2 θ₂'‖ := fun θ₁' θ₂' => by
    simpa using hlip t θ θ₁' θ θ₂'
  exact norm_integral_sub_le_w2H hC hker μ μ'

/-- Example 5.4, the law statistics are `W₂`-Lipschitz. -/
theorem ex_fulllaw_lip : PaperSpec.A.ex_fulllaw_lip.{v} := by
  intro E _ ν _ _ n m d J q qb qh Q φ Lq Lqb Lqh LQ K hLq hLqb hLqh hLQ hq hqb hqh hQ hφ μ₀ Λ₀ μ μ'
  exact ⟨abs_radial_w2H_sub_le hLq hq μ₀ μ μ', abs_radial_margU_sub_le hLqb hqb Λ₀ μ μ',
    abs_radial_margU_sub_le hLqh hqh Λ₀ μ μ', abs_cylindrical_margU_sub_le hLQ hQ hφ μ μ'⟩

/-- The perturbation of Example 5.4 is the library's `fullLawPert`. -/
theorem ex54Pert_eq {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n d J : ℕ) (ε : ℝ) (q qb qh : ℝ → ℝ)
    (Q : EuclideanSpace ℝ (Fin J) → ℝ) (φ : Fin J → Lp (EuclideanSpace ℝ (Fin n)) 2 ν → ℝ)
    (μ₀ : P2 (TupleH ν n n d)) (Λ₀ : P2 (Lp (EuclideanSpace ℝ (Fin n)) 2 ν))
    (w₀ w₁ v₀ : EuclideanSpace ℝ (Fin n)) (hhat : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    PaperSpec.A.ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat
      = fullLawPert ⟨ε, q, qb, qh, Q, φ, μ₀, Λ₀, w₀, w₁, v₀, hhat⟩ :=
  rfl

/-- Example 5.4, the perturbation. -/
theorem ex_fulllaw_pert : PaperSpec.A.ex_fulllaw_pert.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n d J P _ D h𝒢₀ _ _ _ T _ G ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat Lq Lqb
    Lqh LQ K hε hLq hLqb hLqh hLQ hq hqb hqh hQ hφ
  have hD : FullLawData.Lip ⟨ε, q, qb, qh, Q, φ, μ₀, Λ₀, w₀, w₁, v₀, hhat⟩ Lq Lqb Lqh LQ K :=
    ⟨hε.le, hLq, hLqb, hLqh, hLQ, hq, hqb, hqh, hQ, hφ⟩
  rw [ex54Pert_eq]
  exact ⟨tupleIndep_fullLaw, originValues_iff_coeffOrigin.mpr (coeffOrigin_fullLaw T),
    lawLip35_iff.mpr (diagonalLawLipschitzH_fullLaw hD),
    lipInterior_iff_diagonalLipschitzH.mpr (diagonalLipschitzH_fullLaw hD),
    pairingBound34_iff.mpr (diagonalPairingBound_fullLaw hD G)⟩

/-- Example 5.4, well-posedness. -/
theorem ex_fulllaw_wp : PaperSpec.A.ex_fulllaw_wp.{u, v, w} := by
  obtain ⟨Cstab, hcor⟩ := cor_robust_wp.{u, v, w}
  refine ⟨Cstab, ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n d J P _ D h𝒢₀ hind₀ hn hd T hT L₀ α β₁ β₂ cdiss G C ξ₀ hJ h22 h23
    hG h25 h213 hcdiss ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat Lq Lqb Lqh LQ K hε hLq hLqb hLqh hLQ
    hq hqb hqh hQ hφ hsmall
  obtain ⟨-, horig, -, hLI, h34⟩ := ex_fulllaw_pert 𝒢₀ ν n d J P D h𝒢₀ hind₀ hn hd T hT G ε q qb
    qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat Lq Lqb Lqh LQ K hε hLq hLqb hLqh hLQ hq hqb hqh hQ hφ
  have hD : FullLawData.Lip ⟨ε, q, qb, qh, Q, φ, μ₀, Λ₀, w₀, w₁, v₀, hhat⟩ Lq Lqb Lqh LQ K :=
    ⟨hε.le, hLq, hLqb, hLqh, hLQ, hq, hqb, hqh, hQ, hφ⟩
  have hLp0 := FullLawData.lipConst_nonneg hD
  have hJp : JointBorel T (C.perturb (PaperSpec.A.ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁
      v₀ hhat)) := by
    rw [ex54Pert_eq]
    exact jointBorel_iff.mpr ⟨(jointBorel_iff.mp hJ).1.perturb (coeffBorelW2_fullLaw hD T),
      (jointBorel_iff.mp hJ).2⟩
  have hc : ‖GX G‖ * (ε * (‖w₀‖ * Lq + ‖v₀‖ * Lqb + ‖w₁‖ * (LQ * Real.sqrt (∑ j, K j ^ 2))
      + ‖hhat‖ * Lqh)) < cdiss := by
    calc _ = ε * ‖GX G‖ * (‖w₀‖ * Lq + ‖v₀‖ * Lqb + ‖w₁‖ * (LQ * Real.sqrt (∑ j, K j ^ 2))
          + ‖hhat‖ * Lqh) := by ring
      _ < cdiss := hsmall
  obtain ⟨h22', ⟨L, h23'⟩, -, h25', h213'⟩ := cor_robust 𝒢₀ ν n d P D h𝒢₀ hind₀ hn hd T hT L₀ _
    α β₁ β₂ cdiss _ G C _ ξ₀ hJ h22 h23 hG h25 h213 hcdiss horig hLI hLp0 h34
    (mul_nonneg (norm_nonneg _) hLp0) hJp hc
  have hwp := thm_cwp 𝒢₀ ν n n d P D h𝒢₀ hind₀ hn hn hd T hT L α β₁ β₂ G _ ξ₀ hJp h22' h23' hG
    h25'
  have hstab := (hcor 𝒢₀ ν n d P D h𝒢₀ hind₀ hn hd T hT L₀ _ α β₁ β₂ cdiss _ G C _ ξ₀ hJ h22 h23
    hG h25 h213 hcdiss horig hLI hLp0 h34 (mul_nonneg (norm_nonneg _) hLp0) hJp hc).2.2
  exact ⟨hJp, h22', ⟨L, h23'⟩, h25', h213', hwp.1, hwp.2, hstab⟩

/-- Example 5.4, the affine cylindrical term. -/
theorem ex_fulllaw_affineQ : PaperSpec.A.ex_fulllaw_affineQ.{v} := by
  intro E _ ν _ _ n m d J Q φ K a c hφ hQ μ
  have hs : ∀ j, StronglyMeasurable (φ j) := fun j => stronglyMeasurable_of_abs_sub_le (hφ j)
  have hint : ∀ j, Integrable (fun θ' : TupleH ν n m d => φ j θ'.2.2.2) μ.law := fun j => by
    have h : Integrable (φ j) μ.margU.law := integrable_of_norm_sub_le (hs j) (K := K j)
      (fun x y => by simpa only [Real.norm_eq_abs] using hφ j x y) μ.margU.secondMoment_ne_top
    rw [margU_law] at h
    exact (integrable_map_measure (hs j).aestronglyMeasurable
      measurable_projUH.aemeasurable).mp h
  have heq : ∀ j, ∫ u, φ j u ∂μ.margU.law = ∫ θ', φ j θ'.2.2.2 ∂μ.law := fun j => by
    rw [margU_law, integral_map measurable_projUH.aemeasurable (hs j).aestronglyMeasurable]
    rfl
  rw [hQ μ, integral_add (integrable_const a)
    (integrable_finsetSum _ fun j _ => (hint j).const_mul (c j)), integral_const,
    integral_finsetSum _ fun j _ => (hint j).const_mul (c j)]
  simp only [probReal_univ, one_smul, integral_const_mul, heq]

/-- Example 5.4, the radial statistic of the full law is no expectation functional. -/
theorem ex_fulllaw_beyond_radial : PaperSpec.A.ex_fulllaw_beyond_radial.{v} := by
  intro E _ ν _ _ n m d hn q Lq B hq hB hne μ₀ φ hφ
  exact exists_ne_integral_of_not_affineAlongMixtures (radial_not_affine_ref hn μ₀ hB hne) hφ

/-- Example 5.4, the radial statistic of the `U`-marginal is no expectation functional when
`L²(ν; ℝᵐ)` is not reduced to `0`. -/
theorem ex_fulllaw_beyond_U_corr : PaperSpec.A.ex_fulllaw_beyond_U_corr.{v} := by
  intro E _ ν _ _ n m d hu q Lq B hq hB hne Λ₀ φ hφ
  obtain ⟨u₀, hu₀⟩ := hu
  exact exists_ne_integral_of_not_affineAlongMixtures (radialU_not_affine_ref hu₀ Λ₀ hB hne) hφ

/-- Example 5.4, the cylindrical term is no expectation functional when `Q` is not affine on the
attained range of the feature vector. -/
theorem ex_fulllaw_beyond_Q : PaperSpec.A.ex_fulllaw_beyond_Q.{v} := by
  intro E _ ν _ _ n m d J Q φ LQ B K hQ hφ hφB hnot φ' hφ'
  by_contra hall
  push Not at hall
  exact hnot (exists_affine_cylindrical_of_eq_integral hφ hφ' hall)

end Dissertation.Acceptance.A
