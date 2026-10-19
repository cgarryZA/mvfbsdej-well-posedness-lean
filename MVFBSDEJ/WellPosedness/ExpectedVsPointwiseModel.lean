/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Support
import MVFBSDEJ.WellPosedness.ExpectedVsPointwise
import MVFBSDEJ.WellPosedness.System.HilbertLipschitz

/-!
# Expected diagonal monotonicity is strictly weaker than pointwise monotonicity, on the model

Proposition 3.8 of the well-posedness paper, on the tuple space `H = ℝ × ℝ × ℝ^{1×d} × L²(ν; ℝ)`
of the case `n = m = 1`, `G = 1`. The drift (3.6) is

`b(t, θ, μ) = −β₁ y + ε g₀(y − m_Y(μ))`, `g₀(r) = max(−1, min(1, r))`,

with `m_Y(μ) = ∫_H y μ(dθ)` the `Y`-marginal mean of a law of finite second moment. By (2.10)
for the map `θ ↦ y`, the mean is `1`-Lipschitz for `W₂`, so the drift is Lipschitz in the state
and in the law with constant `β₁ + ε`, at every pair of points and laws:

`|δb| ≤ (β₁ + ε) (|δy| + W₂(μ, μ'))`,

with `W₂` the 2-Wasserstein distance of the Hilbert norm (and a fortiori of the maximum of the
channel norms). Along diagonal inputs `(Θ, Law Θ)`, `(Θ', Law Θ')` with `Θ, Θ'` square integrable
the mean is the expectation, the clamp difference is bounded by the centred increment
`|δY − 𝔼 δY|`, and so

`𝔼⟨δb, δY⟩ ≤ −(β₁ − ε) 𝔼|δY|²`, (3.7)

with no integrability hypothesis beyond `Θ, Θ' ∈ L²`. Pointwise monotonicity fails on the supports:
for the two-point laws `μ = ½ δ_{(0,0,0,0)} + ½ δ_{(0,−2,0,0)}` and
`μ' = ½ δ_{(0,−s,0,0)} + ½ δ_{(0,−s+2,0,0)}`, `s = ε/β₁`, and the points `θ = (0, 0, 0, 0)`,
`θ' = (0, −s, 0, 0)` of their supports, the clamp arguments are `±1` and
`⟨δb, δy⟩ = s (2ε − β₁ s) = ε²/β₁ > 0`, which violates `⟨δb, δy⟩ ≤ −β |δy|²` for every `β ≥ 0`
at once.

## Main definitions

* `clampVec` — the clamp `g₀` on `ℝ¹`.
* `meanY` — the `Y`-marginal mean of a law of finite second moment on `H`.
* `clampDrift` — the drift (3.6).
* `twoPointLaw` — the law `½ δ_a + ½ δ_b`.
* `pointY` — the tuple `(0, c, 0, 0)`.

## Main statements

* `norm_meanY_sub_le_w2P`, `norm_meanY_sub_le_w2H` — the mean is `1`-Lipschitz for `W₂`.
* `norm_clampDrift_sub_le`, `norm_clampDrift_sub_le_w2P` — the Lipschitz bound with constant
  `β₁ + ε`.
* `integrable_inner_clampDrift`, `integral_inner_clampDrift_le` — the pairing is integrable along
  diagonal inputs, and (3.7).
* `exists_mem_support_forall_lt_inner_clampDrift`, `pointwise_monotonicity_fails_on_supports` —
  failure of pointwise monotonicity on the supports.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped ENNReal Topology

namespace MVFBSDEJ.WellPosedness.System

/-! ### The one-dimensional channel -/

section OneDim

/-- The Euclidean norm on `ℝ¹` is the absolute value of the coordinate. -/
theorem norm_eq_abs_fin_one (v : EuclideanSpace ℝ (Fin 1)) : ‖v‖ = |v 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, Real.sqrt_sq_eq_abs, abs_abs]

/-- The inner product on `ℝ¹` is the product of the coordinates. -/
theorem inner_eq_mul_fin_one (v w : EuclideanSpace ℝ (Fin 1)) : inner ℝ v w = v 0 * w 0 := by
  simp [PiLp.inner_apply]
  ring

/-- The clamp `g₀(r) = max(-1, min(1, r))` of (3.6), on `ℝ¹`. -/
noncomputable def clampVec (v : EuclideanSpace ℝ (Fin 1)) : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 fun i => clamp01 (v i)

/-- The coordinate of the clamp on `ℝ¹` is the clamp of the coordinate. -/
@[simp]
theorem clampVec_apply (v : EuclideanSpace ℝ (Fin 1)) (i : Fin 1) :
    clampVec v i = clamp01 (v i) := rfl

/-- The clamp is continuous. -/
theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

/-- The clamp is bounded by `1`. -/
theorem abs_clamp01_le (r : ℝ) : |clamp01 r| ≤ 1 :=
  abs_le.mpr (clamp01_mem r)

end OneDim

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {d : ℕ}

/-! ### The drift (3.6) -/

/-- The `Y`-marginal mean `m_Y(μ) = ∫_H y μ(dθ)` of a law of finite second moment on the tuple
space `H = ℝ × ℝ × ℝ^{1×d} × L²(ν; ℝ)`. -/
noncomputable def meanY (μ : P2 (TupleH ν 1 1 d)) : EuclideanSpace ℝ (Fin 1) :=
  ∫ θ, θ.2.1 ∂μ.law

/-- The drift (3.6) on the tuple space `H = ℝ × ℝ × ℝ^{1×d} × L²(ν; ℝ)`:
`b(t, θ, μ) = −β₁ y + ε g₀(y − m_Y(μ))`, with `g₀` the clamp to `[-1, 1]` and `m_Y(μ)` the
`Y`-marginal mean. -/
noncomputable def clampDrift (β₁ ε : ℝ) (_t : ℝ) (θ : TupleH ν 1 1 d)
    (μ : P2 (TupleH ν 1 1 d)) : EuclideanSpace ℝ (Fin 1) :=
  -(β₁ • θ.2.1) + ε • clampVec (θ.2.1 - meanY μ)

/-- The coordinate of the drift (3.6) is the scalar drift at the `Y`-coordinate and the
coordinate of the `Y`-marginal mean. -/
theorem clampDrift_apply (β₁ ε t : ℝ) (θ : TupleH ν 1 1 d) (μ : P2 (TupleH ν 1 1 d)) :
    clampDrift β₁ ε t θ μ 0 = drift β₁ ε (θ.2.1 0) (meanY μ 0) := by
  simp [clampDrift, drift]

/-- The `Y`-channel norm of a tuple is at most its Hilbert norm. -/
theorem norm_y_le_norm_toL2 {HX HY HZY HUY : Type*} [NormedAddCommGroup HX]
    [InnerProductSpace ℝ HX] [NormedAddCommGroup HY] [InnerProductSpace ℝ HY]
    [NormedAddCommGroup HZY] [InnerProductSpace ℝ HZY] [NormedAddCommGroup HUY]
    [InnerProductSpace ℝ HUY] (θ : Tuple HX HY HZY HUY) : ‖θ.2.1‖ ≤ ‖toL2 θ‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [norm_toL2_sq, channelSq]
  nlinarith [sq_nonneg ‖θ.1‖, sq_nonneg ‖θ.2.2.1‖, sq_nonneg ‖θ.2.2.2‖]

section Lipschitz

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- The `Y`-marginal mean is `1`-Lipschitz for the 2-Wasserstein distance of the maximum of the
channel norms. -/
theorem norm_meanY_sub_le_w2P (μ μ' : P2 (TupleH ν 1 1 d)) :
    ‖meanY μ - meanY μ'‖ ≤ w2P μ μ' := by
  have hm : StronglyMeasurable fun θ : TupleH ν 1 1 d => θ.2.1 :=
    (measurable_fst.comp measurable_snd).stronglyMeasurable
  have hlip : ∀ θ θ' : TupleH ν 1 1 d, ‖θ.2.1 - θ'.2.1‖ ≤ 1 * ‖θ - θ'‖ := fun θ θ' => by
    rw [one_mul]
    exact (norm_fst_le (θ - θ').2).trans (norm_snd_le (θ - θ'))
  simpa only [one_mul, meanY, w2P] using norm_integral_sub_le_w2_of_nonneg hm zero_le_one hlip
    (integrable_of_norm_sub_le hm hlip μ.secondMoment_ne_top)
    (integrable_of_norm_sub_le hm hlip μ'.secondMoment_ne_top) (w2sq_ne_top μ μ')

/-- **The `Y`-marginal mean is `1`-Lipschitz for `W₂`**, (2.10) for the map `θ ↦ y`, with `W₂`
the 2-Wasserstein distance of the Hilbert norm. -/
theorem norm_meanY_sub_le_w2H (μ μ' : P2 (TupleH ν 1 1 d)) :
    ‖meanY μ - meanY μ'‖ ≤ w2H μ μ' := by
  have h := norm_integral_sub_le_w2H (φ := fun θ : TupleH ν 1 1 d => θ.2.1) zero_le_one
    (fun θ θ' => by rw [one_mul, ← toL2_sub]; exact norm_y_le_norm_toL2 (θ - θ')) μ μ'
  simpa only [one_mul, meanY] using h

variable {β₁ ε : ℝ}

/-- The drift (3.6) is Lipschitz in the state and in the law, with constant `β₁ + ε` and `W₂`
the 2-Wasserstein distance of the maximum of the channel norms:
`|δb| ≤ (β₁ + ε) (|δy| + W₂(μ, μ'))` at every pair of points and laws. -/
theorem norm_clampDrift_sub_le_w2P (hβ₁ : 0 ≤ β₁) (hε : 0 ≤ ε) (t : ℝ)
    (θ θ' : TupleH ν 1 1 d) (μ μ' : P2 (TupleH ν 1 1 d)) :
    ‖clampDrift β₁ ε t θ μ - clampDrift β₁ ε t θ' μ'‖
      ≤ (β₁ + ε) * (‖θ.2.1 - θ'.2.1‖ + w2P μ μ') := by
  have h := drift_lipschitz hβ₁ hε (θ.2.1 0) (meanY μ 0) (θ'.2.1 0) (meanY μ' 0)
  have hm : |meanY μ 0 - meanY μ' 0| ≤ w2P μ μ' := by
    have := norm_meanY_sub_le_w2P μ μ'
    rwa [norm_eq_abs_fin_one, PiLp.sub_apply] at this
  rw [norm_eq_abs_fin_one, PiLp.sub_apply, clampDrift_apply, clampDrift_apply,
    norm_eq_abs_fin_one, PiLp.sub_apply]
  refine h.trans ?_
  have : 0 ≤ β₁ + ε := by linarith
  gcongr

/-- **Proposition 3.8, the Lipschitz bound.** The drift (3.6) is Lipschitz in the state and in
the law with constant `β₁ + ε`: `|δb| ≤ (β₁ + ε) (|δy| + W₂(μ, μ'))` at every pair of points and
laws, with `W₂` the 2-Wasserstein distance of the Hilbert norm. -/
theorem norm_clampDrift_sub_le (hβ₁ : 0 ≤ β₁) (hε : 0 ≤ ε) (t : ℝ) (θ θ' : TupleH ν 1 1 d)
    (μ μ' : P2 (TupleH ν 1 1 d)) :
    ‖clampDrift β₁ ε t θ μ - clampDrift β₁ ε t θ' μ'‖
      ≤ (β₁ + ε) * (‖θ.2.1 - θ'.2.1‖ + w2H μ μ') := by
  refine (norm_clampDrift_sub_le_w2P hβ₁ hε t θ θ' μ μ').trans ?_
  have : 0 ≤ β₁ + ε := by linarith
  gcongr
  exact w2P_le_w2H μ μ'

end Lipschitz

/-! ### The expected diagonal bound (3.7) -/

section Expected

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- The `Y`-coordinate of a square-integrable random tuple is square integrable. -/
theorem memLp_y_apply {Θ : Ω → TupleH ν 1 1 d} (hΘ : MemLp Θ 2 P) :
    MemLp (fun ω => (Θ ω).2.1 0) 2 P := by
  refine hΘ.of_le ?_ (ae_of_all _ fun ω => ?_)
  · exact ((continuous_apply 0).comp ((PiLp.continuous_ofLp 2 _).comp
      (continuous_fst.comp continuous_snd))).comp_aestronglyMeasurable hΘ.aestronglyMeasurable
  · rw [Real.norm_eq_abs, ← norm_eq_abs_fin_one]
    exact (norm_fst_le (Θ ω).2).trans (norm_snd_le (Θ ω))

/-- Along a diagonal input the `Y`-marginal mean is the expectation of the `Y`-coordinate. -/
theorem meanY_lawP2_apply {Θ : Ω → TupleH ν 1 1 d} (hΘ : MemLp Θ 2 P) :
    meanY (lawP2 P Θ) 0 = ∫ ω, (Θ ω).2.1 0 ∂P := by
  have hm : StronglyMeasurable fun θ : TupleH ν 1 1 d => θ.2.1 :=
    (measurable_fst.comp measurable_snd).stronglyMeasurable
  have hY : MemLp (fun ω => (Θ ω).2.1) 2 P :=
    hΘ.of_le ((continuous_fst.comp continuous_snd).comp_aestronglyMeasurable
        hΘ.aestronglyMeasurable)
      (ae_of_all _ fun ω => (norm_fst_le (Θ ω).2).trans (norm_snd_le (Θ ω)))
  rw [meanY, lawP2_law hΘ, integral_map hΘ.aestronglyMeasurable.aemeasurable
    hm.aestronglyMeasurable]
  exact ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).integral_comp_comm
    (hY.integrable one_le_two)).symm

/-- The clamp difference of (3.6) at two square-integrable scalars, recentred at two constants,
is bounded, and its product with the difference of the scalars is integrable. -/
theorem integrable_clampDiff {Y Y' : Ω → ℝ} (hY : MemLp Y 2 P) (hY' : MemLp Y' 2 P) (c c' : ℝ) :
    Integrable (fun ω => (clamp01 (Y ω - c) - clamp01 (Y' ω - c')) ^ 2) P ∧
      Integrable (fun ω => (clamp01 (Y ω - c) - clamp01 (Y' ω - c')) * (Y ω - Y' ω)) P := by
  have hGm : AEStronglyMeasurable (fun ω => clamp01 (Y ω - c) - clamp01 (Y' ω - c')) P :=
    (continuous_clamp01.comp_aestronglyMeasurable
        (hY.aestronglyMeasurable.sub aestronglyMeasurable_const)).sub
      (continuous_clamp01.comp_aestronglyMeasurable
        (hY'.aestronglyMeasurable.sub aestronglyMeasurable_const))
  have hGb : ∀ ω, ‖clamp01 (Y ω - c) - clamp01 (Y' ω - c')‖ ≤ 2 := fun ω => by
    rw [Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    linarith [abs_clamp01_le (Y ω - c), abs_clamp01_le (Y' ω - c')]
  refine ⟨Integrable.of_bound (hGm.pow 2) 4 (ae_of_all _ fun ω => ?_),
    ((hY.sub hY').integrable one_le_two).bdd_mul hGm (ae_of_all _ hGb)⟩
  rw [norm_pow]
  have h0 := norm_nonneg (clamp01 (Y ω - c) - clamp01 (Y' ω - c'))
  nlinarith [hGb ω]

variable {β₁ ε : ℝ}

/-- Along two diagonal inputs the pairing `⟨δb, δY⟩` of the drift (3.6) is the scalar pairing of
the `Y`-coordinates, recentred at their expectations. -/
theorem inner_clampDrift_lawP2 {Θ Θ' : Ω → TupleH ν 1 1 d} (hΘ : MemLp Θ 2 P)
    (hΘ' : MemLp Θ' 2 P) (t : ℝ) (ω : Ω) :
    inner ℝ (clampDrift β₁ ε t (Θ ω) (lawP2 P Θ) - clampDrift β₁ ε t (Θ' ω) (lawP2 P Θ'))
        ((Θ ω).2.1 - (Θ' ω).2.1)
      = (drift β₁ ε ((Θ ω).2.1 0) (∫ x, (Θ x).2.1 0 ∂P)
          - drift β₁ ε ((Θ' ω).2.1 0) (∫ x, (Θ' x).2.1 0 ∂P))
        * ((Θ ω).2.1 0 - (Θ' ω).2.1 0) := by
  rw [inner_eq_mul_fin_one, PiLp.sub_apply, PiLp.sub_apply, clampDrift_apply,
    clampDrift_apply, meanY_lawP2_apply hΘ, meanY_lawP2_apply hΘ']

/-- Along two diagonal inputs with square-integrable tuples, the pairing `⟨δb, δY⟩` of the drift
(3.6) is integrable. -/
theorem integrable_inner_clampDrift {Θ Θ' : Ω → TupleH ν 1 1 d} (hΘ : MemLp Θ 2 P)
    (hΘ' : MemLp Θ' 2 P) (t : ℝ) :
    Integrable (fun ω => inner ℝ
      (clampDrift β₁ ε t (Θ ω) (lawP2 P Θ) - clampDrift β₁ ε t (Θ' ω) (lawP2 P Θ'))
      ((Θ ω).2.1 - (Θ' ω).2.1)) P := by
  have hY := memLp_y_apply hΘ
  have hY' := memLp_y_apply hΘ'
  have hGd := (integrable_clampDiff hY hY' (∫ x, (Θ x).2.1 0 ∂P)
    (∫ x, (Θ' x).2.1 0 ∂P)).2
  refine ((((hY.sub hY').integrable_sq).const_mul (-β₁)).add (hGd.const_mul ε)).congr
    (ae_of_all _ fun ω => ?_)
  simp only [Pi.add_apply, Pi.sub_apply, inner_clampDrift_lawP2 hΘ hΘ' t ω, drift]
  ring

/-- **Proposition 3.8, the expected diagonal bound (3.7).** Along two diagonal inputs
`(Θ, Law Θ)`, `(Θ', Law Θ')` with `Θ, Θ'` square integrable, the drift (3.6) satisfies
`𝔼⟨δb, δY⟩ ≤ −(β₁ − ε) 𝔼|δY|²`, for every `ε ≥ 0`. -/
theorem integral_inner_clampDrift_le (hε : 0 ≤ ε) {Θ Θ' : Ω → TupleH ν 1 1 d}
    (hΘ : MemLp Θ 2 P) (hΘ' : MemLp Θ' 2 P) (t : ℝ) :
    ∫ ω, inner ℝ (clampDrift β₁ ε t (Θ ω) (lawP2 P Θ) - clampDrift β₁ ε t (Θ' ω) (lawP2 P Θ'))
        ((Θ ω).2.1 - (Θ' ω).2.1) ∂P
      ≤ -(β₁ - ε) * ∫ ω, ‖(Θ ω).2.1 - (Θ' ω).2.1‖ ^ 2 ∂P := by
  have hY := memLp_y_apply hΘ
  have hY' := memLp_y_apply hΘ'
  have hd := hY.sub hY'
  obtain ⟨hG2, hGd⟩ := integrable_clampDiff hY hY' (∫ x, (Θ x).2.1 0 ∂P)
    (∫ x, (Θ' x).2.1 0 ∂P)
  have key := drift_expected_diagonal (beta1 := β₁) hε (hY.integrable one_le_two)
    (hY'.integrable one_le_two) hd.aestronglyMeasurable.aemeasurable hd.aestronglyMeasurable
    (hd.integrable one_le_two) hd.integrable_sq hG2 hGd
  have hrhs : ∀ ω, ‖(Θ ω).2.1 - (Θ' ω).2.1‖ ^ 2 = ((Θ ω).2.1 0 - (Θ' ω).2.1 0) ^ 2 := by
    intro ω
    rw [norm_eq_abs_fin_one, PiLp.sub_apply, sq_abs]
  simp_rw [inner_clampDrift_lawP2 hΘ hΘ' t, hrhs]
  exact key

end Expected

/-! ### Failure of pointwise monotonicity on the supports -/

section TwoPoint

variable {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]

/-- The two-point law `½ δ_a + ½ δ_b`, as a law of finite second moment. -/
noncomputable def twoPointLaw (a b : F) : P2 F where
  law := (2⁻¹ : ℝ≥0∞) • Measure.dirac a + (2⁻¹ : ℝ≥0∞) • Measure.dirac b
  isProbabilityMeasure := ⟨by simp [ENNReal.inv_two_add_inv_two]⟩
  secondMoment_ne_top := by
    have hm : Measurable fun x : F => ENNReal.ofReal (‖x‖ ^ 2) := by fun_prop
    rw [secondMoment, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac' _ hm, lintegral_dirac' _ hm]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top⟩

/-- The first atom of a two-point law lies in its support. -/
theorem mem_support_twoPointLaw_left (a b : F) : a ∈ (twoPointLaw a b).law.support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have h : (2⁻¹ : ℝ≥0∞) • Measure.dirac a U ≤ (twoPointLaw a b).law U := by
    simp only [twoPointLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply]
    exact le_self_add
  refine lt_of_lt_of_le ?_ h
  rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)]
  simp

/-- The integral of a strongly measurable map against a two-point law is the average of its two
values. -/
theorem integral_twoPointLaw {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : F → G}
    (hf : StronglyMeasurable f) (a b : F) :
    ∫ x, f x ∂(twoPointLaw a b).law = (2⁻¹ : ℝ) • f a + (2⁻¹ : ℝ) • f b := by
  have hi : ∀ c : F, Integrable f ((2⁻¹ : ℝ≥0∞) • Measure.dirac c) := fun c =>
    (integrable_dirac' hf enorm_lt_top).smul_measure (by simp)
  simp only [twoPointLaw]
  rw [integral_add_measure (hi a) (hi b), integral_smul_measure, integral_smul_measure,
    integral_dirac' _ _ hf, integral_dirac' _ _ hf]
  simp

end TwoPoint

section Pointwise

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- The tuple `(0, c, 0, 0)` of `H = ℝ × ℝ × ℝ^{1×d} × L²(ν; ℝ)`. -/
noncomputable def pointY (ν : Measure E) (d : ℕ) (c : ℝ) : TupleH ν 1 1 d :=
  (0, WithLp.toLp 2 fun _ => c, 0, 0)

/-- The `Y`-coordinate of `(0, c, 0, 0)` is `c`. -/
@[simp]
theorem pointY_y_apply (c : ℝ) (i : Fin 1) : (pointY ν d c).2.1 i = c := rfl

/-- The `Y`-marginal mean of the two-point law at `(0, a, 0, 0)` and `(0, b, 0, 0)` is the
average of `a` and `b`. -/
theorem meanY_twoPointLaw_apply (a b : ℝ) :
    meanY (twoPointLaw (pointY ν d a) (pointY ν d b)) 0 = (a + b) / 2 := by
  have hm : StronglyMeasurable fun θ : TupleH ν 1 1 d => θ.2.1 :=
    (measurable_fst.comp measurable_snd).stronglyMeasurable
  rw [meanY, integral_twoPointLaw hm]
  simp only [PiLp.add_apply, PiLp.smul_apply, pointY_y_apply, smul_eq_mul]
  ring

variable {β₁ ε : ℝ}

/-- **Pointwise monotonicity fails on the supports, at every rate at once.** For `β₁, ε > 0`
there are points `θ = (0, 0, 0, 0)`, `θ' = (0, −ε/β₁, 0, 0)` and two-point laws `μ ∋ θ`,
`μ' ∋ θ'` of their supports at which `⟨δb, δy⟩ > −β |δy|²` for every `β ≥ 0`, with `δy ≠ 0`. -/
theorem exists_mem_support_forall_lt_inner_clampDrift (hβ₁ : 0 < β₁) (hε : 0 < ε) (t : ℝ) :
    ∃ (θ θ' : TupleH ν 1 1 d) (μ μ' : P2 (TupleH ν 1 1 d)),
      θ ∈ μ.law.support ∧ θ' ∈ μ'.law.support ∧ θ.2.1 ≠ θ'.2.1 ∧
      ∀ β : ℝ, 0 ≤ β → -β * ‖θ.2.1 - θ'.2.1‖ ^ 2
        < inner ℝ (clampDrift β₁ ε t θ μ - clampDrift β₁ ε t θ' μ') (θ.2.1 - θ'.2.1) := by
  set s : ℝ := ε / β₁ with hs
  have hs0 : 0 < s := div_pos hε hβ₁
  have hsβ : β₁ * s = ε := by rw [hs]; field_simp
  refine ⟨pointY ν d 0, pointY ν d (-s), twoPointLaw (pointY ν d 0) (pointY ν d (-2)),
    twoPointLaw (pointY ν d (-s)) (pointY ν d (-s + 2)), mem_support_twoPointLaw_left _ _,
    mem_support_twoPointLaw_left _ _, fun h => ?_, fun β hβ => ?_⟩
  · have := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h
    simp only [pointY_y_apply] at this
    linarith
  · have hm : meanY (twoPointLaw (pointY ν d 0) (pointY ν d (-2))) 0 = -1 := by
      rw [meanY_twoPointLaw_apply]; norm_num
    have hm' : meanY (twoPointLaw (pointY ν d (-s)) (pointY ν d (-s + 2))) 0 = -s + 1 := by
      rw [meanY_twoPointLaw_apply]; ring
    have h1 : clamp01 ((0 : ℝ) - -1) = 1 := clamp01_eq_one (by norm_num)
    have h2 : clamp01 (-s - (-s + 1)) = -1 := clamp01_eq_neg_one (by linarith)
    rw [inner_eq_mul_fin_one, norm_eq_abs_fin_one, PiLp.sub_apply, PiLp.sub_apply,
      clampDrift_apply, clampDrift_apply, hm, hm', pointY_y_apply, pointY_y_apply]
    simp only [drift, h1, h2]
    have hpos : 0 < (-(β₁ * 0) + ε * 1 - (-(β₁ * -s) + ε * -1)) * (0 - -s) := by
      nlinarith
    nlinarith [sq_nonneg |(0 : ℝ) - -s|, abs_nonneg ((0 : ℝ) - -s)]

/-- **Proposition 3.8, pointwise failure on the supports.** For `β₁, ε > 0` and every `β ≥ 0`,
the pointwise bound `⟨δb, δy⟩ ≤ −β |δy|²` fails at a pair of inputs `(θ, μ)`, `(θ', μ')` with
`θ` in the support of `μ` and `θ'` in the support of `μ'`. -/
theorem pointwise_monotonicity_fails_on_supports (hβ₁ : 0 < β₁) (hε : 0 < ε) (t : ℝ) {β : ℝ}
    (hβ : 0 ≤ β) :
    ∃ (θ θ' : TupleH ν 1 1 d) (μ μ' : P2 (TupleH ν 1 1 d)),
      θ ∈ μ.law.support ∧ θ' ∈ μ'.law.support ∧
      ¬ inner ℝ (clampDrift β₁ ε t θ μ - clampDrift β₁ ε t θ' μ') (θ.2.1 - θ'.2.1)
        ≤ -β * ‖θ.2.1 - θ'.2.1‖ ^ 2 := by
  obtain ⟨θ, θ', μ, μ', hθ, hθ', -, h⟩ :=
    exists_mem_support_forall_lt_inner_clampDrift (ν := ν) (d := d) hβ₁ hε t
  exact ⟨θ, θ', μ, μ', hθ, hθ', not_le.mpr (h β hβ)⟩

end Pointwise

end MVFBSDEJ.WellPosedness.System
