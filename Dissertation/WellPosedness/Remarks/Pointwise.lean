/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Robustness.LawPerturb
import Dissertation.WellPosedness.Existence.ClampAffine

/-!
# Pointwise and expected diagonal monotonicity

Remark 2.8 of the well-posedness paper compares Assumption 2.5, imposed in expectation along the
diagonal, with the *pointwise* `G`-monotonicity condition: the inequality (2.7) without
expectations, for almost every `t ∈ [0, T]`, at every pair of points `θ, θ' ∈ H` and every pair
of laws `μ, μ' ∈ P₂(H)`. Applied at `θ = Θ(ω)`, `θ' = Θ'(ω)`, `μ = Law(Θ)`, `μ' = Law(Θ')` and
integrated, the pointwise condition gives Assumption 2.5, interior.

The integration step needs the expectation of the interior pairing. The right-hand side of (2.7)
is integrable along square-integrable tuples, and the pairing is integrable as soon as it is
measurable and the coefficient differences are bounded by
`L (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + w)` with `w` a constant: by Cauchy–Schwarz it is then
bounded by a constant plus a multiple of `|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}`. Both hold
under Assumption 2.3 along the diagonal together with the joint measurability (2.3).
For a coefficient without such a bound the pairing need not be integrable (for instance
`b = −y − y³` along `Y ∈ L² \ L⁴`). Its positive part is still integrable, being bounded by the
right-hand side, so its expectation exists in `[−∞, ∞)`; the Bochner integral, however, takes
the value `0` at a non-integrable function, so the integrated inequality requires an integrable
pairing.

The converse fails. The affine system of Example 5.1(i) with the drift (3.6) of Proposition 3.8
satisfies Assumption 2.5, interior, at `G = 1` with the constants `(β₁ − ε, β₂)`, while for
`β₁, ε > 0` the pointwise bound `⟨δb, δy⟩ ≤ −β |δy|²` fails at every rate `β ≥ 0`; at points
with `δX = δZ = δU = 0` this is the failure of the pointwise condition with any constants
`β ≥ 0`, `β'`. Example 5.1(i) itself satisfies the pointwise condition, with equality.

## Main definitions

* `PointwiseGMonotone` — (2.7) without expectations, at every pair of points and laws.

## Main statements

* `aestronglyMeasurable_interiorPairing_diagDiff`, `integrable_interiorPairing_of_ae_le` — the
  pairing along two square-integrable tuples is integrable under a bound of Assumption 2.3 type.
* `PointwiseGMonotone.diagonalMonotone_of_integrable` — pointwise monotonicity gives
  Assumption 2.5, interior, when the pairing is integrable along the diagonal.
* `measurable_section_of_cutoff`, `PointwiseGMonotone.diagonalMonotone_of_diagonalLipschitzH`,
  `PointwiseGMonotone.diagonalMonotone_of_coeffBorelW2` — under Assumption 2.3 along the
  diagonal and (2.3).
* `pointwiseGMonotone_affine` — Example 5.1(i) is pointwise `G`-monotone.
* `not_pointwiseGMonotone_clampAffine` — the drift (3.6) gives a system that is not pointwise
  `G`-monotone.
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}

/-- **Pointwise `G`-monotonicity**: the inequality (2.7) without expectations, for almost every
`t ∈ [0, T]`, at every pair of points `θ, θ'` of the tuple space and every pair of laws
`μ, μ'` of finite second moment,
`⟨δb, Gᵀ δy⟩ + ⟨δσ, Gᵀ δz⟩_F − ⟨δf, G δx⟩ + ⟨δh, Gᵀ δu⟩_{L²(ν)}
  ≤ −β₁ (|Gᵀ δy|² + |Gᵀ δz|²_F + ‖Gᵀ δu‖²_{L²(ν)}) − β₂ |G δx|²`. -/
def PointwiseGMonotone (T : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (β₁ β₂ : ℝ) (C : Coeffs ν n m d) :
    Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ (θ θ' : TupleH ν n m d)
    (μ μ' : P2 (TupleH ν n m d)),
    interiorPairing (GX G) (GZ G) (GU G ν) (diagDiff C t θ θ' μ μ')
      ≤ dissipation (GX G) (GZ G) (GU G ν) β₁ β₂ (diagDiff C t θ θ' μ μ')

/-! ### Integrability of the interior pairing -/

section Integrable

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Θ Θ' : Ω → TupleH ν n m d}

/-- **The interior pairing along two tuples is measurable** when the tuples and the four
coefficient differences are. -/
theorem aestronglyMeasurable_interiorPairing_diagDiff (G : Matrix (Fin m) (Fin n) ℝ)
    (C : Coeffs ν n m d) (t : ℝ) (μ μ' : P2 (TupleH ν n m d)) (hΘ : AEStronglyMeasurable Θ P)
    (hΘ' : AEStronglyMeasurable Θ' P)
    (hb : AEStronglyMeasurable (fun ω => C.b t (Θ ω) μ - C.b t (Θ' ω) μ') P)
    (hσ : AEStronglyMeasurable (fun ω => C.σ t (Θ ω) μ - C.σ t (Θ' ω) μ') P)
    (hh : AEStronglyMeasurable (fun ω => C.h t (Θ ω) μ - C.h t (Θ' ω) μ') P)
    (hf : AEStronglyMeasurable (fun ω => C.f t (Θ ω) μ - C.f t (Θ' ω) μ') P) :
    AEStronglyMeasurable (fun ω => interiorPairing (GX G) (GZ G) (GU G ν)
      (diagDiff C t (Θ ω) (Θ' ω) μ μ')) P := by
  have hX : AEStronglyMeasurable (fun ω => (Θ ω).1 - (Θ' ω).1) P :=
    (continuous_fst.comp_aestronglyMeasurable hΘ).sub
      (continuous_fst.comp_aestronglyMeasurable hΘ')
  have hY : AEStronglyMeasurable (fun ω => (Θ ω).2.1 - (Θ' ω).2.1) P :=
    ((continuous_fst.comp continuous_snd).comp_aestronglyMeasurable hΘ).sub
      ((continuous_fst.comp continuous_snd).comp_aestronglyMeasurable hΘ')
  have hZ : AEStronglyMeasurable (fun ω => (Θ ω).2.2.1 - (Θ' ω).2.2.1) P :=
    ((continuous_fst.comp (continuous_snd.comp continuous_snd)).comp_aestronglyMeasurable
      hΘ).sub
      ((continuous_fst.comp (continuous_snd.comp continuous_snd)).comp_aestronglyMeasurable hΘ')
  have hU : AEStronglyMeasurable (fun ω => (Θ ω).2.2.2 - (Θ' ω).2.2.2) P :=
    ((continuous_snd.comp (continuous_snd.comp continuous_snd)).comp_aestronglyMeasurable
      hΘ).sub
      ((continuous_snd.comp (continuous_snd.comp continuous_snd)).comp_aestronglyMeasurable hΘ')
  have h1 := hb.inner (𝕜 := ℝ)
    ((ContinuousLinearMap.adjoint (GX G)).continuous.comp_aestronglyMeasurable hY)
  have h2 := hσ.inner (𝕜 := ℝ)
    ((ContinuousLinearMap.adjoint (GZ G)).continuous.comp_aestronglyMeasurable hZ)
  have h3 := hf.neg.inner (𝕜 := ℝ) ((GX G).continuous.comp_aestronglyMeasurable hX)
  have h4 := hh.inner (𝕜 := ℝ)
    ((ContinuousLinearMap.adjoint (GU G ν)).continuous.comp_aestronglyMeasurable hU)
  exact ((h1.add h2).add h3).add h4

/-- **The interior pairing along two square-integrable tuples is integrable** when it is
measurable and, almost surely,
`|δb| + |δσ|_F + ‖δh‖_{L²(ν)} + |δf| ≤ L (|δX| + |δY| + |δZ|_F + ‖δU‖_{L²(ν)} + w)` for
constants `L` and `w ≥ 0`. -/
theorem integrable_interiorPairing_of_ae_le [IsFiniteMeasure P] {G : Matrix (Fin m) (Fin n) ℝ}
    {C : Coeffs ν n m d} {t : ℝ} {μ μ' : P2 (TupleH ν n m d)} {L w : ℝ} (hw : 0 ≤ w)
    (hΘ : MemLp Θ 2 P)
    (hΘ' : MemLp Θ' 2 P)
    (hm : AEStronglyMeasurable (fun ω => interiorPairing (GX G) (GZ G) (GU G ν)
      (diagDiff C t (Θ ω) (Θ' ω) μ μ')) P)
    (hle : ∀ᵐ ω ∂P, ‖C.b t (Θ ω) μ - C.b t (Θ' ω) μ'‖ + ‖C.σ t (Θ ω) μ - C.σ t (Θ' ω) μ'‖
        + ‖C.h t (Θ ω) μ - C.h t (Θ' ω) μ'‖ + ‖C.f t (Θ ω) μ - C.f t (Θ' ω) μ'‖
      ≤ L * (tupleNorm (Θ ω - Θ' ω) + w)) :
    Integrable (fun ω => interiorPairing (GX G) (GZ G) (GU G ν)
      (diagDiff C t (Θ ω) (Θ' ω) μ μ')) P := by
  have hL : 0 ≤ max L 0 := le_max_right L 0
  have hK : 0 ≤ ‖GX G‖ * max L 0 := mul_nonneg (norm_nonneg _) hL
  have hgi : Integrable (fun ω =>
      ‖GX G‖ * max L 0 * (9 * channelSq (Θ ω - Θ' ω) + 2 * w ^ 2) / 2) P :=
    ((((integrable_channelSq_sub hΘ hΘ').const_mul 9).add
      (integrable_const (2 * w ^ 2))).const_mul _).div_const 2
  refine hgi.mono' hm (hle.mono fun ω hω => ?_)
  have htn0 : 0 ≤ tupleNorm (Θ ω - Θ' ω) := by unfold tupleNorm; positivity
  have hω' := hω.trans (mul_le_mul_of_nonneg_right (le_max_left L 0) (add_nonneg htn0 hw))
  have habs := abs_interiorPairing_diagDiff_le G C t (Θ ω) (Θ' ω) μ μ' hL hω'
  have htn := tupleNorm_sq_le (Θ ω - Θ' ω)
  have hW2 : (tupleNorm (Θ ω - Θ' ω) + w) ^ 2 ≤ 8 * channelSq (Θ ω - Θ' ω) + 2 * w ^ 2 := by
    nlinarith [sq_nonneg (tupleNorm (Θ ω - Θ' ω) - w)]
  rw [Real.norm_eq_abs]
  refine habs.trans ?_
  have hin : (tupleNorm (Θ ω - Θ' ω) + w) ^ 2 + channelSq (Θ ω - Θ' ω)
      ≤ 9 * channelSq (Θ ω - Θ' ω) + 2 * w ^ 2 := by linarith
  have := mul_le_mul_of_nonneg_left hin hK
  linarith

end Integrable

/-! ### Pointwise monotonicity gives Assumption 2.5 -/

section Implication

variable {Ω : Type*} [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d}

/-- **Pointwise monotonicity gives Assumption 2.5 when the pairing is integrable**: if (2.7)
holds pointwise and, for almost every `t ∈ [0, T]`, the interior pairing along any two diagonal
inputs is integrable, then (2.7) holds along the diagonal. -/
theorem PointwiseGMonotone.diagonalMonotone_of_integrable (h : PointwiseGMonotone T G β₁ β₂ C)
    (hint : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ Θ Θ' : Ω → TupleH ν n m d,
      StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
      Integrable (fun ω => interiorPairing (GX G) (GZ G) (GU G ν)
        (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ'))) P) :
    DiagonalMonotone ℱ P T G β₁ β₂ C := by
  filter_upwards [h, hint] with t ht hti Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  exact integral_mono (hti Θ Θ' hΘ hΘ' hΘ2 hΘ2')
    (integrable_dissipation_diagDiff _ _ _ β₁ β₂ C t _ _ hΘ2 hΘ2') fun ω => ht _ _ _ _

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The sections of a measurable cut-off coefficient are measurable**: if
`(t, θ, μ) ↦ 1_{[0, T]}(t) ψ(t, θ, μ)` is measurable, then `θ ↦ ψ(t, θ, μ)` is measurable for
every `t ∈ [0, T]` and every law `μ`. -/
theorem measurable_section_of_cutoff {W : Type*} [MeasurableSpace W] [Zero W]
    {ψ : ℝ → TupleH ν n m d → P2 (TupleH ν n m d) → W}
    (hψ : Measurable fun p : ℝ × TupleH ν n m d × P2 (TupleH ν n m d) =>
      (Set.Icc (0 : ℝ) T).indicator (fun t => ψ t p.2.1 p.2.2) p.1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (μ : P2 (TupleH ν n m d)) :
    Measurable fun θ => ψ t θ μ := by
  have h := hψ.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const) :
    Measurable fun θ : TupleH ν n m d => (t, θ, μ))
  simpa only [Function.comp_def, Set.indicator_of_mem ht] using h

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **A measurable cut-off coefficient along two measurable tuples**: for `t ∈ [0, T]` and laws
`μ, μ'`, `ω ↦ ψ(t, Θ(ω), μ) − ψ(t, Θ'(ω), μ')` is measurable. -/
theorem aestronglyMeasurable_sub_of_cutoff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : Type*} [NormedAddCommGroup W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W] {ψ : ℝ → TupleH ν n m d → P2 (TupleH ν n m d) → W}
    (hψ : Measurable fun p : ℝ × TupleH ν n m d × P2 (TupleH ν n m d) =>
      (Set.Icc (0 : ℝ) T).indicator (fun t => ψ t p.2.1 p.2.2) p.1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {Θ Θ' : Ω → TupleH ν n m d} (hΘ : AEMeasurable Θ P)
    (hΘ' : AEMeasurable Θ' P) (μ μ' : P2 (TupleH ν n m d)) :
    AEStronglyMeasurable (fun ω => ψ t (Θ ω) μ - ψ t (Θ' ω) μ') P :=
  (((measurable_section_of_cutoff hψ ht μ).comp_aemeasurable hΘ).aestronglyMeasurable).sub
    (((measurable_section_of_cutoff hψ ht μ').comp_aemeasurable hΘ').aestronglyMeasurable)

/-- **Pointwise monotonicity gives Assumption 2.5 under Assumption 2.3 and joint measurability**
(Remark 2.8): if (2.7) holds pointwise, the coefficients satisfy Assumption 2.3 along the
diagonal with the Hilbert-norm `W₂`, and their cut-offs `1_{[0, T]}(t) ψ(t, θ, μ)` are jointly
measurable, then (2.7) holds along the diagonal. -/
theorem PointwiseGMonotone.diagonalMonotone_of_diagonalLipschitzH {L : ℝ}
    (h : PointwiseGMonotone T G β₁ β₂ C) (hL : DiagonalLipschitzH ℱ P T L C)
    (hB : Existence.CoeffBorel T C) : DiagonalMonotone ℱ P T G β₁ β₂ C := by
  refine h.diagonalMonotone_of_integrable ?_
  filter_upwards [hL, ae_restrict_mem measurableSet_Icc] with t hLt htI Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  have ha := hΘ2.aestronglyMeasurable
  have ha' := hΘ2'.aestronglyMeasurable
  exact integrable_interiorPairing_of_ae_le (w2H_nonneg _ _) hΘ2 hΘ2'
    (aestronglyMeasurable_interiorPairing_diagDiff G C t _ _ ha ha'
      (aestronglyMeasurable_sub_of_cutoff hB.b_meas htI ha.aemeasurable ha'.aemeasurable _ _)
      (aestronglyMeasurable_sub_of_cutoff hB.σ_meas htI ha.aemeasurable ha'.aemeasurable _ _)
      (aestronglyMeasurable_sub_of_cutoff hB.h_meas htI ha.aemeasurable ha'.aemeasurable _ _)
      (aestronglyMeasurable_sub_of_cutoff hB.f_meas htI ha.aemeasurable ha'.aemeasurable _ _))
    (hLt Θ Θ' hΘ hΘ' hΘ2 hΘ2')

/-- **Pointwise monotonicity gives Assumption 2.5 under Assumption 2.3 and (2.3)** (Remark 2.8):
if (2.7) holds pointwise, the coefficients satisfy Assumption 2.3 along the diagonal with the
Hilbert-norm `W₂`, and they are jointly Borel on `[0, T] × H × P₂(H)` with the Hilbert-norm `W₂`,
then (2.7) holds along the diagonal. -/
theorem PointwiseGMonotone.diagonalMonotone_of_coeffBorelW2 {L : ℝ}
    (h : PointwiseGMonotone T G β₁ β₂ C) (hL : DiagonalLipschitzH ℱ P T L C)
    (hB : Existence.CoeffBorelW2 T C) : DiagonalMonotone ℱ P T G β₁ β₂ C :=
  h.diagonalMonotone_of_diagonalLipschitzH hL hB.toCoeffBorel

end Implication

/-! ### Example 5.1(i) and the drift (3.6) -/

section Examples

/-- **Example 5.1(i) is pointwise `G`-monotone**: at `G = I` and its own constants `β₁, β₂`,
(2.7) holds at every pair of points and laws, with equality. -/
theorem pointwiseGMonotone_affine {T β₁ β₂ : ℝ} {σc : EuclideanSpace ℝ (Fin n × Fin d)}
    {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν} :
    PointwiseGMonotone T (1 : Matrix (Fin n) (Fin n) ℝ) β₁ β₂
      (Existence.affineCoeffs β₁ β₂ σc hc) :=
  Eventually.of_forall fun t θ θ' μ μ' => (Existence.interiorPairing_affine t θ θ' μ μ').le

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {β₁ β₂ ε T : ℝ}
  {σc : EuclideanSpace ℝ (Fin 1 × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν}

/-- **The drift (3.6) is not pointwise `G`-monotone**: for `β₁, ε > 0` and a horizon `T > 0`, the
affine system of Example 5.1(i) at `n = m = 1` with the drift (3.6) is not pointwise
`G`-monotone at `G = 1` for any constants `β ≥ 0`, `β'`. -/
theorem not_pointwiseGMonotone_clampAffine (hβ₁ : 0 < β₁) (hε : 0 < ε) (hT : 0 < T) {β β' : ℝ}
    (hβ : 0 ≤ β) :
    ¬ PointwiseGMonotone T (1 : Matrix (Fin 1) (Fin 1) ℝ) β β'
      (Existence.clampAffineCoeffs β₁ β₂ ε σc hc) := by
  intro hpw
  haveI : (ae (volume.restrict (Set.Icc (0 : ℝ) T))).NeBot := by
    rw [ae_restrict_neBot, Real.volume_Icc, sub_zero]
    exact ENNReal.ofReal_ne_zero_iff.mpr hT
  obtain ⟨t, ht⟩ := hpw.exists
  obtain ⟨θ, θ', μ, μ', -, -, -, hlt⟩ :=
    exists_mem_support_forall_lt_inner_clampDrift (ν := ν) (d := d) hβ₁ hε t
  have key := ht ((0, θ.2.1, 0, 0) : TupleH ν 1 1 d) ((0, θ'.2.1, 0, 0) : TupleH ν 1 1 d) μ μ'
  rw [Existence.interiorPairing_clampAffine] at key
  have hb : clampDrift β₁ ε t ((0, θ.2.1, 0, 0) : TupleH ν 1 1 d) μ = clampDrift β₁ ε t θ μ :=
    rfl
  have hb' : clampDrift β₁ ε t ((0, θ'.2.1, 0, 0) : TupleH ν 1 1 d) μ'
      = clampDrift β₁ ε t θ' μ' := rfl
  rw [hb, hb'] at key
  simp only [dissipation, diagDiff, GX_one, GZ_one, GU_one, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_apply, sub_self, norm_zero] at key
  have := hlt β hβ
  norm_num at key
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P]

end Examples

end Dissertation.WellPosedness.System
