/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# Expected diagonal monotonicity of a clamped mean-field drift

The scalar mean-field drift `b(y, m) = -β₁ y + ε g₀(y - m)` of (3.6), with `g₀` the clamp to
`[-1, 1]` and `m` the `Y`-marginal mean, is Lipschitz in the pair `(y, m)` with constant `β₁ + ε`.
Along diagonal inputs `(Y, 𝔼 Y)` and `(Y', 𝔼 Y')` the clamp contribution is bounded pointwise by
the centred increment `|δY − 𝔼 δY|`, and centring does not increase the second moment, so

`𝔼 [δb δY] ≤ -(β₁ - ε) 𝔼 |δY|²`,

which is the expected diagonal monotonicity (3.7).

## Main statements

* `drift_lipschitz` — the free-measure Lipschitz bound with constant `β₁ + ε`.
* `expected_diagonal_bound`, `drift_expected_diagonal` — the expected diagonal bound (3.7) at
  rate `β₁ - ε`.
-/

namespace MVFBSDEJ.WellPosedness

open Set

/-- The clamp `g₀(r) = max(-1, min(1, r))` truncating a real to `[-1, 1]`. -/
noncomputable def clamp01 (r : ℝ) : ℝ := max (-1) (min 1 r)

/-- The clamp takes values in `[-1, 1]`. -/
theorem clamp01_mem (r : ℝ) : clamp01 r ∈ Icc (-1 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

/-- The clamp is `1`-Lipschitz. -/
theorem clamp01_lipschitz (r s : ℝ) : |clamp01 r - clamp01 s| ≤ |r - s| := by
  unfold clamp01
  rcases abs_cases (r - s) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    rcases le_total r s with hrs | hrs <;>
      · rw [abs_le]
        constructor <;>
          · simp only [max_def, min_def]
            split_ifs <;> linarith [abs_nonneg (r - s), le_abs_self (r - s),
              neg_abs_le (r - s)]

/-- The clamp is `1` from `1` on. -/
theorem clamp01_eq_one {r : ℝ} (h : 1 ≤ r) : clamp01 r = 1 := by
  unfold clamp01
  rw [min_eq_left h]
  norm_num

/-- The clamp is `-1` up to `-1`. -/
theorem clamp01_eq_neg_one {r : ℝ} (h : r ≤ -1) : clamp01 r = -1 := by
  unfold clamp01
  rw [min_eq_right (by linarith), max_eq_left h]

/-- The scalar mean-field drift of (3.6): a linear dissipative term of rate `β₁` plus a
clamped deviation-from-the-mean term of size `ε`. -/
noncomputable def drift (beta1 eps y m : ℝ) : ℝ := -beta1 * y + eps * clamp01 (y - m)

/-- The drift is Lipschitz in the state and the mean jointly, with constant `β₁ + ε`. -/
theorem drift_lipschitz {beta1 eps : ℝ} (hb : 0 ≤ beta1) (he : 0 ≤ eps) (y m y' m' : ℝ) :
    |drift beta1 eps y m - drift beta1 eps y' m'| ≤ (beta1 + eps) * (|y - y'| + |m - m'|) := by
  have hclamp : |clamp01 (y - m) - clamp01 (y' - m')| ≤ |y - y'| + |m - m'| := by
    refine (clamp01_lipschitz _ _).trans ?_
    have : (y - m) - (y' - m') = (y - y') - (m - m') := by ring
    rw [this]
    exact (abs_sub _ _).trans_eq rfl
  have hsplit : drift beta1 eps y m - drift beta1 eps y' m'
      = -beta1 * (y - y') + eps * (clamp01 (y - m) - clamp01 (y' - m')) := by
    unfold drift; ring
  rw [hsplit]
  have h1 : |(-beta1) * (y - y')| = beta1 * |y - y'| := by
    rw [abs_mul, abs_neg, abs_of_nonneg hb]
  have h2 : |eps * (clamp01 (y - m) - clamp01 (y' - m'))|
      = eps * |clamp01 (y - m) - clamp01 (y' - m')| := by
    rw [abs_mul, abs_of_nonneg he]
  have hy : (0:ℝ) ≤ |y - y'| := abs_nonneg _
  have hm : (0:ℝ) ≤ |m - m'| := abs_nonneg _
  calc |(-beta1) * (y - y') + eps * (clamp01 (y - m) - clamp01 (y' - m'))|
      ≤ |(-beta1) * (y - y')| + |eps * (clamp01 (y - m) - clamp01 (y' - m'))| := abs_add_le _ _
    _ = beta1 * |y - y'| + eps * |clamp01 (y - m) - clamp01 (y' - m')| := by rw [h1, h2]
    _ ≤ beta1 * (|y - y'| + |m - m'|) + eps * (|y - y'| + |m - m'|) := by
        gcongr
        · linarith
    _ = (beta1 + eps) * (|y - y'| + |m - m'|) := by ring

section Expected

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Centring cannot increase the second moment. -/
theorem integral_sub_mean_sq_le {dY : Ω → ℝ} (hm : AEMeasurable dY μ)
    (hsm : AEStronglyMeasurable dY μ) :
    ∫ ω, (dY ω - ∫ x, dY x ∂μ) ^ 2 ∂μ ≤ ∫ ω, dY ω ^ 2 ∂μ := by
  rw [← variance_eq_integral hm]
  simpa using variance_le_expectation_sq (μ := μ) hsm

/-- The expected diagonal bound (3.7). The clamp contribution `G` is controlled pointwise by
the centred increment, so on average it costs at most `ε` against the dissipative rate `β₁`. -/
theorem expected_diagonal_bound {dY G : Ω → ℝ} {beta1 eps : ℝ} (heps : 0 ≤ eps)
    (hm : AEMeasurable dY μ) (hsm : AEStronglyMeasurable dY μ)
    (hdY1 : Integrable dY μ)
    (hdY2 : Integrable (fun ω => dY ω ^ 2) μ)
    (hG2 : Integrable (fun ω => G ω ^ 2) μ)
    (hGdY : Integrable (fun ω => G ω * dY ω) μ)
    (hcentre : ∀ ω, |G ω| ≤ |dY ω - ∫ x, dY x ∂μ|) :
    ∫ ω, (-beta1 * dY ω + eps * G ω) * dY ω ∂μ
      ≤ -(beta1 - eps) * ∫ ω, dY ω ^ 2 ∂μ := by
  have hcsq : Integrable (fun ω => (dY ω - ∫ x, dY x ∂μ) ^ 2) μ := by
    have hbase : Integrable (fun ω => dY ω ^ 2 - 2 * (∫ x, dY x ∂μ) * dY ω
        + (∫ x, dY x ∂μ) ^ 2) μ :=
      (hdY2.sub (hdY1.const_mul _)).add (integrable_const _)
    refine hbase.congr (Filter.Eventually.of_forall fun ω => ?_)
    ring
  -- split the integral
  have hsplit : ∫ ω, (-beta1 * dY ω + eps * G ω) * dY ω ∂μ
      = -beta1 * ∫ ω, dY ω ^ 2 ∂μ + eps * ∫ ω, G ω * dY ω ∂μ := by
    have hL : Integrable (fun ω => -beta1 * (dY ω ^ 2)) μ := hdY2.const_mul _
    have hR : Integrable (fun ω => eps * (G ω * dY ω)) μ := hGdY.const_mul _
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add hL hR]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    ring
  -- AM-GM pointwise, then the centring bound
  have hcross : ∫ ω, G ω * dY ω ∂μ ≤ ∫ ω, dY ω ^ 2 ∂μ := by
    have hAM : ∫ ω, G ω * dY ω ∂μ
        ≤ ∫ ω, (G ω ^ 2 + dY ω ^ 2) / 2 ∂μ := by
      refine integral_mono hGdY (((hG2.add hdY2).div_const 2)) fun ω => ?_
      nlinarith [sq_nonneg (G ω - dY ω)]
    have hG2le : ∫ ω, G ω ^ 2 ∂μ ≤ ∫ ω, (dY ω - ∫ x, dY x ∂μ) ^ 2 ∂μ := by
      refine integral_mono hG2 hcsq fun ω => ?_
      have := hcentre ω
      nlinarith [abs_nonneg (G ω), abs_nonneg (dY ω - ∫ x, dY x ∂μ),
        sq_abs (G ω), sq_abs (dY ω - ∫ x, dY x ∂μ)]
    have hvar : ∫ ω, (dY ω - ∫ x, dY x ∂μ) ^ 2 ∂μ ≤ ∫ ω, dY ω ^ 2 ∂μ :=
      integral_sub_mean_sq_le hm hsm
    have hdiv : ∫ ω, (G ω ^ 2 + dY ω ^ 2) / 2 ∂μ
        = (∫ ω, G ω ^ 2 ∂μ + ∫ ω, dY ω ^ 2 ∂μ) / 2 := by
      rw [integral_div, integral_add hG2 hdY2]
    rw [hdiv] at hAM
    linarith
  rw [hsplit]
  nlinarith [hcross]

omit [IsProbabilityMeasure μ] in
/-- At diagonal inputs the clamp contribution of (3.6) is controlled pointwise by the centred
increment. -/
theorem clamp_diff_le_centred {Y Y' : Ω → ℝ} (hY : Integrable Y μ) (hY' : Integrable Y' μ)
    (ω : Ω) :
    |clamp01 (Y ω - ∫ x, Y x ∂μ) - clamp01 (Y' ω - ∫ x, Y' x ∂μ)|
      ≤ |(Y ω - Y' ω) - ∫ x, (Y x - Y' x) ∂μ| := by
  have h : (Y ω - ∫ x, Y x ∂μ) - (Y' ω - ∫ x, Y' x ∂μ)
      = (Y ω - Y' ω) - ∫ x, (Y x - Y' x) ∂μ := by
    rw [integral_sub hY hY']; ring
  calc |clamp01 (Y ω - ∫ x, Y x ∂μ) - clamp01 (Y' ω - ∫ x, Y' x ∂μ)|
      ≤ |(Y ω - ∫ x, Y x ∂μ) - (Y' ω - ∫ x, Y' x ∂μ)| := clamp01_lipschitz _ _
    _ = |(Y ω - Y' ω) - ∫ x, (Y x - Y' x) ∂μ| := by rw [h]

/-- Expected diagonal monotonicity (3.7) for the drift (3.6): along diagonal inputs the drift
is dissipative at rate `β₁ - ε` in expectation. -/
theorem drift_expected_diagonal {Y Y' : Ω → ℝ} {beta1 eps : ℝ} (heps : 0 ≤ eps)
    (hY : Integrable Y μ) (hY' : Integrable Y' μ)
    (hm : AEMeasurable (fun ω => Y ω - Y' ω) μ)
    (hsm : AEStronglyMeasurable (fun ω => Y ω - Y' ω) μ)
    (hd1 : Integrable (fun ω => Y ω - Y' ω) μ)
    (hd2 : Integrable (fun ω => (Y ω - Y' ω) ^ 2) μ)
    (hG2 : Integrable (fun ω =>
      (clamp01 (Y ω - ∫ x, Y x ∂μ) - clamp01 (Y' ω - ∫ x, Y' x ∂μ)) ^ 2) μ)
    (hGd : Integrable (fun ω =>
      (clamp01 (Y ω - ∫ x, Y x ∂μ) - clamp01 (Y' ω - ∫ x, Y' x ∂μ)) * (Y ω - Y' ω)) μ) :
    ∫ ω, (drift beta1 eps (Y ω) (∫ x, Y x ∂μ)
            - drift beta1 eps (Y' ω) (∫ x, Y' x ∂μ)) * (Y ω - Y' ω) ∂μ
      ≤ -(beta1 - eps) * ∫ ω, (Y ω - Y' ω) ^ 2 ∂μ := by
  set dY : Ω → ℝ := fun ω => Y ω - Y' ω with hdY
  set G : Ω → ℝ := fun ω =>
    clamp01 (Y ω - ∫ x, Y x ∂μ) - clamp01 (Y' ω - ∫ x, Y' x ∂μ) with hG
  have hmeanY : ∫ x, dY x ∂μ = (∫ x, Y x ∂μ) - ∫ x, Y' x ∂μ := by
    rw [hdY]; exact integral_sub hY hY'
  have hcentre : ∀ ω, |G ω| ≤ |dY ω - ∫ x, dY x ∂μ| := by
    intro ω
    have := clamp_diff_le_centred hY hY' ω
    rw [hG, hdY]
    simpa [hdY, integral_sub hY hY'] using this
  have hrw : ∀ ω, (drift beta1 eps (Y ω) (∫ x, Y x ∂μ)
      - drift beta1 eps (Y' ω) (∫ x, Y' x ∂μ)) * (Y ω - Y' ω)
      = (-beta1 * dY ω + eps * G ω) * dY ω := by
    intro ω; unfold drift; rw [hG, hdY]; ring
  calc ∫ ω, (drift beta1 eps (Y ω) (∫ x, Y x ∂μ)
          - drift beta1 eps (Y' ω) (∫ x, Y' x ∂μ)) * (Y ω - Y' ω) ∂μ
      = ∫ ω, (-beta1 * dY ω + eps * G ω) * dY ω ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hrw)
    _ ≤ -(beta1 - eps) * ∫ ω, dY ω ^ 2 ∂μ :=
        expected_diagonal_bound heps hm hsm hd1 hd2 hG2 hGd hcentre

end Expected

end MVFBSDEJ.WellPosedness
