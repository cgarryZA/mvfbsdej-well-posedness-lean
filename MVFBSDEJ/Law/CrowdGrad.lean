/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntegrableOn
import MVFBSDEJ.Law.LipschitzFunctional
import MVFBSDEJ.Law.P2

/-!
# The crowding gradient and the crowding operator

On a real inner product space `F` the crowding potential `V(w) = √(1 + ‖w‖²) − 1` is even and
convex, and on a Hilbert space its gradient is

`∇V(w) = w / √(1 + ‖w‖²)`.

The map `∇V` vanishes at the origin, is odd, has norm less than `1`, and is monotone and
`1`-Lipschitz:

`⟨∇V(w) − ∇V(w'), w − w'⟩ ≥ 0`,   `‖∇V(w) − ∇V(w')‖ ≤ ‖w − w'‖`.

Both inequalities reduce, through the Cauchy–Schwarz inequality `⟨w, w'⟩ ≤ ‖w‖ ‖w'‖`, to the
profile `φ(r) = r / √(1 + r²)` on `[0, ∞)`, which is nondecreasing and `1`-Lipschitz, the latter
because `r ↦ r (1 − 1/√(1 + r²))` is nondecreasing.

For a measure `Λ` on a separable Hilbert space `F`, the crowding operator is

`A_Λ(u) = ∫ ∇V(u − v) Λ(dv)`.

For a probability measure `Λ` the integrand is continuous and bounded by `1`, so `‖A_Λ(u)‖ ≤ 1`
and `u ↦ A_Λ(u)` is `1`-Lipschitz; for laws `Λ, Λ'` of finite second moment, `v ↦ ∇V(u' − v)`
being `1`-Lipschitz, the gap `A_Λ(u') − A_Λ'(u')` is at most `W₂(Λ, Λ')` by the Lipschitz bound
for integrals across a coupling, so

`‖A_Λ(u) − A_Λ'(u')‖ ≤ ‖u − u'‖ + W₂(Λ, Λ')`.

## Main definitions

* `MVFBSDEJ.Law.crowdPot` — the crowding potential `V(w) = √(1 + ‖w‖²) − 1`.
* `MVFBSDEJ.Law.crowdGrad` — its gradient `∇V(w) = w / √(1 + ‖w‖²)`.
* `MVFBSDEJ.Law.crowdOp` — the crowding operator `A_Λ(u) = ∫ ∇V(u − v) Λ(dv)`.

## Main statements

* `crowdPot_neg`, `convexOn_crowdPot`, `hasGradientAt_crowdPot` — `V` is even and convex, with
  gradient `∇V`.
* `crowdGrad_zero`, `crowdGrad_neg`, `norm_crowdGrad_lt_one` — `∇V(0) = 0`, `∇V` is odd and
  `‖∇V(w)‖ < 1`.
* `inner_crowdGrad_sub_nonneg` — `∇V` is monotone.
* `norm_crowdGrad_sub_le`, `lipschitzWith_one_crowdGrad` — `∇V` is `1`-Lipschitz.
* `norm_crowdOp_le_one`, `crowdOp_dirac` — `‖A_Λ(u)‖ ≤ 1`, and `A_{δ_a}(u) = ∇V(u − a)`.
* `norm_crowdOp_sub_crowdOp_le` — `u ↦ A_Λ(u)` is `1`-Lipschitz.
* `norm_crowdOp_sub_le` — `‖A_Λ(u) − A_Λ'(u')‖ ≤ ‖u − u'‖ + W₂(Λ, Λ')`.
-/

namespace MVFBSDEJ.Law

open MeasureTheory
open scoped RealInnerProductSpace

/-! ### The scalar profile -/

section Profile

/-- The profile `r ↦ r / √(1 + r²)` is nondecreasing on `[0, ∞)`, with increments at most those
of the identity: for `0 ≤ r' ≤ r`, `0 ≤ r / √(1 + r²) − r' / √(1 + r'²) ≤ r − r'`. -/
private theorem profile_le {r r' : ℝ} (hr' : 0 ≤ r') (h : r' ≤ r) :
    r' * (Real.sqrt (1 + r' ^ 2))⁻¹ ≤ r * (Real.sqrt (1 + r ^ 2))⁻¹
      ∧ r * (Real.sqrt (1 + r ^ 2))⁻¹ - r' * (Real.sqrt (1 + r' ^ 2))⁻¹ ≤ r - r' := by
  have hr : 0 ≤ r := hr'.trans h
  have hs2 : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 := Real.sq_sqrt (by positivity)
  have hs2' : Real.sqrt (1 + r' ^ 2) ^ 2 = 1 + r' ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 < Real.sqrt (1 + r ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs0' : 0 < Real.sqrt (1 + r' ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs1' : 1 ≤ Real.sqrt (1 + r' ^ 2) := (Real.le_sqrt' one_pos).mpr (by nlinarith)
  have hss : Real.sqrt (1 + r' ^ 2) ≤ Real.sqrt (1 + r ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  refine ⟨?_, ?_⟩
  · rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hs0' hs0]
    have hsq : (r' * Real.sqrt (1 + r ^ 2)) ^ 2 ≤ (r * Real.sqrt (1 + r' ^ 2)) ^ 2 := by
      rw [mul_pow, mul_pow, hs2, hs2']
      nlinarith [mul_le_mul h h hr' hr]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  · have h1 : (Real.sqrt (1 + r ^ 2))⁻¹ ≤ (Real.sqrt (1 + r' ^ 2))⁻¹ := inv_anti₀ hs0' hss
    have h2 : (Real.sqrt (1 + r' ^ 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1'
    have key := mul_le_mul h (sub_le_sub_left h1 1) (by linarith) hr
    nlinarith [key]

/-- The two facts on the profile `φ(r) = r / √(1 + r²)` behind the monotonicity and the Lipschitz
bound of the crowding gradient: for `r, r' ≥ 0`, `(r − r') (φ(r) − φ(r')) ≥ 0` and
`(φ(r) − φ(r'))² ≤ (r − r')²`. -/
private theorem profile_pair {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') :
    0 ≤ (r - r') * (r * (Real.sqrt (1 + r ^ 2))⁻¹ - r' * (Real.sqrt (1 + r' ^ 2))⁻¹)
      ∧ (r * (Real.sqrt (1 + r ^ 2))⁻¹ - r' * (Real.sqrt (1 + r' ^ 2))⁻¹) ^ 2
        ≤ (r - r') ^ 2 := by
  rcases le_total r' r with h | h
  · obtain ⟨h1, h2⟩ := profile_le hr' h
    refine ⟨mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr h1), ?_⟩
    exact pow_le_pow_left₀ (sub_nonneg.mpr h1) h2 2
  · obtain ⟨h1, h2⟩ := profile_le hr h
    refine ⟨mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h) (sub_nonpos.mpr h1), ?_⟩
    nlinarith [sub_nonneg.mpr h1]

end Profile

/-! ### The crowding potential and its gradient -/

section Gradient

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The crowding potential `V(w) = √(1 + ‖w‖²) − 1`. -/
noncomputable def crowdPot (w : F) : ℝ :=
  Real.sqrt (1 + ‖w‖ ^ 2) - 1

/-- The crowding gradient `∇V(w) = w / √(1 + ‖w‖²)`. -/
noncomputable def crowdGrad (w : F) : F :=
  (Real.sqrt (1 + ‖w‖ ^ 2))⁻¹ • w

/-- The crowding potential vanishes at the origin. -/
@[simp]
theorem crowdPot_zero : crowdPot (0 : F) = 0 := by
  simp [crowdPot]

/-- The crowding potential is even. -/
@[simp]
theorem crowdPot_neg (w : F) : crowdPot (-w) = crowdPot w := by
  simp [crowdPot]

/-- The crowding gradient vanishes at the origin. -/
@[simp]
theorem crowdGrad_zero : crowdGrad (0 : F) = 0 := by
  simp [crowdGrad]

/-- The crowding gradient is odd. -/
@[simp]
theorem crowdGrad_neg (w : F) : crowdGrad (-w) = -crowdGrad w := by
  simp [crowdGrad]

/-- The crowding gradient at `c • w` for a unit vector `w`: `∇V(c w) = (c / √(1 + c²)) w`. -/
theorem crowdGrad_smul_of_norm_eq_one {w : F} (hw : ‖w‖ = 1) (c : ℝ) :
    crowdGrad (c • w) = (c / Real.sqrt (1 + c ^ 2)) • w := by
  rw [crowdGrad, norm_smul, hw, mul_one, Real.norm_eq_abs, sq_abs, smul_smul, div_eq_inv_mul]

/-- The norm of the crowding gradient, `‖∇V(w)‖ = ‖w‖ / √(1 + ‖w‖²)`. -/
theorem norm_crowdGrad (w : F) : ‖crowdGrad w‖ = ‖w‖ * (Real.sqrt (1 + ‖w‖ ^ 2))⁻¹ := by
  rw [crowdGrad, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_comm]

/-- **The crowding gradient has norm less than one.** -/
theorem norm_crowdGrad_lt_one (w : F) : ‖crowdGrad w‖ < 1 := by
  rw [norm_crowdGrad, ← div_eq_mul_inv, div_lt_one (Real.sqrt_pos.mpr (by positivity))]
  exact (Real.lt_sqrt (norm_nonneg _)).mpr (by linarith)

/-- The crowding gradient has norm at most one. -/
theorem norm_crowdGrad_le_one (w : F) : ‖crowdGrad w‖ ≤ 1 :=
  (norm_crowdGrad_lt_one w).le

/-- The scalar `1 / √(1 + ‖w‖²)` of the crowding gradient lies in `(0, 1]`. -/
private theorem crowdScalar_mem (w : F) :
    0 < (Real.sqrt (1 + ‖w‖ ^ 2))⁻¹ ∧ (Real.sqrt (1 + ‖w‖ ^ 2))⁻¹ ≤ 1 := by
  refine ⟨inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)), inv_le_one_of_one_le₀ ?_⟩
  exact (Real.le_sqrt' one_pos).mpr (by nlinarith [sq_nonneg ‖w‖])

/-- **The crowding gradient is monotone**: `⟨∇V(w) − ∇V(w'), w − w'⟩ ≥ 0`. -/
theorem inner_crowdGrad_sub_nonneg (w w' : F) :
    0 ≤ ⟪crowdGrad w - crowdGrad w', w - w'⟫ := by
  obtain ⟨ha, -⟩ := crowdScalar_mem w
  obtain ⟨hb, -⟩ := crowdScalar_mem w'
  have hcs : ⟪w, w'⟫ ≤ ‖w‖ * ‖w'‖ := real_inner_le_norm w w'
  have hprod := (profile_pair (norm_nonneg w) (norm_nonneg w')).1
  have hexp : ⟪crowdGrad w - crowdGrad w', w - w'⟫
      = (Real.sqrt (1 + ‖w‖ ^ 2))⁻¹ * ‖w‖ ^ 2 + (Real.sqrt (1 + ‖w'‖ ^ 2))⁻¹ * ‖w'‖ ^ 2
        - ((Real.sqrt (1 + ‖w‖ ^ 2))⁻¹ + (Real.sqrt (1 + ‖w'‖ ^ 2))⁻¹) * ⟪w, w'⟫ := by
    simp only [crowdGrad, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, real_inner_comm w w']
    ring
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_left hcs (add_pos ha hb).le]

/-- **The crowding gradient is `1`-Lipschitz**: `‖∇V(w) − ∇V(w')‖ ≤ ‖w − w'‖`. -/
theorem norm_crowdGrad_sub_le (w w' : F) : ‖crowdGrad w - crowdGrad w'‖ ≤ ‖w - w'‖ := by
  obtain ⟨ha, ha1⟩ := crowdScalar_mem w
  obtain ⟨hb, hb1⟩ := crowdScalar_mem w'
  have hcs : ⟪w, w'⟫ ≤ ‖w‖ * ‖w'‖ := real_inner_le_norm w w'
  have hsq := (profile_pair (norm_nonneg w) (norm_nonneg w')).2
  have hab : 0 ≤ 1 - (Real.sqrt (1 + ‖w‖ ^ 2))⁻¹ * (Real.sqrt (1 + ‖w'‖ ^ 2))⁻¹ := by
    nlinarith [mul_le_mul ha1 hb1 hb.le zero_le_one]
  have h : ‖crowdGrad w - crowdGrad w'‖ ^ 2 ≤ ‖w - w'‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real]
    simp only [crowdGrad, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_of_nonneg ha.le, Real.norm_of_nonneg hb.le]
    nlinarith [mul_le_mul_of_nonneg_left hcs hab]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- The crowding gradient is Lipschitz with constant `1`. -/
theorem lipschitzWith_one_crowdGrad : LipschitzWith 1 (crowdGrad : F → F) :=
  LipschitzWith.of_dist_le_mul fun w w' => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact norm_crowdGrad_sub_le w w'

/-- The crowding gradient is continuous. -/
theorem continuous_crowdGrad : Continuous (crowdGrad : F → F) :=
  lipschitzWith_one_crowdGrad.continuous

/-- **The crowding potential is convex.** -/
theorem convexOn_crowdPot : ConvexOn ℝ Set.univ (crowdPot : F → ℝ) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hsx : Real.sqrt (1 + ‖x‖ ^ 2) ^ 2 = 1 + ‖x‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hsy : Real.sqrt (1 + ‖y‖ ^ 2) ^ 2 = 1 + ‖y‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hx0 := Real.sqrt_nonneg (1 + ‖x‖ ^ 2)
  have hy0 := Real.sqrt_nonneg (1 + ‖y‖ ^ 2)
  have hcs : ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  have hst : 1 + ‖x‖ * ‖y‖ ≤ Real.sqrt (1 + ‖x‖ ^ 2) * Real.sqrt (1 + ‖y‖ ^ 2) := by
    have h2 : (1 + ‖x‖ * ‖y‖) ^ 2
        ≤ (Real.sqrt (1 + ‖x‖ ^ 2) * Real.sqrt (1 + ‖y‖ ^ 2)) ^ 2 := by
      rw [mul_pow, hsx, hsy]
      nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2
  have hnorm : ‖a • x + b • y‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 + 2 * (a * b) * ⟪x, y⟫ + b ^ 2 * ‖y‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb,
      real_inner_smul_left, real_inner_smul_right]
    ring
  have hkey : Real.sqrt (1 + ‖a • x + b • y‖ ^ 2)
      ≤ a * Real.sqrt (1 + ‖x‖ ^ 2) + b * Real.sqrt (1 + ‖y‖ ^ 2) := by
    rw [Real.sqrt_le_left (by positivity)]
    rw [hnorm]
    have hab2 : (a + b) ^ 2 = 1 := by rw [hab]; norm_num
    have hin : 1 + ⟪x, y⟫ ≤ Real.sqrt (1 + ‖x‖ ^ 2) * Real.sqrt (1 + ‖y‖ ^ 2) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hin (mul_nonneg ha hb)]
  simp only [crowdPot, smul_eq_mul]
  nlinarith [hkey]

/-- **The crowding gradient is the gradient of the crowding potential.** -/
theorem hasGradientAt_crowdPot [CompleteSpace F] (w : F) :
    HasGradientAt crowdPot (crowdGrad w) w := by
  have h1 : HasFDerivAt (fun x : F => 1 + ‖x‖ ^ 2) (2 • innerSL ℝ w) w :=
    (hasStrictFDerivAt_norm_sq w).hasFDerivAt.const_add 1
  have h2 := (h1.sqrt (by positivity)).sub_const 1
  have hs : Real.sqrt (1 + ‖w‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have e : (1 / (2 * Real.sqrt (1 + ‖w‖ ^ 2))) • (2 • innerSL ℝ w)
      = InnerProductSpace.toDual ℝ F (crowdGrad w) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [crowdGrad, InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
      smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
    field_simp
    ring
  rw [e] at h2
  exact hasGradientAt_iff_hasFDerivAt.mpr h2

end Gradient

/-! ### The crowding operator -/

section Operator

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F]

/-- The crowding operator `A_Λ(u) = ∫ ∇V(u − v) Λ(dv)` of a measure `Λ` on `F`. -/
noncomputable def crowdOp (Λ : Measure F) (u : F) : F :=
  ∫ v, crowdGrad (u - v) ∂Λ

variable [BorelSpace F] [SecondCountableTopology F]

/-- The integrand `v ↦ ∇V(u − v)` of the crowding operator is strongly measurable. -/
theorem stronglyMeasurable_crowdGrad_sub (u : F) :
    StronglyMeasurable fun v : F => crowdGrad (u - v) :=
  (continuous_crowdGrad.comp (continuous_const.sub continuous_id)).stronglyMeasurable

/-- The integrand `v ↦ ∇V(u − v)` of the crowding operator is integrable against every finite
measure. -/
theorem integrable_crowdGrad_sub (Λ : Measure F) [IsFiniteMeasure Λ] (u : F) :
    Integrable (fun v => crowdGrad (u - v)) Λ :=
  Integrable.of_bound (stronglyMeasurable_crowdGrad_sub u).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun _ => norm_crowdGrad_le_one _)

/-- **The crowding operator of a probability measure has norm at most one.** -/
theorem norm_crowdOp_le_one (Λ : Measure F) [IsProbabilityMeasure Λ] (u : F) :
    ‖crowdOp Λ u‖ ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := Λ)
    (Filter.Eventually.of_forall fun v => norm_crowdGrad_le_one (u - v))
  rwa [probReal_univ, mul_one] at h

/-- The crowding operator of a Dirac mass: `A_{δ_a}(u) = ∇V(u − a)`. -/
theorem crowdOp_dirac (a u : F) : crowdOp (Measure.dirac a) u = crowdGrad (u - a) :=
  integral_dirac' _ a (stronglyMeasurable_crowdGrad_sub u)

/-- The crowding operator of the Dirac mass at the origin vanishes at the origin. -/
theorem crowdOp_dirac_zero : crowdOp (Measure.dirac (0 : F)) 0 = 0 := by
  rw [crowdOp_dirac, sub_zero, crowdGrad_zero]

/-- **The crowding operator of a probability measure is `1`-Lipschitz**:
`‖A_Λ(u) − A_Λ(u')‖ ≤ ‖u − u'‖`. -/
theorem norm_crowdOp_sub_crowdOp_le (Λ : Measure F) [IsProbabilityMeasure Λ] (u u' : F) :
    ‖crowdOp Λ u - crowdOp Λ u'‖ ≤ ‖u - u'‖ := by
  rw [crowdOp, crowdOp, ← integral_sub (integrable_crowdGrad_sub Λ u)
    (integrable_crowdGrad_sub Λ u')]
  have h : ‖∫ v, (crowdGrad (u - v) - crowdGrad (u' - v)) ∂Λ‖ ≤ ‖u - u'‖ * Λ.real Set.univ :=
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun v => by
      simpa only [sub_sub_sub_cancel_right] using norm_crowdGrad_sub_le (u - v) (u' - v))
  rwa [probReal_univ, mul_one] at h

/-- The crowding operator of a probability measure is continuous. -/
theorem continuous_crowdOp (Λ : Measure F) [IsProbabilityMeasure Λ] :
    Continuous (crowdOp Λ) :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun u u' => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    exact norm_crowdOp_sub_crowdOp_le Λ u u').continuous

/-- **The crowding operator is jointly Lipschitz**: for laws `Λ, Λ'` of finite second moment and
points `u, u'`, `‖A_Λ(u) − A_Λ'(u')‖ ≤ ‖u − u'‖ + W₂(Λ, Λ')`. -/
theorem norm_crowdOp_sub_le (Λ Λ' : P2 F) (u u' : F) :
    ‖crowdOp Λ.law u - crowdOp Λ'.law u'‖ ≤ ‖u - u'‖ + w2P Λ Λ' := by
  have h1 := norm_crowdOp_sub_crowdOp_le Λ.law u u'
  have h2 : ‖crowdOp Λ.law u' - crowdOp Λ'.law u'‖ ≤ 1 * w2P Λ Λ' :=
    norm_integral_sub_le_w2_of_nonneg (stronglyMeasurable_crowdGrad_sub u') zero_le_one
      (fun v v' => by
        calc ‖crowdGrad (u' - v) - crowdGrad (u' - v')‖ ≤ ‖(u' - v) - (u' - v')‖ :=
              norm_crowdGrad_sub_le _ _
          _ = 1 * ‖v - v'‖ := by rw [sub_sub_sub_cancel_left, norm_sub_rev, one_mul])
      (integrable_crowdGrad_sub _ u') (integrable_crowdGrad_sub _ u') (w2sq_ne_top Λ Λ')
  rw [one_mul] at h2
  calc ‖crowdOp Λ.law u - crowdOp Λ'.law u'‖
      = ‖(crowdOp Λ.law u - crowdOp Λ.law u') + (crowdOp Λ.law u' - crowdOp Λ'.law u')‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖crowdOp Λ.law u - crowdOp Λ.law u'‖ + ‖crowdOp Λ.law u' - crowdOp Λ'.law u'‖ :=
        norm_add_le _ _
    _ ≤ ‖u - u'‖ + w2P Λ Λ' := add_le_add h1 h2

end Operator

end MVFBSDEJ.Law
