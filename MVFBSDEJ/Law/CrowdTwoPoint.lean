/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Law.CrowdGrad
import MVFBSDEJ.Law.Mixture
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# The crowding operator at symmetric two-point laws

For a point `a` of a separable Hilbert space `F`, the symmetric two-point law
`½ (δ_{−a} + δ_a)` has mean `0`, and the crowding operator `A_λ(u) = ∫ ∇V(u − v) λ(dv)`,
`∇V(w) = w / √(1 + ‖w‖²)`, at it is `A(u) = ½ (∇V(u + a) + ∇V(u − a))`. For a unit vector `w`,
the laws `λ₁ = ½ (δ_{−w} + δ_w)` and `λ₂ = ½ (δ_{−2w} + δ_{2w})` share their mean `0`, while

`A_{λ₁}(w) = ½ (∇V(2w) + ∇V(0)) = (1/√5) w`,
`A_{λ₂}(w) = ½ (∇V(3w) + ∇V(−w)) = ½ (3/√10 − 1/√2) w`,

and `½ (3/√10 − 1/√2) < 1/4 < 1/√5`. So the crowding operator at `w` is not a function of the mean
of the law.

## Main definitions

* `MVFBSDEJ.Law.P2.twoPoint` — the symmetric two-point law `½ (δ_{−a} + δ_a)`.

## Main statements

* `MVFBSDEJ.Law.integral_twoPoint` — the symmetric two-point law has mean `0`.
* `MVFBSDEJ.Law.crowdOp_twoPoint` — `A_{½(δ_{−a} + δ_a)}(u) = ½ (∇V(u + a) + ∇V(u − a))`.
* `MVFBSDEJ.Law.crowdOp_twoPoint_one`, `MVFBSDEJ.Law.crowdOp_twoPoint_two` — the two
  values `(1/√5) w` and `½ (3/√10 − 1/√2) w`.
* `MVFBSDEJ.Law.crowdOp_not_mean_function` — the crowding operator at a unit vector is not a
  function of the mean of the law.
-/

namespace MVFBSDEJ.Law

open MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- `1/2` lies in `[0, 1]`. -/
private theorem half_mem_Icc : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by norm_num, by norm_num⟩

/-- The symmetric two-point law `½ (δ_{−a} + δ_a)`, as a law of finite second moment. -/
noncomputable def P2.twoPoint (a : F) : P2 F :=
  P2.mix (1 / 2) half_mem_Icc (P2.dirac (-a)) (P2.dirac a)

omit [InnerProductSpace ℝ F] in
/-- The integral of a map against `½ (δ_{−a} + δ_a)` is the average of its values at `∓a`. -/
theorem integral_twoPoint {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (f : F → G) (a : F) :
    ∫ v, f v ∂(P2.twoPoint a).law = (1 / 2 : ℝ) • (f (-a) + f a) := by
  have hlaw : (P2.twoPoint a).law
      = ENNReal.ofReal (1 - 1 / 2) • Measure.dirac (-a)
        + ENNReal.ofReal (1 / 2) • Measure.dirac a :=
    rfl
  have hi : ∀ b : F, Integrable f (Measure.dirac b) := fun _ => integrable_dirac enorm_lt_top
  rw [hlaw, integral_add_measure ((hi _).smul_measure ENNReal.ofReal_ne_top)
    ((hi _).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, smul_add]
  norm_num

/-- **The symmetric two-point law has mean `0`.** -/
theorem integral_id_twoPoint (a : F) : ∫ v, v ∂(P2.twoPoint a).law = 0 := by
  have h := integral_twoPoint (fun v : F => v) a
  rw [h, neg_add_cancel, smul_zero]

/-- **The crowding operator at a symmetric two-point law**:
`A_{½(δ_{−a} + δ_a)}(u) = ½ (∇V(u + a) + ∇V(u − a))`. -/
theorem crowdOp_twoPoint (a u : F) :
    crowdOp (P2.twoPoint a).law u = (1 / 2 : ℝ) • (crowdGrad (u + a) + crowdGrad (u - a)) := by
  rw [crowdOp, integral_twoPoint, sub_neg_eq_add]

/-- **The first two-point value**: for a unit vector `w` and `λ₁ = ½ (δ_{−w} + δ_w)`,
`A_{λ₁}(w) = (1/√5) w`. -/
theorem crowdOp_twoPoint_one {w : F} (hw : ‖w‖ = 1) :
    crowdOp (P2.twoPoint w).law w = (1 / Real.sqrt 5) • w := by
  have e : w + w = (2 : ℝ) • w := (two_smul ℝ w).symm
  rw [crowdOp_twoPoint, e, sub_self, crowdGrad_zero, add_zero,
    crowdGrad_smul_of_norm_eq_one hw, smul_smul]
  congr 1
  rw [show (1 : ℝ) + 2 ^ 2 = 5 by norm_num]
  ring

/-- **The second two-point value**: for a unit vector `w` and `λ₂ = ½ (δ_{−2w} + δ_{2w})`,
`A_{λ₂}(w) = ½ (3/√10 − 1/√2) w`. -/
theorem crowdOp_twoPoint_two {w : F} (hw : ‖w‖ = 1) :
    crowdOp (P2.twoPoint ((2 : ℝ) • w)).law w
      = ((3 / Real.sqrt 10 - 1 / Real.sqrt 2) / 2) • w := by
  have e₁ : w + (2 : ℝ) • w = (3 : ℝ) • w := by
    rw [show (3 : ℝ) = 1 + 2 by norm_num, add_smul, one_smul]
  have e₂ : w - (2 : ℝ) • w = (-1 : ℝ) • w := by
    rw [show (-1 : ℝ) = 1 - 2 by norm_num, sub_smul, one_smul]
  rw [crowdOp_twoPoint, e₁, e₂, crowdGrad_smul_of_norm_eq_one hw,
    crowdGrad_smul_of_norm_eq_one hw, ← add_smul, smul_smul]
  congr 1
  rw [show (1 : ℝ) + 3 ^ 2 = 10 by norm_num, show (1 : ℝ) + (-1) ^ 2 = 2 by norm_num]
  ring

/-- The two two-point values differ: `½ (3/√10 − 1/√2) < 1/4 < 1/√5`. -/
theorem twoPoint_values_ne : (3 / Real.sqrt 10 - 1 / Real.sqrt 2) / 2 ≠ 1 / Real.sqrt 5 := by
  have h10 : 3 < Real.sqrt 10 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have h2 : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have h5 : Real.sqrt 5 < 3 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have h2p : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h5p : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have a1 : 3 / Real.sqrt 10 < 1 := (div_lt_one (by linarith)).mpr h10
  have a2 : 1 / 2 < 1 / Real.sqrt 2 := one_div_lt_one_div_of_lt h2p h2
  have a3 : 1 / 3 < 1 / Real.sqrt 5 := one_div_lt_one_div_of_lt h5p h5
  intro h
  linarith

/-- **The crowding operator is not a function of the mean.** For a unit vector `w`, there is no
map `Φ : F → F` with `A_λ(w) = Φ(∫ v λ(dv))` for every law `λ` of finite second moment: the laws
`½ (δ_{−w} + δ_w)` and `½ (δ_{−2w} + δ_{2w})` have the same mean `0` and different values of the
crowding operator at `w`. -/
theorem crowdOp_not_mean_function {w : F} (hw : ‖w‖ = 1) :
    ¬ ∃ Φ : F → F, ∀ Λ : P2 F, crowdOp Λ.law w = Φ (∫ v, v ∂Λ.law) := by
  rintro ⟨Φ, hΦ⟩
  have h1 := hΦ (P2.twoPoint w)
  have h2 := hΦ (P2.twoPoint ((2 : ℝ) • w))
  rw [integral_id_twoPoint, crowdOp_twoPoint_one hw] at h1
  rw [integral_id_twoPoint, crowdOp_twoPoint_two hw, ← h1] at h2
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; exact one_ne_zero)
  exact twoPoint_values_ne (smul_left_injective ℝ hw0 h2)

end MVFBSDEJ.Law
