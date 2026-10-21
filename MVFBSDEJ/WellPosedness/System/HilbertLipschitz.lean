/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Law.LipschitzFunctional
import MVFBSDEJ.WellPosedness.System.HilbertW2

/-!
# Lipschitz law functionals for the Hilbert norm of the tuple space

For a map `φ̄` from the tuple space `H` into a normed space with
`‖φ̄ θ − φ̄ θ'‖ ≤ K |θ − θ'|_H`, `K ≥ 0`, where `|·|_H` is the Hilbert norm
`(|x|² + |y|² + |z|²_F + ‖u‖²_{L²(ν)})^{1/2}`, the law functional `μ ↦ ∫_H φ̄ dμ` on the laws of
finite second moment is Lipschitz for the 2-Wasserstein distance of that norm with the same
constant, (2.10) of the well-posedness paper:

`‖∫_H φ̄ dμ − ∫_H φ̄ dμ'‖ ≤ K W₂(μ, μ')`.

Such a map is strongly measurable and integrable against every law of finite second moment, so
the two integrals are Bochner integrals of integrable maps.

## Main statements

* `stronglyMeasurable_of_norm_sub_le_toL2`, `integrable_of_norm_sub_le_toL2` — a map with a
  Lipschitz bound for the Hilbert norm is strongly measurable, and integrable against every law of
  finite second moment.
* `norm_integral_sub_le_w2H` — (2.10) for the Hilbert norm.
-/

open MeasureTheory MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

section Lipschitz

variable {HX HY HZY HUY : Type*} [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [NormedAddCommGroup HZY]
  [InnerProductSpace ℝ HZY] [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY]
  [MeasurableSpace HX] [MeasurableSpace HY] [MeasurableSpace HZY] [MeasurableSpace HUY]
  [BorelSpace HX] [BorelSpace HY] [BorelSpace HZY] [BorelSpace HUY]
  [SecondCountableTopology HX] [SecondCountableTopology HY] [SecondCountableTopology HZY]
  [SecondCountableTopology HUY]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- A map from the tuple space with a Lipschitz bound for the Hilbert norm is strongly
measurable. -/
theorem stronglyMeasurable_of_norm_sub_le_toL2 {φ : Tuple HX HY HZY HUY → F} {K : ℝ}
    (hK : 0 ≤ K) (hlip : ∀ θ θ', ‖φ θ - φ θ'‖ ≤ K * ‖toL2 θ - toL2 θ'‖) :
    StronglyMeasurable φ := by
  have hL : LipschitzWith (Real.toNNReal (2 * K)) φ := by
    refine LipschitzWith.of_dist_le_mul fun θ θ' => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    have h := norm_toL2_le (θ - θ')
    rw [toL2_sub] at h
    calc ‖φ θ - φ θ'‖ ≤ K * ‖toL2 θ - toL2 θ'‖ := hlip θ θ'
      _ ≤ K * (2 * ‖θ - θ'‖) := mul_le_mul_of_nonneg_left h hK
      _ = 2 * K * ‖θ - θ'‖ := by ring
  exact hL.continuous.stronglyMeasurable

omit [NormedSpace ℝ F] in
/-- A map from the tuple space with a Lipschitz bound for the Hilbert norm is integrable against
every law of finite second moment. -/
theorem integrable_of_norm_sub_le_toL2 {φ : Tuple HX HY HZY HUY → F} {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ θ θ', ‖φ θ - φ θ'‖ ≤ K * ‖toL2 θ - toL2 θ'‖) (μ : P2 (Tuple HX HY HZY HUY)) :
    Integrable φ μ.law := by
  refine integrable_of_norm_sub_le (stronglyMeasurable_of_norm_sub_le_toL2 hK hlip)
    (K := 2 * K) (fun θ θ' => ?_) μ.secondMoment_ne_top
  have h := norm_toL2_le (θ - θ')
  rw [toL2_sub] at h
  calc ‖φ θ - φ θ'‖ ≤ K * ‖toL2 θ - toL2 θ'‖ := hlip θ θ'
    _ ≤ K * (2 * ‖θ - θ'‖) := mul_le_mul_of_nonneg_left h hK
    _ = 2 * K * ‖θ - θ'‖ := by ring

/-- **(2.10) for the Hilbert norm.** For a map `φ̄` from the tuple space into a normed space with
`‖φ̄ θ − φ̄ θ'‖ ≤ K |θ − θ'|_H`, `K ≥ 0`, and two laws of finite second moment,
`‖∫ φ̄ dμ − ∫ φ̄ dμ'‖ ≤ K W₂(μ, μ')`, with `W₂` the 2-Wasserstein distance for the Hilbert
norm. -/
theorem norm_integral_sub_le_w2H {φ : Tuple HX HY HZY HUY → F} {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ θ θ', ‖φ θ - φ θ'‖ ≤ K * ‖toL2 θ - toL2 θ'‖) (μ μ' : P2 (Tuple HX HY HZY HUY)) :
    ‖(∫ θ, φ θ ∂μ.law) - ∫ θ, φ θ ∂μ'.law‖ ≤ K * w2H μ μ' := by
  have hφ := stronglyMeasurable_of_norm_sub_le_toL2 hK hlip
  set ψ : TupleL2 HX HY HZY HUY → F := fun w => φ (ofL2 w) with hψdef
  have hψ : StronglyMeasurable ψ := hφ.comp_measurable measurable_ofL2
  have hψlip : ∀ w w', ‖ψ w - ψ w'‖ ≤ K * ‖w - w'‖ := fun w w' => by
    simpa only [hψdef, toL2_ofL2] using hlip (ofL2 w) (ofL2 w')
  have hmap : ∀ ρ : P2 (Tuple HX HY HZY HUY),
      IsProbabilityMeasure (ρ.law.map toL2) ∧ Integrable ψ (ρ.law.map toL2) ∧
        ∫ w, ψ w ∂(ρ.law.map toL2) = ∫ θ, φ θ ∂ρ.law := fun ρ =>
    ⟨Measure.isProbabilityMeasure_map measurable_toL2.aemeasurable,
      (integrable_map_measure hψ.aestronglyMeasurable measurable_toL2.aemeasurable).mpr
        (integrable_of_norm_sub_le_toL2 hK hlip ρ),
      integral_map measurable_toL2.aemeasurable hψ.aestronglyMeasurable⟩
  obtain ⟨hμ1, hμ2, hμ3⟩ := hmap μ
  obtain ⟨hμ'1, hμ'2, hμ'3⟩ := hmap μ'
  rw [← hμ3, ← hμ'3]
  exact norm_integral_sub_le_w2_of_nonneg hψ hK hψlip hμ2 hμ'2 (w2sq_map_toL2_ne_top μ μ')

end Lipschitz

end MVFBSDEJ.WellPosedness.System
