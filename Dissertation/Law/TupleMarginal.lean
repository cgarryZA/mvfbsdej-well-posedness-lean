/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.HilbertW2Space

/-!
# The `U`-marginal of a law on the tuple space

A law `μ` of finite second moment on the tuple space `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)` has a
`U`-marginal `μ^U ∈ P₂(L²(ν; ℝᵐ))`, the image of `μ` under the projection `θ = (x, y, z, u) ↦ u`.
The projection does not increase the maximum of the channel norms nor the Hilbert norm
`(|x|² + |y|² + |z|²_F + ‖u‖²)^{1/2}`, so pushing a coupling of `μ, μ'` forward along it gives a
coupling of `μ^U, μ'^U` of no larger cost: marginal projection is `1`-Lipschitz for `W₂`, (2.11)
of the paper, both for the 2-Wasserstein distance `w2P` of the maximum of the channel norms and
for that of the Hilbert norm, `w2H`.

## Main definitions

* `projUH` — the projection of the tuple space onto its jump channel, a continuous linear map.
* `Dissertation.Law.P2.margU` — the `U`-marginal of a law of finite second moment on `H`.

## Main statements

* `norm_projUH_le`, `norm_projUH_le_norm_toL2` — the projection does not increase either norm.
* `w2P_margU_le`, `w2P_margU_le_w2H` — `W₂(μ^U, μ'^U) ≤ W₂(μ, μ')`, for the maximum of the channel
  norms and for the Hilbert norm.
* `margU_lawP2` — the `U`-marginal of the law of a random tuple is the law of its `U`-channel.
-/

open MeasureTheory

namespace Dissertation.WellPosedness.System

open Dissertation.Law

/-! ### The projection onto the jump channel -/

section Projection

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}

/-- The projection `θ = (x, y, z, u) ↦ u` of the tuple space `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)`
onto its jump channel, as a continuous linear map. -/
noncomputable def projUH : TupleH ν n m d →L[ℝ] Lp (EuclideanSpace ℝ (Fin m)) 2 ν :=
  (ContinuousLinearMap.snd ℝ _ _).comp
    ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))

/-- `projUH` reads the jump channel. -/
@[simp]
theorem projUH_apply (θ : TupleH ν n m d) : projUH θ = θ.2.2.2 :=
  rfl

/-- The projection onto the jump channel does not increase the maximum of the channel norms. -/
theorem norm_projUH_le (θ : TupleH ν n m d) : ‖projUH θ‖ ≤ ‖θ‖ :=
  ((norm_snd_le θ.2.2).trans (norm_snd_le θ.2)).trans (norm_snd_le θ)

/-- The projection onto the jump channel does not increase the Hilbert norm
`(|x|² + |y|² + |z|²_F + ‖u‖²)^{1/2}`. -/
theorem norm_projUH_le_norm_toL2 (θ : TupleH ν n m d) : ‖projUH θ‖ ≤ ‖toL2 θ‖ := by
  have h : ‖projUH θ‖ ^ 2 ≤ ‖toL2 θ‖ ^ 2 := by
    rw [norm_toL2_sq, channelSq, projUH_apply]
    nlinarith [sq_nonneg ‖θ.1‖, sq_nonneg ‖θ.2.1‖, sq_nonneg ‖θ.2.2.1‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- The projection onto the jump channel is measurable. -/
theorem measurable_projUH : Measurable (projUH : TupleH ν n m d → _) :=
  measurable_snd.comp (measurable_snd.comp measurable_snd)

end Projection

/-! ### The `U`-marginal -/

section Marginal

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-- The `U`-marginal `μ^U ∈ P₂(L²(ν; ℝᵐ))` of a law `μ` of finite second moment on the tuple
space: the image of `μ` under the projection onto the jump channel. -/
noncomputable def _root_.Dissertation.Law.P2.margU (μ : P2 (TupleH ν n m d)) :
    P2 (Lp (EuclideanSpace ℝ (Fin m)) 2 ν) :=
  μ.map measurable_projUH norm_projUH_le

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The law of `μ^U` is the image of the law of `μ` under the projection onto the jump
channel. -/
theorem margU_law (μ : P2 (TupleH ν n m d)) : μ.margU.law = μ.law.map projUH :=
  rfl

/-- **Marginal projection is `1`-Lipschitz for `W₂`**, for the maximum of the channel norms:
`W₂(μ^U, μ'^U) ≤ W₂(μ, μ')`. -/
theorem w2P_margU_le (μ μ' : P2 (TupleH ν n m d)) : w2P μ.margU μ'.margU ≤ w2P μ μ' :=
  w2P_map_le_of_norm_sub_le μ μ' measurable_projUH norm_projUH_le fun θ θ' => by
    rw [← map_sub]
    exact norm_projUH_le _

/-- **Marginal projection is `1`-Lipschitz for `W₂`**, (2.11), for the Hilbert norm of the tuple
space: `W₂(μ^U, μ'^U) ≤ W₂(μ, μ')`. -/
theorem w2P_margU_le_w2H (μ μ' : P2 (TupleH ν n m d)) : w2P μ.margU μ'.margU ≤ w2H μ μ' := by
  set p : TupleL2 (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν) →
      Lp (EuclideanSpace ℝ (Fin m)) 2 ν := fun w => projUH (ofL2 w) with hp
  have hpm : Measurable p := measurable_projUH.comp measurable_ofL2
  have hlip : ∀ w w', ‖p w - p w'‖ ≤ ‖w - w'‖ := fun w w' => by
    have h := norm_projUH_le_norm_toL2 (ν := ν) (ofL2 w - ofL2 w')
    rwa [map_sub, toL2_sub, toL2_ofL2, toL2_ofL2] at h
  have hcomp : ∀ ρ : Measure (TupleH ν n m d), ρ.map projUH = (ρ.map toL2).map p := by
    intro ρ
    rw [Measure.map_map hpm measurable_toL2]
    rfl
  have h := w2_map_le_of_norm_sub_le hpm hlip (μ.law.map toL2) (μ'.law.map toL2)
    (w2sq_map_toL2_ne_top μ μ')
  rw [← hcomp, ← hcomp] at h
  exact h

/-- **The `U`-marginal of the law of a random tuple is the law of its `U`-channel**: for `Θ`
square integrable, `(Law Θ)^U = Law U`. -/
theorem margU_lawP2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Ω → TupleH ν n m d} (hΘ : MemLp Θ 2 P) :
    (lawP2 P Θ).margU = lawP2 P fun ω => (Θ ω).2.2.2 := by
  have hU : MemLp (fun ω => (Θ ω).2.2.2) 2 P := hΘ.snd.snd.snd
  refine P2.ext_law ?_
  rw [margU_law, lawP2_law hΘ, lawP2_law hU, AEMeasurable.map_map_of_aemeasurable
    measurable_projUH.aemeasurable hΘ.aestronglyMeasurable.aemeasurable]
  rfl

end Marginal

end Dissertation.WellPosedness.System
