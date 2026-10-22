/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Law.LawP2

/-!
# The evaluation σ-algebra on the laws of finite second moment

The space of measures on `F` carries the Giry σ-algebra, the coarsest one for which every
evaluation `μ ↦ μ(A)`, `A` measurable, is measurable. The laws of finite second moment `P2 F` are
given the σ-algebra pulled back along `P2.law`: the coarsest one for which every evaluation is
measurable. For a Polish `F` it is the Borel σ-algebra of the 2-Wasserstein distance, a classical
identification.

For a process `Θ` jointly measurable in the sample point and the time, the law flow
`s ↦ Law(Θ_s)` is measurable for this σ-algebra, at every time and for the exact law
`lawP2 P Θ_s`: `P(Θ_s ∈ A)` is measurable in `s` by Tonelli's theorem, and so is the set of times
at which `Θ_s` is square integrable, off which `lawP2` is the Dirac mass at the origin.

## Main definitions

* `MVFBSDEJ.Law.P2.instMeasurableSpace`: the evaluation σ-algebra on `P2 F`.

## Main statements

* `MVFBSDEJ.Law.P2.measurable_law`: `P2.law` is measurable into the Giry σ-algebra.
* `MVFBSDEJ.Law.P2.measurable_of_law`: a map into `P2 F` is measurable when its evaluation
  at each measurable set is.
* `MVFBSDEJ.Law.measurable_lawP2_flow`: the law flow of a jointly measurable process is
  measurable.
-/

namespace MVFBSDEJ.Law

open MeasureTheory
open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F]

/-- The evaluation σ-algebra on the laws of finite second moment: the Giry σ-algebra of the
underlying measures, pulled back along `P2.law`. -/
noncomputable instance P2.instMeasurableSpace : MeasurableSpace (P2 F) :=
  MeasurableSpace.comap P2.law Measure.instMeasurableSpace

/-- The underlying measure of a law of finite second moment depends measurably on the law. -/
theorem P2.measurable_law : Measurable (P2.law : P2 F → Measure F) :=
  comap_measurable _

/-- **A map into the laws of finite second moment is measurable** when its evaluation at every
measurable set is measurable. -/
theorem P2.measurable_of_law {β : Type*} [MeasurableSpace β] {f : β → P2 F}
    (h : ∀ A, MeasurableSet A → Measurable fun b => (f b).law A) : Measurable f := by
  have hm : Measurable fun b => (f b).law := Measure.measurable_of_measurable_coe _ h
  rintro _ ⟨t, ht, rfl⟩
  exact hm ht

variable [BorelSpace F] [SecondCountableTopology F] {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The law flow of a jointly measurable process is measurable**: for `Θ` measurable in
`(ω, s)`, the map `s ↦ lawP2 P Θ_s` is measurable for the evaluation σ-algebra. -/
theorem measurable_lawP2_flow {Θ : Ω → ℝ → F} (hΘ : Measurable (Function.uncurry Θ)) :
    Measurable fun s => lawP2 P fun ω => Θ ω s := by
  classical
  have hs : ∀ s, Measurable fun ω => Θ ω s := fun s =>
    hΘ.comp (measurable_id.prodMk measurable_const)
  set S : Set ℝ := {s | MemLp (fun ω => Θ ω s) 2 P} with hS_def
  have hnorm : Measurable fun s => ∫⁻ ω, ‖Θ ω s‖ₑ ^ (2 : ℝ) ∂P :=
    (hΘ.enorm.pow_const _).lintegral_prod_left'
  have hS : MeasurableSet S := by
    have : S = {s | ∫⁻ ω, ‖Θ ω s‖ₑ ^ (2 : ℝ) ∂P < ⊤} := by
      ext s
      simp only [hS_def, Set.mem_setOf_eq, MemLp, (hs s).aestronglyMeasurable, true_and]
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat, one_div]
      rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num)]
    rw [this]
    exact measurableSet_lt hnorm measurable_const
  refine P2.measurable_of_law fun A hA => ?_
  have heq : (fun s => (lawP2 P fun ω => Θ ω s).law A)
      = S.piecewise (fun s => P ((fun ω => (ω, s)) ⁻¹' (Function.uncurry Θ ⁻¹' A)))
        (fun _ => (P2.dirac (0 : F)).law A) := by
    funext s
    by_cases h : s ∈ S
    · rw [Set.piecewise_eq_of_mem _ _ _ h, lawP2_law h, Measure.map_apply (hs s) hA]
      rfl
    · rw [Set.piecewise_eq_of_notMem _ _ _ h, lawP2_of_not_memLp h]
  rw [heq]
  exact (measurable_measure_prodMk_right (hΘ hA)).piecewise hS measurable_const

end MVFBSDEJ.Law
