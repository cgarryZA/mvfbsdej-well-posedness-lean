/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measurability of sections into `L²`

A function `H : X × E → F`, jointly measurable, whose sections `H(x, ·)` lie in `L²(ν; F)` defines a
map `X → L²(ν; F)`; for `ν` σ-finite on a countably generated space, `L²(ν; F)` is separable and
the map is Borel measurable. This is the step from the joint pointwise measurability of the jump
coefficient to (2.3) of the well-posedness paper, there by weak measurability and the Pettis
theorem, here through the distances to the points of `L²(ν; F)`.

## Main statements

* `MVFBSDEJ.Law.measurable_of_measurable_dist` — measurability into a separable space through
  distances.
* `MVFBSDEJ.Law.measurable_lp_of_measurable_uncurry` — sections of a jointly measurable
  function are measurable into `L²`.
-/

open MeasureTheory
open scoped ENNReal

namespace MVFBSDEJ.Law

/-- **Measurability through distances.** A map into a separable pseudometric space with its Borel
σ-algebra is measurable when its distance to every point is measurable: every open set is a
countable union of balls centred in a countable dense set. -/
theorem measurable_of_measurable_dist {X Y : Type*} [MeasurableSpace X] [PseudoMetricSpace Y]
    [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y] {g : X → Y}
    (hg : ∀ y, Measurable fun x => dist (g x) y) : Measurable g := by
  refine measurable_of_isOpen fun U hU => ?_
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense Y
  have hset : g ⁻¹' U = ⋃ y ∈ D, ⋃ r : ℚ, ⋃ (_ : Metric.ball y r ⊆ U),
      {x | dist (g x) y < r} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hx
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU (g x) hx
      obtain ⟨y, hyD, hy⟩ := hDd.exists_dist_lt (g x) (by positivity : 0 < ε / 3)
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (by linarith : ε / 3 < 2 * ε / 3)
      refine ⟨y, hyD, r, fun z hz => hball ?_, by linarith⟩
      rw [Metric.mem_ball] at hz ⊢
      calc dist z (g x) ≤ dist z y + dist y (g x) := dist_triangle _ _ _
        _ < ε := by rw [dist_comm y (g x)]; linarith
    · rintro ⟨y, -, r, hsub, hx⟩
      exact hsub (Metric.mem_ball.mpr hx)
  rw [hset]
  exact MeasurableSet.biUnion hDc fun y _ => MeasurableSet.iUnion fun r =>
    MeasurableSet.iUnion fun _ => measurableSet_lt (hg y) measurable_const

/-- **Sections of a jointly measurable function are measurable into `L²`.** For `ν` σ-finite on
a countably generated space and `H : X × E → F` measurable, a map `h : X → L²(ν; F)` with
`h(x) = H(x, ·)` `ν`-almost everywhere for every `x` is measurable for the Borel σ-algebra of
`L²(ν; F)`: its distance to each `y ∈ L²(ν; F)` is `(∫ |H(x, e) − y(e)|² ν(de))^{1/2}`,
measurable in `x` by Tonelli. -/
theorem measurable_lp_of_measurable_uncurry {X E F : Type*} [MeasurableSpace X]
    [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace (Lp F 2 ν)] [BorelSpace (Lp F 2 ν)]
    {H : X × E → F} (hH : Measurable H) {h : X → Lp F 2 ν}
    (hh : ∀ x, (h x : E → F) =ᵐ[ν] fun e => H (x, e)) : Measurable h := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  refine measurable_of_measurable_dist fun y => ?_
  have hy : Measurable (y : E → F) := (Lp.stronglyMeasurable y).measurable
  have hint : Measurable fun x => ∫⁻ e, ‖H (x, e) - y e‖ₑ ^ (2 : ℝ≥0∞).toReal ∂ν :=
    Measurable.lintegral_prod_right' ((hH.sub (hy.comp measurable_snd)).enorm.pow_const _)
  have e : ∀ x, dist (h x) y
      = ((∫⁻ e, ‖H (x, e) - y e‖ₑ ^ (2 : ℝ≥0∞).toReal ∂ν) ^ (1 / (2 : ℝ≥0∞).toReal)).toReal := by
    intro x
    rw [Lp.dist_def, eLpNorm_congr_ae ((hh x).sub (Filter.EventuallyEq.refl _ (y : E → F))),
      eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    rfl
  simp_rw [e]
  exact (hint.pow_const _).ennreal_toReal

end MVFBSDEJ.Law
