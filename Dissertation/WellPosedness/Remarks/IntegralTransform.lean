/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# The probability integral transform

For a probability measure `μ` on `ℝ` without atoms, the cumulative distribution function
`F = cdf μ` is continuous, and it pushes `μ` forward to the uniform law on `[0, 1]`:
`μ {x | F x ≤ a} = a` for every `a ∈ [0, 1]`. Consequently a real random variable `X` whose law has
no atoms gives the uniform variable `F(X)`.

The set `{x | F x ≤ a}` is a closed lower set of `ℝ`; for `a < 1` it is bounded above, so it is
empty or the half-line `(-∞, q]` at its supremum `q`, and continuity of `F` at `q` gives
`F q = a`.

## Main definitions

* `Dissertation.Law.cdfUnit` — the cumulative distribution function as a map into `[0, 1]`.

## Main statements

* `Dissertation.Law.continuous_cdf_of_measure_singleton` — the distribution function of a law
  without atoms is continuous.
* `Dissertation.Law.measure_setOf_cdf_le` — `μ {x | F x ≤ a} = a` for `a ∈ [0, 1]`.
* `Dissertation.Law.map_cdfUnit_eq_volume` — the probability integral transform: `F` pushes `μ`
  forward to the Lebesgue measure on `[0, 1]`.
* `Dissertation.Law.map_cdfUnit_comp_eq_volume` — a random variable whose law has no atoms gives
  a uniform variable.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology unitInterval

namespace Dissertation.Law

/-- The cumulative distribution function of a measure on `ℝ`, as a map into `[0, 1]`. -/
noncomputable def cdfUnit (μ : Measure ℝ) (x : ℝ) : I :=
  ⟨cdf μ x, cdf_nonneg μ x, cdf_le_one μ x⟩

/-- The value of `cdfUnit μ` is the distribution function. -/
@[simp]
theorem coe_cdfUnit (μ : Measure ℝ) (x : ℝ) : (cdfUnit μ x : ℝ) = cdf μ x := rfl

/-- The distribution function, as a map into `[0, 1]`, is measurable. -/
@[fun_prop]
theorem measurable_cdfUnit (μ : Measure ℝ) : Measurable (cdfUnit μ) :=
  (monotone_cdf μ).measurable.subtype_mk

variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

/-- **The distribution function of a law without atoms is continuous.** -/
theorem continuous_cdf_of_measure_singleton (hμ : ∀ x, μ {x} = 0) : Continuous (cdf μ) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  rw [(monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  have h := (cdf μ).measure_singleton x
  rw [measure_cdf, hμ x, eq_comm, ENNReal.ofReal_eq_zero, sub_nonpos] at h
  exact le_antisymm ((monotone_cdf μ).leftLim_le le_rfl) h

/-- **The distribution function of a law without atoms is uniform under the law**:
`μ {x | F x ≤ a} = a` for every `a ∈ [0, 1]`. -/
theorem measure_setOf_cdf_le (hμ : ∀ x, μ {x} = 0) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    μ {x | cdf μ x ≤ a} = ENNReal.ofReal a := by
  rcases ha1.lt_or_eq with ha1 | rfl
  swap
  · simp [cdf_le_one]
  set S := {x | cdf μ x ≤ a} with hS
  have hcont := continuous_cdf_of_measure_singleton hμ
  have hclosed : IsClosed S := isClosed_le hcont continuous_const
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds ha1))
  have hbdd : BddAbove S := ⟨x₀, fun y hy => by
    by_contra h
    exact absurd (hx₀ y (not_le.mp h).le) (not_lt.mpr hy)⟩
  rcases S.eq_empty_or_nonempty with he | hne
  · have ha : a = 0 := by
      refine le_antisymm (not_lt.mp fun ha => ?_) ha0
      obtain ⟨y, hy⟩ := ((tendsto_cdf_atBot μ).eventually (gt_mem_nhds ha)).exists
      have : y ∈ S := hy.le
      rw [he] at this
      exact this
    rw [he, ha]
    simp
  set q := sSup S with hq
  have hqS : q ∈ S := hclosed.csSup_mem hne hbdd
  have hSq : S = Iic q := by
    ext y
    exact ⟨fun hy => le_csSup hbdd hy, fun hy => ((monotone_cdf μ) hy).trans hqS⟩
  have hFq : cdf μ q = a := by
    refine le_antisymm hqS (not_lt.mp fun h => ?_)
    have hev : ∀ᶠ y in 𝓝[>] q, cdf μ y < a :=
      (hcont.continuousAt.eventually (gt_mem_nhds h)).filter_mono nhdsWithin_le_nhds
    obtain ⟨y, hy, hyq⟩ := (hev.and self_mem_nhdsWithin).exists
    exact absurd (le_csSup hbdd hy.le) (not_le.mpr hyq)
  rw [hSq, ← ofReal_cdf, hFq]

/-- **The probability integral transform**: the distribution function `F` of a law `μ` on `ℝ`
without atoms pushes `μ` forward to the Lebesgue measure on `[0, 1]`. -/
theorem map_cdfUnit_eq_volume (hμ : ∀ x, μ {x} = 0) : μ.map (cdfUnit μ) = volume := by
  haveI : IsProbabilityMeasure (μ.map (cdfUnit μ)) :=
    Measure.isProbabilityMeasure_map (measurable_cdfUnit μ).aemeasurable
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply (measurable_cdfUnit μ) measurableSet_Iic, volume_Iic]
  exact measure_setOf_cdf_le hμ a.2.1 a.2.2

variable {Ω : Type*} {m₀ mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → ℝ}

/-- **The probability integral transform of a random variable**: if the law `P ∘ X⁻¹` of a real
random variable `X` has no atoms, then `F(X)`, with `F` the distribution function of that law,
is uniform on `[0, 1]`. -/
theorem map_cdfUnit_comp_eq_volume (hX : AEMeasurable X P) (hat : ∀ x, P.map X {x} = 0) :
    P.map (fun ω => cdfUnit (P.map X) (X ω)) = volume := by
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  rw [← map_cdfUnit_eq_volume hat,
    AEMeasurable.map_map_of_aemeasurable (measurable_cdfUnit _).aemeasurable hX]
  rfl

end Dissertation.Law
