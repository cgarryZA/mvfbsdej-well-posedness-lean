/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import LevyStochCalc.Probability.Progressive
import MVFBSDEJ.WellPosedness.System.Tuple

/-!
# Measurability of the `L²(ν)` channel

For a mark-indexed vector `u(ω, ·) : E → ℝ^ι` depending measurably on a parameter `ω`, jointly
in `(ω, e)`, the class `uLift ν (u ω) ∈ L²(ν; ℝ^ι)` depends measurably on `ω` for the Borel
σ-algebra of `L²(ν; ℝ^ι)`, with no integrability assumption: `uLift` is `0` off `L²(ν)`, and the
set of parameters at which `u(ω, ·)` is square integrable is measurable.

The argument avoids a Pettis theorem. A map into a separable pseudometric space with its Borel
σ-algebra is measurable as soon as its distance to each point is measurable, since each open set
is the countable union of the balls with rational radius about the points of a countable dense
set that it contains. For `φ ∈ L²(ν; ℝ^ι)`, the distance

`‖uLift ν (u ω) − φ‖ = (∫_E |u(ω, e) − φ(e)|² ν(de))^{1/2}`

on the square-integrable parameters is measurable in `ω` by Tonelli's theorem; off them it is the
constant `‖φ‖`. For a σ-finite `ν` on a countably generated mark space `L²(ν; ℝ^ι)` is second
countable, so measurability is strong measurability.

For a process `U` whose coordinates are marked progressively measurable for a filtration `ℱ`,
`(ω, e) ↦ U_s(ω, e)` is `ℱ_s ⊗ 𝓔`-measurable for each time `s`, so the class of `U_s(ω, ·)` in
`L²(ν; ℝᵐ)` is strongly `ℱ_s`-measurable at every time.

## Main statements

* `measurable_of_forall_measurable_dist` — measurability into a separable pseudometric space
  from the measurability of the distances to points.
* `measurable_eLpNorm_two` — the `L²` seminorm of a jointly measurable family is measurable.
* `measurable_uLift`, `stronglyMeasurable_uLift` — the `L²(ν)` class of a jointly measurable
  family is measurable.
* `stronglyMeasurable_uLift_of_markedProgressive` — the `L²(ν)` class of a marked progressively
  measurable process at time `s` is strongly `ℱ_s`-measurable.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

/-- **Measurability from distances.** A map into a separable pseudometric space with its Borel
σ-algebra is measurable when its distance to each point is measurable. -/
theorem measurable_of_forall_measurable_dist {α F : Type*} {mα : MeasurableSpace α}
    [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F] [TopologicalSpace.SeparableSpace F]
    {f : α → F} (hf : ∀ y, Measurable fun a => dist (f a) y) : Measurable f := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense F
  refine measurable_of_isOpen fun s hs => ?_
  have hpre : f ⁻¹' s = ⋃ y ∈ D, ⋃ q : ℚ, ⋃ (_ : Metric.ball y q ⊆ s),
      {a | dist (f a) y < q} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro ha
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hs _ ha
      obtain ⟨y, hyD, hy⟩ := hDd.exists_dist_lt (f a) (half_pos hε)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hy
      refine ⟨y, hyD, q, fun z hz => hball ?_, hq1⟩
      rw [Metric.mem_ball] at hz ⊢
      calc dist z (f a) ≤ dist z y + dist y (f a) := dist_triangle _ _ _
        _ < q + ε / 2 := by rw [dist_comm y]; exact add_lt_add hz hy
        _ < ε := by linarith
    · rintro ⟨y, _, q, hsub, hq⟩
      exact hsub (by rw [Metric.mem_ball]; exact hq)
  rw [hpre]
  exact MeasurableSet.biUnion hDc fun y _ => MeasurableSet.iUnion fun q =>
    MeasurableSet.iUnion fun _ => measurableSet_lt (hf y) measurable_const

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {ι : Type*} [Fintype ι]
  {Ω : Type*} {mΩ : MeasurableSpace Ω}

omit [Fintype ι] in
/-- **The `L²` seminorm of a jointly measurable family is measurable**: for `w` measurable in
`(ω, e)`, `ω ↦ ‖w(ω, ·)‖_{L²(ν)}` is measurable, by Tonelli's theorem. -/
theorem measurable_eLpNorm_two [SFinite ν] {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [OpensMeasurableSpace F] {w : Ω → E → F}
    (hw : Measurable fun p : Ω × E => w p.1 p.2) :
    Measurable fun ω => eLpNorm (w ω) 2 ν := by
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  exact (hw.enorm.pow_const _).lintegral_prod_right'.pow_const _

/-- The distance from the `L²(ν)` class of a square-integrable vector to `φ ∈ L²(ν)` is the `L²`
seminorm of the difference of the vector and a representative of `φ`. -/
theorem edist_uLift_eq {u : E → ι → ℝ} (φ : Lp (EuclideanSpace ℝ ι) 2 ν)
    (h : MemLp (fun e => (WithLp.toLp 2 (u e) : EuclideanSpace ℝ ι)) 2 ν) :
    edist (uLift ν u) φ
      = eLpNorm (fun e => (WithLp.toLp 2 (u e) : EuclideanSpace ℝ ι) - φ e) 2 ν := by
  rw [uLift_of_memLp h, Lp.edist_def]
  exact eLpNorm_congr_ae (h.coeFn_toLp.sub (ae_eq_refl _))

/-- **The `L²(ν)` class of a jointly measurable family is measurable.** For a σ-finite `ν` on a
countably generated mark space and `u` measurable in `(ω, e)`, `ω ↦ uLift ν (u ω)` is measurable
for the Borel σ-algebra of `L²(ν; ℝ^ι)`. -/
theorem measurable_uLift [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    {u : Ω → E → ι → ℝ} (hu : Measurable fun p : Ω × E => u p.1 p.2) :
    Measurable fun ω => uLift ν (u ω) := by
  classical
  set v : Ω → E → EuclideanSpace ℝ ι := fun ω e => WithLp.toLp 2 (u ω e) with hv_def
  have hv : Measurable fun p : Ω × E => v p.1 p.2 := (WithLp.measurable_toLp 2 _).comp hu
  set S : Set Ω := {ω | eLpNorm (v ω) 2 ν < ⊤} with hS_def
  have hS : MeasurableSet S := measurableSet_lt (measurable_eLpNorm_two hv) measurable_const
  have hmem : ∀ ω, MemLp (v ω) 2 ν ↔ ω ∈ S := fun ω =>
    ⟨fun h => h.2, fun h =>
      ⟨(hv.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable, h⟩⟩
  refine measurable_of_forall_measurable_dist fun φ => ?_
  have hφ : Measurable fun e => (φ e : EuclideanSpace ℝ ι) := (Lp.stronglyMeasurable φ).measurable
  have hG : Measurable fun ω => eLpNorm (fun e => v ω e - φ e) 2 ν :=
    measurable_eLpNorm_two (hv.sub (hφ.comp measurable_snd))
  have heq : (fun ω => edist (uLift ν (u ω)) φ)
      = S.piecewise (fun ω => eLpNorm (fun e => v ω e - φ e) 2 ν)
        (fun _ => edist (0 : Lp (EuclideanSpace ℝ ι) 2 ν) φ) := by
    funext ω
    by_cases h : ω ∈ S
    · rw [Set.piecewise_eq_of_mem _ _ _ h]
      exact edist_uLift_eq φ ((hmem ω).2 h)
    · rw [Set.piecewise_eq_of_notMem _ _ _ h]
      unfold uLift
      rw [dif_neg fun h' => h ((hmem ω).1 h')]
  have hE : Measurable fun ω => edist (uLift ν (u ω)) φ := by
    rw [heq]
    exact hG.piecewise hS measurable_const
  simp_rw [dist_edist]
  exact hE.ennreal_toReal

/-- **The `L²(ν)` class of a jointly measurable family is strongly measurable**, for a σ-finite
`ν` on a countably generated mark space. -/
theorem stronglyMeasurable_uLift [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    {u : Ω → E → ι → ℝ} (hu : Measurable fun p : Ω × E => u p.1 p.2) :
    StronglyMeasurable fun ω => uLift ν (u ω) :=
  (measurable_uLift hu).stronglyMeasurable

/-- **The `L²(ν)` class of a marked progressively measurable process is adapted.** For a σ-finite
`ν` on a countably generated mark space and coordinates `U_k` marked progressively measurable
for `ℱ`, the class of `e ↦ (U_{k,s}(ω, e))_k` in `L²(ν; ℝᵐ)` is strongly `ℱ_s`-measurable in `ω`,
at every time `s`. -/
theorem stronglyMeasurable_uLift_of_markedProgressive [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] {ℱ : Filtration ℝ mΩ} {m : ℕ}
    {U : Fin m → ℝ → Ω → E → ℝ}
    (hU : ∀ k, LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U k s ω e)
    (s : ℝ) : StronglyMeasurable[ℱ s] fun ω => uLift ν fun e k => U k s ω e := by
  letI : MeasurableSpace Ω := ℱ s
  have hk : ∀ k, Measurable fun p : Ω × E => U k s p.1 p.2 := fun k => by
    have h := (hU k s).comp_measurable (measurable_fst.prodMk
      (measurable_const.prodMk measurable_snd) : Measurable fun p : Ω × E => (p.1, s, p.2))
    simp only [Function.comp_def, Set.indicator_of_mem (Set.mem_Iic.mpr le_rfl)] at h
    exact h.measurable
  exact stronglyMeasurable_uLift (u := fun ω e k => U k s ω e) (measurable_pi_iff.mpr hk)

end MVFBSDEJ.WellPosedness.System
