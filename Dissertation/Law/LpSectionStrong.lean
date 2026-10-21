/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Strong measurability of sections into `L²`

Let `ν` be a σ-finite measure on an arbitrary measurable space `E`, `F` a separable normed space
and `H : X × E → F` jointly strongly measurable with every section `H(x, ·)` in `L²(ν; F)`. Then
the section map `x ↦ H(x, ·) ∈ L²(ν; F)` is strongly measurable: it is Borel measurable and takes
values in a separable subspace, although `L²(ν; F)` itself need not be separable when `E` is not
countably generated. This is the conclusion that the Pettis measurability theorem draws from weak
measurability.

The proof cuts `E` down to a set `S` of finite measure. For a measurable `A ⊆ X × E` and `c ∈ F`,
`x ↦ 1_{A_x ∩ S} c ∈ L²(ν; F)` is strongly measurable, by induction on `A` from the measurable
rectangles: complements give differences, countable disjoint unions limits of finite sums. By
additivity the section map of a simple function cut down to `S` is strongly measurable, and the
section map of `H` cut down to `S` is the pointwise limit of those of the simple approximations
of `H`. Exhausting `E` by sets of finite measure gives the section map of `H` as a pointwise limit.

## Main statements

* `Dissertation.Law.stronglyMeasurable_indicatorConstLp_section` — sections of a measurable set
  cut down to a set of finite measure.
* `Dissertation.Law.stronglyMeasurable_toLp_indicator_section` — sections of a jointly strongly
  measurable function cut down to a set of finite measure.
* `Dissertation.Law.stronglyMeasurable_lp_of_section` — the section map is strongly measurable.
* `Dissertation.Law.exists_isClosed_isSeparable_submodule_of_stronglyMeasurable`,
  `Dissertation.Law.measurable_borel_of_stronglyMeasurable` — a strongly measurable map takes
  values in a closed separable subspace and is Borel.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Dissertation.Law

variable {X E F : Type*} [MeasurableSpace X] [MeasurableSpace E] {ν : Measure E}
  [NormedAddCommGroup F]

/-! ### Sections of measurable sets -/

section Sets

/-- Two indicators in `L²` of equal sets agree. -/
theorem indicatorConstLp_congr_set {s t : Set E} {hs : MeasurableSet s} {ht : MeasurableSet t}
    {hνs : ν s ≠ ∞} {hνt : ν t ≠ ∞} (h : s = t) (c : F) :
    indicatorConstLp 2 hs hνs c = indicatorConstLp 2 ht hνt c := by
  subst h
  rfl

variable {S : Set E} (hS : MeasurableSet S) (hνS : ν S ≠ ∞)
include hS hνS

/-- **Sections of a measurable set, cut down to a set of finite measure.** For a measurable
`A ⊆ X × E` and `c ∈ F`, the map `x ↦ 1_{A_x ∩ S} c ∈ L²(ν; F)` is strongly measurable. -/
theorem stronglyMeasurable_indicatorConstLp_section {A : Set (X × E)} (hA : MeasurableSet A)
    (c : F) :
    StronglyMeasurable fun x : X => indicatorConstLp 2
      ((measurable_prodMk_left (x := x) hA).inter hS)
      (ne_top_of_le_ne_top hνS (measure_mono inter_subset_right)) c := by
  refine MeasurableSpace.induction_on_inter (C := fun A hA => StronglyMeasurable fun x : X =>
      indicatorConstLp 2 ((measurable_prodMk_left (x := x) hA).inter hS)
        (ne_top_of_le_ne_top hνS (measure_mono inter_subset_right)) c)
    generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ A hA
  · convert stronglyMeasurable_const (b := (0 : Lp F 2 ν)) using 1
    funext x
    rw [indicatorConstLp_congr_set (ht := MeasurableSet.empty) (hνt := by simp)
      (by rw [preimage_empty, empty_inter]), indicatorConstLp_empty]
  · intro t ht
    obtain ⟨B, hB, C, hC, rfl⟩ := ht
    convert (stronglyMeasurable_const (b := indicatorConstLp 2 (hC.inter hS)
      (ne_top_of_le_ne_top hνS (measure_mono inter_subset_right)) c)).indicator hB using 1
    funext x
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      exact indicatorConstLp_congr_set (by rw [mk_preimage_prod_right hx]) c
    · rw [indicator_of_notMem hx, indicatorConstLp_congr_set (ht := MeasurableSet.empty)
        (hνt := by simp) (by rw [mk_preimage_prod_right_eq_empty hx, empty_inter]),
        indicatorConstLp_empty]
  · intro t htm ih
    beta_reduce at ih ⊢
    convert (stronglyMeasurable_const (b := indicatorConstLp 2 hS hνS c)).sub ih using 1
    funext x
    refine eq_sub_of_add_eq ?_
    rw [← indicatorConstLp_disjoint_union _ _ _ _ ?_ c]
    · refine indicatorConstLp_congr_set ?_ c
      ext e
      simp only [mem_union, mem_inter_iff, mem_preimage, mem_compl_iff]
      tauto
    · rw [Set.disjoint_left]
      intro e h1 h2
      exact h1.1 h2.1
  · intro f hdisj hfm ih
    beta_reduce at ih ⊢
    have hpm : ∀ N, MeasurableSet (⋃ i, ⋃ (_ : i < N), f i) := fun N =>
      MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hfm i
    have hgm : ∀ N, StronglyMeasurable fun x : X => indicatorConstLp 2
        ((measurable_prodMk_left (x := x) (hpm N)).inter hS)
        (ne_top_of_le_ne_top hνS (measure_mono inter_subset_right)) c := by
      intro N
      induction N with
      | zero =>
        convert stronglyMeasurable_const (b := (0 : Lp F 2 ν)) using 1
        funext x
        rw [indicatorConstLp_congr_set (ht := MeasurableSet.empty) (hνt := by simp)
          (by ext e; simp), indicatorConstLp_empty]
      | succ N ihN =>
        convert ihN.add (ih N) using 1
        funext x
        rw [Pi.add_apply, ← indicatorConstLp_disjoint_union _ _ _ _ ?_ c]
        · refine indicatorConstLp_congr_set ?_ c
          ext e
          simp only [mem_inter_iff, mem_preimage, mem_iUnion, exists_prop, mem_union]
          constructor
          · rintro ⟨⟨i, hi, he⟩, hS⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
            · exact Or.inl ⟨⟨i, hi, he⟩, hS⟩
            · exact Or.inr ⟨he, hS⟩
          · rintro (⟨⟨i, hi, he⟩, hS⟩ | ⟨he, hS⟩)
            · exact ⟨⟨i, by omega, he⟩, hS⟩
            · exact ⟨⟨N, by omega, he⟩, hS⟩
        · rw [Set.disjoint_left]
          rintro e ⟨he, -⟩ ⟨he', -⟩
          simp only [mem_preimage, mem_iUnion, exists_prop] at he
          obtain ⟨i, hi, hei⟩ := he
          exact Set.disjoint_left.mp (hdisj (Nat.ne_of_lt hi)) hei he'
    refine stronglyMeasurable_of_tendsto atTop hgm (tendsto_pi_nhds.mpr fun x => ?_)
    haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
    refine tendsto_indicatorConstLp_set ENNReal.ofNat_ne_top ?_
    have hmono : Monotone fun N => Prod.mk x ⁻¹' (⋃ i, ⋃ (_ : i < N), f i) ∩ S := by
      intro N M hNM
      refine inter_subset_inter_left _ (preimage_mono (iUnion_mono fun i => ?_))
      exact iUnion_subset fun hi => subset_iUnion_of_subset (lt_of_lt_of_le hi hNM) subset_rfl
    have hsub : ∀ N, Prod.mk x ⁻¹' (⋃ i, ⋃ (_ : i < N), f i) ∩ S
        ⊆ Prod.mk x ⁻¹' (⋃ i, f i) ∩ S := fun N =>
      inter_subset_inter_left _ (preimage_mono (iUnion_mono fun i => iUnion_subset fun _ =>
        subset_rfl))
    simp_rw [symmDiff_of_le (hsub _)]
    have hlim := tendsto_measure_iInter_atTop (μ := ν)
      (s := fun N => (Prod.mk x ⁻¹' (⋃ i, f i) ∩ S)
        \ (Prod.mk x ⁻¹' (⋃ i, ⋃ (_ : i < N), f i) ∩ S))
      (fun N => (((measurable_prodMk_left (x := x) (MeasurableSet.iUnion hfm)).inter hS).diff
        ((measurable_prodMk_left (x := x) (hpm N)).inter hS)).nullMeasurableSet)
      (fun N M hNM => sdiff_le_sdiff_left (hmono hNM))
      ⟨0, ne_top_of_le_ne_top hνS (measure_mono (sdiff_subset.trans inter_subset_right))⟩
    have hempty : (⋂ N, (Prod.mk x ⁻¹' (⋃ i, f i) ∩ S)
        \ (Prod.mk x ⁻¹' (⋃ i, ⋃ (_ : i < N), f i) ∩ S)) = ∅ := by
      refine eq_empty_of_forall_notMem fun e he => ?_
      rw [mem_iInter] at he
      obtain ⟨⟨heU, heS⟩, -⟩ := he 0
      rw [mem_preimage, mem_iUnion] at heU
      obtain ⟨i, hi⟩ := heU
      refine (he (i + 1)).2 ⟨?_, heS⟩
      rw [mem_preimage, mem_iUnion]
      exact ⟨i, mem_iUnion.mpr ⟨Nat.lt_succ_self i, hi⟩⟩
    rw [hempty, measure_empty] at hlim
    exact hlim

end Sets

/-! ### Sections of simple functions and of strongly measurable functions -/

section Functions

variable {S : Set E} (hS : MeasurableSet S) (hνS : ν S ≠ ∞)
include hS hνS

/-- A section of a simple function, cut down to a set of finite measure, is square
integrable. -/
theorem memLp_indicator_section_simpleFunc (s : SimpleFunc (X × E) F) (x : X) :
    MemLp (S.indicator fun e => s (x, e)) 2 ν := by
  haveI : IsFiniteMeasure (ν.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hνS.lt_top⟩
  rw [memLp_indicator_iff_restrict hS]
  exact (s.comp (Prod.mk x) measurable_prodMk_left).memLp_of_isFiniteMeasure 2 (ν.restrict S)

/-- **Sections of a simple function, cut down to a set of finite measure, depend strongly
measurably on the point.** -/
theorem stronglyMeasurable_toLp_indicator_section_simpleFunc (s : SimpleFunc (X × E) F) :
    StronglyMeasurable fun x => (memLp_indicator_section_simpleFunc hS hνS s x).toLp _ := by
  induction s using SimpleFunc.induction with
  | @const c A hA =>
    convert stronglyMeasurable_indicatorConstLp_section hS hνS hA c using 1
    funext x
    rw [indicatorConstLp]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun e => ?_)
    simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const, indicator, mem_inter_iff,
      mem_preimage, Set.piecewise, Function.const_apply]
    by_cases he : e ∈ S <;> by_cases hA' : (x, e) ∈ A <;> simp [he, hA']
  | @add f g hdisj hf hg =>
    convert hf.add hg using 1
    funext x
    rw [Pi.add_apply, ← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun e => ?_)
    simp only [SimpleFunc.coe_add, Pi.add_apply, indicator_add]

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- **Sections of a jointly strongly measurable function, cut down to a set of finite measure,
depend strongly measurably on the point.** -/
theorem stronglyMeasurable_toLp_indicator_section {H : X × E → F} (hH : StronglyMeasurable H)
    (hmem : ∀ x, MemLp (fun e => H (x, e)) 2 ν) :
    StronglyMeasurable fun x => ((hmem x).indicator hS).toLp _ := by
  refine stronglyMeasurable_of_tendsto atTop
    (fun n => stronglyMeasurable_toLp_indicator_section_simpleFunc hS hνS
      (SimpleFunc.approxOn H hH.measurable univ 0 (mem_univ 0) n))
    (tendsto_pi_nhds.mpr fun x => ?_)
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hcomp : ∀ n e, SimpleFunc.approxOn H hH.measurable univ 0 (mem_univ 0) n (x, e)
      = SimpleFunc.approxOn (fun e => H (x, e)) (hH.measurable.comp measurable_prodMk_left)
          univ 0 (mem_univ 0) n e := fun n e => by
    have h := SimpleFunc.approxOn_comp (s := univ) hH.measurable
      (measurable_prodMk_left : Measurable (Prod.mk x : E → X × E)) (mem_univ (0 : F)) n
    exact (congrArg (fun φ : SimpleFunc E F => φ e) h).symm
  have heq : ∀ n, eLpNorm (⇑((memLp_indicator_section_simpleFunc hS hνS
      (SimpleFunc.approxOn H hH.measurable univ 0 (mem_univ 0) n) x).toLp _)
      - ⇑(((hmem x).indicator hS).toLp _)) 2 ν
      = eLpNorm (⇑(SimpleFunc.approxOn (fun e => H (x, e))
          (hH.measurable.comp measurable_prodMk_left) univ 0 (mem_univ 0) n)
          - fun e => H (x, e)) 2 (ν.restrict S) := by
    intro n
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hS]
    refine eLpNorm_congr_ae ?_
    have h1 := MemLp.coeFn_toLp (memLp_indicator_section_simpleFunc hS hνS
      (SimpleFunc.approxOn H hH.measurable univ 0 (mem_univ 0) n) x)
    have hm2 : MemLp (S.indicator fun e => H (x, e)) 2 ν := (hmem x).indicator hS
    have h2 : ⇑(hm2.toLp _) =ᵐ[ν] S.indicator fun e => H (x, e) := MemLp.coeFn_toLp hm2
    refine (h1.sub h2).trans (Eventually.of_forall fun e => ?_)
    by_cases he : e ∈ S
    · simp only [Pi.sub_apply, indicator_of_mem he, hcomp n]
    · simp only [Pi.sub_apply, indicator_of_notMem he, sub_zero]
  simp_rw [heq]
  refine SimpleFunc.tendsto_approxOn_Lp_eLpNorm (hH.measurable.comp measurable_prodMk_left)
    (mem_univ 0) ENNReal.ofNat_ne_top (by simp) ?_
  simp only [sub_zero]
  exact ((hmem x).restrict S).eLpNorm_lt_top

end Functions

/-! ### Exhaustion -/

section Exhaustion

variable [SigmaFinite ν]

/-- Cutting a square-integrable function down to the spanning sets of `ν` approximates it in
`L²(ν; F)`. -/
theorem tendsto_toLp_indicator_spanningSets {f : E → F} (hfm : StronglyMeasurable f)
    (hf : MemLp f 2 ν) :
    Tendsto (fun k => (hf.indicator (measurableSet_spanningSets ν k)).toLp _) atTop
      (𝓝 (hf.toLp f)) := by
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have heq : ∀ k, eLpNorm (⇑((hf.indicator (measurableSet_spanningSets ν k)).toLp _)
      - ⇑(hf.toLp f)) 2 ν = eLpNorm ((spanningSets ν k).indicator f - f) 2 ν := fun k =>
    eLpNorm_congr_ae ((MemLp.coeFn_toLp _).sub (MemLp.coeFn_toLp _))
  simp_rw [heq, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat]
  have hbound : ∫⁻ e, ‖f e‖ₑ ^ (2 : ℝ) ∂ν ≠ ∞ := by
    have h := hf.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat] at h
    exact ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp h).ne
  have hlim : Tendsto (fun k => ∫⁻ e, ‖((spanningSets ν k).indicator f - f) e‖ₑ ^ (2 : ℝ) ∂ν)
      atTop (𝓝 0) := by
    have h0 := tendsto_lintegral_of_dominated_convergence (μ := ν)
      (F := fun k e => ‖((spanningSets ν k).indicator f - f) e‖ₑ ^ (2 : ℝ))
      (f := fun _ => 0) (fun e => ‖f e‖ₑ ^ (2 : ℝ))
      (fun k => (((hfm.indicator (measurableSet_spanningSets ν k)).sub
        hfm).enorm.pow_const _))
      (fun k => Eventually.of_forall fun e => by
        by_cases he : e ∈ spanningSets ν k
        · simp [he]
        · simp [he])
      hbound
      (Eventually.of_forall fun e => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop (spanningSetsIndex ν e)] with k hk
        have he : e ∈ spanningSets ν k :=
          monotone_spanningSets ν hk (mem_spanningSetsIndex ν e)
        simp [he])
    simpa using h0
  have h := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  exact h.comp hlim

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- **The section map into `L²` is strongly measurable.** For `ν` σ-finite on any measurable
space and `H : X × E → F` jointly strongly measurable, a map `h : X → L²(ν; F)` with
`h(x) = H(x, ·)` `ν`-almost everywhere for every `x` is strongly measurable: Borel measurable,
with values in a separable subspace of `L²(ν; F)`. -/
theorem stronglyMeasurable_lp_of_section {H : X × E → F} (hH : StronglyMeasurable H)
    {h : X → Lp F 2 ν} (hh : ∀ x, (h x : E → F) =ᵐ[ν] fun e => H (x, e)) :
    StronglyMeasurable h := by
  have hmem : ∀ x, MemLp (fun e => H (x, e)) 2 ν := fun x =>
    (Lp.memLp (h x)).ae_eq (hh x)
  have hrep : ∀ x, h x = (hmem x).toLp _ := fun x => by
    rw [← Lp.toLp_coeFn (h x) (Lp.memLp (h x))]
    exact MemLp.toLp_congr _ _ (hh x)
  refine stronglyMeasurable_of_tendsto atTop (fun k => stronglyMeasurable_toLp_indicator_section
    (measurableSet_spanningSets ν k) (measure_spanningSets_lt_top ν k).ne hH hmem)
    (tendsto_pi_nhds.mpr fun x => ?_)
  rw [hrep x]
  exact tendsto_toLp_indicator_spanningSets (hH.comp_measurable measurable_prodMk_left) (hmem x)

end Exhaustion

/-! ### Separable range -/

section Range

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A strongly measurable map into a normed space takes values in a closed separable subspace:
the closure of the span of its range. -/
theorem exists_isClosed_isSeparable_submodule_of_stronglyMeasurable {f : X → G}
    (hf : StronglyMeasurable f) :
    ∃ V : Submodule ℝ G, IsClosed (V : Set G) ∧ TopologicalSpace.IsSeparable (V : Set G)
      ∧ ∀ x, f x ∈ V := by
  refine ⟨(Submodule.span ℝ (Set.range f)).topologicalClosure,
    Submodule.isClosed_topologicalClosure _, ?_, fun x => ?_⟩
  · rw [Submodule.topologicalClosure_coe]
    exact hf.isSeparable_range.span.closure
  · exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x, rfl⟩)

/-- A strongly measurable map into a normed space is measurable for the Borel σ-algebra. -/
theorem measurable_borel_of_stronglyMeasurable {f : X → G} (hf : StronglyMeasurable f) :
    @Measurable X G _ (borel G) f := by
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  exact hf.measurable

end Range

end Dissertation.Law
