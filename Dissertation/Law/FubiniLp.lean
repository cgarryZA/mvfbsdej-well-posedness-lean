/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.LpSection
import Dissertation.Law.LpSectionStrong

/-!
# The Fubini isometry `L²(μ ⊗ ν; F) ≃ L²(μ; L²(ν; F))`

For σ-finite measures `μ` on `X` and `ν` on `E`, and a separable Banach space `F`, taking a
function on `X × E` to the family of its sections is a linear isometric equivalence
`L²(μ ⊗ ν; F) ≃ L²(μ; L²(ν; F))`, the identification (2.4) of the well-posedness paper. Each
element of `L²(μ; L²(ν; F))` therefore has a jointly measurable representative, and two jointly
measurable representatives of the same sections agree `μ ⊗ ν`-almost everywhere.

The section of a representative `g` is square integrable at almost every point by Tonelli; cutting
`g` to the points where it is (`cutSec`) gives sections in `L²(ν; F)` at every point, strongly
measurable in the point (`stronglyMeasurable_lp_of_section`), and Tonelli gives the isometry. The
range is closed and contains every indicator of a set of finite measure times an element of
`L²(ν; F)`, so it is everything (`Lp.induction`).

## Main definitions

* `Dissertation.Law.secLp` — the section map of a function on the product into `L²(ν; F)`.
* `Dissertation.Law.fubiniLp`, `fubiniLI`, `fubiniEquiv` — the section map on `L²(μ ⊗ ν; F)`, as a
  map, a linear isometry and a linear isometric equivalence.

## Main statements

* `Dissertation.Law.ae_coeFn_fubiniEquiv` — the sections of `fubiniEquiv f` represent `f`.
* `Dissertation.Law.ae_eq_of_ae_sections` — jointly measurable representatives of the same
  sections agree almost everywhere.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace Dissertation.Law

section Two

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}

/-- The square of the `L²` seminorm is the integral of the squared norm. -/
theorem eLpNorm_two_rpow (f : α → F) :
    eLpNorm f 2 μ ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := (2 : ℝ≥0)) two_ne_zero
  simpa using h

/-- A function with finite integral of the squared norm is square integrable. -/
theorem memLp_two_of_lintegral_lt_top {f : α → F} (hf : AEStronglyMeasurable f μ)
    (hfin : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ⊤) : MemLp f 2 μ := by
  refine ⟨hf, ?_⟩
  have h := eLpNorm_two_rpow (μ := μ) f
  rw [← h] at hfin
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp hfin

end Two

variable {X E F : Type*} [MeasurableSpace X] [MeasurableSpace E] {μ : Measure X} {ν : Measure E}
  [SigmaFinite μ] [SigmaFinite ν]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

/-- The points at which a function on a product has a square-integrable section. -/
def goodSet (ν : Measure E) (g : X × E → F) : Set X :=
  {x | ∫⁻ e, ‖g (x, e)‖ₑ ^ (2 : ℝ) ∂ν < ⊤}

omit [NormedSpace ℝ F] [CompleteSpace F]
    [SecondCountableTopology F] in
/-- The points with a square-integrable section form a measurable set. -/
theorem measurableSet_goodSet {g : X × E → F} (hg : StronglyMeasurable g) :
    MeasurableSet (goodSet ν g) :=
  measurableSet_lt (Measurable.lintegral_prod_right' (hg.measurable.enorm.pow_const _))
    measurable_const

/-- A function on a product cut down to its square-integrable sections. -/
noncomputable def cutSec (ν : Measure E) (g : X × E → F) : X × E → F :=
  (goodSet ν g ×ˢ Set.univ).indicator g

omit [NormedSpace ℝ F] [CompleteSpace F]
    [SecondCountableTopology F] in
/-- The cut function is strongly measurable. -/
theorem stronglyMeasurable_cutSec {g : X × E → F} (hg : StronglyMeasurable g) :
    StronglyMeasurable (cutSec ν g) :=
  hg.indicator ((measurableSet_goodSet hg).prod MeasurableSet.univ)

omit [MeasurableSpace X] [SigmaFinite ν]
    [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] in
/-- At a point with a square-integrable section the cut function is the function. -/
theorem cutSec_apply_of_mem {g : X × E → F} {x : X} (hx : x ∈ goodSet ν g) (e : E) :
    cutSec ν g (x, e) = g (x, e) :=
  Set.indicator_of_mem (Set.mk_mem_prod hx (Set.mem_univ e)) g

omit [MeasurableSpace X] [SigmaFinite ν]
    [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] in
/-- At a point without a square-integrable section the cut function vanishes. -/
theorem cutSec_apply_of_notMem {g : X × E → F} {x : X} (hx : x ∉ goodSet ν g) (e : E) :
    cutSec ν g (x, e) = 0 :=
  Set.indicator_of_notMem (fun h => hx h.1) g

omit [NormedSpace ℝ F] [CompleteSpace F]
    [SecondCountableTopology F] in
/-- Every section of the cut function is square integrable. -/
theorem memLp_cutSec {g : X × E → F} (hg : StronglyMeasurable g) (x : X) :
    MemLp (fun e => cutSec ν g (x, e)) 2 ν := by
  refine memLp_two_of_lintegral_lt_top (μ := ν)
    ((stronglyMeasurable_cutSec hg).comp_measurable measurable_prodMk_left).aestronglyMeasurable
    ?_
  by_cases hx : x ∈ goodSet ν g
  · simp only [cutSec_apply_of_mem hx]
    exact hx
  · simp [cutSec_apply_of_notMem hx]

/-- The sections of a function on a product, as elements of `L²(ν; F)`. -/
noncomputable def secLp (ν : Measure E) [SigmaFinite ν] {g : X × E → F}
    (hg : StronglyMeasurable g) (x : X) : Lp F 2 ν :=
  (memLp_cutSec (ν := ν) hg x).toLp _

omit [NormedSpace ℝ F] [CompleteSpace F]
    [SecondCountableTopology F] in
/-- The section in `L²(ν; F)` is represented by the section of the cut function. -/
theorem coeFn_secLp {g : X × E → F} (hg : StronglyMeasurable g) (x : X) :
    (secLp ν hg x : E → F) =ᵐ[ν] fun e => cutSec ν g (x, e) :=
  (memLp_cutSec hg x).coeFn_toLp

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- The section map is strongly measurable into `L²(ν; F)`. -/
theorem stronglyMeasurable_secLp {g : X × E → F} (hg : StronglyMeasurable g) :
    StronglyMeasurable (secLp ν hg) :=
  stronglyMeasurable_lp_of_section (stronglyMeasurable_cutSec hg) (coeFn_secLp hg)

omit [NormedSpace ℝ F] [CompleteSpace F]
    [SecondCountableTopology F] in
/-- The squared norm of a section is the integral of the squared norm of the cut function. -/
theorem enorm_secLp_rpow {g : X × E → F} (hg : StronglyMeasurable g) (x : X) :
    ‖secLp ν hg x‖ₑ ^ (2 : ℝ) = ∫⁻ e, ‖cutSec ν g (x, e)‖ₑ ^ (2 : ℝ) ∂ν := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (coeFn_secLp hg x), eLpNorm_two_rpow]

omit [SigmaFinite μ] [NormedSpace ℝ F] [CompleteSpace F]
    [SecondCountableTopology F] in
/-- A function with finite integral of the squared norm on the product has square-integrable
sections at almost every point. -/
theorem ae_mem_goodSet {g : X × E → F} (hg : StronglyMeasurable g)
    (hfin : ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(μ.prod ν) < ⊤) : ∀ᵐ x ∂μ, x ∈ goodSet ν g := by
  rw [lintegral_prod _ (hg.measurable.enorm.pow_const _).aemeasurable] at hfin
  exact ae_lt_top (Measurable.lintegral_prod_right' (hg.measurable.enorm.pow_const _)) hfin.ne

omit [SigmaFinite μ] in
omit [NormedSpace ℝ F] [CompleteSpace F]
    [SecondCountableTopology F] in
/-- **Tonelli for the sections**: the integral of the squared norms of the sections is the
integral of the squared norm on the product. -/
theorem lintegral_enorm_secLp_rpow {g : X × E → F} (hg : StronglyMeasurable g)
    (hfin : ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(μ.prod ν) < ⊤) :
    ∫⁻ x, ‖secLp ν hg x‖ₑ ^ (2 : ℝ) ∂μ = ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(μ.prod ν) := by
  rw [lintegral_prod _ (hg.measurable.enorm.pow_const _).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_goodSet hg hfin] with x hx
  rw [enorm_secLp_rpow]
  simp only [cutSec_apply_of_mem hx]

omit [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] in
/-- An element of `L²` has finite integral of the squared norm. -/
theorem lintegral_lp_rpow_lt_top {Y : Type*} [MeasurableSpace Y] {ρ : Measure Y}
    (f : Lp F 2 ρ) : ∫⁻ p, ‖f p‖ₑ ^ (2 : ℝ) ∂ρ < ⊤ := by
  rw [← eLpNorm_two_rpow]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (Lp.eLpNorm_ne_top f)

omit [SigmaFinite μ] in
omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- The sections of an element of `L²(μ ⊗ ν; F)` form an element of `L²(μ; L²(ν; F))`. -/
theorem memLp_secLp_lp (f : Lp F 2 (μ.prod ν)) :
    MemLp (secLp ν (Lp.stronglyMeasurable f)) 2 μ := by
  refine memLp_two_of_lintegral_lt_top (stronglyMeasurable_secLp _).aestronglyMeasurable ?_
  rw [lintegral_enorm_secLp_rpow _ (lintegral_lp_rpow_lt_top f)]
  exact lintegral_lp_rpow_lt_top f

/-- The map `L²(μ ⊗ ν; F) → L²(μ; L²(ν; F))` taking a function to its sections. -/
noncomputable def fubiniLp (f : Lp F 2 (μ.prod ν)) : Lp (Lp F 2 ν) 2 μ :=
  (memLp_secLp_lp f).toLp _

omit [SigmaFinite μ] in
omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- `fubiniLp f` is represented by the section map. -/
theorem coeFn_fubiniLp (f : Lp F 2 (μ.prod ν)) :
    (fubiniLp f : X → Lp F 2 ν) =ᵐ[μ] secLp ν (Lp.stronglyMeasurable f) :=
  (memLp_secLp_lp f).coeFn_toLp

omit [SigmaFinite μ] in
omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- The sections of `fubiniLp f` represent `f`. -/
theorem ae_coeFn_fubiniLp (f : Lp F 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, (fubiniLp f x : E → F) =ᵐ[ν] fun e => f (x, e) := by
  filter_upwards [coeFn_fubiniLp f, ae_mem_goodSet (Lp.stronglyMeasurable f)
    (lintegral_lp_rpow_lt_top f)] with x h1 h2
  rw [h1]
  filter_upwards [coeFn_secLp (Lp.stronglyMeasurable f) x] with e he
  rw [he, cutSec_apply_of_mem h2]

omit [SigmaFinite μ] in
omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- The section map preserves the `L²` norm. -/
theorem norm_fubiniLp (f : Lp F 2 (μ.prod ν)) : ‖fubiniLp f‖ = ‖f‖ := by
  have h : eLpNorm (fubiniLp f) 2 μ = eLpNorm f 2 (μ.prod ν) := by
    refine (ENNReal.rpow_left_injective (x := (2 : ℝ)) two_ne_zero) ?_
    simp only
    rw [eLpNorm_two_rpow, eLpNorm_two_rpow, lintegral_congr_ae (by
      filter_upwards [coeFn_fubiniLp f] with x hx; rw [hx]),
      lintegral_enorm_secLp_rpow _ (lintegral_lp_rpow_lt_top f)]
  rw [Lp.norm_def, Lp.norm_def, h]

omit [SigmaFinite μ] in
omit [NormedSpace ℝ F] [CompleteSpace F]
    [SecondCountableTopology F] in
/-- Two functions on the product with almost everywhere equal sections have almost everywhere
equal section maps. -/
theorem ae_secLp_eq {f₁ f₂ : X × E → F} (hf₁ : StronglyMeasurable f₁)
    (hf₂ : StronglyMeasurable f₂) (hfin₁ : ∫⁻ p, ‖f₁ p‖ₑ ^ (2 : ℝ) ∂(μ.prod ν) < ⊤)
    (G : X → Lp F 2 ν)
    (hG : ∀ᵐ x ∂μ, x ∈ goodSet ν f₂ → (G x : E → F) =ᵐ[ν] fun e => f₂ (x, e))
    (hfin₂ : ∫⁻ p, ‖f₂ p‖ₑ ^ (2 : ℝ) ∂(μ.prod ν) < ⊤)
    (h : ∀ᵐ x ∂μ, (fun e => f₁ (x, e)) =ᵐ[ν] fun e => f₂ (x, e)) :
    ∀ᵐ x ∂μ, secLp ν hf₁ x = G x := by
  filter_upwards [ae_mem_goodSet hf₁ hfin₁, ae_mem_goodSet hf₂ hfin₂, hG, h] with x h1 h2 h3 h4
  refine Lp.ext ?_
  filter_upwards [coeFn_secLp hf₁ x, h3 h2, h4] with e e1 e2 e3
  rw [e1, cutSec_apply_of_mem h1, e2]
  exact e3

omit [SigmaFinite μ] in
omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- The section map is additive. -/
theorem fubiniLp_add (f f' : Lp F 2 (μ.prod ν)) :
    fubiniLp (f + f') = fubiniLp f + fubiniLp f' := by
  refine Lp.ext ?_
  have hsum := Lp.coeFn_add f f'
  have hsec : ∀ᵐ x ∂μ, (fun e => (f + f') (x, e)) =ᵐ[ν] fun e => (⇑f + ⇑f') (x, e) :=
    Measure.ae_ae_of_ae_prod hsum
  have hG : ∀ᵐ x ∂μ, x ∈ goodSet ν (⇑f + ⇑f') →
      ((secLp ν (Lp.stronglyMeasurable f) x + secLp ν (Lp.stronglyMeasurable f') x : Lp F 2 ν)
        : E → F) =ᵐ[ν] fun e => (⇑f + ⇑f') (x, e) := by
    filter_upwards [ae_mem_goodSet (Lp.stronglyMeasurable f) (lintegral_lp_rpow_lt_top f),
      ae_mem_goodSet (Lp.stronglyMeasurable f') (lintegral_lp_rpow_lt_top f')] with x h1 h2 _
    filter_upwards [Lp.coeFn_add (secLp ν (Lp.stronglyMeasurable f) x)
      (secLp ν (Lp.stronglyMeasurable f') x), coeFn_secLp (Lp.stronglyMeasurable f) x,
      coeFn_secLp (Lp.stronglyMeasurable f') x] with e e1 e2 e3
    rw [e1, Pi.add_apply, e2, e3, cutSec_apply_of_mem h1, cutSec_apply_of_mem h2]
    rfl
  have hfin : ∫⁻ p, ‖(⇑f + ⇑f') p‖ₑ ^ (2 : ℝ) ∂(μ.prod ν) < ⊤ := by
    rw [lintegral_congr_ae (by filter_upwards [hsum] with p hp; rw [← hp])]
    exact lintegral_lp_rpow_lt_top (f + f')
  have key := ae_secLp_eq (Lp.stronglyMeasurable (f + f'))
    ((Lp.stronglyMeasurable f).add (Lp.stronglyMeasurable f')) (lintegral_lp_rpow_lt_top _) _
    hG hfin hsec
  filter_upwards [coeFn_fubiniLp (f + f'), coeFn_fubiniLp f, coeFn_fubiniLp f',
    Lp.coeFn_add (fubiniLp f) (fubiniLp f'), key] with x h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, h5]

omit [SigmaFinite μ] in
omit [CompleteSpace F] in
/-- The section map is homogeneous. -/
theorem fubiniLp_smul (c : ℝ) (f : Lp F 2 (μ.prod ν)) : fubiniLp (c • f) = c • fubiniLp f := by
  refine Lp.ext ?_
  have hsm := Lp.coeFn_smul c f
  have hsec : ∀ᵐ x ∂μ, (fun e => (c • f) (x, e)) =ᵐ[ν] fun e => (c • ⇑f) (x, e) :=
    Measure.ae_ae_of_ae_prod hsm
  have hG : ∀ᵐ x ∂μ, x ∈ goodSet ν (c • ⇑f) →
      ((c • secLp ν (Lp.stronglyMeasurable f) x : Lp F 2 ν) : E → F)
        =ᵐ[ν] fun e => (c • ⇑f) (x, e) := by
    filter_upwards [ae_mem_goodSet (Lp.stronglyMeasurable f) (lintegral_lp_rpow_lt_top f)]
      with x h1 _
    filter_upwards [Lp.coeFn_smul c (secLp ν (Lp.stronglyMeasurable f) x),
      coeFn_secLp (Lp.stronglyMeasurable f) x] with e e1 e2
    rw [e1, Pi.smul_apply, e2, cutSec_apply_of_mem h1]
    rfl
  have hfin : ∫⁻ p, ‖(c • ⇑f) p‖ₑ ^ (2 : ℝ) ∂(μ.prod ν) < ⊤ := by
    rw [lintegral_congr_ae (by filter_upwards [hsm] with p hp; rw [← hp])]
    exact lintegral_lp_rpow_lt_top (c • f)
  have key := ae_secLp_eq (Lp.stronglyMeasurable (c • f))
    ((Lp.stronglyMeasurable f).const_smul c) (lintegral_lp_rpow_lt_top _) _ hG hfin hsec
  filter_upwards [coeFn_fubiniLp (c • f), coeFn_fubiniLp f,
    Lp.coeFn_smul c (fubiniLp f), key] with x h1 h2 h3 h4
  rw [h1, h3, Pi.smul_apply, h2, h4]

/-- The section map `L²(μ ⊗ ν; F) → L²(μ; L²(ν; F))` as a linear isometry. -/
noncomputable def fubiniLI : Lp F 2 (μ.prod ν) →ₗᵢ[ℝ] Lp (Lp F 2 ν) 2 μ where
  toFun := fubiniLp
  map_add' := fubiniLp_add
  map_smul' := fubiniLp_smul
  norm_map' := norm_fubiniLp

omit [SigmaFinite μ] in
/-- **The section map is onto**: its range is closed and contains the indicators of sets of
finite measure times elements of `L²(ν; F)`. -/
theorem fubiniLp_surjective :
    Function.Surjective (fubiniLp : Lp F 2 (μ.prod ν) → Lp (Lp F 2 ν) 2 μ) := by
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  intro u
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top (fun u => ∃ f, fubiniLp f = u) ?_ ?_ ?_ u
  · intro c s hs hμs
    set g : X × E → F := (s ×ˢ Set.univ).indicator fun p => (c : E → F) p.2 with hgdef
    have hgm : StronglyMeasurable g :=
      ((Lp.stronglyMeasurable c).comp_measurable measurable_snd).indicator
        (hs.prod MeasurableSet.univ)
    have hsec : ∀ x, ∫⁻ e, ‖g (x, e)‖ₑ ^ (2 : ℝ) ∂ν
        = s.indicator (fun _ => ∫⁻ e, ‖c e‖ₑ ^ (2 : ℝ) ∂ν) x := by
      intro x
      by_cases hx : x ∈ s
      · simp [hgdef, Set.indicator, hx]
      · simp [hgdef, Set.indicator, hx]
    have hfin : ∫⁻ p, ‖g p‖ₑ ^ (2 : ℝ) ∂(μ.prod ν) < ⊤ := by
      rw [lintegral_prod _ (hgm.measurable.enorm.pow_const _).aemeasurable]
      simp_rw [hsec]
      rw [lintegral_indicator hs, setLIntegral_const]
      exact ENNReal.mul_lt_top (lintegral_lp_rpow_lt_top c) hμs
    have hg2 : MemLp g 2 (μ.prod ν) := memLp_two_of_lintegral_lt_top hgm.aestronglyMeasurable hfin
    refine ⟨hg2.toLp g, Lp.ext ?_⟩
    rw [Lp.simpleFunc.coe_indicatorConst]
    have hsecs : ∀ᵐ x ∂μ, (fun e => (hg2.toLp g) (x, e)) =ᵐ[ν] fun e => g (x, e) :=
      Measure.ae_ae_of_ae_prod hg2.coeFn_toLp
    filter_upwards [ae_coeFn_fubiniLp (hg2.toLp g), hsecs,
      indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := c)]
      with x h1 h2 h3
    rw [h3]
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      refine Lp.ext ?_
      filter_upwards [h1, h2] with e e1 e2
      rw [e1, e2, hgdef, Set.indicator_of_mem (Set.mk_mem_prod hx (Set.mem_univ e))]
    · rw [Set.indicator_of_notMem hx]
      refine Lp.ext ?_
      filter_upwards [h1, h2, Lp.coeFn_zero F 2 ν] with e e1 e2 e3
      rw [e1, e2, e3, hgdef, Set.indicator_of_notMem (fun h => hx h.1)]
      rfl
  · rintro f g hf hg - ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [fubiniLp_add, ha, hb]⟩
  · exact (fubiniLI (μ := μ) (ν := ν) (F := F)).isometry.isClosedEmbedding.isClosed_range

/-- **The Fubini isometry** `L²(μ ⊗ ν; F) ≃ L²(μ; L²(ν; F))`, taking a function to its
sections. -/
noncomputable def fubiniEquiv : Lp F 2 (μ.prod ν) ≃ₗᵢ[ℝ] Lp (Lp F 2 ν) 2 μ :=
  LinearIsometryEquiv.ofSurjective fubiniLI fubiniLp_surjective

omit [SigmaFinite μ] in
/-- The sections of `fubiniEquiv f` represent `f`. -/
theorem ae_coeFn_fubiniEquiv (f : Lp F 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, (fubiniEquiv f x : E → F) =ᵐ[ν] fun e => f (x, e) :=
  ae_coeFn_fubiniLp f

omit [SigmaFinite μ] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
/-- **Two jointly measurable representatives of the same sections agree almost everywhere.** -/
theorem ae_eq_of_ae_sections {u : X → Lp F 2 ν} {g g' : X × E → F} (hg : StronglyMeasurable g)
    (hg' : StronglyMeasurable g') (h : ∀ᵐ x ∂μ, (u x : E → F) =ᵐ[ν] fun e => g (x, e))
    (h' : ∀ᵐ x ∂μ, (u x : E → F) =ᵐ[ν] fun e => g' (x, e)) : g =ᵐ[μ.prod ν] g' := by
  rw [Filter.EventuallyEq, Measure.ae_prod_iff_ae_ae (hg.measurableSet_eq_fun hg')]
  filter_upwards [h, h'] with x hx hx'
  filter_upwards [hx, hx'] with e e1 e2
  rw [← e1, ← e2]

end Dissertation.Law
