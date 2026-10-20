/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.Compensator
import LevyStochCalc.Poisson.Simplicity
import LevyStochCalc.Poisson.Atomic
import LevyStochCalc.Ito.JumpCoefficientPredictableCriteria
import Mathlib.Probability.Process.Stopping

/-!
# Integrals against a Poisson random measure, as processes in time

For a Poisson random measure `N` carried by a filtration `ℱ` and a nonnegative marked predictable
function `g`, the integral `A_t = ∫_{(0, t] × E} g dN` and its left version
`A_{t−} = ∫_{(0, t) × E} g dN` are nondecreasing in `t`. On the event `G` of full measure on which
every bounded window of finite mark measure carries finite mass, `A_t` is `ℱ_t`-measurable: the
slices of marked predictable sets form a Dynkin system there. Cut to `G`, the left version is
adapted and left continuous, hence predictable, and the first time `A` reaches a level is a
stopping time of a right-continuous filtration. Almost surely no two points of `N` share a time.

## Main definitions

* `Dissertation.WellPosedness.Martingale.countGood` — the event `G`.
* `Dissertation.WellPosedness.Martingale.countInt` — `1_G ∫_{(0, t] × E} g dN`.
* `Dissertation.WellPosedness.Martingale.countIntLeft` — `1_G ∫_{(0, t) × E} g dN`.
* `Dissertation.WellPosedness.Martingale.levelHit` — the first time a nondecreasing process
  reaches a level.

## Main statements

* `Dissertation.WellPosedness.Martingale.measurable_countInt` — `A_t` is `ℱ_t`-measurable.
* `Dissertation.WellPosedness.Martingale.measurable_predictableSigma_countIntLeft` — the left
  version is predictable.
* `Dissertation.WellPosedness.Martingale.isStoppingTime_levelHit` — the first passage time is a
  stopping time.
* `Dissertation.WellPosedness.Martingale.ae_count_time_le_one` — almost surely every time
  carries at most one point.
-/

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal Topology

namespace Dissertation.WellPosedness.Martingale

open LevyStochCalc LevyStochCalc.Probability

universe u v w

section Predictable

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}

/-- An adapted `[0, ∞]`-valued process frozen at the dyadic grid point below the time is
predictable. -/
theorem measurable_predictableSigma_comp_leftGridPoint_ennreal {Z : ℝ → Ω → ℝ≥0∞}
    (hZ : ∀ t : ℝ, Measurable[ℱ t] (Z t)) (k : ℕ) :
    Measurable[predictableSigma ℱ] fun p : ℝ × Ω => Z (leftGridPoint k p.1) p.2 := by
  intro U hU
  have hpre : (fun p : ℝ × Ω => Z (leftGridPoint k p.1) p.2) ⁻¹' U
      = ⋃ j : ℤ, Ioc ((j : ℝ) / 2 ^ k) (((j : ℝ) + 1) / 2 ^ k) ×ˢ
          (Z ((j : ℝ) / 2 ^ k) ⁻¹' U) := by
    ext p
    simp only [mem_preimage, mem_iUnion, mem_prod]
    constructor
    · intro hs
      exact ⟨⌈p.1 * 2 ^ k⌉ - 1, (mem_Ioc_iff_ceil_sub_one_eq k p.1 _).mpr rfl, hs⟩
    · rintro ⟨j, hj, hzu⟩
      have hg : leftGridPoint k p.1 = (j : ℝ) / 2 ^ k := by
        rw [leftGridPoint, (mem_Ioc_iff_ceil_sub_one_eq k p.1 j).mp hj]
      rw [hg]
      exact hzu
  rw [hpre]
  refine MeasurableSet.iUnion fun j => ?_
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have hle : (j : ℝ) / 2 ^ k ≤ ((j : ℝ) + 1) / 2 ^ k := by
    rw [div_le_div_iff_of_pos_right hk]
    linarith
  exact measurableSet_predictableSigma_Ioc_prod hle (hZ _ hU)

/-- **An adapted, left-continuous `[0, ∞]`-valued process is predictable.** -/
theorem measurable_predictableSigma_of_leftContinuous_ennreal {Y : ℝ → Ω → ℝ≥0∞}
    (hY : ∀ t : ℝ, Measurable[ℱ t] (Y t))
    (hleft : ∀ (t : ℝ) (ω : Ω), Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 (Y t ω))) :
    Measurable[predictableSigma ℱ] fun p : ℝ × Ω => Y p.1 p.2 := by
  have hrw : (fun p : ℝ × Ω => Y p.1 p.2)
      = fun p : ℝ × Ω => limsup (fun k : ℕ => Y (leftGridPoint k p.1) p.2) atTop := by
    funext p
    exact (((hleft p.1 p.2).comp (tendsto_leftGridPoint p.1)).limsup_eq).symm
  rw [hrw]
  exact Measurable.limsup fun k => measurable_predictableSigma_comp_leftGridPoint_ennreal hY k

end Predictable

section Count

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν)

/-- The sample points at which every bounded window `(0, n] × E_k`, `E_k` the spanning sets of
`ν`, carries finite mass. -/
def countGood : Set Ω :=
  {ω | ∀ k n : ℕ, N.N ω (Ioc (0 : ℝ) n ×ˢ spanningSets ν k) ≠ ⊤}

theorem measurableSet_countGood : MeasurableSet (countGood N) := by
  have hset : countGood N = ⋂ k : ℕ, ⋂ n : ℕ,
      (fun ω => N.N ω (Ioc (0 : ℝ) n ×ˢ spanningSets ν k)) ⁻¹' {⊤}ᶜ := by
    ext ω
    simp [countGood]
  rw [hset]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun n =>
    (N.measurable_eval (measurableSet_Ioc.prod (measurableSet_spanningSets ν k)))
      (measurableSet_singleton ⊤).compl

theorem ae_mem_countGood : ∀ᵐ ω ∂P, ω ∈ countGood N := by
  have h : ∀ᵐ ω ∂P, ∀ k n : ℕ, N.N ω (Ioc (0 : ℝ) n ×ˢ spanningSets ν k) ≠ ⊤ :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun n =>
      Poisson.count_Ioc_ne_top N (measurableSet_spanningSets ν k)
        (measure_spanningSets_lt_top ν k).ne n
  filter_upwards [h] with ω hω
  exact hω

/-- The good event lies in every `ℱ_t`, `t ≥ 0`, when the null sets lie in `ℱ_0`. -/
theorem measurableSet_countGood_filtration {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) {t : ℝ}
    (ht : 0 ≤ t) : MeasurableSet[ℱ t] (countGood N) := by
  have hc : MeasurableSet[ℱ 0] (countGood N)ᶜ :=
    hnull _ (measurableSet_countGood N).compl (ae_iff.mp (ae_mem_countGood N))
  exact ℱ.mono ht _ hc.of_compl

/-- On the good event a window `(0, t] × E_k` carries finite mass. -/
theorem count_window_ne_top {ω : Ω} (hω : ω ∈ countGood N) (t : ℝ) (k : ℕ) :
    N.N ω (Ioc (0 : ℝ) t ×ˢ spanningSets ν k) ≠ ⊤ := by
  obtain ⟨n, hn⟩ := exists_nat_ge t
  refine ne_top_of_le_ne_top (hω k n) (measure_mono (prod_mono ?_ le_rfl))
  exact Ioc_subset_Ioc_right hn

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **The count of a slice of a marked predictable set is adapted**, cut to an event of
`ℱ_t` on which the window `(0, t] × A` carries finite mass. -/
theorem measurable_indicator_sliceCount (hℱ : Poisson.IsPoissonFiltration N ℱ) {G : Set Ω}
    {t : ℝ} (hG : MeasurableSet[ℱ t] G) {A : Set E} (hA : MeasurableSet A)
    (hfin : ∀ ω ∈ G, N.N ω (Ioc (0 : ℝ) t ×ˢ A) ≠ ⊤)
    {S : Set (Ω × ℝ × E)} (hS : MeasurableSet[markedPredictableSigma ℱ ν] S) :
    Measurable[ℱ t] (G.indicator fun ω => N.N ω (Prod.mk ω ⁻¹' S ∩ Ioc (0 : ℝ) t ×ˢ A)) := by
  classical
  set R : Set (ℝ × E) := Ioc (0 : ℝ) t ×ˢ A with hRdef
  have hRm : MeasurableSet R := measurableSet_Ioc.prod hA
  have hRsub : R ⊆ Iic t ×ˢ (univ : Set E) :=
    prod_mono (fun s hs => mem_Iic.mpr hs.2) (subset_univ _)
  have hNR : Measurable[ℱ t] fun ω => N.N ω R := hℱ.measurable hRsub hRm
  refine MeasurableSpace.induction_on_inter
    (C := fun S' _ => Measurable[ℱ t]
      (G.indicator fun ω => N.N ω (Prod.mk ω ⁻¹' S' ∩ R)))
    rfl (isPiSystem_markedPredictableRect ℱ ν) ?_ ?_ ?_ ?_ S hS
  · have h0 : (G.indicator fun ω => N.N ω (Prod.mk ω ⁻¹' (∅ : Set (Ω × ℝ × E)) ∩ R))
        = fun _ => 0 := by
      funext ω
      simp
    rw [h0]
    exact measurable_const
  · rintro _ ⟨r, q, F, B, hr, hF, hB, -, rfl⟩
    have hslice : ∀ ω : Ω, Prod.mk ω ⁻¹' (F ×ˢ (Ioc r q ×ˢ B)) ∩ R
        = if ω ∈ F then Ioc r (min q t) ×ˢ (B ∩ A) else ∅ := by
      intro ω
      by_cases hω : ω ∈ F
      · rw [if_pos hω, hRdef]
        ext p
        have hpos : r < p.1 → (0 : ℝ) < p.1 := fun h => lt_of_le_of_lt hr h
        simp only [mem_inter_iff, mem_preimage, mem_prod, mem_Ioc, le_min_iff, hω, true_and]
        tauto
      · rw [if_neg hω]
        ext p
        simp [hω]
    rcases le_or_gt t r with htr | hrt
    · have h0 : (G.indicator fun ω => N.N ω (Prod.mk ω ⁻¹' (F ×ˢ (Ioc r q ×ˢ B)) ∩ R))
          = fun _ => 0 := by
        funext ω
        have he : Ioc r (min q t) = ∅ := Ioc_eq_empty (not_lt.mpr ((min_le_right q t).trans htr))
        by_cases hG' : ω ∈ G
        · rw [indicator_of_mem hG', hslice ω]
          by_cases hω : ω ∈ F <;> simp [hω, he]
        · rw [indicator_of_notMem hG']
      rw [h0]
      exact measurable_const
    · have hsub : Ioc r (min q t) ×ˢ (B ∩ A) ⊆ Iic t ×ˢ (univ : Set E) :=
        prod_mono (fun s hs => mem_Iic.mpr (hs.2.trans (min_le_right q t))) (subset_univ _)
      have hm : Measurable[ℱ t] fun ω => N.N ω (Ioc r (min q t) ×ˢ (B ∩ A)) :=
        hℱ.measurable hsub (measurableSet_Ioc.prod (hB.inter hA))
      have heq : (G.indicator fun ω => N.N ω (Prod.mk ω ⁻¹' (F ×ˢ (Ioc r q ×ˢ B)) ∩ R))
          = G.indicator (F.indicator fun ω => N.N ω (Ioc r (min q t) ×ˢ (B ∩ A))) := by
        funext ω
        by_cases hG' : ω ∈ G
        · rw [indicator_of_mem hG', indicator_of_mem hG', hslice ω]
          by_cases hω : ω ∈ F
          · rw [if_pos hω, indicator_of_mem hω]
          · rw [if_neg hω, indicator_of_notMem hω, measure_empty]
        · rw [indicator_of_notMem hG', indicator_of_notMem hG']
      rw [heq]
      exact (hm.indicator (ℱ.mono hrt.le _ hF)).indicator hG
  · intro S' hSm ih
    have hXm : ∀ ω : Ω, MeasurableSet (Prod.mk ω ⁻¹' S') := fun ω => measurableSet_slice hSm ω
    have heq : (G.indicator fun ω => N.N ω (Prod.mk ω ⁻¹' S'ᶜ ∩ R))
        = fun ω => G.indicator (fun ω => N.N ω R) ω
          - G.indicator (fun ω => N.N ω (Prod.mk ω ⁻¹' S' ∩ R)) ω := by
      funext ω
      by_cases hω : ω ∈ G
      · simp only [indicator_of_mem hω]
        have hsum : N.N ω (R ∩ Prod.mk ω ⁻¹' S') + N.N ω (R \ Prod.mk ω ⁻¹' S') = N.N ω R :=
          measure_inter_add_sdiff _ (hXm ω)
        have h1 : Prod.mk ω ⁻¹' S' ∩ R = R ∩ Prod.mk ω ⁻¹' S' := inter_comm _ _
        have h2 : Prod.mk ω ⁻¹' S'ᶜ ∩ R = R \ Prod.mk ω ⁻¹' S' := by
          rw [preimage_compl, inter_comm, Set.sdiff_eq]
        rw [h1, h2, ← hsum]
        refine (ENNReal.add_sub_cancel_left ?_).symm
        exact ne_top_of_le_ne_top (hfin ω hω) (measure_mono inter_subset_left)
      · simp [hω]
    rw [heq]
    exact (hNR.indicator hG).sub ih
  · intro f hd hfm ih
    have hdisj : ∀ ω : Ω, Pairwise (Function.onFun Disjoint
        fun i => Prod.mk ω ⁻¹' f i ∩ R) := fun ω i j hij =>
      Disjoint.mono inter_subset_left inter_subset_left ((hd hij).preimage (Prod.mk ω))
    have heq : (G.indicator fun ω => N.N ω (Prod.mk ω ⁻¹' (⋃ i, f i) ∩ R))
        = fun ω => ∑' i, G.indicator (fun ω => N.N ω (Prod.mk ω ⁻¹' f i ∩ R)) ω := by
      funext ω
      by_cases hω : ω ∈ G
      · simp only [indicator_of_mem hω]
        rw [preimage_iUnion, iUnion_inter,
          measure_iUnion (hdisj ω) fun i => (measurableSet_slice (hfm i) ω).inter hRm]
      · simp [hω]
    rw [heq]
    simp_rw [ENNReal.tsum_eq_iSup_sum]
    exact Measurable.iSup fun s => Finset.measurable_sum s fun i _ => ih i

/-- **The integral of a marked predictable function against `N` over a window is adapted**, cut
to an event of `ℱ_t` on which the window `(0, t] × A` carries finite mass. -/
theorem measurable_indicator_setLIntegral_count (hℱ : Poisson.IsPoissonFiltration N ℱ)
    {G : Set Ω} {t : ℝ} (hG : MeasurableSet[ℱ t] G) {A : Set E} (hA : MeasurableSet A)
    (hfin : ∀ ω ∈ G, N.N ω (Ioc (0 : ℝ) t ×ˢ A) ≠ ⊤)
    {g : Ω × ℝ × E → ℝ≥0∞} (hg : Measurable[markedPredictableSigma ℱ ν] g) :
    Measurable[ℱ t] (G.indicator fun ω => ∫⁻ x in Ioc (0 : ℝ) t ×ˢ A, g (ω, x) ∂(N.N ω)) := by
  classical
  set R : Set (ℝ × E) := Ioc (0 : ℝ) t ×ˢ A with hRdef
  have hRm : MeasurableSet R := measurableSet_Ioc.prod hA
  have hle := markedPredictableSigma_le ℱ ν
  refine @Measurable.ennreal_induction _ (markedPredictableSigma ℱ ν)
    (fun g => Measurable[ℱ t] (G.indicator fun ω => ∫⁻ x in R, g (ω, x) ∂(N.N ω)))
    ?_ ?_ ?_ g hg
  · intro c S hS
    have heq : (G.indicator fun ω => ∫⁻ x in R, S.indicator (fun _ => c) (ω, x) ∂(N.N ω))
        = fun ω => c * G.indicator (fun ω => N.N ω (Prod.mk ω ⁻¹' S ∩ R)) ω := by
      funext ω
      have hsl : MeasurableSet (Prod.mk ω ⁻¹' S) := measurableSet_slice hS ω
      have hfun : (fun x : ℝ × E => S.indicator (fun _ => c) (ω, x))
          = (Prod.mk ω ⁻¹' S).indicator fun _ => c := by
        funext x
        by_cases hx : (ω, x) ∈ S
        · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ Prod.mk ω ⁻¹' S from hx)]
        · rw [indicator_of_notMem hx, indicator_of_notMem (show x ∉ Prod.mk ω ⁻¹' S from hx)]
      by_cases hω : ω ∈ G
      · simp only [indicator_of_mem hω]
        rw [hfun, lintegral_indicator_const hsl, Measure.restrict_apply hsl]
      · simp [hω]
    rw [heq]
    exact (measurable_indicator_sliceCount N hℱ hG hA hfin hS).const_mul c
  · intro f₁ f₂ _ hf₁ hf₂ ih₁ ih₂
    have hf₁' : Measurable f₁ := hf₁.mono hle le_rfl
    have heq : (G.indicator fun ω => ∫⁻ x in R, (f₁ + f₂) (ω, x) ∂(N.N ω))
        = fun ω => G.indicator (fun ω => ∫⁻ x in R, f₁ (ω, x) ∂(N.N ω)) ω
          + G.indicator (fun ω => ∫⁻ x in R, f₂ (ω, x) ∂(N.N ω)) ω := by
      funext ω
      by_cases hω : ω ∈ G
      · simp only [indicator_of_mem hω, Pi.add_apply]
        exact lintegral_add_left (hf₁'.comp measurable_prodMk_left) _
      · simp [hω]
    rw [heq]
    exact ih₁.add ih₂
  · intro f hf hmono ih
    have heq : (G.indicator fun ω => ∫⁻ x in R, (fun y => ⨆ n, f n y) (ω, x) ∂(N.N ω))
        = fun ω => ⨆ n, G.indicator (fun ω => ∫⁻ x in R, f n (ω, x) ∂(N.N ω)) ω := by
      funext ω
      by_cases hω : ω ∈ G
      · simp only [indicator_of_mem hω]
        exact lintegral_iSup (fun n => ((hf n).mono hle le_rfl).comp measurable_prodMk_left)
          fun n m hnm x => hmono hnm (ω, x)
      · simp [hω]
    rw [heq]
    exact Measurable.iSup ih

/-- The window `(0, t] × E` is the directed union of the windows `(0, t] × E_k`. -/
theorem iUnion_Ioc_prod_spanningSets (t : ℝ) :
    (⋃ k, Ioc (0 : ℝ) t ×ˢ spanningSets ν k) = Ioc (0 : ℝ) t ×ˢ (univ : Set E) := by
  rw [← prod_iUnion, iUnion_spanningSets]

theorem directed_Ioc_prod_spanningSets (t : ℝ) :
    Directed (· ⊆ ·) fun k => Ioc (0 : ℝ) t ×ˢ spanningSets ν k :=
  ((monotone_spanningSets ν).directed_le).mono_comp _ fun _ _ h => prod_mono le_rfl h

/-- On the good event, the integral of `g` against `N` over `(0, t] × E`; `0` off it. -/
noncomputable def countInt (g : Ω × ℝ × E → ℝ≥0∞) (t : ℝ) (ω : Ω) : ℝ≥0∞ :=
  (countGood N).indicator
    (fun ω => ∫⁻ x in Ioc (0 : ℝ) t ×ˢ (univ : Set E), g (ω, x) ∂(N.N ω)) ω

/-- On the good event, the integral of `g` against `N` over `(0, t) × E`; `0` off it. -/
noncomputable def countIntLeft (g : Ω × ℝ × E → ℝ≥0∞) (t : ℝ) (ω : Ω) : ℝ≥0∞ :=
  (countGood N).indicator
    (fun ω => ∫⁻ x in Ioo (0 : ℝ) t ×ˢ (univ : Set E), g (ω, x) ∂(N.N ω)) ω

variable {g : Ω × ℝ × E → ℝ≥0∞}

theorem countInt_of_mem {ω : Ω} (hω : ω ∈ countGood N) (t : ℝ) :
    countInt N g t ω = ∫⁻ x in Ioc (0 : ℝ) t ×ˢ (univ : Set E), g (ω, x) ∂(N.N ω) := by
  rw [countInt, indicator_of_mem hω]

theorem countIntLeft_of_mem {ω : Ω} (hω : ω ∈ countGood N) (t : ℝ) :
    countIntLeft N g t ω = ∫⁻ x in Ioo (0 : ℝ) t ×ˢ (univ : Set E), g (ω, x) ∂(N.N ω) := by
  rw [countIntLeft, indicator_of_mem hω]

theorem countInt_mono (ω : Ω) : Monotone fun t => countInt N g t ω := by
  intro t t' h
  dsimp only
  by_cases hω : ω ∈ countGood N
  · rw [countInt_of_mem N hω, countInt_of_mem N hω]
    exact lintegral_mono_set (prod_mono (Ioc_subset_Ioc_right h) le_rfl)
  · simp [countInt, hω]

theorem countIntLeft_mono (ω : Ω) : Monotone fun t => countIntLeft N g t ω := by
  intro t t' h
  dsimp only
  by_cases hω : ω ∈ countGood N
  · rw [countIntLeft_of_mem N hω, countIntLeft_of_mem N hω]
    exact lintegral_mono_set (prod_mono (Ioo_subset_Ioo_right h) le_rfl)
  · simp [countIntLeft, hω]

theorem countIntLeft_le_countInt (t : ℝ) (ω : Ω) : countIntLeft N g t ω ≤ countInt N g t ω := by
  by_cases hω : ω ∈ countGood N
  · rw [countInt_of_mem N hω, countIntLeft_of_mem N hω]
    exact lintegral_mono_set (prod_mono Ioo_subset_Ioc_self le_rfl)
  · simp [countInt, countIntLeft, hω]

theorem countInt_le_countIntLeft {t t' : ℝ} (h : t < t') (ω : Ω) :
    countInt N g t ω ≤ countIntLeft N g t' ω := by
  by_cases hω : ω ∈ countGood N
  · rw [countInt_of_mem N hω, countIntLeft_of_mem N hω]
    exact lintegral_mono_set (prod_mono (fun s hs => ⟨hs.1, hs.2.trans_lt h⟩) le_rfl)
  · simp [countInt, countIntLeft, hω]

/-- The left version is the supremum of the integrals over `(0, t − 1/(n + 1)]`. -/
theorem countIntLeft_eq_iSup (t : ℝ) (ω : Ω) :
    countIntLeft N g t ω = ⨆ n : ℕ, countInt N g (t - 1 / ((n : ℝ) + 1)) ω := by
  by_cases hω : ω ∈ countGood N
  · simp only [countIntLeft_of_mem N hω, countInt_of_mem N hω]
    have hU : Ioo (0 : ℝ) t ×ˢ (univ : Set E)
        = ⋃ n : ℕ, Ioc (0 : ℝ) (t - 1 / ((n : ℝ) + 1)) ×ˢ (univ : Set E) := by
      rw [← iUnion_prod_const]
      congr 1
      ext s
      simp only [mem_Ioo, mem_iUnion, mem_Ioc]
      constructor
      · rintro ⟨hs0, hst⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hst)
        exact ⟨n, hs0, by linarith⟩
      · rintro ⟨n, hs0, hsn⟩
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        exact ⟨hs0, by linarith⟩
    have hdir : Directed (· ⊆ ·)
        fun n : ℕ => Ioc (0 : ℝ) (t - 1 / ((n : ℝ) + 1)) ×ˢ (univ : Set E) := by
      refine Monotone.directed_le fun n m hnm => prod_mono (Ioc_subset_Ioc_right ?_) le_rfl
      have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
      linarith
    rw [hU, setLIntegral_iUnion_of_directed _ hdir]
  · simp [countInt, countIntLeft, hω]

/-- The left version is the supremum of its values at earlier times. -/
theorem countIntLeft_eq_biSup (t : ℝ) (ω : Ω) :
    countIntLeft N g t ω = ⨆ s ∈ Iio t, countIntLeft N g s ω := by
  refine le_antisymm ?_ (iSup₂_le fun s hs => countIntLeft_mono N ω (le_of_lt hs))
  rw [countIntLeft_eq_iSup]
  refine iSup_le fun n => ?_
  have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
  refine le_trans (countInt_le_countIntLeft N (t' := t - 1 / ((n : ℝ) + 1) / 2) ?_ ω) ?_
  · linarith
  · exact le_iSup₂_of_le (f := fun s (_ : s ∈ Iio t) => countIntLeft N g s ω)
      (t - 1 / ((n : ℝ) + 1) / 2) (by simp only [mem_Iio]; linarith) le_rfl

/-- The left version is left continuous. -/
theorem tendsto_countIntLeft (t : ℝ) (ω : Ω) :
    Tendsto (fun s => countIntLeft N g s ω) (𝓝[<] t) (𝓝 (countIntLeft N g t ω)) := by
  have h := (countIntLeft_mono (g := g) N ω).tendsto_nhdsLT t
  rw [sSup_image'] at h
  convert h using 2
  rw [countIntLeft_eq_biSup N t ω, iSup_subtype']

/-- The integral of a nonnegative marked predictable function against `N` over a window of
finite mark measure is a directed supremum, and over `(0, t] × E` it is adapted on the good
event. -/
theorem measurable_countInt (hℱ : Poisson.IsPoissonFiltration N ℱ)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hg : Measurable[markedPredictableSigma ℱ ν] g) (t : ℝ) :
    Measurable[ℱ t] (countInt N g t) := by
  rcases lt_or_ge t 0 with ht | ht
  · have h0 : countInt N g t = fun _ => 0 := by
      funext ω
      simp [countInt, Ioc_eq_empty (not_lt.mpr ht.le)]
    rw [h0]
    exact measurable_const
  have hG := measurableSet_countGood_filtration N hnull ht
  have heq : countInt N g t = fun ω => ⨆ k, (countGood N).indicator
      (fun ω => ∫⁻ x in Ioc (0 : ℝ) t ×ˢ spanningSets ν k, g (ω, x) ∂(N.N ω)) ω := by
    funext ω
    by_cases hω : ω ∈ countGood N
    · simp only [countInt_of_mem N hω, indicator_of_mem hω]
      rw [← iUnion_Ioc_prod_spanningSets (ν := ν) t,
        setLIntegral_iUnion_of_directed _ (directed_Ioc_prod_spanningSets (ν := ν) t)]
    · simp [countInt, hω]
  rw [heq]
  exact Measurable.iSup fun k => measurable_indicator_setLIntegral_count N hℱ hG
    (measurableSet_spanningSets ν k) (fun ω hω => count_window_ne_top N hω t k) hg

/-- The left version is adapted. -/
theorem measurable_countIntLeft (hℱ : Poisson.IsPoissonFiltration N ℱ)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hg : Measurable[markedPredictableSigma ℱ ν] g) (t : ℝ) :
    Measurable[ℱ t] (countIntLeft N g t) := by
  have heq : countIntLeft N g t = fun ω => ⨆ n : ℕ, countInt N g (t - 1 / ((n : ℝ) + 1)) ω :=
    funext fun ω => countIntLeft_eq_iSup N t ω
  rw [heq]
  refine Measurable.iSup fun n => ?_
  have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
  exact (measurable_countInt N hℱ hnull hg _).mono (ℱ.mono (by linarith)) le_rfl

/-- **The left version is predictable.** -/
theorem measurable_predictableSigma_countIntLeft (hℱ : Poisson.IsPoissonFiltration N ℱ)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hg : Measurable[markedPredictableSigma ℱ ν] g) :
    Measurable[predictableSigma ℱ] fun p : ℝ × Ω => countIntLeft N g p.1 p.2 :=
  measurable_predictableSigma_of_leftContinuous_ennreal
    (measurable_countIntLeft N hℱ hnull hg) (tendsto_countIntLeft N)

end Count

section Hit

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- The nonnegative times by which the process `X` has reached `δ`. -/
def levelHitSet (X : ℝ → Ω → ℝ≥0∞) (δ : ℝ≥0∞) (ω : Ω) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ δ ≤ X t ω}

open scoped Classical in
/-- The first time at which the process `X` reaches `δ`, and `⊤` if it never does. -/
noncomputable def levelHit (X : ℝ → Ω → ℝ≥0∞) (δ : ℝ≥0∞) (ω : Ω) : WithTop ℝ :=
  if (levelHitSet X δ ω).Nonempty then ((sInf (levelHitSet X δ ω) : ℝ) : WithTop ℝ) else ⊤

variable {X : ℝ → Ω → ℝ≥0∞} {δ : ℝ≥0∞}

theorem bddBelow_levelHitSet (X : ℝ → Ω → ℝ≥0∞) (δ : ℝ≥0∞) (ω : Ω) :
    BddBelow (levelHitSet X δ ω) := ⟨0, fun _ ht => ht.1⟩

/-- Strictly before the passage time the process is below the level. -/
theorem lt_of_lt_levelHit {ω : Ω} {s : ℝ} (hs : 0 ≤ s)
    (h : ((s : ℝ) : WithTop ℝ) < levelHit X δ ω) : X s ω < δ := by
  classical
  by_contra hcon
  push Not at hcon
  have hmem : s ∈ levelHitSet X δ ω := ⟨hs, hcon⟩
  have hne : (levelHitSet X δ ω).Nonempty := ⟨s, hmem⟩
  rw [levelHit, if_pos hne] at h
  have hle : sInf (levelHitSet X δ ω) ≤ s := csInf_le (bddBelow_levelHitSet X δ ω) hmem
  exact absurd (WithTop.coe_lt_coe.mp h) (not_lt.mpr hle)

/-- **A time at which a nondecreasing process is below the level comes no later than the
passage time.** -/
theorem le_levelHit_of_lt {ω : Ω} (hmono : Monotone fun t => X t ω) {T : ℝ}
    (h : X T ω < δ) : ((T : ℝ) : WithTop ℝ) ≤ levelHit X δ ω := by
  classical
  rw [levelHit]
  split_ifs with hne
  · refine WithTop.coe_le_coe.mpr (le_csInf hne fun t ht => ?_)
    by_contra htT
    push Not at htT
    exact absurd (ht.2.trans (hmono htT.le)) (not_le.mpr h)
  · exact le_top

/-- **The passage time of a nondecreasing adapted process is a stopping time** of a
right-continuous filtration. -/
theorem isStoppingTime_levelHit {ℱ : Filtration ℝ mΩ} [ℱ.IsRightContinuous]
    (hX : ∀ t : ℝ, Measurable[ℱ t] (X t)) (hmono : ∀ ω, Monotone fun t => X t ω)
    (δ : ℝ≥0∞) : IsStoppingTime ℱ (levelHit X δ) := by
  classical
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun i => ?_
  have hset : {ω | levelHit X δ ω < ((i : ℝ) : WithTop ℝ)}
      = ⋃ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) < i), {ω | δ ≤ X (q : ℝ) ω} := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, exists_prop]
    constructor
    · intro h
      have hne : (levelHitSet X δ ω).Nonempty := by
        by_contra hne
        rw [levelHit, if_neg hne] at h
        exact absurd h (not_lt.mpr le_top)
      rw [levelHit, if_pos hne] at h
      obtain ⟨t, ht, hti⟩ := exists_lt_of_csInf_lt hne (WithTop.coe_lt_coe.mp h)
      obtain ⟨q, htq, hqi⟩ := exists_rat_btwn hti
      exact ⟨q, ⟨ht.1.trans htq.le, hqi⟩, ht.2.trans (hmono ω htq.le)⟩
    · rintro ⟨q, ⟨hq0, hqi⟩, hq⟩
      have hmem : (q : ℝ) ∈ levelHitSet X δ ω := ⟨hq0, hq⟩
      have hne : (levelHitSet X δ ω).Nonempty := ⟨q, hmem⟩
      rw [levelHit, if_pos hne]
      exact WithTop.coe_lt_coe.mpr
        (lt_of_le_of_lt (csInf_le (bddBelow_levelHitSet X δ ω) hmem) hqi)
  rw [hset]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
  exact ℱ.mono hq.2.le _ (measurableSet_le measurable_const (hX q))

end Hit

section Simple

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure.{u, v, w} P ν)

/-- **Almost surely every positive time carries at most one point of `N`.** -/
theorem ae_count_time_le_one : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → N.N ω ({s} ×ˢ (univ : Set E)) ≤ 1 := by
  have h : ∀ᵐ ω ∂P, ∀ k n : ℕ, ∀ s : ℝ,
      N.N ω ((Ioc (0 : ℝ) n ×ˢ spanningSets ν k) ∩ {s} ×ˢ (univ : Set E)) ≤ 1 :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun n =>
      Poisson.ae_count_time_singleton_le_one N
        (measurableSet_Ioc.prod (measurableSet_spanningSets ν k))
        (Poisson.referenceIntensity_Ioc_prod_ne_top (measure_spanningSets_lt_top ν k).ne n)
  filter_upwards [h] with ω hω s hs
  obtain ⟨n, hn⟩ := exists_nat_ge s
  have hU : ({s} ×ˢ (univ : Set E)) = ⋃ k, {s} ×ˢ spanningSets ν k := by
    rw [← prod_iUnion, iUnion_spanningSets]
  have hdir : Directed (· ⊆ ·) fun k => ({s} : Set ℝ) ×ˢ spanningSets ν k :=
    ((monotone_spanningSets ν).directed_le).mono_comp _ fun _ _ h => prod_mono le_rfl h
  rw [hU, hdir.measure_iUnion]
  refine iSup_le fun k => le_trans (measure_mono ?_) (hω k n s)
  rintro ⟨x, e⟩ ⟨hx, he⟩
  simp only [mem_singleton_iff] at hx
  subst hx
  exact ⟨⟨⟨hs, hn⟩, he⟩, rfl, mem_univ _⟩

end Simple

end Dissertation.WellPosedness.Martingale
