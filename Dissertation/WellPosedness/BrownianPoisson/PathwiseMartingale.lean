/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.Compensation
import LevyStochCalc.Ito.JumpCoefficientPredictableCriteria

/-!
# The pathwise compensated integral of an integrable predictable integrand is a martingale

For a Poisson random measure `N` with intensity `dt ⊗ ν(de)` carried by a filtration `ℱ`, and a
nonnegative function `ψ` measurable for the marked predictable σ-algebra with
`𝔼 ∫_0^T ∫_E ψ ν(de) ds < ∞`, the pathwise compensated integral

`M_t = ∫_{(0, t] × E} ψ dN − ∫_0^t ∫_E ψ ν(de) ds`

is a martingale on `[0, T]`: `M_t` is integrable, almost surely equal to an `ℱ_t`-measurable
random variable, and `𝔼[M_t | ℱ_s] = M_s` almost surely for `0 ≤ s ≤ t ≤ T`.

* **Measurability.** Cut to the times up to `t`, `ψ` is measurable for `ℱ_t ⊗ 𝓑 ⊗ 𝓔`, and the
  random measure restricted to `(0, t] × A`, for `ν(A) < ∞`, is an `ℱ_t`-measurable random
  measure; it is finite almost surely, and the restrictions on the events `{N((0, t] × A) ≤ n}`
  are finite kernels, so the lower integral of `ψ` against it is `ℱ_t`-measurable off a null
  set. Exhausting `E` by sets of finite measure gives the integral against `N` on `(0, t] × E`.
* **Martingale property.** For `A ∈ ℱ_s` the integrand `1_A 1_{(s, t]} ψ` is marked
  predictable, so the compensated integral (2.2) gives `𝔼[1_A (M_t − M_s)] = 0`.

## Main definitions

* `pathwiseCompensated` — `t ↦ ∫_{(0, t] × E} ψ dN − ∫_0^t ∫_E ψ ν(de) ds`.

## Main statements

* `aestronglyMeasurable_pathwiseCompensated` — `M_t` is `ℱ_t`-measurable up to a null set.
* `integrable_pathwiseCompensated` — `M_t` is integrable.
* `condExp_pathwiseCompensated` — `𝔼[M_t | ℱ_s] = M_s` almost surely.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace Dissertation.WellPosedness.BrownianPoisson

open LevyStochCalc

universe u' v' w'

variable {Ω : Type u'} [MeasurableSpace Ω] {E : Type v'} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {N : Poisson.PoissonRandomMeasure.{u', v', w'} P ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- The pathwise compensated integral `∫_{(0, t] × E} ψ dN − ∫_0^t ∫_E ψ ν(de) ds`. -/
noncomputable def pathwiseCompensated (N : Poisson.PoissonRandomMeasure.{u', v', w'} P ν)
    (ψ : Ω × ℝ × E → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (∫ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ, ψ (ω, p) ∂(N.N ω))
    - ∫ s in Set.Ioc (0 : ℝ) t, ∫ e, ψ (ω, s, e) ∂ν

/-- The compensator part `ω ↦ ∫_I ∫_E f(ω, s, e) ν(de) ds` of a jointly measurable integrand is
strongly measurable. -/
theorem stronglyMeasurable_compensatorPart {Ω' : Type*} {m : MeasurableSpace Ω'} {E' : Type*}
    [MeasurableSpace E'] {ν' : Measure E'} [SFinite ν'] {f : Ω' × ℝ × E' → ℝ} (hf : Measurable f)
    (I : Set ℝ) : StronglyMeasurable fun ω => ∫ s in I, ∫ e, f (ω, s, e) ∂ν' := by
  have hf' : Measurable fun x : (Ω' × ℝ) × E' => f (x.1.1, x.1.2, x.2) :=
    hf.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have h1 : StronglyMeasurable fun q : Ω' × ℝ => ∫ e, f (q.1, q.2, e) ∂ν' :=
    hf'.stronglyMeasurable.integral_prod_right'
  exact h1.integral_prod_right' (ν := volume.restrict I)

/-! ### Measurability at time `t` -/

omit [SigmaFinite ν] in
/-- **A marked predictable function cut to the times up to `t` is measurable for
`ℱ_t ⊗ 𝓑 ⊗ 𝓔`.** -/
theorem measurable_cut_of_markedPredictable {ψ : Ω × ℝ × E → ℝ}
    (hψ : Measurable[Probability.markedPredictableSigma ℱ ν] ψ) (t : ℝ) :
    Measurable[@Prod.instMeasurableSpace Ω (ℝ × E) (ℱ t) inferInstance]
      fun p : Ω × ℝ × E => if p.2.1 ≤ t then ψ p else 0 := by
  intro V hV
  have hS := Probability.measurableSet_inter_timeIic (ℱ := ℱ) (ν := ν) (hψ hV) t
  have hT := Probability.measurableSet_timeIic (Ω := Ω) (E := E) (ℱ := ℱ) t
  by_cases h0 : (0 : ℝ) ∈ V
  · have hrw : (fun p : Ω × ℝ × E => if p.2.1 ≤ t then ψ p else 0) ⁻¹' V
        = (ψ ⁻¹' V ∩ {p : Ω × ℝ × E | p.2.1 ≤ t}) ∪ {p : Ω × ℝ × E | p.2.1 ≤ t}ᶜ := by
      ext p
      by_cases hp : p.2.1 ≤ t <;> simp [hp, h0]
    rw [hrw]
    exact hS.union hT.compl
  · have hrw : (fun p : Ω × ℝ × E => if p.2.1 ≤ t then ψ p else 0) ⁻¹' V
        = ψ ⁻¹' V ∩ {p : Ω × ℝ × E | p.2.1 ≤ t} := by
      ext p
      by_cases hp : p.2.1 ≤ t <;> simp [hp, h0]
    rw [hrw]
    exact hS

/-- **The lower integral against the random measure on `(0, t] × E` is `ℱ_t`-measurable off a
null set**, for an integrand measurable for `ℱ_t ⊗ 𝓑 ⊗ 𝓔`. -/
theorem exists_measurable_ae_eq_lintegral_N (hℱN : Poisson.IsPoissonFiltration N ℱ) {t : ℝ}
    {G : Ω × ℝ × E → ℝ≥0∞}
    (hG : Measurable[@Prod.instMeasurableSpace Ω (ℝ × E) (ℱ t) inferInstance] G) :
    ∃ g : Ω → ℝ≥0∞, Measurable[ℱ t] g
      ∧ (fun ω => ∫⁻ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ, G (ω, p) ∂(N.N ω)) =ᵐ[P] g := by
  classical
  set A := spanningSets ν
  set R : ℕ → Set (ℝ × E) := fun k => Set.Ioc (0 : ℝ) t ×ˢ A k with hRdef
  have hRm : ∀ k, MeasurableSet (R k) := fun k =>
    measurableSet_Ioc.prod (measurableSet_spanningSets ν k)
  have hRsub : ∀ k, R k ⊆ Set.Iic t ×ˢ Set.univ := fun k p hp =>
    ⟨Set.mem_Iic.mpr hp.1.2, Set.mem_univ _⟩
  have hNR : ∀ k, Measurable[ℱ t] fun ω => N.N ω (R k) := fun k =>
    hℱN.measurable (hRsub k) (hRm k)
  -- the counts on the windows are finite almost surely
  have hfin : ∀ k, ∀ᵐ ω ∂P, N.N ω (R k) < ⊤ := by
    intro k
    have hint : Poisson.referenceIntensity ν (R k) ≠ ⊤ := by
      rw [Poisson.referenceIntensity, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc]
      refine ENNReal.mul_ne_top ?_ (measure_spanningSets_lt_top ν k).ne
      exact (measure_mono Set.inter_subset_left).trans_lt (by simp) |>.ne
    filter_upwards [N.integer_valued (hRm k) hint] with ω ⟨n, hn⟩
    rw [hn]
    exact ENNReal.natCast_lt_top n
  -- on each window, the integral against the truncated kernels
  have key : ∀ k, ∃ gk : Ω → ℝ≥0∞, Measurable[ℱ t] gk
      ∧ ∀ ω, N.N ω (R k) < ⊤ → gk ω = ∫⁻ p in R k, G (ω, p) ∂(N.N ω) := by
    intro k
    have hNB : ∀ B : Set (ℝ × E), MeasurableSet B → B ⊆ Set.Iic t ×ˢ Set.univ →
        Measurable[ℱ t] fun ω => N.N ω B := fun B hB hsub => hℱN.measurable hsub hB
    set NN : Ω → Measure (ℝ × E) := N.N with hNN
    clear_value NN
    letI mt : MeasurableSpace Ω := ℱ t
    have hκm : ∀ n : ℕ, Measurable fun ω =>
        (if NN ω (R k) ≤ n then (NN ω).restrict (R k) else 0 : Measure (ℝ × E)) := by
      intro n
      refine Measure.measurable_of_measurable_coe _ fun B hB => ?_
      have hset : MeasurableSet {ω | NN ω (R k) ≤ n} :=
        measurableSet_le (hNR k) measurable_const
      have e : (fun ω => (if NN ω (R k) ≤ n then (NN ω).restrict (R k) else 0 :
          Measure (ℝ × E)) B) = fun ω => if NN ω (R k) ≤ n then NN ω (B ∩ R k) else 0 := by
        funext ω
        split_ifs
        · rw [Measure.restrict_apply hB]
        · rfl
      rw [e]
      exact Measurable.ite hset (hNB _ (hB.inter (hRm k))
        (Set.inter_subset_right.trans (hRsub k))) measurable_const
    let κ : ℕ → Kernel Ω (ℝ × E) := fun n => ⟨_, hκm n⟩
    have hκfin : ∀ n, IsFiniteKernel (κ n) := by
      intro n
      refine ⟨⟨n, ENNReal.natCast_lt_top n, fun ω => ?_⟩⟩
      change (if NN ω (R k) ≤ n then (NN ω).restrict (R k) else 0 :
        Measure (ℝ × E)) Set.univ ≤ n
      split_ifs with h
      · rw [Measure.restrict_apply_univ]
        exact h
      · simp
    have hf : ∀ n, Measurable fun ω => ∫⁻ p, G (ω, p) ∂(κ n ω) := fun n => by
      haveI := hκfin n
      exact hG.lintegral_kernel_prod_right'
    refine ⟨fun ω => ⨆ n : ℕ, ∫⁻ p, G (ω, p) ∂(κ n ω), Measurable.iSup hf,
      fun ω hω => le_antisymm (iSup_le fun n => ?_) ?_⟩
    · change ∫⁻ p, G (ω, p) ∂(if NN ω (R k) ≤ n then (NN ω).restrict (R k) else 0 :
        Measure (ℝ × E)) ≤ _
      split_ifs
      · exact le_rfl
      · simp
    · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hω.ne
      refine le_iSup_of_le n (le_of_eq ?_)
      change _ = ∫⁻ p, G (ω, p) ∂(if NN ω (R k) ≤ n then (NN ω).restrict (R k) else 0 :
        Measure (ℝ × E))
      rw [if_pos hn.le]
  choose g hgm hg using key
  refine ⟨fun ω => ⨆ k, g k ω, Measurable.iSup hgm, ?_⟩
  filter_upwards [ae_all_iff.mpr hfin] with ω hω
  have hU : (⋃ k, R k) = Set.Ioc (0 : ℝ) t ×ˢ Set.univ := by
    rw [hRdef, ← Set.prod_iUnion, iUnion_spanningSets]
  have hdir : Directed (· ⊆ ·) R :=
    ((monotone_spanningSets ν).directed_le).mono_comp _ fun _ _ h => Set.prod_mono le_rfl h
  rw [← hU, setLIntegral_iUnion_of_directed _ hdir]
  exact iSup_congr fun k => (hg k ω (hω k)).symm

/-! ### Integrability and the martingale property -/

section Martingale

variable {ψ : Ω × ℝ × E → ℝ} {T : ℝ}

omit [SigmaFinite ν] in
/-- Every section of a marked predictable integrand is measurable. -/
theorem measurable_section_of_markedPredictable
    (hψ : Measurable[Probability.markedPredictableSigma ℱ ν] ψ) (ω : Ω) :
    Measurable fun p : ℝ × E => ψ (ω, p) :=
  (hψ.mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl).comp measurable_prodMk_left

/-- The integral of a nonnegative integrand against the random measure is the real part of its
lower integral. -/
theorem integral_N_eq_toReal (hψ : Measurable[Probability.markedPredictableSigma ℱ ν] ψ)
    (hψ0 : ∀ p, 0 ≤ ψ p) (S : Set (ℝ × E)) (ω : Ω) :
    ∫ p in S, ψ (ω, p) ∂(N.N ω) = (∫⁻ p in S, ENNReal.ofReal (ψ (ω, p)) ∂(N.N ω)).toReal :=
  integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => hψ0 _)
    (measurable_section_of_markedPredictable hψ ω).aestronglyMeasurable

/-- **The integral against the random measure on `(0, t] × E` has finite expectation**, equal to
that of the compensator. -/
theorem lintegral_N_eq_compensator (hℱN : Poisson.IsPoissonFiltration N ℱ)
    (hψ : Measurable[Probability.markedPredictableSigma ℱ ν] ψ) (t : ℝ) :
    ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ, ENNReal.ofReal (ψ (ω, p)) ∂(N.N ω) ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) t, ∫⁻ e, ENNReal.ofReal (ψ (ω, s, e)) ∂ν ∂volume ∂P :=
  (aemeasurable_and_lintegral_compensation hℱN t (ψ := fun x => ENNReal.ofReal (ψ x))
    (ENNReal.measurable_ofReal.comp hψ)).2.2

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The compensator over `(0, t]` is at most that over `(0, T]`, for `t ≤ T`. -/
theorem lintegral_compensator_mono {t : ℝ} (htT : t ≤ T) :
    ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) t, ∫⁻ e, ENNReal.ofReal (ψ (ω, s, e)) ∂ν ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (ψ (ω, s, e)) ∂ν ∂volume ∂P :=
  lintegral_mono fun _ => lintegral_mono_set (Set.Ioc_subset_Ioc_right htT)

/-- **The pathwise compensated integral is integrable** on `[0, T]`. -/
theorem integrable_pathwiseCompensated (hℱN : Poisson.IsPoissonFiltration N ℱ)
    (hψ : Measurable[Probability.markedPredictableSigma ℱ ν] ψ) (hψ0 : ∀ p, 0 ≤ ψ p)
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (ψ (ω, s, e)) ∂ν ∂volume ∂P
      < ⊤) {t : ℝ} (htT : t ≤ T) :
    Integrable (pathwiseCompensated N ψ t) P := by
  have hfint := (lintegral_compensator_mono (P := P) (ν := ν) (ψ := ψ) htT).trans_lt hfin
  have hA : Integrable (fun ω => ∫ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ, ψ (ω, p) ∂(N.N ω)) P := by
    have e : (fun ω => ∫ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ, ψ (ω, p) ∂(N.N ω))
        = fun ω => (∫⁻ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ, ENNReal.ofReal (ψ (ω, p))
          ∂(N.N ω)).toReal := funext fun ω => integral_N_eq_toReal hψ hψ0 _ ω
    rw [e]
    refine integrable_toReal_of_lintegral_ne_top
      (aemeasurable_and_lintegral_compensation hℱN t (ψ := fun x => ENNReal.ofReal (ψ x))
        (ENNReal.measurable_ofReal.comp hψ)).1 ?_
    rw [lintegral_N_eq_compensator hℱN hψ t]
    exact hfint.ne
  have hψm : Measurable ψ := hψ.mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hB : Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) t, ∫ e, ψ (ω, s, e) ∂ν) P := by
    refine ⟨(stronglyMeasurable_compensatorPart hψm _).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hfint
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun s => ?_)
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun e => ?_))
    exact Real.enorm_of_nonneg (hψ0 _)
  exact hA.sub hB

/-- **The pathwise compensated integral at time `t` is `ℱ_t`-measurable off a null set.** -/
theorem aestronglyMeasurable_pathwiseCompensated (hℱN : Poisson.IsPoissonFiltration N ℱ)
    (hψ : Measurable[Probability.markedPredictableSigma ℱ ν] ψ) (hψ0 : ∀ p, 0 ≤ ψ p) (t : ℝ) :
    AEStronglyMeasurable[ℱ t] (pathwiseCompensated N ψ t) P := by
  set ψt : Ω × ℝ × E → ℝ := fun p => if p.2.1 ≤ t then ψ p else 0 with hψt
  have hψtm := measurable_cut_of_markedPredictable hψ t
  obtain ⟨g, hg, hge⟩ := exists_measurable_ae_eq_lintegral_N (P := P) hℱN
    (G := fun p => ENNReal.ofReal (ψt p)) (ENNReal.measurable_ofReal.comp hψtm)
  have hcut : ∀ ω, ∀ p ∈ Set.Ioc (0 : ℝ) t ×ˢ (Set.univ : Set E), ψt (ω, p) = ψ (ω, p) :=
    fun ω p hp => by simp only [hψt, if_pos hp.1.2]
  have hcutB : ∀ ω, ∀ s ∈ Set.Ioc (0 : ℝ) t, ∀ e : E, ψt (ω, s, e) = ψ (ω, s, e) :=
    fun ω s hs e => by simp only [hψt, if_pos hs.2]
  have hBm : StronglyMeasurable[ℱ t] fun ω => ∫ s in Set.Ioc (0 : ℝ) t, ∫ e, ψt (ω, s, e) ∂ν := by
    letI : MeasurableSpace Ω := ℱ t
    exact stronglyMeasurable_compensatorPart hψtm _
  have hgm : StronglyMeasurable[ℱ t] fun ω => (g ω).toReal := by
    letI : MeasurableSpace Ω := ℱ t
    exact hg.ennreal_toReal.stronglyMeasurable
  refine ⟨fun ω => (g ω).toReal - ∫ s in Set.Ioc (0 : ℝ) t, ∫ e, ψt (ω, s, e) ∂ν,
    hgm.sub hBm, ?_⟩
  filter_upwards [hge] with ω hω
  have h1 : ∫⁻ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ, ENNReal.ofReal (ψt (ω, p)) ∂(N.N ω)
      = ∫⁻ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ, ENNReal.ofReal (ψ (ω, p)) ∂(N.N ω) :=
    setLIntegral_congr_fun (measurableSet_Ioc.prod MeasurableSet.univ) fun p hp => by
      rw [hcut ω p hp]
  have h2 : ∫ s in Set.Ioc (0 : ℝ) t, ∫ e, ψt (ω, s, e) ∂ν
      = ∫ s in Set.Ioc (0 : ℝ) t, ∫ e, ψ (ω, s, e) ∂ν :=
    setIntegral_congr_fun measurableSet_Ioc fun s hs =>
      integral_congr_ae (ae_of_all _ fun e => hcutB ω s hs e)
  have hω' : ∫⁻ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ, ENNReal.ofReal (ψt (ω, p)) ∂(N.N ω) = g ω :=
    hω
  rw [← hω', h1, h2, pathwiseCompensated, integral_N_eq_toReal hψ hψ0]

/-- An integral over `(0, t] × E` minus that over `(0, s] × E` is the integral over `(s, t] × E`,
for `0 ≤ s ≤ t` and an integrand integrable on `(0, t] × E`. -/
theorem setIntegral_Ioc_prod_sub {μ : Measure (ℝ × E)} {f : ℝ × E → ℝ} {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (hf : IntegrableOn f (Set.Ioc (0 : ℝ) t ×ˢ Set.univ) μ) :
    ∫ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ, f p ∂μ - ∫ p in Set.Ioc (0 : ℝ) s ×ˢ Set.univ, f p ∂μ
      = ∫ p in Set.Ioc s t ×ˢ Set.univ, f p ∂μ := by
  have hU : Set.Ioc (0 : ℝ) t ×ˢ (Set.univ : Set E)
      = Set.Ioc (0 : ℝ) s ×ˢ Set.univ ∪ Set.Ioc s t ×ˢ Set.univ := by
    rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc hs hst]
  have hD : Disjoint (Set.Ioc (0 : ℝ) s ×ˢ (Set.univ : Set E)) (Set.Ioc s t ×ˢ Set.univ) :=
    Set.disjoint_prod.mpr (Or.inl (Set.Ioc_disjoint_Ioc_of_le le_rfl))
  rw [hU, setIntegral_union hD (measurableSet_Ioc.prod MeasurableSet.univ)
    (hf.mono_set (hU ▸ Set.subset_union_left)) (hf.mono_set (hU ▸ Set.subset_union_right))]
  ring

/-- An integral over `(0, t]` minus that over `(0, s]` is the integral over `(s, t]`, for
`0 ≤ s ≤ t` and an integrand integrable on `(0, t]`. -/
theorem setIntegral_Ioc_sub {g : ℝ → ℝ} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hg : IntegrableOn g (Set.Ioc (0 : ℝ) t)) :
    (∫ r in Set.Ioc (0 : ℝ) t, g r) - ∫ r in Set.Ioc (0 : ℝ) s, g r = ∫ r in Set.Ioc s t, g r := by
  have hU : Set.Ioc (0 : ℝ) t = Set.Ioc (0 : ℝ) s ∪ Set.Ioc s t :=
    (Set.Ioc_union_Ioc_eq_Ioc hs hst).symm
  have hD : Disjoint (Set.Ioc (0 : ℝ) s) (Set.Ioc s t) := Set.Ioc_disjoint_Ioc_of_le le_rfl
  have h := setIntegral_union (μ := volume) (f := g) hD measurableSet_Ioc
    (hg.mono_set (Set.Ioc_subset_Ioc_right hst)) (hg.mono_set (Set.Ioc_subset_Ioc_left hs))
  rw [← hU] at h
  linarith

/-- **The increments of the pathwise compensated integral are orthogonal to the past**: for
`0 ≤ s ≤ t ≤ T` and `A ∈ ℱ_s`, `𝔼[1_A M_t] = 𝔼[1_A M_s]`. -/
theorem setIntegral_pathwiseCompensated_eq (hℱN : Poisson.IsPoissonFiltration N ℱ)
    (hψ : Measurable[Probability.markedPredictableSigma ℱ ν] ψ) (hψ0 : ∀ p, 0 ≤ ψ p)
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (ψ (ω, s, e)) ∂ν ∂volume ∂P
      < ⊤) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) {A : Set Ω}
    (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, pathwiseCompensated N ψ t ω ∂P = ∫ ω in A, pathwiseCompensated N ψ s ω ∂P := by
  classical
  have hψm : Measurable ψ := hψ.mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hfint := (lintegral_compensator_mono (P := P) (ν := ν) (ψ := ψ) htT).trans_lt hfin
  set S : Set (Ω × ℝ × E) := A ×ˢ (Set.Ioc s t ×ˢ Set.univ) with hSdef
  have hSm : MeasurableSet[Probability.markedPredictableSigma ℱ ν] S := by
    have h1 := Probability.measurableSet_markedPredictableSigma_prod_Ioi (ν := ν) hs hA
    have h2 := Probability.measurableSet_markedPredictableSigma_prod_Ioi (ν := ν) (ℱ := ℱ)
      (hs.trans hst) (A := Set.univ) MeasurableSet.univ
    have e : S = (A ×ˢ (Set.Ioi s ×ˢ Set.univ)) \ (Set.univ ×ˢ (Set.Ioi t ×ˢ Set.univ)) := by
      ext ⟨ω, r, x⟩
      simp only [hSdef, Set.mem_prod, Set.mem_Ioc, Set.mem_univ, and_true, Set.mem_sdiff,
        Set.mem_Ioi, true_and, not_lt]
      tauto
    rw [e]
    exact h1.diff h2
  set ψA : Ω × ℝ × E → ℝ := S.indicator ψ with hψAdef
  have hψA : Measurable[Probability.markedPredictableSigma ℱ ν] ψA := by
    letI : MeasurableSpace (Ω × ℝ × E) := Probability.markedPredictableSigma ℱ ν
    exact hψ.indicator hSm
  have hfinA : ∫⁻ ω, (∫⁻ r in Set.Ioc (0 : ℝ) t, ∫⁻ e, ‖ψA (ω, r, e)‖ₑ ∂ν) ∂P < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun r =>
      lintegral_mono fun e => ?_) hfint
    rw [hψAdef]
    by_cases hp : (ω, r, e) ∈ S
    · rw [Set.indicator_of_mem hp, Real.enorm_of_nonneg (hψ0 _)]
    · rw [Set.indicator_of_notMem hp, enorm_zero]
      exact zero_le
  have hz := integral_compensated_eq_zero hℱN t hψA hfinA
  -- almost surely the integrands are integrable on `(0, t]`
  have hNae := (aemeasurable_and_lintegral_compensation hℱN t
    (ψ := fun x => ENNReal.ofReal (ψ x)) (ENNReal.measurable_ofReal.comp hψ))
  have hNfin : ∀ᵐ ω ∂P,
      ∫⁻ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ, ENNReal.ofReal (ψ (ω, p)) ∂(N.N ω) < ⊤ :=
    ae_lt_top' hNae.1 (by rw [hNae.2.2]; exact hfint.ne)
  have hCfin : ∀ᵐ ω ∂P,
      ∫⁻ r in Set.Ioc (0 : ℝ) t, ∫⁻ e, ENNReal.ofReal (ψ (ω, r, e)) ∂ν < ⊤ :=
    ae_lt_top' hNae.2.1 hfint.ne
  have hpt : ∀ᵐ ω ∂P, (∫ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ, ψA (ω, p) ∂(N.N ω))
      - ∫ r in Set.Ioc (0 : ℝ) t, ∫ e, ψA (ω, r, e) ∂ν
      = A.indicator (fun ω => pathwiseCompensated N ψ t ω - pathwiseCompensated N ψ s ω) ω := by
    filter_upwards [hNfin, hCfin] with ω h1 h2
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      have hsec := measurable_section_of_markedPredictable hψ ω
      have hI1 : IntegrableOn (fun p => ψ (ω, p)) (Set.Ioc (0 : ℝ) t ×ˢ Set.univ) (N.N ω) := by
        refine ⟨hsec.aestronglyMeasurable, ?_⟩
        rw [HasFiniteIntegral]
        refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun p => ?_)) h1
        exact Real.enorm_of_nonneg (hψ0 _)
      have hgm : StronglyMeasurable fun r => ∫ e, ψ (ω, r, e) ∂ν :=
        (hsec.stronglyMeasurable).integral_prod_right' (f := fun q : ℝ × E => ψ (ω, q))
      have hI2 : IntegrableOn (fun r => ∫ e, ψ (ω, r, e) ∂ν) (Set.Ioc (0 : ℝ) t) := by
        refine ⟨hgm.aestronglyMeasurable, ?_⟩
        rw [HasFiniteIntegral]
        refine lt_of_le_of_lt (lintegral_mono fun r => ?_) h2
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun e => ?_))
        exact Real.enorm_of_nonneg (hψ0 _)
      have hA1 : (fun p : ℝ × E => ψA (ω, p))
          = (Set.Ioc s t ×ˢ (Set.univ : Set E)).indicator fun p => ψ (ω, p) := by
        funext p
        by_cases hp : p ∈ Set.Ioc s t ×ˢ (Set.univ : Set E)
        · rw [Set.indicator_of_mem hp, hψAdef, Set.indicator_of_mem (show (ω, p) ∈ S from
            ⟨hω, hp⟩)]
        · rw [Set.indicator_of_notMem hp, hψAdef, Set.indicator_of_notMem (show (ω, p) ∉ S from
            fun h => hp h.2)]
      have hA2 : (fun r => ∫ e, ψA (ω, r, e) ∂ν)
          = (Set.Ioc s t).indicator fun r => ∫ e, ψ (ω, r, e) ∂ν := by
        funext r
        by_cases hr : r ∈ Set.Ioc s t
        · rw [Set.indicator_of_mem hr]
          refine integral_congr_ae (ae_of_all _ fun e => ?_)
          change S.indicator ψ (ω, r, e) = ψ (ω, r, e)
          rw [Set.indicator_of_mem (show (ω, r, e) ∈ S from ⟨hω, hr, Set.mem_univ _⟩)]
        · rw [Set.indicator_of_notMem hr]
          have h0 : ∀ e, ψA (ω, r, e) = 0 := fun e => by
            rw [hψAdef, Set.indicator_of_notMem (show (ω, r, e) ∉ S from fun h => hr h.2.1)]
          simp only [h0, integral_zero]
      have hsub1 : Set.Ioc (0 : ℝ) t ×ˢ (Set.univ : Set E) ∩ Set.Ioc s t ×ˢ Set.univ
          = Set.Ioc s t ×ˢ Set.univ := by
        rw [Set.prod_inter_prod, Set.inter_univ,
          Set.inter_eq_right.mpr (Set.Ioc_subset_Ioc_left hs)]
      have hsub2 : Set.Ioc (0 : ℝ) t ∩ Set.Ioc s t = Set.Ioc s t :=
        Set.inter_eq_right.mpr (Set.Ioc_subset_Ioc_left hs)
      have e1 : ∫ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ, ψA (ω, p) ∂(N.N ω)
          = ∫ p in Set.Ioc s t ×ˢ Set.univ, ψ (ω, p) ∂(N.N ω) := by
        change ∫ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ, (fun p : ℝ × E => ψA (ω, p)) p ∂(N.N ω) = _
        rw [hA1, setIntegral_indicator (measurableSet_Ioc.prod MeasurableSet.univ), hsub1]
      have e2 : ∫ r in Set.Ioc (0 : ℝ) t, ∫ e, ψA (ω, r, e) ∂ν
          = ∫ r in Set.Ioc s t, ∫ e, ψ (ω, r, e) ∂ν := by
        change ∫ r in Set.Ioc (0 : ℝ) t, (fun r => ∫ e, ψA (ω, r, e) ∂ν) r = _
        rw [hA2, setIntegral_indicator measurableSet_Ioc, hsub2]
      have k1 := setIntegral_Ioc_prod_sub hs hst hI1
      have k2 := setIntegral_Ioc_sub hs hst hI2
      rw [e1, e2, ← k1, ← k2]
      simp only [pathwiseCompensated]
      ring
    · rw [Set.indicator_of_notMem hω]
      have h0 : ∀ r e, ψA (ω, r, e) = 0 := fun r e => by
        rw [hψAdef, Set.indicator_of_notMem (show (ω, r, e) ∉ S from fun h => hω h.1)]
      simp only [h0, integral_zero, sub_zero]
  have hA' : MeasurableSet A := ℱ.le s A hA
  have hint := (integral_congr_ae hpt).symm.trans hz
  rw [integral_indicator hA', integral_sub
    ((integrable_pathwiseCompensated hℱN hψ hψ0 hfin htT).integrableOn)
    ((integrable_pathwiseCompensated hℱN hψ hψ0 hfin (hst.trans htT)).integrableOn)] at hint
  linarith

/-- **The pathwise compensated integral is a martingale** on `[0, T]`: `𝔼[M_t | ℱ_s] = M_s`
almost surely for `0 ≤ s ≤ t ≤ T`. -/
theorem condExp_pathwiseCompensated (hℱN : Poisson.IsPoissonFiltration N ℱ)
    (hψ : Measurable[Probability.markedPredictableSigma ℱ ν] ψ) (hψ0 : ∀ p, 0 ≤ ψ p)
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (ψ (ω, s, e)) ∂ν ∂volume ∂P
      < ⊤) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    P[pathwiseCompensated N ψ t | ℱ s] =ᵐ[P] pathwiseCompensated N ψ s :=
  (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s)
    (integrable_pathwiseCompensated hℱN hψ hψ0 hfin htT)
    (fun _ _ _ => (integrable_pathwiseCompensated hℱN hψ hψ0 hfin (hst.trans htT)).integrableOn)
    (fun _ hA _ => (setIntegral_pathwiseCompensated_eq hℱN hψ hψ0 hfin hs hst htT hA).symm)
    (aestronglyMeasurable_pathwiseCompensated hℱN hψ hψ0 s)).symm

end Martingale

end Dissertation.WellPosedness.BrownianPoisson
