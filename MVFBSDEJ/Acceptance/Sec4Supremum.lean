/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec4Supremum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The supremum criterion of Section 4 of the well-posedness paper: proof

## Main statements

* `MVFBSDEJ.Acceptance.sec4_supremum_criterion` — along a localising sequence `τ_k`,
  `𝔼[M^{τ_k}_t 1_{τ_k > 0}] = 𝔼[M^{τ_k}_s 1_{τ_k > 0}]`; as `k → ∞` the stopped values tend
  to `M_t` and `M_s` almost surely, under the integrable bound `sup_{u ≤ T} |M_u|`, so dominated
  convergence gives `𝔼 M_t = 𝔼 M_s`.
* `MVFBSDEJ.Acceptance.sec4_supremum_criterion_hypotheses` — the single-jump martingale
  `M_t = ξ 1_{t ≥ 1}` of a fair sign `ξ` meets the hypotheses on `[0, 2]`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace MVFBSDEJ.Acceptance

universe u

section RunningSup

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {M : ℝ≥0 → Ω → ℝ}

/-- For a function right-continuous at every time and a dense set `D`, the supremum over
`[0, T]` is the supremum over `insert T (D ∩ [0, T])`. -/
theorem iSup_le_eq_biSup_insert_inter {f : ℝ≥0 → ℝ≥0∞} {D : Set ℝ≥0} (hD : Dense D)
    (T : ℝ≥0) (hf : ∀ t, ContinuousWithinAt f (Set.Ici t) t) :
    ⨆ u ≤ T, f u = ⨆ q ∈ insert T (D ∩ Set.Iic T), f q := by
  apply le_antisymm
  · refine iSup₂_le fun u hu => ?_
    rcases hu.lt_or_eq with hlt | heq
    · have hcl : u ∈ closure (Set.Ioo u T ∩ D) := by
        have h1 : u ∈ closure (Set.Ioo u T) := by
          rw [closure_Ioo hlt.ne]
          exact ⟨le_rfl, hu⟩
        exact closure_minimal (hD.open_subset_closure_inter isOpen_Ioo) isClosed_closure h1
      have hcw : ContinuousWithinAt f (Set.Ioo u T ∩ D) u :=
        (hf u).mono fun v hv => Set.mem_Ici.2 hv.1.1.le
      have hmaps : Set.MapsTo f (Set.Ioo u T ∩ D)
          (Set.Iic (⨆ q ∈ insert T (D ∩ Set.Iic T), f q)) := fun v hv =>
        le_iSup₂_of_le (f := fun q (_ : q ∈ insert T (D ∩ Set.Iic T)) => f q) v
          (Set.mem_insert_of_mem _ ⟨hv.2, hv.1.2.le⟩) le_rfl
      have := hcw.mem_closure hcl hmaps
      rwa [isClosed_Iic.closure_eq] at this
    · rw [heq]
      exact le_iSup₂_of_le (f := fun q (_ : q ∈ insert T (D ∩ Set.Iic T)) => f q) T
        (Set.mem_insert _ _) le_rfl
  · refine iSup₂_le fun q hq => ?_
    have hqT : q ≤ T := hq.elim (fun h => h.le) fun h => h.2
    exact le_iSup₂_of_le (f := fun u (_ : u ≤ T) => f u) q hqT le_rfl

/-- The running supremum `sup_{u ≤ T} |M_u|` of an adapted process with almost surely
right-continuous paths is almost everywhere measurable. -/
theorem aemeasurable_iSup_le_enorm (hM : Adapted 𝓕 M)
    (hrc : ∀ᵐ ω ∂P, ∀ t, ContinuousWithinAt (fun u => M u ω) (Set.Ici t) t) (T : ℝ≥0) :
    AEMeasurable (fun ω => ⨆ u ≤ T, ‖M u ω‖ₑ) P := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  refine ⟨fun ω => ⨆ q ∈ insert T (D ∩ Set.Iic T), ‖M q ω‖ₑ, ?_, ?_⟩
  · exact Measurable.biSup _ ((hDc.mono Set.inter_subset_left).insert T)
      fun q _ => (hM.measurable (i := q)).enorm
  · filter_upwards [hrc] with ω hω
    exact iSup_le_eq_biSup_insert_inter hD T fun t =>
      continuous_enorm.continuousAt.comp_continuousWithinAt (hω t)

end RunningSup

/-- The supremum criterion of §4. -/
theorem sec4_supremum_criterion : PaperSpec.sec4_supremum_criterion.{u} := by
  intro Ω mΩ P _ 𝓕 M T hM hcad hloc hsup
  set S : Ω → ℝ≥0∞ := fun ω => ⨆ u ≤ T, ‖M u ω‖ₑ with hS_def
  have hSm : AEMeasurable S P :=
    aemeasurable_iSup_le_enorm hM (hcad.mono fun ω hω t => (hω t).1) T
  have hSint : Integrable (fun ω => (S ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hSm hsup.ne
  have hbound : ∀ᵐ ω ∂P, ∀ u ≤ T, ‖M u ω‖ ≤ (S ω).toReal := by
    filter_upwards [ae_lt_top' hSm hsup.ne] with ω hω u hu
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono hω.ne
      (le_iSup₂_of_le (f := fun u (_ : u ≤ T) => ‖M u ω‖ₑ) u hu le_rfl)
  have hint : ∀ t ≤ T, Integrable (M t) P := fun t ht =>
    hSint.mono' (hM.measurable (i := t)).aestronglyMeasurable (hbound.mono fun ω hω => hω t ht)
  obtain ⟨τ, hτ, hmart⟩ := hloc
  set X : ℕ → ℝ≥0 → Ω → ℝ := fun n =>
    stoppedProcess (fun i => {ω | ⊥ < τ n ω}.indicator (M i)) (τ n) with hX_def
  have hlim : ∀ t ≤ T, Tendsto (fun n => ∫ ω, X n t ω ∂P) atTop (𝓝 (∫ ω, M t ω ∂P)) := by
    intro t ht
    refine tendsto_integral_of_dominated_convergence (fun ω => (S ω).toReal)
      (fun n => ((hmart n).integrable t).aestronglyMeasurable) hSint (fun n => ?_) ?_
    · filter_upwards [hbound] with ω hω
      simp only [hX_def]
      rw [stoppedProcess_indicator_comm]
      refine (norm_indicator_le_norm_self _ _).trans ?_
      rcases le_total (t : WithTop ℝ≥0) (τ n ω) with h | h
      · rw [stoppedProcess_eq_of_le h]
        exact hω t ht
      · rw [stoppedProcess_eq_of_ge h]
        obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (h.trans_lt (WithTop.coe_lt_top t)).ne
        rw [← hr] at h ⊢
        rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
        exact hω r ((WithTop.coe_le_coe.mp h).trans ht)
    · filter_upwards [hτ.tendsto_top] with ω hω
      have hev : ∀ᶠ n in atTop, τ n ω ∈ Set.Ioi (t : WithTop ℝ≥0) :=
        hω.eventually_mem (Ioi_mem_nhds (WithTop.coe_lt_top t))
      refine tendsto_const_nhds.congr' (hev.mono fun n hn => ?_)
      simp only [hX_def]
      have hn' : (t : WithTop ℝ≥0) < τ n ω := Set.mem_Ioi.mp hn
      have hpos : ω ∈ {ω | ⊥ < τ n ω} := show ⊥ < τ n ω from bot_le.trans_lt hn'
      rw [stoppedProcess_eq_of_le hn'.le, Set.indicator_of_mem hpos]
  have heq : ∀ s t, s ≤ t → ∀ n, ∫ ω, X n t ω ∂P = ∫ ω, X n s ω ∂P := by
    intro s t hst n
    have := (hmart n).setIntegral_eq hst MeasurableSet.univ
    simpa only [Measure.restrict_univ] using this.symm
  refine ⟨hint, fun s t hst htT => ?_⟩
  have hts : ∫ ω, M t ω ∂P = ∫ ω, M s ω ∂P :=
    tendsto_nhds_unique (hlim t htT)
      ((hlim s (hst.trans htT)).congr fun n => (heq s t hst n).symm)
  rw [integral_sub (hint t htT) (hint s (hst.trans htT)), hts, sub_self]

section Witness

/-- The fair-coin law on `Bool`. -/
private noncomputable def coinLaw : Measure Bool :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

private instance : IsProbabilityMeasure coinLaw :=
  ⟨by simp [coinLaw, ENNReal.inv_two_add_inv_two]⟩

/-- The filtration on `Bool` that is trivial before time `1` and full from time `1` on. -/
private noncomputable def coinFiltration :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace Bool) where
  seq t := if t < 1 then ⊥ else inferInstance
  mono' s t hst := by
    dsimp only
    split_ifs with hs ht ht
    · exact le_rfl
    · exact bot_le
    · exact absurd (hst.trans_lt ht) hs
    · exact le_rfl
  le' t := by
    split_ifs
    · exact bot_le
    · exact le_rfl

/-- The single-jump process `M_t = ξ 1_{t ≥ 1}` of the fair sign `ξ(true) = 1`,
`ξ(false) = -1`. -/
private noncomputable def coinJump (t : ℝ≥0) (ω : Bool) : ℝ :=
  if 1 ≤ t then (if ω then 1 else -1) else 0

private theorem coinJump_of_lt {t : ℝ≥0} (ht : t < 1) : coinJump t = fun _ => 0 :=
  funext fun ω => by simp [coinJump, not_le.2 ht]

private theorem integral_coinJump (t : ℝ≥0) : ∫ ω, coinJump t ω ∂coinLaw = 0 := by
  rw [coinLaw, integral_smul_measure, integral_add_measure (Integrable.of_finite)
    (Integrable.of_finite), integral_dirac, integral_dirac]
  by_cases h : 1 ≤ t <;> simp [coinJump, h]

private theorem martingale_coinJump : Martingale coinJump coinFiltration coinLaw := by
  refine ⟨fun t => ?_, fun i j hij => ?_⟩
  · by_cases ht : t < 1
    · rw [coinJump_of_lt ht]
      exact stronglyMeasurable_const
    · have hF : coinFiltration t = (inferInstance : MeasurableSpace Bool) := by
        simp [coinFiltration, ht]
      rw [hF]
      exact (measurable_of_finite _).stronglyMeasurable
  · by_cases hi : i < 1
    · have hF : coinFiltration i = ⊥ := by simp [coinFiltration, hi]
      rw [hF, condExp_bot, integral_coinJump, coinJump_of_lt hi]
    · have hF : coinFiltration i = (inferInstance : MeasurableSpace Bool) := by
        simp [coinFiltration, hi]
      have hj : ¬ j < 1 := fun h => hi (hij.trans_lt h)
      have hji : coinJump j = coinJump i := funext fun ω => by
        simp [coinJump, not_lt.1 hi, not_lt.1 hj]
      rw [hF, hji, condExp_of_stronglyMeasurable le_rfl
        (measurable_of_finite _).stronglyMeasurable Integrable.of_finite]

private theorem cadlag_coinJump (ω : Bool) (t : ℝ≥0) :
    ContinuousWithinAt (fun u => coinJump u ω) (Set.Ici t) t
      ∧ ∃ l : ℝ, Tendsto (fun u => coinJump u ω) (𝓝[<] t) (𝓝 l) := by
  set c : ℝ := if ω then 1 else -1 with hc
  have hval : ∀ u : ℝ≥0, 1 ≤ u → coinJump u ω = c := fun u hu => by simp [coinJump, hu, hc]
  have hzero : ∀ u : ℝ≥0, u < 1 → coinJump u ω = 0 := fun u hu => by
    simp [coinJump, not_le.2 hu]
  refine ⟨?_, ?_⟩
  · rcases le_or_gt 1 t with ht | ht
    · exact (continuousWithinAt_const (b := c)).congr
        (fun u hu => hval u (ht.trans hu)) (hval t ht)
    · refine (continuousAt_const (y := (0 : ℝ)).congr ?_).continuousWithinAt
      exact (eventually_lt_nhds ht).mono fun u hu => (hzero u hu).symm
  · rcases le_or_gt t 1 with ht | ht
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      exact eventually_nhdsWithin_of_forall fun u hu => (hzero u (lt_of_lt_of_le hu ht)).symm
    · refine ⟨c, tendsto_const_nhds.congr' ?_⟩
      exact ((eventually_gt_nhds ht).filter_mono nhdsWithin_le_nhds).mono fun u hu =>
        (hval u (le_of_lt hu)).symm

/-- **The hypotheses of the supremum criterion can be met.** On `Bool` with the fair-coin law and
the filtration trivial before time `1` and full from time `1`, the process `M_t = ξ 1_{t ≥ 1}`,
`ξ = ±1`, is adapted, càdlàg and a local martingale, with `𝔼 sup_{u ≤ 2} |M_u| < ∞`, and
`M_2 ≠ M_0` on every path. -/
theorem sec4_supremum_criterion_hypotheses :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0),
      Adapted 𝓕 M
      ∧ (∀ᵐ ω ∂P, ∀ t : ℝ≥0, ContinuousWithinAt (fun u => M u ω) (Set.Ici t) t
        ∧ ∃ l : ℝ, Tendsto (fun u => M u ω) (𝓝[<] t) (𝓝 l))
      ∧ Locally (fun X => Martingale X 𝓕 P) 𝓕 M P
      ∧ ∫⁻ ω, ⨆ u ≤ T, ‖M u ω‖ₑ ∂P < ∞
      ∧ ∀ ω, M T ω ≠ M 0 ω := by
  have hle : ∀ u ω, ‖coinJump u ω‖ₑ ≤ 1 := fun u ω => by
    unfold coinJump
    split_ifs <;> simp
  refine ⟨Bool, inferInstance, coinLaw, inferInstance, coinFiltration, coinJump, 2,
    fun t => (martingale_coinJump.stronglyAdapted t).measurable,
    ae_of_all _ fun ω t => cadlag_coinJump ω t, Locally.of_prop martingale_coinJump, ?_, ?_⟩
  · refine (lintegral_mono fun ω => iSup₂_le fun u _ => hle u ω).trans_lt ?_
    simp
  · intro ω
    cases ω <;> norm_num [coinJump]

end Witness

end MVFBSDEJ.Acceptance
