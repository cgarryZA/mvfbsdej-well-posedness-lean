/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.LawFlowPredictable
import MVFBSDEJ.WellPosedness.System.JumpLeftEnergy
import MVFBSDEJ.WellPosedness.Martingale.LocalWeight

/-!
# A predictable representative of the jump coefficient at the left limits

The jump coefficient of (1.1) is evaluated at the predictable tuple
`Θ⁻_s = (X_{s−}, Y_{s−}, Z_s, U_s)` and its law. For `X, Y` adapted on `[0, T]` with left limits on
`(0, T]` and `Z, U` predictable, the tuple `Θ⁻`, cut to the times of `(0, T]`, is a predictable
field in the tuple space `H`; composed with a jointly measurable function of the time, the tuple and
the mark, and cut to the positive times, it gives a marked predictable integrand. With the canonical
representative `MVFBSDEJ.Law.lpRep` of the elements of `L²(ν; ℝⁿ)`, this gives a marked
predictable representative of `MVFBSDEJ.WellPosedness.Existence.coeffJump` at `Θ⁻`, equal to it
at every time of `(0, T]`.

## Main statements

* `markedPredictable_ite_comp` — a jointly measurable function of the time, a predictable state
  in any measurable space and the mark, cut to the positive times, is marked predictable.
* `measurable_predictableSigma_tupleAt_leftLim_Ioc` — the left-limit tuple cut to `(0, T]` is
  predictable.
* `exists_markedPredictable_coeffJump_leftLim` — a marked predictable integrand equal to the jump
  process of `MVFBSDEJ.WellPosedness.Existence.coeffJump` at `Θ⁻` at every time of `(0, T]` and
  vanishing off `(0, T]`.
* `ae_markedEnergyMeasure_mem_Ioc` — almost every point of `Ω × [0, T] × E` has its time in
  `(0, T]`.
-/

open MeasureTheory Filter Topology LevyStochCalc.Probability MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.Existence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {E : Type*} [MeasurableSpace E] {ν : Measure E}

/-! ### Composition with a predictable state -/

/-- **A jointly measurable function of the time, a predictable state and the mark is marked
predictable once it is cut to the positive times**, for a state in any measurable space. -/
theorem markedPredictable_ite_comp [SigmaFinite ν] {ℱ : Filtration ℝ mΩ} {S : Type*}
    [MeasurableSpace S] {Λ : ℝ → Ω → S}
    (hΛ : Measurable[predictableSigma ℱ] fun p : ℝ × Ω => Λ p.1 p.2) {f : ℝ → S → E → ℝ}
    (hf : Measurable fun q : ℝ × S × E => f q.1 q.2.1 q.2.2) :
    MarkedPredictable ℱ ν fun (ω : Ω) (s : ℝ) (e : E) => if 0 < s then f s (Λ s ω) e else 0 := by
  classical
  have hpos := measurableSet_markedPredictableSigma_pos (Ω := Ω) (E := E) ℱ ν
  have h1 : Measurable[traceSigma (markedPredictableSigma ℱ ν) hpos]
      fun p : Ω × ℝ × E => p.2.1 := by
    intro D hD
    have hrw : ((fun p : Ω × ℝ × E => p.2.1) ⁻¹' D) ∩ {p : Ω × ℝ × E | 0 < p.2.1}
        = (Set.univ : Set Ω) ×ˢ ((D ×ˢ (Set.univ : Set E))
            ∩ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E)) := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod,
        Set.mem_univ, true_and, and_true, Set.mem_Ioi]
    change MeasurableSet[markedPredictableSigma ℱ ν] (_ ∩ _)
    rw [hrw]
    exact measurableSet_markedPredictableSigma_univ_prod_pos (hD.prod MeasurableSet.univ)
  have h2 : Measurable[traceSigma (markedPredictableSigma ℱ ν) hpos]
      fun p : Ω × ℝ × E => p.2.2 := by
    intro D hD
    have hrw : ((fun p : Ω × ℝ × E => p.2.2) ⁻¹' D) ∩ {p : Ω × ℝ × E | 0 < p.2.1}
        = (Set.univ : Set Ω) ×ˢ (((Set.univ : Set ℝ) ×ˢ D)
            ∩ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E)) := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_prod,
        Set.mem_univ, true_and, and_true, Set.mem_Ioi]
    change MeasurableSet[markedPredictableSigma ℱ ν] (_ ∩ _)
    rw [hrw]
    exact measurableSet_markedPredictableSigma_univ_prod_pos (MeasurableSet.univ.prod hD)
  have h3 : Measurable[traceSigma (markedPredictableSigma ℱ ν) hpos]
      fun p : Ω × ℝ × E => Λ p.2.1 p.1 := fun D hD =>
    measurableSet_markedPredictableSigma_of_predictableSigma (E := E) (ν := ν) (hΛ hD)
  have hcomp : Measurable[traceSigma (markedPredictableSigma ℱ ν) hpos]
      fun p : Ω × ℝ × E => f p.2.1 (Λ p.2.1 p.1) p.2.2 :=
    hf.comp (h1.prodMk (h3.prodMk h2))
  intro V hV
  have hkey : MeasurableSet[markedPredictableSigma ℱ ν]
      (((fun p : Ω × ℝ × E => f p.2.1 (Λ p.2.1 p.1) p.2.2) ⁻¹' V)
        ∩ {p : Ω × ℝ × E | 0 < p.2.1}) := hcomp hV
  change MeasurableSet[markedPredictableSigma ℱ ν]
    ((fun p : Ω × ℝ × E => if 0 < p.2.1 then f p.2.1 (Λ p.2.1 p.1) p.2.2 else 0) ⁻¹' V)
  by_cases h0 : (0 : ℝ) ∈ V
  · have hrw : (fun p : Ω × ℝ × E =>
        if 0 < p.2.1 then f p.2.1 (Λ p.2.1 p.1) p.2.2 else 0) ⁻¹' V
        = (((fun p : Ω × ℝ × E => f p.2.1 (Λ p.2.1 p.1) p.2.2) ⁻¹' V)
            ∩ {p : Ω × ℝ × E | 0 < p.2.1}) ∪ {p : Ω × ℝ × E | 0 < p.2.1}ᶜ := by
      ext p
      by_cases hp : 0 < p.2.1 <;> simp [hp, h0]
    rw [hrw]
    exact hkey.union hpos.compl
  · have hrw : (fun p : Ω × ℝ × E =>
        if 0 < p.2.1 then f p.2.1 (Λ p.2.1 p.1) p.2.2 else 0) ⁻¹' V
        = ((fun p : Ω × ℝ × E => f p.2.1 (Λ p.2.1 p.1) p.2.2) ⁻¹' V)
            ∩ {p : Ω × ℝ × E | 0 < p.2.1} := by
      ext p
      by_cases hp : 0 < p.2.1 <;> simp [hp, h0]
    rw [hrw]
    exact hkey

/-! ### The left-limit tuple on `(0, T]` -/

/-- The left limits of a family of processes at the times of `(0, T]`, and `0` at other times. -/
noncomputable def leftLimIoc {ι : Type*} (T : ℝ) (X : ι → ℝ → Ω → ℝ) : ι → ℝ → Ω → ℝ :=
  fun i s ω => if s ∈ Set.Ioc (0 : ℝ) T then leftLimProc X i s ω else 0

/-- On `(0, T]` the cut left limits are the left limits. -/
theorem leftLimIoc_of_mem {ι : Type*} {T : ℝ} (X : ι → ℝ → Ω → ℝ) {s : ℝ}
    (hs : s ∈ Set.Ioc (0 : ℝ) T) (i : ι) (ω : Ω) : leftLimIoc T X i s ω = leftLimProc X i s ω := by
  simp only [leftLimIoc, if_pos hs]

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-- **The left-limit tuple cut to `(0, T]` is predictable**: for `X, Y` adapted on `[0, T]` with
left limits on `(0, T]`, `Z` predictable and `U` marked predictable,
`(s, ω) ↦ (X_{s−}, Y_{s−}, Z_s, U_s)(ω)`, the left limits cut to `(0, T]`, is measurable into the
tuple space for the predictable σ-algebra. -/
theorem measurable_predictableSigma_tupleAt_leftLim_Ioc {ℱ : Filtration ℝ mΩ} {T : ℝ}
    {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
    {U : Fin m → ℝ → Ω → E → ℝ}
    (hXad : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (X i t))
    (hXl : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 l))
    (hYad : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (Y k t))
    (hYl : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l))
    (hZ : ∀ k j, Predictable ℱ fun ω s => Z k s ω j)
    (hU : ∀ k, MarkedPredictable ℱ ν fun ω s e => U k s ω e) :
    Measurable[predictableSigma ℱ] fun p : ℝ × Ω =>
      tupleAt ν (leftLimIoc T X) (leftLimIoc T Y) Z U p.1 p.2 := by
  letI : MeasurableSpace (ℝ × Ω) := predictableSigma ℱ
  have hX : ∀ i, Measurable fun p : ℝ × Ω => leftLimIoc T X i p.1 p.2 := fun i =>
    (MVFBSDEJ.WellPosedness.Martingale.predictable_leftLim_Ioc (hXad i) (hXl i)).measurable
  have hY : ∀ k, Measurable fun p : ℝ × Ω => leftLimIoc T Y k p.1 p.2 := fun k =>
    (MVFBSDEJ.WellPosedness.Martingale.predictable_leftLim_Ioc (hYad k) (hYl k)).measurable
  have hZm : ∀ k j, Measurable fun p : ℝ × Ω => Z k p.1 p.2 j := fun k j => (hZ k j).measurable
  have hUm : StronglyMeasurable fun p : ℝ × Ω => uLift ν fun e k => U k p.1 p.2 e :=
    predictable_uLift_of_markedPredictable hU
  exact ((WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr hX)).prodMk
    (((WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr hY)).prodMk
      (((WithLp.measurable_toLp 2 _).comp
        (measurable_pi_iff.mpr fun q : Fin m × Fin d => hZm q.1 q.2)).prodMk hUm.measurable))

/-- **A marked predictable representative of the jump coefficient at the left limits.** For
coefficients with the joint measurability (2.3), `X, Y` adapted on `[0, T]` with left limits on
`(0, T]`, `Z` predictable and `U` marked predictable, there is, for each coordinate, a marked
predictable integrand equal at every time of `(0, T]` to the jump process of `coeffJump` at the
left-limit tuple `Θ⁻`, the canonical representative of `h(s, Θ⁻_s, ·, μ⁻_s)`, and vanishing at the
other times. -/
theorem exists_markedPredictable_coeffJump_leftLim [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹_›}
    {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ} {C : Coeffs ν n m d} (hC : CoeffBorel T C)
    {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
    {U : Fin m → ℝ → Ω → E → ℝ}
    (hXad : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (X i t))
    (hXl : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 l))
    (hYad : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (Y k t))
    (hYl : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l))
    (hZ : ∀ k j, Predictable ℱ fun ω s => Z k s ω j)
    (hU : ∀ k, MarkedPredictable ℱ ν fun ω s e => U k s ω e) :
    ∃ H : Fin n → Ω → ℝ → E → ℝ, (∀ i, MarkedPredictable ℱ ν (H i))
      ∧ (∀ i ω s e, s ∈ Set.Ioc (0 : ℝ) T →
          H i ω s e = jumpProc T (coeffJump P T C (leftLimProc X) (leftLimProc Y) Z U) i s ω e)
      ∧ ∀ i ω s e, s ∉ Set.Ioc (0 : ℝ) T → H i ω s e = 0 := by
  classical
  set Λ : ℝ → Ω → TupleH ν n m d := fun s ω => tupleAt ν (leftLimIoc T X) (leftLimIoc T Y) Z U s ω
    with hΛdef
  have hΛ : Measurable[predictableSigma ℱ] fun p : ℝ × Ω => Λ p.1 p.2 :=
    measurable_predictableSigma_tupleAt_leftLim_Ioc hXad hXl hYad hYl hZ hU
  have hΛm : Measurable (Function.uncurry fun ω s => Λ s ω) :=
    (hΛ.mono (LevyStochCalc.Brownian.Ito.predictableSigma_le ℱ) le_rfl).comp measurable_swap
  set μ : ℝ → P2 (TupleH ν n m d) := fun s => lawP2 P (Λ s) with hμdef
  have hμ : Measurable μ := measurable_lawP2_flow (Θ := fun ω s => Λ s ω) hΛm
  have hjm : Measurable fun p : ℝ × TupleH ν n m d =>
      (Set.Icc (0 : ℝ) T).indicator (fun t => C.h t p.2 (μ t)) p.1 :=
    measurable_cutoff_along hC.h_meas hμ measurable_id rfl
  set F : Fin n → ℝ → TupleH ν n m d → E → ℝ := fun i s θ e =>
    if s ≤ T then lpRep ν (EuclideanSpace ℝ (Fin n))
      ((Set.Icc (0 : ℝ) T).indicator (fun t => C.h t θ (μ t)) s, e) i else 0 with hFdef
  have hF : ∀ i, Measurable fun q : ℝ × TupleH ν n m d × E => F i q.1 q.2.1 q.2.2 := by
    intro i
    have hproj : Measurable fun v : EuclideanSpace ℝ (Fin n) => v i :=
      (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.measurable
    have hG : Measurable fun q : ℝ × TupleH ν n m d × E =>
        lpRep ν (EuclideanSpace ℝ (Fin n))
          ((Set.Icc (0 : ℝ) T).indicator (fun t => C.h t q.2.1 (μ t)) q.1, q.2.2) i :=
      hproj.comp (stronglyMeasurable_lpRep.measurable.comp
        ((hjm.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
    exact Measurable.ite (measurableSet_le measurable_fst measurable_const) hG measurable_const
  refine ⟨fun i ω s e => if 0 < s then F i s (Λ s ω) e else 0,
    fun i => markedPredictable_ite_comp hΛ (hF i), fun i ω s e hs => ?_, fun i ω s e hs => ?_⟩
  · have hsI : s ∈ Set.Icc (0 : ℝ) T := Set.Ioc_subset_Icc_self hs
    have hΛs : Λ s = tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s := by
      funext ω'
      simp only [hΛdef, tupleAt, leftLimIoc_of_mem X hs, leftLimIoc_of_mem Y hs]
    simp only [if_pos hs.1, hFdef, if_pos hs.2, jumpProc_coeffJump, coeffJump,
      Set.indicator_of_mem hsI, hμdef, hΛs]
  · by_cases h0 : 0 < s
    · have hsT : ¬ s ≤ T := fun h => hs ⟨h0, h⟩
      simp only [if_pos h0, hFdef, if_neg hsT]
    · simp only [if_neg h0]

omit [MeasurableSpace.CountablyGenerated E] in
/-- **Almost every point of `Ω × [0, T] × E` has its time in `(0, T]`**, for the marked energy
measure. -/
theorem ae_markedEnergyMeasure_mem_Ioc [MeasurableSpace Ω] {P : Measure Ω} [SFinite P] {T : ℝ} :
    ∀ᵐ p ∂(LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T),
      p.2.1 ∈ Set.Ioc (0 : ℝ) T := by
  have h1 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Ioc (0 : ℝ) T := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with s hs hsI
    exact ⟨lt_of_le_of_ne hsI.1 (Ne.symm hs), hsI.2⟩
  have h2 : ∀ᵐ q ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν), q.1 ∈ Set.Ioc (0 : ℝ) T :=
    Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst) h1
  exact ae_prod_of_ae_snd h2

end MVFBSDEJ.WellPosedness.System
