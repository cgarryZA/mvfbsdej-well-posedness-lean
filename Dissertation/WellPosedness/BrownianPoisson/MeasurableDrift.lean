/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.Estimate
import Dissertation.WellPosedness.System.TupleLeft
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import LevyStochCalc.Ito.JumpDiffusionAdapted
import Dissertation.WellPosedness.Stability.PairDiff

/-!
# The Brownian–Poisson `L²` estimate for a jointly measurable drift

Lemma 4.1 of the well-posedness paper takes the drift `φ` of the linear backward equation

`Y_t = ξ + ∫_t^T φ_s ds − ∫_t^T Z_s dW_s − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`

in `L²(Ω × [0, T])`, jointly measurable and square integrable, not necessarily progressive. The
equation makes the primitive `A_t = ∫_0^t φ_s ds` adapted: it is `Y_0 − Y_t` plus increments of
the two stochastic integrals, almost surely, and the filtration contains the null sets. The left
difference quotients `(n + 1)(A_t − A_{t − 1/(n+1)})` of the continuous adapted process `A` are
progressive, and by the Lebesgue differentiation theorem their `limsup` equals `φ_t` at almost
every time, on every path. This `limsup`, cut to `[0, T]`, is a progressive drift with the same
integrals and the same energy, so the estimate for a progressive drift applies.

## Main statements

* `ProgressivelyMeasurable.indicator_time` — cutting a progressive process to a Borel set of times
  keeps it progressive.
* `exists_progressive_ae_eq` — a jointly measurable density with integrable paths and adapted
  primitive has a progressive version, equal to it at almost every time on every path.
* `exists_linearBSDEJ_of_measurable` — a solution `Y` given on `[0, T]` only, of the equation
  with a jointly measurable square-integrable drift, solves the linear backward equation with a
  progressive drift of the same energy.
* `brownianPoisson_estimate_of_measurable` — the estimate of Lemma 4.1 for a jointly measurable
  square-integrable drift and a solution `Y` given on `[0, T]` only.
* `brownianPoisson_estimate_vec_of_measurable` — the same for `ℝᵐ`-valued `Y`, coordinatewise.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Dissertation.WellPosedness.BrownianPoisson

open LevyStochCalc.BSDEJ.Solves LevyStochCalc

/-! ### A progressive version of a density with adapted primitive -/

section Progressive

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- Cutting a progressively measurable process to a Borel set of times keeps it progressively
measurable. -/
theorem _root_.LevyStochCalc.Probability.ProgressivelyMeasurable.indicator_time
    {H : Ω → ℝ → ℝ} (h : Probability.ProgressivelyMeasurable ℱ H) {S : Set ℝ}
    (hS : MeasurableSet S) :
    Probability.ProgressivelyMeasurable ℱ fun ω r => S.indicator (H ω) r := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have heq : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun r => S.indicator (H p.1) r) p.2)
      = (Prod.snd ⁻¹' S).indicator fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2 := by
    funext p
    by_cases h1 : p.2 ∈ Set.Iic t <;> by_cases h2 : p.2 ∈ S <;>
      simp [Set.indicator, h1, h2]
  rw [heq]
  exact (h t).indicator (measurable_snd hS)

/-- **A density with adapted primitive has a progressive version.** Let `φ : Ω → ℝ → ℝ` be
jointly measurable with every path integrable, and let the primitive `t ↦ ∫_0^t φ(ω, s) ds` be
adapted. Then some jointly and progressively measurable `ψ` has every path almost everywhere equal
to that of `φ`: the `limsup` of the left difference quotients of the primitive. -/
theorem exists_progressive_ae_eq {φ : Ω → ℝ → ℝ} (hφi : ∀ ω, Integrable (φ ω))
    (hA : ∀ t, Measurable[ℱ t] fun ω => ∫ s in (0 : ℝ)..t, φ ω s) :
    ∃ ψ : Ω → ℝ → ℝ, Measurable (Function.uncurry ψ)
      ∧ Probability.ProgressivelyMeasurable ℱ ψ ∧ ∀ ω, ψ ω =ᵐ[volume] φ ω := by
  set A : Ω → ℝ → ℝ := fun ω t => ∫ s in (0 : ℝ)..t, φ ω s with hAdef
  have hAc : ∀ ω, Continuous (A ω) := fun ω =>
    intervalIntegral.continuous_primitive (fun _ _ => (hφi ω).intervalIntegrable) 0
  set q : ℕ → Ω → ℝ → ℝ := fun n ω t => ((n : ℝ) + 1) * (A ω t - A ω (t - 1 / ((n : ℝ) + 1)))
    with hqdef
  have hqa : ∀ n t, Measurable[ℱ t] fun ω => q n ω t := by
    intro n t
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h2 : Measurable[ℱ t] fun ω => A ω (t - 1 / ((n : ℝ) + 1)) :=
      (hA _).mono (ℱ.mono (by linarith)) le_rfl
    exact measurable_const.mul ((hA t).sub h2)
  have hqc : ∀ n ω, Continuous (q n ω) := fun n ω =>
    continuous_const.mul ((hAc ω).sub ((hAc ω).comp (continuous_id.sub continuous_const)))
  have hqp : ∀ n, Probability.ProgressivelyMeasurable ℱ (q n) := fun n =>
    Probability.progressivelyMeasurable_of_rightContinuous (X := fun t ω => q n ω t) (hqa n)
      fun ω t => ((hqc n ω).tendsto t).mono_left nhdsWithin_le_nhds
  have hψp := Probability.ProgressivelyMeasurable.limsup hqp
  refine ⟨fun ω s => Filter.limsup (fun n => q n ω s) atTop, hψp.measurable_uncurry, hψp,
    fun ω => ?_⟩
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral (hφi ω).locallyIntegrable] with s hs
  have hd : HasDerivAt (A ω) (φ ω s) s := hs 0
  have hu : Tendsto (fun n : ℕ => s - 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] s) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Eventually.of_forall fun n => ?_)
    · simpa using (tendsto_const_nhds (x := s)).sub tendsto_one_div_add_atTop_nhds_zero_nat
    · have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
  have hlim : Tendsto (fun n => q n ω s) atTop (𝓝 (φ ω s)) := by
    refine ((hasDerivAt_iff_tendsto_slope.mp hd).comp hu).congr fun n => ?_
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    simp only [Function.comp_apply, slope_def_field, hqdef]
    field_simp
    ring
  exact hlim.limsup_eq

end Progressive

/-! ### The estimate for a jointly measurable drift -/

/-- A path right-continuous on `[0, T)`, frozen outside `[0, T]`, is right-continuous
everywhere. -/
theorem tendsto_comp_clamp_nhdsGT_of_Ico {f : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto f (𝓝[>] t) (𝓝 (f t))) (t : ℝ) :
    Tendsto (fun s => f (max 0 (min s T))) (𝓝[>] t) (𝓝 (f (max 0 (min t T)))) := by
  rcases lt_or_ge t 0 with ht | ht
  · have h0 : max 0 (min t T) = 0 := max_eq_left ((min_le_left _ _).trans ht.le)
    rw [h0]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT ht] with s hs
    rw [max_eq_left ((min_le_left _ _).trans hs.2.le)]
  rcases lt_or_ge t T with htT | htT
  · have hc : max 0 (min t T) = t := by rw [min_eq_left htT.le, max_eq_right ht]
    rw [hc]
    refine (hf t ⟨ht, htT⟩).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT htT] with s hs
    rw [min_eq_left hs.2.le, max_eq_right (ht.trans hs.1.le)]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : t < s)
    rw [min_eq_right (htT.trans hs.le), min_eq_right htT]

/-- The squared supremum over `[0, T]` of a process with measurable slices on `[0, T]` and paths
right-continuous on `[0, T)` is measurable. -/
theorem measurable_biSup_sq_of_Ico {Ω : Type*} [MeasurableSpace Ω] {Y : ℝ → Ω → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hm : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (Y t))
    (hrc : ∀ ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω))) :
    Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2 := by
  have hcl : ∀ t : ℝ, max 0 (min t T) ∈ Set.Icc (0 : ℝ) T := fun t =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have h := measurable_biSup_sq_of_rightContinuous hT (M := fun t => Y (max 0 (min t T)))
    (fun t => hm _ (hcl t)) fun ω t => tendsto_comp_clamp_nhdsGT_of_Ico (hrc ω) t
  have heq : (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2)
      = fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y (max 0 (min t T)) ω‖₊ : ℝ≥0∞) ^ 2 :=
    funext fun ω => iSup_congr fun t => iSup_congr fun ht => by
      rw [min_eq_left ht.2, max_eq_right ht.1]
  rw [heq]
  exact h

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {T : ℝ} {ξ : Ω → ℝ} {φ : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
  {U : ℝ → Ω → E → ℝ}

/-- **A progressive version of a jointly measurable drift.** Over a right-continuous filtration
carrying the driver, whose null sets lie in its time-`0` field and whose time-`0` field lies in
its fields at negative times, let `Y` be adapted on `[0, T]` with right-continuous paths on
`[0, T)`, `Z, U` progressive of finite energy and vanishing off `[0, T]`, `ξ` square integrable and
`φ` jointly measurable of finite energy on `[0, T]`, and let the linear backward equation hold at
every `t ∈ [0, T]` almost surely. Then a progressive drift `ψ` with the energy of `φ`, and a process
`Y'` equal to `Y` at every time of `[0, T]`, solve the linear backward equation. -/
theorem exists_linearBSDEJ_of_measurable [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hZm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hZp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
    (hZs : ∀ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤)
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hUp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U s ω e)
    (hUv : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0)
    (hUs : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤)
    (hφm : Measurable (Function.uncurry φ)) (hφs : Brownian.Ito.energy P T φ ≠ ⊤)
    (hξ : MemLp ξ 2 P) (hYa : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (Y t))
    (hYr : ∀ ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω)))
    (heq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      Y t ω = ξ ω + (∫ s in Set.Icc t T, φ ω s)
        - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z hZm hZp
              (sq_int_global_of_vanishing hZv hZs) T ω
            - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z hZm hZp
              (sq_int_global_of_vanishing hZv hZs) t ω)
        - (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) hUm hUp
              (marked_sq_int_global_of_vanishing hUv hUs) T ω
            - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) hUm hUp
              (marked_sq_int_global_of_vanishing hUv hUs) t ω)) :
    ∃ (ψ : Ω → ℝ → ℝ) (Y' : ℝ → Ω → ℝ), LinearBSDEJ D ℱ hℱW hℱN T ξ ψ Y' Z U
      ∧ Brownian.Ito.energy P T ψ = Brownian.Ito.energy P T φ
      ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, Y' t = Y t := by
  classical
  have hrc : ℱ.rightCont = ℱ := Filtration.IsRightContinuous.eq
  have hneg : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t := fun t ht => by
    simpa only [hrc] using hℱ0 t ht
  have hnullt : ∀ t : ℝ, ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ t] s :=
    fun t s hs h0 => by
      rcases le_total 0 t with ht | ht
      · exact ℱ.mono ht _ (hnull s hs h0)
      · exact hneg t ht _ (hnull s hs h0)
  have hT0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  -- the sample points with an integrable drift path
  set S := integrablePaths φ T with hSdef
  have hSm : MeasurableSet S := measurableSet_integrablePaths hφm
  have hSae : ∀ᵐ ω ∂P, ω ∈ S := ae_mem_integrablePaths hφm hφs
  -- the drift cut to `S × [0, T]`
  set φ₀ : Ω → ℝ → ℝ := fun ω s => (S ×ˢ Set.Icc (0 : ℝ) T).indicator (Function.uncurry φ) (ω, s)
    with hφ₀
  have hφ₀m : Measurable (Function.uncurry φ₀) := hφm.indicator (hSm.prod measurableSet_Icc)
  have hφ₀S : ∀ ω ∈ S, ∀ s ∈ Set.Icc (0 : ℝ) T, φ₀ ω s = φ ω s := fun ω hω s hs => by
    simp only [hφ₀, Set.indicator_of_mem (Set.mk_mem_prod hω hs), Function.uncurry_apply_pair]
  have hφ₀out : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → φ₀ ω s = 0 := fun ω s hs => by
    simp only [hφ₀]
    exact Set.indicator_of_notMem (fun h => hs (Set.mem_prod.mp h).2) _
  have hφ₀i : ∀ ω, Integrable (φ₀ ω) := by
    intro ω
    by_cases hω : ω ∈ S
    · have he : φ₀ ω = (Set.Icc (0 : ℝ) T).indicator (φ ω) := by
        funext s
        by_cases hs : s ∈ Set.Icc (0 : ℝ) T
        · rw [hφ₀S ω hω s hs, Set.indicator_of_mem hs]
        · rw [hφ₀out ω s hs, Set.indicator_of_notMem hs]
      rw [he, integrable_indicator_iff measurableSet_Icc]
      exact hω
    · have he : φ₀ ω = 0 := by
        funext s
        simp only [hφ₀, Pi.zero_apply]
        exact Set.indicator_of_notMem (fun h => hω (Set.mem_prod.mp h).1) _
      rw [he]
      exact integrable_zero _ _ _
  -- the stochastic integrals, and the primitive of the drift, are adapted
  set I := Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z hZm hZp
    (sq_int_global_of_vanishing hZv hZs) with hIdef
  set J := Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) hUm hUp
    (marked_sq_int_global_of_vanishing hUv hUs) with hJdef
  have hIa : ∀ t, Measurable[ℱ t] (I t) := fun t =>
    (Brownian.Multidim.MultidimBrownianMotion.stronglyAdapted_stochasticIntegral D.W ℱ hℱW Z hZm
      hZp (sq_int_global_of_vanishing hZv hZs) t).measurable
  have hJa : ∀ t, Measurable[ℱ t] (J t) := fun t => by
    have h := Poisson.Compensated.stochasticIntegral_adapted D.N ℱ hℱN (fun ω' s e => U s ω' e)
      hUm hUp (marked_sq_int_global_of_vanishing hUv hUs) t
    rw [hrc] at h
    exact h
  have hIm : ∀ t, Measurable (I t) := fun t => (hIa t).mono (ℱ.le t) le_rfl
  have hJm : ∀ t, Measurable (J t) := fun t => (hJa t).mono (ℱ.le t) le_rfl
  have hPm : ∀ t, Measurable fun ω => ∫ s in (0 : ℝ)..t, φ₀ ω s := fun t => by
    simp only [intervalIntegral]
    exact (hφ₀m.stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Set.Ioc (0 : ℝ) t))).measurable.sub
      (hφ₀m.stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Set.Ioc t (0 : ℝ)))).measurable
  -- the primitive of the cut drift is adapted
  have hint : ∀ ω ∈ S, ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → IntervalIntegrable (φ ω) volume a b :=
    fun ω hω a b ha hab hb => (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      ((show IntegrableOn (φ ω) (Set.Icc (0 : ℝ) T) volume from hω).mono_set
        (Set.Icc_subset_Icc ha hb))
  have hIcc : ∀ ω a b, a ≤ b → ∫ s in Set.Icc a b, φ ω s = ∫ s in a..b, φ ω s :=
    fun ω a b hab => by rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  have hPaT : ∀ t, 0 < t → t ≤ T → Measurable[ℱ t] fun ω => ∫ s in (0 : ℝ)..t, φ₀ ω s := by
    intro t ht0 htT
    have htI : t ∈ Set.Icc (0 : ℝ) T := ⟨ht0.le, htT⟩
    refine Probability.measurable_of_ae_eq_of_null_sets (hnullt t) (hPm t)
      (g := fun ω => Y 0 ω - Y t ω - I 0 ω + I t ω - J 0 ω + J t ω) ?_ ?_
    · have h0 : ℱ 0 ≤ ℱ t := ℱ.mono ht0.le
      exact (((((hYa 0 hT0).mono h0 le_rfl).sub (hYa t htI)).sub ((hIa 0).mono h0 le_rfl)).add
        (hIa t)).sub ((hJa 0).mono h0 le_rfl) |>.add (hJa t)
    · filter_upwards [heq t htI, heq 0 hT0, hSae] with ω h1 h2 hω
      have e1 : ∫ s in (0 : ℝ)..t, φ₀ ω s = ∫ s in (0 : ℝ)..t, φ ω s :=
        intervalIntegral.integral_congr fun s hs => by
          rw [Set.uIcc_of_le ht0.le] at hs
          exact hφ₀S ω hω s ⟨hs.1, hs.2.trans htT⟩
      have e4 := intervalIntegral.integral_add_adjacent_intervals
        (hint ω hω 0 t le_rfl ht0.le htT) (hint ω hω t T ht0.le htT le_rfl)
      rw [hIcc ω t T htT] at h1
      rw [hIcc ω 0 T hT.le] at h2
      rw [e1]
      linarith
  have hPa : ∀ t, Measurable[ℱ t] fun ω => ∫ s in (0 : ℝ)..t, φ₀ ω s := by
    intro t
    rcases le_or_gt t 0 with ht0 | ht0
    · have h0 : (fun ω => ∫ s in (0 : ℝ)..t, φ₀ ω s) = fun _ => 0 := by
        funext ω
        refine (intervalIntegral.integral_congr_ae ?_).trans intervalIntegral.integral_zero
        filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with s hs hsI
        rw [Set.uIoc_of_ge ht0] at hsI
        have hs' : s < 0 := lt_of_le_of_ne hsI.2 hs
        exact hφ₀out ω s fun h => absurd h.1 (not_le.mpr hs')
      rw [h0]
      exact measurable_const
    rcases le_or_gt t T with htT | htT
    · exact hPaT t ht0 htT
    · have he : (fun ω => ∫ s in (0 : ℝ)..t, φ₀ ω s) = fun ω => ∫ s in (0 : ℝ)..T, φ₀ ω s := by
        funext ω
        rw [← intervalIntegral.integral_add_adjacent_intervals (b := T)
          (hφ₀i ω).intervalIntegrable (hφ₀i ω).intervalIntegrable]
        have hz : ∫ s in T..t, φ₀ ω s = 0 := by
          refine (intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hsI => ?_)).trans
            intervalIntegral.integral_zero
          rw [Set.uIoc_of_le htT.le] at hsI
          exact hφ₀out ω s fun h => absurd h.2 (not_le.mpr hsI.1)
        rw [hz, add_zero]
      rw [he]
      exact (hPaT T hT le_rfl).mono (ℱ.mono htT.le) le_rfl
  -- the progressive version of the drift, cut to `[0, T]`
  obtain ⟨ψ, -, hψp, hψe⟩ := exists_progressive_ae_eq hφ₀i hPa
  set ψ' : Ω → ℝ → ℝ := fun ω s => (Set.Icc (0 : ℝ) T).indicator (ψ ω) s with hψ'
  have hψ'p : Probability.ProgressivelyMeasurable ℱ ψ' := hψp.indicator_time measurableSet_Icc
  have hψ'φ : ∀ ω ∈ S, ψ' ω =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)] φ ω := fun ω hω => by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (hψe ω)] with s hs h
    simp only [hψ', Set.indicator_of_mem hs, h, hφ₀S ω hω s hs]
  have hE : Brownian.Ito.energy P T ψ' = Brownian.Ito.energy P T φ := by
    unfold Brownian.Ito.energy
    exact lintegral_congr_ae (hSae.mono fun ω hω =>
      lintegral_congr_ae ((hψ'φ ω hω).mono fun s hs => by simp only [hs]))
  have hI' : ∀ ω ∈ S, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ s in Set.Icc t T, ψ' ω s = ∫ s in Set.Icc t T, φ ω s := fun ω hω t ht =>
    integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc ht.1 le_rfl)
      (hψ'φ ω hω))
  -- the solution frozen outside `[0, T]`
  set Y' : ℝ → Ω → ℝ := fun t ω => Y (max 0 (min t T)) ω with hY'
  have hclamp : ∀ t ∈ Set.Icc (0 : ℝ) T, max 0 (min t T) = t := fun t ht => by
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have hlin : LinearBSDEJ D ℱ hℱW hℱN T ξ ψ' Y' Z U :=
    { Z_meas := hZm
      Z_prog := hZp
      Z_vanish := hZv
      Z_sq := hZs
      U_meas := hUm
      U_prog := hUp
      U_vanish := hUv
      U_sq := hUs
      φ_meas := hψ'p.measurable_uncurry
      φ_prog := hψ'p
      φ_vanish := fun ω s hs => Set.indicator_of_notMem hs _
      φ_sq := by rw [hE]; exact hφs
      ξ_sq := hξ
      Y_adapted := fun t => by
        change Measurable[ℱ t] (Y (max 0 (min t T)))
        rcases lt_or_ge t 0 with ht | ht
        · rw [max_eq_left ((min_le_left _ _).trans ht.le)]
          exact (hYa 0 hT0).mono (hneg t ht.le) le_rfl
        rcases le_or_gt t T with htT | htT
        · rw [hclamp t ⟨ht, htT⟩]
          exact hYa t ⟨ht, htT⟩
        · rw [min_eq_right htT.le, max_eq_right hT.le]
          exact (hYa T ⟨hT.le, le_rfl⟩).mono (ℱ.mono htT.le) le_rfl
      Y_rightCont := fun ω t => tendsto_comp_clamp_nhdsGT_of_Ico (hYr ω) t
      eqn := fun t ht => by
        filter_upwards [heq t ht, hSae] with ω h hω
        change Y (max 0 (min t T)) ω = _
        rw [hclamp t ht, hI' ω hω t ht]
        exact h }
  exact ⟨ψ', Y', hlin, hE, fun t ht => funext fun ω => by simp only [hY', hclamp t ht]⟩

/-- **The Brownian–Poisson `L²` estimate for a jointly measurable drift** (Lemma 4.1). Over a
right-continuous filtration carrying the driver, whose null sets lie in its time-`0` field, whose
time-`0` field lies in its fields at negative times, and which admits a cross witness, let `Y` be
adapted on `[0, T]` with right-continuous paths on `[0, T)`, `Z, U` progressive of finite energy
and vanishing off `[0, T]`, `ξ` square integrable and `φ` jointly measurable of finite energy on
`[0, T]`, and let the linear backward equation hold at every `t ∈ [0, T]` almost surely. Then
`𝔼 sup_{t ≤ T} |Y_t|² + 𝔼 ∫_0^T |Z_s|² ds + 𝔼 ∫_0^T ∫_E U_s(e)² ν(de) ds
  ≤ (13 e^T + 3T) (𝔼|ξ|² + 𝔼 ∫_0^T φ_s² ds)`. -/
theorem brownianPoisson_estimate_of_measurable [ℱ.IsRightContinuous] (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hZm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hZp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
    (hZs : ∀ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤)
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hUp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U s ω e)
    (hUv : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0)
    (hUs : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤)
    (hφm : Measurable (Function.uncurry φ)) (hφs : Brownian.Ito.energy P T φ ≠ ⊤)
    (hξ : MemLp ξ 2 P) (hYa : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (Y t))
    (hYr : ∀ ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω)))
    (heq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      Y t ω = ξ ω + (∫ s in Set.Icc t T, φ ω s)
        - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z hZm hZp
              (sq_int_global_of_vanishing hZv hZs) T ω
            - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z hZm hZp
              (sq_int_global_of_vanishing hZv hZs) t ω)
        - (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) hUm hUp
              (marked_sq_int_global_of_vanishing hUv hUs) T ω
            - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) hUm hUp
              (marked_sq_int_global_of_vanishing hUv hUs) t ω)) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
        + (∑ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i))
        + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e)
      ≤ ENNReal.ofReal (13 * Real.exp T + 3 * T)
        * (∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P + Brownian.Ito.energy P T φ) := by
  obtain ⟨ψ, Y', hlin, hE, hY'⟩ := exists_linearBSDEJ_of_measurable hℱ0 hnull hT hZm hZp hZv hZs
    hUm hUp hUv hUs hφm hφs hξ hYa hYr heq
  have key := hlin.brownianPoisson_estimate 𝒲 hℱ0 hnull hT
  have hsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y' t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
      = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
    refine lintegral_congr fun ω => iSup_congr fun t => iSup_congr fun ht => ?_
    simp only [hY' t ht]
  rw [hsup, hE] at key
  exact key

/-- **The Brownian–Poisson `L²` estimate in `ℝᵐ`, for a jointly measurable drift** (Lemma 4.1),
under the hypotheses of `brownianPoisson_estimate_of_measurable` for each coordinate `k`:
`𝔼 sup_{t ≤ T} |Y_t|² + 𝔼 ∫_0^T (|Z_s|²_F + ‖U_s‖²_{L²(ν)}) ds
  ≤ (13 e^T + 3T) (𝔼|ξ|² + 𝔼 ∫_0^T |φ_s|² ds)`. -/
theorem brownianPoisson_estimate_vec_of_measurable [ℱ.IsRightContinuous] (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    {m : ℕ} {ξ : Fin m → Ω → ℝ} {φ : Fin m → Ω → ℝ → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
    {Z : Fin m → ℝ → Ω → (Fin d → ℝ)} {U : Fin m → ℝ → Ω → E → ℝ}
    (hZm : ∀ k (i : Fin d), Measurable (Function.uncurry fun ω s => Z k s ω i))
    (hZp : ∀ k (i : Fin d), Probability.ProgressivelyMeasurable ℱ fun ω s => Z k s ω i)
    (hZv : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) T → Z k s ω = 0)
    (hZs : ∀ k (i : Fin d), Brownian.Ito.energy P T (fun ω s => Z k s ω i) ≠ ⊤)
    (hUm : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2)
    (hUp : ∀ k, Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U k s ω e)
    (hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → U k s ω e = 0)
    (hUs : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) ≠ ⊤)
    (hφm : ∀ k, Measurable (Function.uncurry (φ k)))
    (hφs : ∀ k, Brownian.Ito.energy P T (φ k) ≠ ⊤) (hξ : ∀ k, MemLp (ξ k) 2 P)
    (hYa : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (Y k t))
    (hYr : ∀ k ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => Y k s ω) (𝓝[>] t) (𝓝 (Y k t ω)))
    (heq : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      Y k t ω = ξ k ω + (∫ s in Set.Icc t T, φ k ω s)
        - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW (Z k) (hZm k)
              (hZp k) (sq_int_global_of_vanishing (hZv k) (hZs k)) T ω
            - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW (Z k)
              (hZm k) (hZp k) (sq_int_global_of_vanishing (hZv k) (hZs k)) t ω)
        - (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U k s ω' e) (hUm k)
              (hUp k) (marked_sq_int_global_of_vanishing (hUv k) (hUs k)) T ω
            - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U k s ω' e)
              (hUm k) (hUp k) (marked_sq_int_global_of_vanishing (hUv k) (hUs k)) t ω)) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, Stability.esq fun k => Y k t ω) ∂P
        + (∑ k, ∑ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z k s ω i))
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)
      ≤ ENNReal.ofReal (13 * Real.exp T + 3 * T)
        * (∫⁻ ω, (Stability.esq fun k => ξ k ω) ∂P + ∑ k, Brownian.Ito.energy P T (φ k)) := by
  have key := fun k => brownianPoisson_estimate_of_measurable 𝒲 hℱ0 hnull hT (hZm k) (hZp k)
    (hZv k) (hZs k) (hUm k) (hUp k) (hUv k) (hUs k) (hφm k) (hφs k) (hξ k) (hYa k) (hYr k)
    (heq k)
  have hsm : ∀ k, Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y k t ω‖₊ : ℝ≥0∞) ^ 2 :=
    fun k => measurable_biSup_sq_of_Ico hT.le (fun t ht => (hYa k t ht).mono (ℱ.le t) le_rfl)
      (hYr k)
  have hsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, Stability.esq fun k => Y k t ω) ∂P
      ≤ ∑ k, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y k t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
    rw [← lintegral_finsetSum _ fun k _ => hsm k]
    refine lintegral_mono fun ω => iSup₂_le fun t ht => ?_
    exact Finset.sum_le_sum fun k _ =>
      le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => (‖Y k t ω‖₊ : ℝ≥0∞) ^ 2) t ht
  have hξe : ∫⁻ ω, (Stability.esq fun k => ξ k ω) ∂P
      = ∑ k, ∫⁻ ω, (‖ξ k ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    simp only [Stability.esq]
    exact lintegral_finsetSum' _ fun k _ =>
      (hξ k).aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal.pow_const 2
  calc _ ≤ ∑ k, (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y k t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
          + (∑ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z k s ω i))
          + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        gcongr
    _ ≤ ∑ k, ENNReal.ofReal (13 * Real.exp T + 3 * T)
          * (∫⁻ ω, (‖ξ k ω‖₊ : ℝ≥0∞) ^ 2 ∂P + Brownian.Ito.energy P T (φ k)) :=
        Finset.sum_le_sum fun k _ => key k
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib, hξe]

end Dissertation.WellPosedness.BrownianPoisson
