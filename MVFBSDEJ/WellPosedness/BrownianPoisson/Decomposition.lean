/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.BrownianPoisson.ItoLevy

/-!
# The forward decomposition of a solution up to indistinguishability

A solution of the linear backward equation (4.4) satisfies
`Y_t = Y_0 − ∫_0^t φ_s ds + M_t` almost surely at each `t ∈ [0, T]`, with `M` any version of the
sum of the two canonical stochastic integrals. When `M` has right-continuous paths, so do both
sides — the drift primitive `driftLeg φ T` is continuous — and one set of full measure serves all
times of `[0, T]` at once: the clamped rationals `max 0 (min T q)` are countably many times of the
horizon, they approach every `t < T` from the right, and `T` is one of them.

## Main statements

* `ae_forall_Icc_eq_of_rightContinuous` — two right-continuous processes agreeing almost surely
  at each time of `[0, T]` agree at all those times on one set of full measure.
* `LinearBSDEJ.ae_forall_eq_decomposition` — the forward decomposition, for all times of the
  horizon on one set of full measure.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.BrownianPoisson

open LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {T : ℝ} {ξ : Ω → ℝ} {φ : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
  {U : ℝ → Ω → E → ℝ}

omit [IsProbabilityMeasure P] in
/-- Two processes with right-continuous paths that agree almost surely at each time of `[0, T]`
agree at every time of `[0, T]` on a single set of full measure. -/
theorem ae_forall_Icc_eq_of_rightContinuous {Y R : ℝ → Ω → ℝ} (hT : 0 ≤ T)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, Y t =ᵐ[P] R t)
    (hY : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω)))
    (hR : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => R s ω) (𝓝[>] t) (𝓝 (R t ω))) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y t ω = R t ω := by
  have hmem : ∀ q : ℚ, max (0 : ℝ) (min T (q : ℝ)) ∈ Set.Icc (0 : ℝ) T :=
    fun _ => ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ,
      Y (max (0 : ℝ) (min T (q : ℝ))) ω = R (max (0 : ℝ) (min T (q : ℝ))) ω :=
    ae_all_iff.mpr fun q => h _ (hmem q)
  filter_upwards [hrat, h T ⟨hT, le_rfl⟩] with ω hω hωT
  intro t ht
  rcases eq_or_lt_of_le ht.2 with heq | htT
  · rw [heq]
    exact hωT
  have hex : ∀ n : ℕ, ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < min (t + 1 / ((n : ℝ) + 1)) T := by
    intro n
    refine exists_rat_btwn (lt_min ?_ htT)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose q hq1 hq2 using hex
  have hq0 : ∀ n, (0 : ℝ) ≤ (q n : ℝ) := fun n => le_of_lt (lt_of_le_of_lt ht.1 (hq1 n))
  have hqT : ∀ n, (q n : ℝ) ≤ T := fun n => le_of_lt (lt_of_lt_of_le (hq2 n) (min_le_right _ _))
  have hclamp : ∀ n, max (0 : ℝ) (min T (q n : ℝ)) = (q n : ℝ) := fun n => by
    rw [min_eq_right (hqT n), max_eq_right (hq0 n)]
  have htend : Tendsto (fun n : ℕ => (q n : ℝ)) atTop (𝓝 t) := by
    have hz : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hup : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) atTop (𝓝 t) := by
      simpa using (tendsto_const_nhds (x := t)).add hz
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => (hq1 n).le) (fun n => le_of_lt (lt_of_lt_of_le (hq2 n) (min_le_left _ _)))
  have hsw : Tendsto (fun n : ℕ => (q n : ℝ)) atTop (𝓝[>] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htend
      (Eventually.of_forall fun n => hq1 n)
  refine tendsto_nhds_unique (((hY ω t).comp hsw).congr fun n => ?_) ((hR ω t).comp hsw)
  have hn := hω (q n)
  rwa [hclamp n] at hn

namespace LinearBSDEJ

/-- **The forward decomposition up to indistinguishability.** For a version `M` of the sum of the
two canonical stochastic integrals with right-continuous paths, on a single set of full measure
`Y_t = Y_0 − ∫_0^t φ_s ds + M_t` at every `t ∈ [0, T]`, the drift integral taken as the
continuous primitive `driftLeg φ T`. -/
theorem ae_forall_eq_decomposition (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (hT : 0 < T)
    {M : ℝ → Ω → ℝ}
    (hMae : ∀ t : ℝ, M t =ᵐ[P] fun ω =>
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z h.Z_meas
          h.Z_prog (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) t ω
        + Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) h.U_meas
          h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) t ω)
    (hMrc : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y t ω = Y 0 ω - driftLeg φ T t ω + M t ω := by
  have hIL := h.isItoLevyProcess_clampT hT
  refine ae_forall_Icc_eq_of_rightContinuous hT.le (fun t ht => ?_) h.Y_rightCont
    (fun ω t => ?_)
  · filter_upwards [hIL.decomposition t ht.1, driftLeg_ae_eq h.φ_meas h.φ_sq t, hMae t]
      with ω h1 h2 h3
    rw [clampT_apply_of_le ht.2 Y] at h1
    rw [h1, h2, h3, integral_neg]
    ring
  · have hA : Tendsto (fun s => driftLeg φ T s ω) (𝓝[>] t) (𝓝 (driftLeg φ T t ω)) :=
      ((continuous_driftLeg h.φ_vanish ω).tendsto t).mono_left nhdsWithin_le_nhds
    exact (tendsto_const_nhds.sub hA).add (hMrc ω t)

end LinearBSDEJ

end MVFBSDEJ.WellPosedness.BrownianPoisson
