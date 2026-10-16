/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.LawFlow
import Dissertation.WellPosedness.System.SolvesPathwise

/-!
# The predictable tuple of a solution

The well-posedness paper evaluates the jump coefficient of (1.1) at the predictable tuple
`Θ⁻_s = (X_{s−}, Y_{s−}, Z_s, U_s)` and its law `μ⁻_s`, while the solution predicate
`SolvesForced` evaluates it at `(Θ_s, μ_s)`. Here `Θ⁻_s` is
`tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s`, built from the left-limit processes
`leftLimProc` as in Lemma A.1, and `μ⁻_s` is `lawP2 P Θ⁻_s`, the law of `Θ⁻_s` when it is square
integrable, as `μ_s = lawP2 P Θ_s` is for `Θ_s`. The integrands `Z`, `U` are those of the
solution, progressively measurable; `SolvesForced.exists_predictable` replaces them by
predictable versions with which the tuple is again a solution.

* A solution has left limits at every time of `(0, T]`, almost surely
  (`SolvesForced.ae_leftLim`). Freeze its paths outside `[0, T]`, `t ↦ X_{max 0 (min t T)}`, and
  set them to `0` off a measurable set of full measure on which they have left limits: the
  resulting paths are right-continuous with left limits at every time, and have the same values
  and left limits as `X` at every time of `(0, T)`. A càdlàg path meets its left limits off a
  countable set of times, so `X_{s−}(ω) = X_s(ω)` and `Y_{s−}(ω) = Y_s(ω)` for
  `dP ⊗ ds`-almost every `(ω, s) ∈ Ω × [0, T]`, and by Fubini's theorem, for almost every
  `s ∈ [0, T]`, almost surely.
* Hence `Θ⁻_s = Θ_s` almost surely and `μ⁻_s = μ_s` for almost every `s ∈ [0, T]`, and the
  representative `γ` of `h(s, Θ_s, ·, μ_s)` in `SolvesForced.jump_rep` represents
  `h(s, Θ⁻_s, ·, μ⁻_s)`, at almost every time almost surely.

No measurability of the coefficients enters: both representations are statements at almost every
time, almost surely, and the second follows from the first by the equality of the arguments.

## Main statements

* `tendsto_comp_clamp_nhdsGT`, `exists_tendsto_comp_clamp_nhdsLT` — a path frozen outside
  `[0, T]` is right-continuous, and has left limits everywhere when it has them on `(0, T]`.
* `ae_leftLimProc_eq` — a jointly measurable family whose paths are almost surely
  right-continuous with left limits on `(0, T]` meets its left limits `dP ⊗ ds`-almost everywhere
  on `Ω × [0, T]`.
* `SolvesForced.ae_leftLimProc_eq`, `SolvesForced.ae_tupleAt_leftLimProc_eq` — `Θ⁻ = Θ`,
  `dP ⊗ ds`-almost everywhere.
* `SolvesForced.ae_ae_tupleAt_leftLimProc_eq` — `Θ⁻_s = Θ_s` almost surely, for almost every `s`.
* `SolvesForced.jump_rep_left` — `γ` represents `h(s, Θ⁻_s, ·, μ⁻_s)`.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.System

open LevyStochCalc

/-! ### Freezing a path outside the horizon -/

section Clamp

variable {T : ℝ}

private theorem monotone_clamp : Monotone fun t : ℝ => max 0 (min t T) :=
  fun _ _ hab => max_le_max le_rfl (min_le_min hab le_rfl)

private theorem continuous_clamp : Continuous fun t : ℝ => max 0 (min t T) :=
  continuous_const.max (continuous_id.min continuous_const)

private theorem clamp_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) : max 0 (min t T) = t := by
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- **A path frozen outside `[0, T]` is right-continuous**: if `f` is right-continuous at every
time, so is `t ↦ f (max 0 (min t T))`. -/
theorem tendsto_comp_clamp_nhdsGT {f : ℝ → ℝ} (hf : ∀ t : ℝ, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (t : ℝ) :
    Tendsto (fun s => f (max 0 (min s T))) (𝓝[>] t) (𝓝 (f (max 0 (min t T)))) := by
  have hc : Tendsto (fun s : ℝ => max 0 (min s T)) (𝓝[>] t) (𝓝[≥] (max 0 (min t T))) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuous_clamp.tendsto t).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun _ hs => monotone_clamp (le_of_lt hs))
  exact (continuousWithinAt_Ioi_iff_Ici.mp (hf _)).tendsto.comp hc

/-- **A path frozen outside `[0, T]` has left limits everywhere** when it has left limits at every
time of `(0, T]`. -/
theorem exists_tendsto_comp_clamp_nhdsLT {f : ℝ → ℝ}
    (hf : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L)) (t : ℝ) :
    ∃ L : ℝ, Tendsto (fun s => f (max 0 (min s T))) (𝓝[<] t) (𝓝 L) := by
  rcases le_or_gt t 0 with ht0 | ht0
  · refine ⟨f 0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s (hs : s < t)
    rw [max_eq_left ((min_le_left s T).trans (hs.le.trans ht0))]
  rcases le_or_gt t T with htT | htT
  · obtain ⟨L, hL⟩ := hf t ⟨ht0, htT⟩
    refine ⟨L, hL.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT ht0] with s hs
    rw [clamp_of_mem ⟨hs.1.le, hs.2.le.trans htT⟩]
  · refine ⟨f (max 0 T), tendsto_const_nhds.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT htT] with s hs
    rw [min_eq_right hs.1.le]

end Clamp

/-! ### Left limits almost everywhere -/

section LeftLimits

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℝ} {n : ℕ}

/-- **A family with left limits on `(0, T]` meets its left limits almost everywhere**: for a
jointly measurable family `X` whose paths are almost surely right-continuous with left limits at
every time of `(0, T]`, `X_{s−}(ω) = X_s(ω)` for `dP ⊗ ds`-almost every `(ω, s) ∈ Ω × [0, T]`. -/
theorem ae_leftLimProc_eq {X : Fin n → ℝ → Ω → ℝ}
    (hX : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω))
    (hpath : ∀ᵐ ω ∂P, ∀ i, (∀ t : ℝ, Tendsto (fun s => X i s ω) (𝓝[>] t) (𝓝 (X i t ω)))
      ∧ ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 L)) :
    ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T), ∀ i, leftLimProc X i p.2 p.1 = X i p.2 p.1 := by
  obtain ⟨S, hSae, hSm, hSp⟩ := hpath.exists_measurable_mem
  set Xf : Fin n → ℝ → Ω → ℝ := fun i t ω => S.indicator (fun ω => X i (max 0 (min t T)) ω) ω
    with hXf
  have hXfm : ∀ i, Measurable (Function.uncurry fun ω s => Xf i s ω) := by
    intro i
    have heq : (Function.uncurry fun ω s => Xf i s ω)
        = (S ×ˢ (Set.univ : Set ℝ)).indicator
          fun q : Ω × ℝ => X i (max 0 (min q.2 T)) q.1 := by
      funext q
      by_cases hq : q.1 ∈ S
      · rw [Set.indicator_of_mem (Set.mk_mem_prod hq (Set.mem_univ q.2))]
        exact Set.indicator_of_mem hq _
      · rw [Set.indicator_of_notMem fun h => hq h.1]
        exact Set.indicator_of_notMem hq _
    rw [heq]
    exact ((hX i).comp (measurable_fst.prodMk (continuous_clamp.measurable.comp
      measurable_snd))).indicator (hSm.prod MeasurableSet.univ)
  have hXfr : ∀ i ω t, Tendsto (fun s => Xf i s ω) (𝓝[>] t) (𝓝 (Xf i t ω)) := by
    intro i ω t
    by_cases hω : ω ∈ S
    · simp only [hXf, Set.indicator_of_mem hω]
      exact tendsto_comp_clamp_nhdsGT (hSp ω hω i).1 t
    · simp only [hXf, Set.indicator_of_notMem hω]
      exact tendsto_const_nhds
  have hXfl : ∀ i ω t, ∃ L : ℝ, Tendsto (fun s => Xf i s ω) (𝓝[<] t) (𝓝 L) := by
    intro i ω t
    by_cases hω : ω ∈ S
    · simp only [hXf, Set.indicator_of_mem hω]
      exact exists_tendsto_comp_clamp_nhdsLT (hSp ω hω i).2 t
    · simp only [hXf, Set.indicator_of_notMem hω]
      exact ⟨0, tendsto_const_nhds⟩
  have hmeas : MeasurableSet {q : Ω × ℝ | ∀ i, leftLimProc Xf i q.2 q.1 = Xf i q.2 q.1} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_eq_fun (measurable_uncurry_leftLimProc hXfm hXfl i) (hXfm i)
  have hfrozen : ∀ᵐ q ∂(Brownian.Ito.energyMeasure P T),
      ∀ i, leftLimProc Xf i q.2 q.1 = Xf i q.2 q.1 := by
    rw [Brownian.Ito.energyMeasure, Measure.ae_prod_iff_ae_ae hmeas]
    refine ae_of_all _ fun ω => ae_restrict_of_ae ?_
    filter_upwards [ae_all_iff.mpr fun i =>
      Analysis.ae_eq_leftLim_of_cadlag (hXfr i ω) (hXfl i ω)] with s hs i
    exact (hs i).symm
  have hgood : ∀ᵐ q ∂(Brownian.Ito.energyMeasure P T), q.1 ∈ S ∧ q.2 ∈ Set.Ioo (0 : ℝ) T := by
    rw [Brownian.Ito.energyMeasure, Measure.ae_prod_iff_ae_ae
      (p := fun q : Ω × ℝ => q.1 ∈ S ∧ q.2 ∈ Set.Ioo (0 : ℝ) T)
      (hSm.prod measurableSet_Ioo)]
    filter_upwards [hSae] with ω hω
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := T)).mem_iff]
      with s hs hsI
    exact ⟨hω, hs.mpr hsI⟩
  filter_upwards [hfrozen, hgood] with q hq hqg i
  obtain ⟨hS, hs⟩ := hqg
  have hXq : ∀ r ∈ Set.Icc (0 : ℝ) T, Xf i r q.1 = X i r q.1 := fun r hr => by
    simp only [hXf, Set.indicator_of_mem hS, clamp_of_mem hr]
  obtain ⟨L, hL⟩ := (hSp q.1 hS i).2 q.2 ⟨hs.1, hs.2.le⟩
  have hLf : Tendsto (fun r => Xf i r q.1) (𝓝[<] q.2) (𝓝 L) := by
    refine hL.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hs.1] with r hr
    exact (hXq r ⟨hr.1.le, hr.2.le.trans hs.2.le⟩).symm
  calc leftLimProc X i q.2 q.1 = L := leftLim_eq_of_tendsto hL
    _ = leftLimProc Xf i q.2 q.1 := (leftLim_eq_of_tendsto hLf).symm
    _ = Xf i q.2 q.1 := hq i
    _ = X i q.2 q.1 := hXq q.2 ⟨hs.1.le, hs.2.le⟩

end LeftLimits

/-! ### The predictable tuple of a solution -/

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

namespace SolvesForced

variable (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ) (hT : 0 ≤ T)
include h hT

/-- **A solution meets its left limits almost everywhere**: for a solution of the `λ`-forced
system (4.1), `X_{s−}(ω) = X_s(ω)` and `Y_{s−}(ω) = Y_s(ω)`, coordinatewise, for
`dP ⊗ ds`-almost every `(ω, s) ∈ Ω × [0, T]`. -/
theorem ae_leftLimProc_eq :
    ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T),
      (∀ i, leftLimProc X i p.2 p.1 = X i p.2 p.1)
        ∧ ∀ k, leftLimProc Y k p.2 p.1 = Y k p.2 p.1 := by
  have hL := h.ae_leftLim hT
  have hXm : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω) := fun i =>
    (Probability.measurable_uncurry_of_rightContinuous (h.fwd i).X_adapted
      (h.fwd i).X_rightCont).comp measurable_swap
  have hYm : ∀ k, Measurable (Function.uncurry fun ω s => Y k s ω) := fun k =>
    (Probability.measurable_uncurry_of_rightContinuous (h.bwd k).Y_adapted
      (h.bwd k).Y_rightCont).comp measurable_swap
  filter_upwards [System.ae_leftLimProc_eq hXm (hL.mono fun ω hω i =>
      ⟨(h.fwd i).X_rightCont ω, fun t ht => (hω t ht).1 i⟩),
    System.ae_leftLimProc_eq hYm (hL.mono fun ω hω k =>
      ⟨(h.bwd k).Y_rightCont ω, fun t ht => (hω t ht).2 k⟩)] with p h1 h2
  exact ⟨h1, h2⟩

/-- **The predictable tuple of a solution is its tuple almost everywhere**: for a solution of the
`λ`-forced system (4.1), `Θ⁻_s(ω) = (X_{s−}, Y_{s−}, Z_s, U_s)(ω)` equals `Θ_s(ω)` for
`dP ⊗ ds`-almost every `(ω, s) ∈ Ω × [0, T]`. -/
theorem ae_tupleAt_leftLimProc_eq :
    ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T),
      tupleAt ν (leftLimProc X) (leftLimProc Y) Z U p.2 p.1 = tupleAt ν X Y Z U p.2 p.1 := by
  filter_upwards [h.ae_leftLimProc_eq hT] with p hp
  simp only [tupleAt, hp.1, hp.2]

/-- **The predictable tuple of a solution is its tuple at almost every time**: for almost every
`s ∈ [0, T]`, `Θ⁻_s = Θ_s` almost surely. -/
theorem ae_ae_tupleAt_leftLimProc_eq :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s =ᵐ[P] tupleAt ν X Y Z U s := by
  have hp := h.ae_tupleAt_leftLimProc_eq hT
  rw [Brownian.Ito.energyMeasure, ← Measure.prod_swap] at hp
  exact Measure.ae_ae_of_ae_prod
    ((MeasurableEquiv.prodComm (α := ℝ) (β := Ω)).measurableEmbedding.ae_map_iff.mp hp)

/-- **The jump coefficient at the predictable tuple**: for a solution of the `λ`-forced system
(4.1), `γ` represents `e ↦ h(s, Θ⁻_s(ω), e, μ⁻_s)` in `L²(ν)` for almost every `s ∈ [0, T]` and
almost every `ω`, with `Θ⁻_s = (X_{s−}, Y_{s−}, Z_s, U_s)` and `μ⁻_s = lawP2 P Θ⁻_s`. -/
theorem jump_rep_left :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
        =ᵐ[ν] C.h s (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
          (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)) := by
  filter_upwards [h.jump_rep, h.ae_ae_tupleAt_leftLimProc_eq hT] with s hs heq
  filter_upwards [hs, heq] with ω hω hωeq
  rw [hωeq, lawP2_congr heq]
  exact hω

end SolvesForced

end Dissertation.WellPosedness.System
