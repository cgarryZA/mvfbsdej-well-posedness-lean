/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.JumpLeftEnergy
import MVFBSDEJ.WellPosedness.System.WeakTupleProg

/-!
# The jump coefficient at the predictable tuple of a tuple of `ℍ²`

Let `Θ = (X, Y, Z, U)` be a tuple of `ℍ²` every path of whose `X` and `Y` has left limits at
every time of `(0, T]`. The canonical representative `coeffJump` of the jump coefficient at the
predictable tuple `Θ⁻_s = (X_{s−}, Y_{s−}, Z_s, U_s)` has the marked energy of `coeffJump` at the
tuple `Θ`: `Θ⁻_s = Θ_s` almost surely at almost every time, so `Law(Θ⁻_s) = Law(Θ_s)` there.

The argument freezes the paths outside `[0, T]`, which leaves both sides unchanged; the frozen
paths are càdlàg at every time, so both integrands are jointly measurable, and they agree at
almost every time, almost surely, for every mark, which by Fubini's theorem is agreement almost
everywhere for the marked energy measure.

## Main statements

* `PaperWeakTuple.markedEnergy_coeffJump_leftLim_eq` — the marked energies of `coeffJump` at
  `Θ⁻` and at `Θ` agree.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.Existence LevyStochCalc

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  {C : Coeffs ν n m d} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}

/-- **The jump coefficient at the predictable tuple of a tuple of `ℍ²`.** For `T ≥ 0`,
coefficients with the joint measurability (2.3) and a tuple `Θ` of `ℍ²` every path of whose `X`
and `Y` has left limits at every time of `(0, T]`, coordinatewise,
`𝔼 ∫_0^T ∫_E |coeffJump(h, Θ⁻)|² dν dt = 𝔼 ∫_0^T ∫_E |coeffJump(h, Θ)|² dν dt`, that is,
`𝔼 ∫_0^T ‖h(t, Θ⁻_t, ·, μ⁻_t)‖²_{L²(ν)} dt = 𝔼 ∫_0^T ‖h(t, Θ_t, ·, μ_t)‖²_{L²(ν)} dt` in
coordinates. -/
theorem PaperWeakTuple.markedEnergy_coeffJump_leftLim_eq (hΘ : PaperWeakTuple ℱ P ν T X Y Z U)
    (hT : 0 ≤ T)
    (hXl : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 l))
    (hYl : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l))
    (hC : CoeffBorel T C) (i : Fin n) :
    Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
        jumpProc T (coeffJump P T C (leftLimProc X) (leftLimProc Y) Z U) i s ω e)
      = Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
          jumpProc T (coeffJump P T C X Y Z U) i s ω e) := by
  obtain ⟨X', Y', hXe, hYe, hP, -, -⟩ := hΘ.exists_progTuple hT
  have hclamp : Measurable fun t : ℝ => max 0 (min t T) :=
    (continuous_const.max (continuous_id.min continuous_const)).measurable
  have hclampI : ∀ t ∈ Set.Icc (0 : ℝ) T, max 0 (min t T) = t := fun t ht => by
    rw [min_eq_left ht.2, max_eq_right ht.1]
  -- the frozen paths
  set Xf : Fin n → ℝ → Ω → ℝ := fun i t => X' i (max 0 (min t T)) with hXf
  set Yf : Fin m → ℝ → Ω → ℝ := fun k t => Y' k (max 0 (min t T)) with hYf
  have hXfm : ∀ i, Measurable (Function.uncurry fun ω s => Xf i s ω) := fun i =>
    (hP.measurable_X i).comp (measurable_fst.prodMk (hclamp.comp measurable_snd))
  have hYfm : ∀ k, Measurable (Function.uncurry fun ω s => Yf k s ω) := fun k =>
    (hP.measurable_Y k).comp (measurable_fst.prodMk (hclamp.comp measurable_snd))
  have hXeq : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Xf i t = X i t := fun i t ht => by
    simp only [hXf, hclampI t ht, hXe i t ht]
  have hYeq : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Yf k t = Y k t := fun k t ht => by
    simp only [hYf, hclampI t ht, hYe k t ht]
  have hX'l : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
      Tendsto (fun s => X' i s ω) (𝓝[<] t) (𝓝 l) := fun i ω =>
    exists_tendsto_nhdsLT_of_eqOn (fun t ht => congrFun (hXe i t ht) ω) (hXl i ω)
  have hY'l : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
      Tendsto (fun s => Y' k s ω) (𝓝[<] t) (𝓝 l) := fun k ω =>
    exists_tendsto_nhdsLT_of_eqOn (fun t ht => congrFun (hYe k t ht) ω) (hYl k ω)
  have hXfr : ∀ i ω t, Tendsto (fun s => Xf i s ω) (𝓝[>] t) (𝓝 (Xf i t ω)) := fun i ω t =>
    tendsto_comp_clamp_nhdsGT (hP.X_rightCont i ω) t
  have hYfr : ∀ k ω t, Tendsto (fun s => Yf k s ω) (𝓝[>] t) (𝓝 (Yf k t ω)) := fun k ω t =>
    tendsto_comp_clamp_nhdsGT (hP.Y_rightCont k ω) t
  have hXfl : ∀ i ω t, ∃ l : ℝ, Tendsto (fun s => Xf i s ω) (𝓝[<] t) (𝓝 l) := fun i ω t =>
    exists_tendsto_comp_clamp_nhdsLT (hX'l i ω) t
  have hYfl : ∀ k ω t, ∃ l : ℝ, Tendsto (fun s => Yf k s ω) (𝓝[<] t) (𝓝 l) := fun k ω t =>
    exists_tendsto_comp_clamp_nhdsLT (hY'l k ω) t
  have hZm : ∀ k j, Measurable (Function.uncurry fun ω s => Z k s ω j) := fun k j =>
    Brownian.Ito.measurable_uncurry_of_predictable (hΘ.Z_pred k j)
  have hUm : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2 := fun k =>
    (hΘ.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  -- the left limits of the frozen paths are those of `X` and `Y` on `(0, T]`
  have hleft : ∀ s ∈ Set.Ioc (0 : ℝ) T,
      tupleAt ν (leftLimProc Xf) (leftLimProc Yf) Z U s
        = tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s := by
    intro s hsI
    have hx : ∀ i, leftLimProc Xf i s = leftLimProc X i s := fun i => funext fun ω =>
      leftLim_eq_of_eqOn (fun t ht => congrFun (hXeq i t ht) ω) (hXl i ω) hsI
    have hy : ∀ k, leftLimProc Yf k s = leftLimProc Y k s := fun k => funext fun ω =>
      leftLim_eq_of_eqOn (fun t ht => congrFun (hYeq k t ht) ω) (hYl k ω) hsI
    funext ω
    simp only [tupleAt, hx, hy]
  -- both sides are unchanged by freezing
  have hR : Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
        jumpProc T (coeffJump P T C (leftLimProc X) (leftLimProc Y) Z U) i s ω e)
      = Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
        jumpProc T (coeffJump P T C (leftLimProc Xf) (leftLimProc Yf) Z U) i s ω e) := by
    unfold Poisson.Compensated.markedEnergy
    refine lintegral_congr fun ω => ?_
    refine lintegral_congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := T)).mem_iff]
      with s hs' hsI
    have hsI' : s ∈ Set.Ioc (0 : ℝ) T := hs'.mpr hsI
    refine lintegral_congr fun e => ?_
    simp only [jumpProc, Set.indicator_of_mem hsI,
      coeffJump_eq_of_tupleAt_eq hsI (hleft s hsI')]
  rw [hR, ← coeffJump_eq_of_eqOn hXeq hYeq]
  -- both integrands are jointly measurable
  have hm₁ := measurable_jumpProc_coeffJump (P := P) hC (measurable_uncurry_leftLimProc hXfm hXfl)
    (measurable_uncurry_leftLimProc hYfm hYfl) hZm hUm i
  have hm₂ := measurable_jumpProc_coeffJump (P := P) hC hXfm hYfm hZm hUm i
  rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq hm₁,
    Poisson.Compensated.markedEnergy_eq_eLpNorm_sq hm₂]
  congr 1
  refine eLpNorm_congr_ae ?_
  refine ae_markedEnergyMeasure_of_ae_ae_ae (measurableSet_eq_fun hm₁ hm₂) ?_
  -- the frozen predictable tuple is the frozen tuple at almost every time, almost surely
  have hθ := MVFBSDEJ.WellPosedness.System.ae_ae_tupleAt_leftLimProc_eq (ν := ν) (P := P)
    (Z := Z) (U := U) hXfm hYfm hXfr hXfl hYfr hYfl
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hθ] with s hsI hs
  have hlaw := lawP2_congr hs
  filter_upwards [hs] with ω hω
  refine ae_of_all _ fun e => ?_
  simp only [jumpProc_coeffJump, coeffJump, Set.indicator_of_mem hsI, hω, hlaw]

end MVFBSDEJ.WellPosedness.System
