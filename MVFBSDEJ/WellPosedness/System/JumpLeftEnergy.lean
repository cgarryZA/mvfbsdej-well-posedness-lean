/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Existence.PaperStabilityBorel

/-!
# The jump difference of Theorem 3.1 at the predictable tuple

Statement numbers refer to the well-posedness paper. Theorem 3.1 measures the jump difference
`δh = h¹(t, Θ²⁻_t, ·, μ²⁻_t) − h²(t, Θ²⁻_t, ·, μ²⁻_t)` at the predictable tuple
`Θ²⁻_t = (X²_{t−}, Y²_{t−}, Z²_t, U²_t)` of the second solution. With the canonical representative
`coeffJump` of a coefficient along a tuple, its energy `𝔼 ∫_0^T ‖δh‖²_{L²(ν)} dt` equals the energy
of `coeffJump` of `h¹` along `Θ²` minus the jump representative `γ²` of the solution.

The argument freezes the paths of the solution outside `[0, T]`, so that they are càdlàg at every
time and meet their left limits off a countable set of times; the frozen tuple has the same left
limits at every time of `(0, T]`. Both integrands are then jointly measurable and agree at almost
every time, almost surely, for almost every mark, which by Fubini's theorem is agreement almost
everywhere for the marked energy measure.

## Main statements

* `ae_markedEnergyMeasure_of_ae_ae_ae` — a measurable property holding at almost every time,
  almost surely, for almost every mark holds almost everywhere for the marked energy measure.
* `measurable_jumpProc_coeffJump` — `coeffJump` along a jointly measurable tuple is jointly
  measurable.
* `MVFBSDEJ.WellPosedness.System.PaperSolution.markedEnergy_coeffJump_sub_eq_leftLim` — the
  two energies of the jump difference agree.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.System LevyStochCalc

/-! ### Almost everywhere for the marked energy measure -/

section Swap

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {P : Measure Ω}
  {ν : Measure E} [SFinite P] [SFinite ν] {T : ℝ}

/-- A property with a measurable set that holds at almost every time of `[0, T]`, almost surely,
for almost every mark, holds almost everywhere for the marked energy measure. -/
theorem ae_markedEnergyMeasure_of_ae_ae_ae {p : Ω × ℝ × E → Prop}
    (hp : MeasurableSet {q | p q})
    (h : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, ∀ᵐ e ∂ν, p (ω, s, e)) :
    ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T), p q := by
  rw [Poisson.Compensated.markedEnergyMeasure, Measure.ae_prod_iff_ae_ae hp]
  have hS : MeasurableSet {z : (Ω × ℝ) × E | ¬ p (z.1.1, z.1.2, z.2)} :=
    (hp.preimage MeasurableEquiv.prodAssoc.measurable).compl
  have hr : MeasurableSet {q : Ω × ℝ | ∀ᵐ e ∂ν, p (q.1, q.2, e)} := by
    have hm : Measurable fun q : Ω × ℝ => ν (Prod.mk q ⁻¹' {z | ¬ p (z.1.1, z.1.2, z.2)}) :=
      measurable_measure_prodMk_left hS
    have heq : {q : Ω × ℝ | ∀ᵐ e ∂ν, p (q.1, q.2, e)}
        = (fun q : Ω × ℝ => ν (Prod.mk q ⁻¹' {z | ¬ p (z.1.1, z.1.2, z.2)})) ⁻¹' {0} := by
      ext q
      simp [ae_iff]
    rw [heq]
    exact hm (measurableSet_singleton 0)
  have h' : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν, p (ω, s, e) :=
    (Measure.ae_ae_comm (p := fun ω s => ∀ᵐ e ∂ν, p (ω, s, e)) hr).mpr h
  filter_upwards [h'] with ω hω
  exact (Measure.ae_prod_iff_ae_ae (p := fun y : ℝ × E => p (ω, y))
    (measurable_prodMk_left hp)).mpr hω

end Swap

/-! ### Measurability of the canonical jump representative -/

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ} {C : Coeffs ν n m d}

/-- **`coeffJump` along a jointly measurable tuple is jointly measurable** in the sample point,
the time and the mark, for coefficients with the joint measurability (2.3). -/
theorem measurable_jumpProc_coeffJump (hC : CoeffBorel T C) {X : Fin n → ℝ → Ω → ℝ}
    {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
    (hX : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω))
    (hY : ∀ k, Measurable (Function.uncurry fun ω s => Y k s ω))
    (hZ : ∀ k j, Measurable (Function.uncurry fun ω s => Z k s ω j))
    (hU : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2) (i : Fin n) :
    Measurable fun p : Ω × ℝ × E => jumpProc T (coeffJump P T C X Y Z U) i p.2.1 p.1 p.2.2 := by
  have hΘm := measurable_uncurry_tupleAt (ν := ν) hX hY hZ hU
  have hμ : Measurable fun s => lawP2 P (tupleAt ν X Y Z U s) :=
    measurable_lawP2_flow (Θ := fun ω s => tupleAt ν X Y Z U s ω) hΘm
  have hproj : Measurable fun v : EuclideanSpace ℝ (Fin n) => v i :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.measurable
  have hjm : Measurable fun p : ℝ × TupleH ν n m d =>
      (Set.Icc (0 : ℝ) T).indicator
        (fun t => C.h t p.2 (lawP2 P (tupleAt ν X Y Z U t))) p.1 :=
    measurable_cutoff_along hC.h_meas hμ measurable_id rfl
  have hG : Measurable fun p : ℝ × TupleH ν n m d × E =>
      lpRep ν (EuclideanSpace ℝ (Fin n))
        ((Set.Icc (0 : ℝ) T).indicator
          (fun t => C.h t p.2.1 (lawP2 P (tupleAt ν X Y Z U t))) p.1, p.2.2) i :=
    hproj.comp (stronglyMeasurable_lpRep.measurable.comp
      ((hjm.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
  have e : ∀ p : Ω × ℝ × E, jumpProc T (coeffJump P T C X Y Z U) i p.2.1 p.1 p.2.2
      = lpRep ν (EuclideanSpace ℝ (Fin n))
        ((Set.Icc (0 : ℝ) T).indicator
          (fun t => C.h t (tupleAt ν X Y Z U p.2.1 p.1) (lawP2 P (tupleAt ν X Y Z U t)))
          p.2.1, p.2.2) i := fun p => jumpProc_coeffJump i p.2.1 p.1 p.2.2
  simp only [e]
  exact hG.comp (measurable_snd.fst.prodMk
    ((hΘm.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))

/-- `coeffJump` at a time of `[0, T]` depends on the tuple only through its value at that time. -/
theorem coeffJump_eq_of_tupleAt_eq {X X' : Fin n → ℝ → Ω → ℝ} {Y Y' : Fin m → ℝ → Ω → ℝ}
    {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T) (h : tupleAt ν X' Y' Z U s = tupleAt ν X Y Z U s)
    (i : Fin n) (ω : Ω) (e : E) :
    coeffJump P T C X' Y' Z U i s ω e = coeffJump P T C X Y Z U i s ω e := by
  simp only [coeffJump, Set.indicator_of_mem hs, h]

/-! ### The frozen paths -/

section Frozen

variable {X : Fin n → ℝ → Ω → ℝ}

/-- A path equal to `f` on `[0, T]` has left limits at every time of `(0, T]` if `f` has. -/
theorem exists_tendsto_nhdsLT_of_eqOn {f g : ℝ → ℝ} (hfg : ∀ t ∈ Set.Icc (0 : ℝ) T, g t = f t)
    (hf : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l)) :
    ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto g (𝓝[<] t) (𝓝 l) := by
  intro t ht
  obtain ⟨l, hl⟩ := hf t ht
  refine ⟨l, hl.congr' ?_⟩
  filter_upwards [Ioo_mem_nhdsLT ht.1] with r hr
  exact (hfg r ⟨hr.1.le, hr.2.le.trans ht.2⟩).symm

/-- A path equal to `f` on `[0, T]` has the left limits of `f` at every time of `(0, T]`. -/
theorem leftLim_eq_of_eqOn {f g : ℝ → ℝ} (hfg : ∀ t ∈ Set.Icc (0 : ℝ) T, g t = f t)
    (hf : ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto f (𝓝[<] t) (𝓝 l)) {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) T) : Function.leftLim g t = Function.leftLim f t := by
  obtain ⟨l, hl⟩ := hf t ht
  have hg : Tendsto g (𝓝[<] t) (𝓝 l) := by
    refine hl.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT ht.1] with r hr
    exact (hfg r ⟨hr.1.le, hr.2.le.trans ht.2⟩).symm
  rw [leftLim_eq_of_tendsto hg, leftLim_eq_of_tendsto hl]

end Frozen

/-! ### The two energies of the jump difference -/

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {C₁ C₂ : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- **The energy of the jump difference of Theorem 3.1 at the predictable tuple.** Let `Θ` be a
solution of (1.1) for `C²` in the sense of the paper, with jump representative `γ`, whose paths of
`X` and `Y` have left limits at every time of `(0, T]`, and let `C¹, C²` have the joint
measurability (2.3). Then, coordinatewise,

`𝔼 ∫_0^T ∫_E |coeffJump(h¹, Θ) − γ|² dν dt
  = 𝔼 ∫_0^T ∫_E |coeffJump(h¹, Θ⁻) − coeffJump(h², Θ⁻)|² dν dt`,

the right-hand side being `𝔼 ∫_0^T ‖h¹(t, Θ⁻_t, ·, μ⁻_t) − h²(t, Θ⁻_t, ·, μ⁻_t)‖²_{L²(ν)} dt` in
coordinates. -/
theorem _root_.MVFBSDEJ.WellPosedness.System.PaperSolution.markedEnergy_coeffJump_sub_eq_leftLim
    (h : PaperSolution D ℱ hℱW hℱN T C₂ ξ₀ X Y Z U γ) (hT : 0 < T)
    (hXl : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 l))
    (hYl : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l))
    (hC₁ : CoeffBorel T C₁) (hC₂ : CoeffBorel T C₂) (i : Fin n) :
    Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => jumpProc T (coeffJump P T C₁ X Y Z U) i s ω e - jumpProc T γ i s ω e)
      = Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
          jumpProc T (coeffJump P T C₁ (leftLimProc X) (leftLimProc Y) Z U) i s ω e
            - jumpProc T (coeffJump P T C₂ (leftLimProc X) (leftLimProc Y) Z U) i s ω e) := by
  obtain ⟨X', Y', hXe, hYe, hs⟩ := h.exists_solves hT.le
  have hclamp : Measurable fun t : ℝ => max 0 (min t T) :=
    (continuous_const.max (continuous_id.min continuous_const)).measurable
  have hclampI : ∀ t ∈ Set.Icc (0 : ℝ) T, max 0 (min t T) = t := fun t ht => by
    rw [min_eq_left ht.2, max_eq_right ht.1]
  -- the frozen paths
  set Xf : Fin n → ℝ → Ω → ℝ := fun i t => X' i (max 0 (min t T)) with hXf
  set Yf : Fin m → ℝ → Ω → ℝ := fun k t => Y' k (max 0 (min t T)) with hYf
  have hX'm : ∀ i, Measurable (Function.uncurry fun ω s => X' i s ω) := fun i =>
    (Probability.measurable_uncurry_of_rightContinuous (hs.fwd i).X_adapted
      (hs.fwd i).X_rightCont).comp measurable_swap
  have hY'm : ∀ k, Measurable (Function.uncurry fun ω s => Y' k s ω) := fun k =>
    (Probability.measurable_uncurry_of_rightContinuous (hs.bwd k).Y_adapted
      (hs.bwd k).Y_rightCont).comp measurable_swap
  have hXfm : ∀ i, Measurable (Function.uncurry fun ω s => Xf i s ω) := fun i =>
    (hX'm i).comp (measurable_fst.prodMk (hclamp.comp measurable_snd))
  have hYfm : ∀ k, Measurable (Function.uncurry fun ω s => Yf k s ω) := fun k =>
    (hY'm k).comp (measurable_fst.prodMk (hclamp.comp measurable_snd))
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
    tendsto_comp_clamp_nhdsGT ((hs.fwd i).X_rightCont ω) t
  have hYfr : ∀ k ω t, Tendsto (fun s => Yf k s ω) (𝓝[>] t) (𝓝 (Yf k t ω)) := fun k ω t =>
    tendsto_comp_clamp_nhdsGT ((hs.bwd k).Y_rightCont ω) t
  have hXfl : ∀ i ω t, ∃ l : ℝ, Tendsto (fun s => Xf i s ω) (𝓝[<] t) (𝓝 l) := fun i ω t =>
    exists_tendsto_comp_clamp_nhdsLT (hX'l i ω) t
  have hYfl : ∀ k ω t, ∃ l : ℝ, Tendsto (fun s => Yf k s ω) (𝓝[<] t) (𝓝 l) := fun k ω t =>
    exists_tendsto_comp_clamp_nhdsLT (hY'l k ω) t
  have hZm : ∀ k j, Measurable (Function.uncurry fun ω s => Z k s ω j) := fun k j =>
    Brownian.Ito.measurable_uncurry_of_predictable (h.Z_pred k j)
  have hUm : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2 := fun k =>
    (h.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  -- the left limits of the frozen paths are those of the solution on `(0, T]`
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
  -- the right-hand side is unchanged by freezing
  have hR : Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
        jumpProc T (coeffJump P T C₁ (leftLimProc X) (leftLimProc Y) Z U) i s ω e
          - jumpProc T (coeffJump P T C₂ (leftLimProc X) (leftLimProc Y) Z U) i s ω e)
      = Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
        jumpProc T (coeffJump P T C₁ (leftLimProc Xf) (leftLimProc Yf) Z U) i s ω e
          - jumpProc T (coeffJump P T C₂ (leftLimProc Xf) (leftLimProc Yf) Z U) i s ω e) := by
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
  -- the left-hand side is unchanged by freezing
  have hL : coeffJump P T C₁ X Y Z U = coeffJump P T C₁ Xf Yf Z U :=
    (coeffJump_eq_of_eqOn hXeq hYeq).symm
  rw [hR, hL]
  -- both integrands are jointly measurable
  have hm₁ : Measurable fun p : Ω × ℝ × E =>
      jumpProc T (coeffJump P T C₁ Xf Yf Z U) i p.2.1 p.1 p.2.2 - jumpProc T γ i p.2.1 p.1 p.2.2 :=
    (measurable_jumpProc_coeffJump hC₁ hXfm hYfm hZm hUm i).sub (h.γ_meas i)
  have hXlm := measurable_uncurry_leftLimProc hXfm hXfl
  have hYlm := measurable_uncurry_leftLimProc hYfm hYfl
  have hm₂ : Measurable fun p : Ω × ℝ × E =>
      jumpProc T (coeffJump P T C₁ (leftLimProc Xf) (leftLimProc Yf) Z U) i p.2.1 p.1 p.2.2
        - jumpProc T (coeffJump P T C₂ (leftLimProc Xf) (leftLimProc Yf) Z U) i p.2.1 p.1
          p.2.2 :=
    (measurable_jumpProc_coeffJump hC₁ hXlm hYlm hZm hUm i).sub
      (measurable_jumpProc_coeffJump hC₂ hXlm hYlm hZm hUm i)
  rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq hm₁,
    Poisson.Compensated.markedEnergy_eq_eLpNorm_sq hm₂]
  congr 1
  refine eLpNorm_congr_ae ?_
  refine ae_markedEnergyMeasure_of_ae_ae_ae (measurableSet_eq_fun hm₁ hm₂) ?_
  -- the frozen predictable tuple is the frozen tuple at almost every time, almost surely
  have hΘ := ae_ae_tupleAt_leftLimProc_eq (ν := ν) (P := P) (Z := Z) (U := U) hXfm hYfm hXfr
    hXfl hYfr hYfl
  filter_upwards [ae_restrict_mem measurableSet_Icc, h.jump_rep_tupleAt hT.le,
    ae_restrict_of_ae hΘ] with s hsI hγ hθ
  have htup : tupleAt ν Xf Yf Z U s = tupleAt ν X Y Z U s := tupleAt_eq_of_eqOn hXeq hYeq hsI
  filter_upwards [hγ, hθ] with ω hγω hθω
  have e₁ := coeffJump_ae_eq (P := P) (C := C₁) (X := Xf) (Y := Yf) (Z := Z) (U := U) hsI ω
  have e₂ := coeffJump_ae_eq (P := P) (C := C₁) (X := leftLimProc Xf) (Y := leftLimProc Yf)
    (Z := Z) (U := U) hsI ω
  have e₃ := coeffJump_ae_eq (P := P) (C := C₂) (X := leftLimProc Xf) (Y := leftLimProc Yf)
    (Z := Z) (U := U) hsI ω
  rw [hθω, lawP2_congr hθ, htup] at e₂ e₃
  rw [htup] at e₁
  filter_upwards [e₁, e₂, e₃, hγω] with e h₁ h₂ h₃ h₄
  have c₁ := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) (h₁.trans h₂.symm)
  have c₂ := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) (h₄.trans h₃.symm)
  simp only at c₁ c₂
  simp only [jumpProc, Set.indicator_of_mem hsI, c₁, c₂]

end MVFBSDEJ.WellPosedness.Existence
