/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.BridgeDiffInt
import Dissertation.WellPosedness.System.PaperWeakSolutionForcedIntSolves
import Dissertation.WellPosedness.System.JumpLeftEnergy

/-!
# Two solutions of the `λ`-forced system in `ℍ²` and their difference

Let `Θ¹, Θ²` solve the `λ`-forced system (4.1) of the well-posedness paper in `ℍ²`, in the
sense of `PaperWeakSolutionForcedInt`, with jump representatives `γ¹, γ²`. The proof of Lemma 4.3
works with their difference:

* extended off `[0, T]`, the solutions solve `SolvesForcedInt`, and under Assumptions 2.3 and 2.5
  along the diagonal the difference of the extensions is the difference system
  `Dissertation.WellPosedness.Stability.PairDiff`, whose coefficient processes are those along
  `Θ¹, Θ²` themselves;
* the forced jump integrand `λ h(s, Θ⁻_s, ·, μ⁻_s) + q^h_s`, read through the canonical
  representative `Dissertation.WellPosedness.Existence.coeffJump` along the predictable tuple,
  agrees with `λ γ + q^h` almost everywhere for the marked energy measure when every path of `X` and
  `Y` has left limits on `(0, T]`. The predictable tuple at the time `0` involves the paths before
  `0`, on which nothing is assumed; the time `0` is a null set, and the argument runs through the
  paths frozen outside `[0, T]`.

## Main statements

* `ae_ae_of_ae_markedEnergyMeasure` — a property holding almost everywhere for the marked energy
  measure holds, at almost every point of the window, for almost every mark.
* `ae_window_mem` — almost every point of the window has its time in `[0, T]`.
* `PaperWeakSolutionForcedInt.exists_pairDiff` — the difference of the extended solutions is a
  `Dissertation.WellPosedness.Stability.PairDiff`.
* `PaperWeakSolutionForcedInt.ae_forcedJump_leftLim_eq`,
  `PaperWeakSolutionForcedInt.ae_forcedJump_sub_leftLim_eq` — the forced jump integrand at the
  predictable tuple agrees with that of the representative.
* `Forcing.dataSize_ne_top_of_memLp` — the data size of a square-integrable initial datum and a
  forcing is finite.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open LevyStochCalc Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability

universe u v w

/-! ### The marked energy measure -/

section Marked

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {P : Measure Ω}
  {ν : Measure E} [SFinite P] [SFinite ν] {T : ℝ}

/-- A property holding almost everywhere for the marked energy measure holds, at almost every
point of the window `Ω × [0, T]`, for almost every mark. -/
theorem ae_ae_of_ae_markedEnergyMeasure {p : Ω × ℝ × E → Prop}
    (h : ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T), p q) :
    ∀ᵐ x ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), ∀ᵐ e ∂ν, p (x.1, x.2, e) := by
  rw [Poisson.Compensated.markedEnergyMeasure, ← Measure.prodAssoc_prod,
    MeasurableEquiv.prodAssoc.measurableEmbedding.ae_map_iff] at h
  exact Measure.ae_ae_of_ae_prod h

omit [SFinite P] in
/-- Almost every point of the window `Ω × [0, T]` has its time in `[0, T]`. -/
theorem ae_window_mem :
    ∀ᵐ x ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), x.2 ∈ Set.Icc (0 : ℝ) T :=
  (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)).mpr
    (ae_of_all _ fun _ => ae_restrict_mem measurableSet_Icc)

end Marked

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam : ℝ} {C : Coeffs ν n m d}
  {ξ₀ ξ₁ ξ₂ : Fin n → Ω → ℝ}
  {qb qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf qf₁ qf₂ : Fin m → Ω → ℝ → ℝ}
  {qg qg₁ qg₂ : Fin m → Ω → ℝ}
  {X X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ} {L α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}

/-- **The difference of two solutions in `ℍ²` is a difference system.** For two solutions of
the `λ`-forced system in `ℍ²` with the same coefficients and `T ≥ 0`, satisfying Assumption
2.3 along the diagonal with constant `L` and Assumption 2.5 along the diagonal with coupling
matrix `G` and constants `α, β₁, β₂`, there are `X'^k, Y'^k` equal to `X^k, Y^k` at every time of
`[0, T]` such that the difference `(X'¹ − X'², Y'¹ − Y'², δZ, δU)` is a `PairDiff` with Lipschitz
constants `10 L²` and `4 L²`, with the coefficient differences along `Θ¹, Θ²`, the differences of
the jump representatives and of the forcings, and the initial difference `δξ₀`. -/
theorem PaperWeakSolutionForcedInt.exists_pairDiff
    (h₁ : PaperWeakSolutionForcedInt D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : PaperWeakSolutionForcedInt D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hT : 0 ≤ T) (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g)
    (hM : DiagonalMonotone ℱ P T G β₁ β₂ C) (hMT : TerminalMonotone ℱ P T G α C.g) :
    ∃ (X₁' X₂' : Fin n → ℝ → Ω → ℝ) (Y₁' Y₂' : Fin m → ℝ → Ω → ℝ),
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁' i t = X₁ i t ∧ X₂' i t = X₂ i t)
      ∧ (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁' k t = Y₁ k t ∧ Y₂' k t = Y₂ k t)
      ∧ PairDiff D ℱ hℱW hℱN T lam (10 * L ^ 2) (4 * L ^ 2) α β₁ β₂ G
        (fun i ω => ξ₁ i ω - ξ₂ i ω)
        (fun i t ω => X₁' i t ω - X₂' i t ω) (fun k t ω => Y₁' k t ω - Y₂' k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
        (fun i ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
        (fun i s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
          - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
        (fun i s ω e => jumpProc T γ₁ i s ω e - jumpProc T γ₂ i s ω e)
        (fun k ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
        (fun k ω => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
        (fun i ω s => qb₁ i ω s - qb₂ i ω s) (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
        (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
        (fun k ω => qg₁ k ω - qg₂ k ω) := by
  obtain ⟨X₁', Y₁', hX₁, hY₁, hs₁⟩ := h₁.exists_solvesForcedInt hT
  obtain ⟨X₂', Y₂', hX₂, hY₂, hs₂⟩ := h₂.exists_solvesForcedInt hT
  have hD := hs₁.pairDiff_of_assumptions hs₂ hT hL hLT hM hMT
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  rw [driftProc_eq_of_eqOn (P := P) (C := C) (Z := Z₁) (U := U₁) hX₁ hY₁,
    driftProc_eq_of_eqOn (P := P) (C := C) (Z := Z₂) (U := U₂) hX₂ hY₂,
    diffusionProc_eq_of_eqOn (P := P) (C := C) (Z := Z₁) (U := U₁) hX₁ hY₁,
    diffusionProc_eq_of_eqOn (P := P) (C := C) (Z := Z₂) (U := U₂) hX₂ hY₂,
    driverProc_eq_of_eqOn (P := P) (C := C) (Z := Z₁) (U := U₁) hX₁ hY₁,
    driverProc_eq_of_eqOn (P := P) (C := C) (Z := Z₂) (U := U₂) hX₂ hY₂,
    terminalVal_eq_of_eq (P := P) (C := C) fun i => hX₁ i T hTm,
    terminalVal_eq_of_eq (P := P) (C := C) fun i => hX₂ i T hTm] at hD
  exact ⟨X₁', X₂', Y₁', Y₂', fun i t ht => ⟨hX₁ i t ht, hX₂ i t ht⟩,
    fun k t ht => ⟨hY₁ k t ht, hY₂ k t ht⟩, hD⟩

/-- **The forced jump integrand at the predictable tuple.** For a solution of the `λ`-forced
system in `ℍ²` with jump representative `γ`, coefficients with the joint measurability (2.3),
`T ≥ 0`, and every path of `X` and `Y` with left limits at every time of `(0, T]`, the forced jump
integrand `λ γ_{i,s}(ω, e) + q^h_{i,s}(ω, e)` agrees, almost everywhere for the marked energy
measure on `[0, T]`, with `λ coeffJump(h, Θ⁻)_{i,s}(ω, e) + q^h_{i,s}(ω, e)`, the canonical
representative of `λ h(s, Θ⁻_s, e, μ⁻_s) + q^h_s(e)`. -/
theorem PaperWeakSolutionForcedInt.ae_forcedJump_leftLim_eq
    (h : PaperWeakSolutionForcedInt D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ)
    (hT : 0 ≤ T) (hC : Existence.CoeffBorel T C)
    (hXl : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 l))
    (hYl : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l))
    (i : Fin n) :
    ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
      lam * jumpProc T (Existence.coeffJump P T C (leftLimProc X) (leftLimProc Y) Z U) i q.2.1
          q.1 q.2.2 + qh i q.2.1 q.1 q.2.2
        = lam * jumpProc T γ i q.2.1 q.1 q.2.2 + qh i q.2.1 q.1 q.2.2 := by
  obtain ⟨X', Y', hXe, hYe, hs⟩ := h.exists_solvesForcedInt hT
  have hclamp : Measurable fun t : ℝ => max 0 (min t T) :=
    (continuous_const.max (continuous_id.min continuous_const)).measurable
  have hclampI : ∀ t ∈ Set.Icc (0 : ℝ) T, max 0 (min t T) = t := fun t ht => by
    rw [min_eq_left ht.2, max_eq_right ht.1]
  -- the paths frozen outside `[0, T]`
  set Xf : Fin n → ℝ → Ω → ℝ := fun i t => X' i (max 0 (min t T)) with hXf
  set Yf : Fin m → ℝ → Ω → ℝ := fun k t => Y' k (max 0 (min t T)) with hYf
  have hXfm : ∀ i, Measurable (Function.uncurry fun ω s => Xf i s ω) := fun i =>
    (hs.measurable_X i).comp (measurable_fst.prodMk (hclamp.comp measurable_snd))
  have hYfm : ∀ k, Measurable (Function.uncurry fun ω s => Yf k s ω) := fun k =>
    (hs.measurable_Y k).comp (measurable_fst.prodMk (hclamp.comp measurable_snd))
  have hXeq : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Xf i t = X i t := fun i t ht => by
    simp only [hXf, hclampI t ht, hXe i t ht]
  have hYeq : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Yf k t = Y k t := fun k t ht => by
    simp only [hYf, hclampI t ht, hYe k t ht]
  have hX'l : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
      Tendsto (fun s => X' i s ω) (𝓝[<] t) (𝓝 l) := fun i ω =>
    Existence.exists_tendsto_nhdsLT_of_eqOn (fun t ht => congrFun (hXe i t ht) ω) (hXl i ω)
  have hY'l : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
      Tendsto (fun s => Y' k s ω) (𝓝[<] t) (𝓝 l) := fun k ω =>
    Existence.exists_tendsto_nhdsLT_of_eqOn (fun t ht => congrFun (hYe k t ht) ω) (hYl k ω)
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
      Existence.leftLim_eq_of_eqOn (fun t ht => congrFun (hXeq i t ht) ω) (hXl i ω) hsI
    have hy : ∀ k, leftLimProc Yf k s = leftLimProc Y k s := fun k => funext fun ω =>
      Existence.leftLim_eq_of_eqOn (fun t ht => congrFun (hYeq k t ht) ω) (hYl k ω) hsI
    funext ω
    simp only [tupleAt, hx, hy]
  -- the frozen forced integrand is jointly measurable and agrees with the solution's
  have hXlm := measurable_uncurry_leftLimProc hXfm hXfl
  have hYlm := measurable_uncurry_leftLimProc hYfm hYfl
  have hF : Measurable fun q : Ω × ℝ × E =>
      lam * jumpProc T (Existence.coeffJump P T C (leftLimProc Xf) (leftLimProc Yf) Z U) i q.2.1
        q.1 q.2.2 + qh i q.2.1 q.1 q.2.2 :=
    ((Existence.measurable_jumpProc_coeffJump hC hXlm hYlm hZm hUm i).const_mul lam).add
      (h.forcing.qh_meas i)
  have hΘ := ae_ae_tupleAt_leftLimProc_eq (ν := ν) (P := P) (Z := Z) (U := U) hXfm hYfm hXfr
    hXfl hYfr hYfl
  have h1 := Existence.ae_markedEnergyMeasure_of_ae_ae_ae (P := P) (ν := ν) (T := T)
    (measurableSet_eq_fun hF (h.γ_meas i)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc, h.jump_rep_tupleAt hT,
        ae_restrict_of_ae hΘ] with s hsI hγ hθ
      have htup : tupleAt ν Xf Yf Z U s = tupleAt ν X Y Z U s := tupleAt_eq_of_eqOn hXeq hYeq hsI
      filter_upwards [hγ, hθ] with ω hγω hθω
      have e₂ := Existence.coeffJump_ae_eq (P := P) (C := C) (X := leftLimProc Xf)
        (Y := leftLimProc Yf) (Z := Z) (U := U) hsI ω
      rw [hθω, lawP2_congr hθ, htup] at e₂
      filter_upwards [e₂, hγω] with e h₂ h₄
      have c := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) (h₂.trans h₄.symm)
      simp only at c
      simp only [jumpProc, Set.indicator_of_mem hsI, c])
  -- almost every time of the horizon lies in `(0, T]`
  have h2 := Existence.ae_markedEnergyMeasure_of_ae_ae_ae (P := P) (ν := ν) (T := T)
    (p := fun q : Ω × ℝ × E => q.2.1 ∈ Set.Ioc (0 : ℝ) T)
    (measurableSet_Ioc.preimage measurable_snd.fst) (by
      have hs : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Ioc (0 : ℝ) T := by
        rw [ae_restrict_iff' measurableSet_Icc]
        filter_upwards [(Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := T)).mem_iff]
          with s hs' hsI
        exact hs'.mpr hsI
      filter_upwards [hs] with s hs
      exact ae_of_all _ fun _ => ae_of_all _ fun _ => hs)
  filter_upwards [h1, h2] with q hq hqI
  have hqI' : q.2.1 ∈ Set.Icc (0 : ℝ) T := Set.Ioc_subset_Icc_self hqI
  rw [← hq]
  simp only [jumpProc, Set.indicator_of_mem hqI',
    Existence.coeffJump_eq_of_tupleAt_eq hqI' (hleft _ hqI)]

/-- **The forced jump integrands of two solutions at the predictable tuples.** For two solutions
of the `λ`-forced system in `ℍ²` with the same coefficients, with the joint measurability
(2.3), `T ≥ 0`, and every path of `X^k` and `Y^k` with left limits at every time of `(0, T]`,
almost everywhere for the marked energy measure on `[0, T]`, for every coordinate `i`,
`λ (coeffJump(h, Θ¹⁻) − coeffJump(h, Θ²⁻))_i + δq^h_i = λ (γ¹ − γ²)_i + δq^h_i`. -/
theorem PaperWeakSolutionForcedInt.ae_forcedJump_sub_leftLim_eq
    (h₁ : PaperWeakSolutionForcedInt D ℱ hℱW hℱN T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : PaperWeakSolutionForcedInt D ℱ hℱW hℱN T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hT : 0 ≤ T) (hC : Existence.CoeffBorel T C)
    (hXl₁ : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X₁ i s ω) (𝓝[<] t) (𝓝 l))
    (hYl₁ : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y₁ k s ω) (𝓝[<] t) (𝓝 l))
    (hXl₂ : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X₂ i s ω) (𝓝[<] t) (𝓝 l))
    (hYl₂ : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y₂ k s ω) (𝓝[<] t) (𝓝 l)) :
    ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T), ∀ i,
      lam * (jumpProc T (Existence.coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
            q.2.1 q.1 q.2.2
          - jumpProc T (Existence.coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
            q.2.1 q.1 q.2.2) + (qh₁ i q.2.1 q.1 q.2.2 - qh₂ i q.2.1 q.1 q.2.2)
        = lam * (jumpProc T γ₁ i q.2.1 q.1 q.2.2 - jumpProc T γ₂ i q.2.1 q.1 q.2.2)
          + (qh₁ i q.2.1 q.1 q.2.2 - qh₂ i q.2.1 q.1 q.2.2) := by
  filter_upwards [ae_all_iff.mpr fun i => h₁.ae_forcedJump_leftLim_eq hT hC hXl₁ hYl₁ i,
    ae_all_iff.mpr fun i => h₂.ae_forcedJump_leftLim_eq hT hC hXl₂ hYl₂ i] with q e₁ e₂ i
  linear_combination e₁ i - e₂ i

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] [IsProbabilityMeasure P] in
/-- **The data size of a square-integrable initial datum and a forcing is finite.** -/
theorem Forcing.dataSize_ne_top_of_memLp
    (hq : Forcing ℱ P ν T qb qσ qh qf qg) (hξ : ∀ i, MemLp (ξ₀ i) 2 P) :
    dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤ := by
  unfold dataSize
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨(lintegral_esq_lt_top hξ).ne, (lintegral_esq_lt_top hq.qg_sq).ne⟩,
      ENNReal.sum_ne_top.mpr fun i _ => hq.qb_sq i⟩,
      ENNReal.sum_ne_top.mpr fun i _ => ENNReal.sum_ne_top.mpr fun j _ => hq.qσ_sq i j⟩,
    ENNReal.sum_ne_top.mpr fun i _ => hq.qh_sq i⟩, ENNReal.sum_ne_top.mpr fun k _ => hq.qf_sq k⟩

end Dissertation.WellPosedness.System
