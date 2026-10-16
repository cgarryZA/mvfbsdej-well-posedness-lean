/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.PicardWellPosed
import LevyStochCalc.Probability.ProgressiveCadlag
import Dissertation.WellPosedness.Enlarged.Driver
import Dissertation.WellPosedness.Existence.Congr
import Dissertation.WellPosedness.Examples.Dealer.ExposureMarks

/-!
# Example 5.5: the linear exposure equation

On the dealer mark space `E = {−1, +1} × (0, 1]` with the mark measure
`ν(dς, dq) = c_ς q^{−1−ϱ} dς dq`, `c_{±1} = (2 − ϱ)/2`, `ϱ < 2`, and a Lévy driver with one
Brownian coordinate `W` and compensated Poisson random measure `Ñ` with mark measure `ν`, the
linear exposure equation of Example 5.5 of the well-posedness paper is

`X⁰_t = ∫_0^t (−X⁰_s ds + ½ dW_s) + ½ ∫_0^t ∫_E (ς q + q X⁰_{s−}) Ñ(ds, dς, dq)`,   `X⁰_0 = 0`,

the forward equation of the exposure-sensitive dealer system along the tuple
`(X⁰, X⁰, ½, ½ (h_c + h_x X⁰))` with `h_c(ς, q) = ς q` and `h_x(ς, q) = q`. Its coefficients
are Lipschitz in the state: `|δ(−x)| = |δx|` and `∫_E (q δx / 2)² ν(dς, dq) = |δx|² / 4`, since
`∫_E q² ν(dς, dq) = 1`. So it has a solution over every right-continuous filtration carrying the
driver whose time-`0` field contains the null sets and which is constant before `0`, in
particular over the initially enlarged filtration `enlJoint 𝒢₀ D h𝒢₀`.

The solution is recorded as a solution of the linear forward equation `LinearFSDEJ` with initial
value `0` and the integrands `exposureDrift`, `exposureDiffusion` and `exposureJump` along it,
each restricted to `[0, T]`. As in `LinearFSDEJ`, the jump integrand is evaluated at `X⁰_s`
rather than `X⁰_{s−}`; the two agree off a countable set of times on every path with left
limits, and the compensated integral does not tell them apart. Every path of the solution is
right-continuous and the solution is adapted.

## Main definitions

* `exposureSDECoeffs` — the coefficients of the exposure equation on `[0, T]`, as a jump
  diffusion.
* `exposureDrift`, `exposureDiffusion`, `exposureJump` — the integrands `−X_s`, `½` and
  `½ (ς q + q X_s)` on `[0, T]`, and `0` off it.

## Main statements

* `isLipschitz_exposureSDECoeffs`, `isRegular_exposureSDECoeffs` — the coefficients are
  Lipschitz in the state with constant `1`, and regular in time and mark.
* `exists_linearFSDEJ_exposure` — the exposure equation has a solution over every filtration
  satisfying the usual conditions and carrying the driver.
* `exists_linearFSDEJ_exposure_enlJoint` — the same over `enlJoint 𝒢₀ D h𝒢₀`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.Stability Dissertation.WellPosedness.Enlarged LevyStochCalc

universe u w

/-! ### The coefficients -/

/-- The coefficients of the exposure equation on the horizon `[0, T]`, as a jump diffusion on
`ℝ¹` driven by one Brownian coordinate and the marks `(ς, q)`: the drift `−x`, the diffusion `½`
and the jump coefficient `½ (ς q + q x)` on `[0, T]`, and `0` off it. -/
noncomputable def exposureSDECoeffs (T : ℝ) :
    LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs 1 1 DealerMark where
  μ s x _ := (Set.Icc (0 : ℝ) T).indicator (fun _ => -x 0) s
  σ s _ _ _ := (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) s
  γ s x e _ := (Set.Icc (0 : ℝ) T).indicator (fun _ => (signedSize e + (e.2 : ℝ) * x 0) / 2) s

/-- The signed size `ς q` of a mark is measurable. -/
theorem measurable_signedSize : Measurable signedSize :=
  ((measurable_of_countable markSide).comp measurable_fst).mul
    (measurable_subtype_coe.comp measurable_snd)

/-- The dealer mark space is countably generated. -/
instance countablyGenerated_dealerMark : MeasurableSpace.CountablyGenerated DealerMark :=
  inferInstance

/-- A bounded nonnegative function of time has finite integral over `[0, T']`. -/
theorem setLIntegral_Icc_lt_top_of_le {f : ℝ → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hf : ∀ s, f s ≤ C) (T' : ℝ) : ∫⁻ s in Set.Icc (0 : ℝ) T', f s < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono hf) ?_
  rw [setLIntegral_const, Real.volume_Icc]
  exact ENNReal.mul_lt_top hC.lt_top ENNReal.ofReal_lt_top

variable {c : Bool → ℝ} {ϱ : ℝ}

/-- With `c_{±1} = (2 − ϱ)/2`, `∫_E q² ν(dς, dq) = 1`, as an extended integral. -/
theorem lintegral_markSize_sq_eq_one (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) :
    ∫⁻ e, ENNReal.ofReal ((e.2 : ℝ) ^ 2) ∂dealerMarks c ϱ = 1 := by
  have h0 : ∀ b, 0 ≤ c b := fun b => by rw [hc]; linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_markSize_sq c hϱ)
    (Eventually.of_forall fun _ => sq_nonneg _), integral_markSize_sq h0 hϱ,
    rate_sum_div_eq_one hϱ hc, ENNReal.ofReal_one]

/-- **The coefficients of the exposure equation are Lipschitz in the state**, with constant `1`:
`|δ(−x)| = |δx|`, the diffusion is constant, and `∫_E (q δx / 2)² ν(dς, dq) ≤ |δx|²`. -/
theorem isLipschitz_exposureSDECoeffs (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) (T : ℝ) :
    (exposureSDECoeffs T).IsLipschitz (dealerMarks c ϱ) 1 := by
  refine ⟨zero_le_one, fun s x₁ x₂ => ?_, fun s x₁ x₂ => ?_, fun s x₁ x₂ => ?_⟩
  · rw [one_mul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    simp only [Pi.sub_apply, exposureSDECoeffs]
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, neg_sub_neg, norm_sub_rev]
      exact norm_le_pi_norm (x₁ - x₂) 0
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, sub_zero, norm_zero]
      exact norm_nonneg _
  · simp only [exposureSDECoeffs, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, one_pow, one_mul]
    positivity
  · have hpt : ∀ e : DealerMark,
        (‖(exposureSDECoeffs T).γ s x₁ e - (exposureSDECoeffs T).γ s x₂ e‖₊ : ℝ≥0∞) ^ 2
          ≤ ENNReal.ofReal ((e.2 : ℝ) ^ 2) * ENNReal.ofReal (‖x₁ - x₂‖ ^ 2) := fun e => by
      set a : ℝ := (Set.Icc (0 : ℝ) T).indicator
          (fun _ => (signedSize e + (e.2 : ℝ) * x₁ 0) / 2) s
        - (Set.Icc (0 : ℝ) T).indicator (fun _ => (signedSize e + (e.2 : ℝ) * x₂ 0) / 2) s
        with ha
      have hv : (exposureSDECoeffs T).γ s x₁ e - (exposureSDECoeffs T).γ s x₂ e
          = fun _ => a := funext fun _ => rfl
      have hδ : (x₁ 0 - x₂ 0) ^ 2 ≤ ‖x₁ - x₂‖ ^ 2 := by
        rw [← sq_abs]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        rw [← Real.norm_eq_abs, ← Pi.sub_apply]
        exact norm_le_pi_norm (x₁ - x₂) 0
      have hle : a ^ 2 ≤ (e.2 : ℝ) ^ 2 * ‖x₁ - x₂‖ ^ 2 := by
        by_cases hs : s ∈ Set.Icc (0 : ℝ) T
        · rw [ha, Set.indicator_of_mem hs, Set.indicator_of_mem hs]
          have e1 : (signedSize e + (e.2 : ℝ) * x₁ 0) / 2 - (signedSize e + (e.2 : ℝ) * x₂ 0) / 2
              = (e.2 : ℝ) * (x₁ 0 - x₂ 0) / 2 := by ring
          rw [e1, div_pow, mul_pow]
          nlinarith [mul_le_mul_of_nonneg_left hδ (sq_nonneg (e.2 : ℝ)),
            sq_nonneg ((e.2 : ℝ) * (x₁ 0 - x₂ 0))]
        · rw [ha, Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, sub_zero]
          norm_num
          positivity
      rw [hv, pi_nnnorm_const, Ito.Picard.sq_coe_nnnorm_real, ← ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hle
    refine le_trans (lintegral_mono hpt) (le_of_eq ?_)
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_markSize_sq_eq_one hϱ hc,
      one_mul, one_pow, one_mul]

/-- **The coefficients of the exposure equation are regular**: jointly measurable, and square
integrable in time at the state `0`. -/
theorem isRegular_exposureSDECoeffs (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) (T : ℝ) :
    (exposureSDECoeffs T).IsRegular (dealerMarks c ϱ) := by
  have hI : MeasurableSet (Set.Icc (0 : ℝ) T) := measurableSet_Icc
  refine ⟨?_, ?_, ?_, fun T' _ => ?_, fun T' _ => ?_, fun T' _ => ?_⟩
  · refine measurable_pi_lambda _ fun _ => ?_
    simp only [Function.uncurry, exposureSDECoeffs, Set.indicator_apply]
    exact Measurable.ite (hI.preimage measurable_fst)
      ((measurable_pi_apply 0).comp measurable_snd).neg measurable_const
  · refine measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => ?_
    simp only [Function.uncurry, exposureSDECoeffs, Set.indicator_apply]
    exact Measurable.ite (hI.preimage measurable_fst) measurable_const measurable_const
  · refine measurable_pi_lambda _ fun _ => ?_
    simp only [exposureSDECoeffs, Set.indicator_apply]
    refine Measurable.ite (hI.preimage measurable_fst) ?_ measurable_const
    exact ((measurable_signedSize.comp (measurable_snd.comp measurable_snd)).add
      ((measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).mul
        ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd)))).div_const 2
  · refine setLIntegral_Icc_lt_top_of_le ENNReal.zero_ne_top (fun s => ?_) T'
    simp [exposureSDECoeffs]
  · refine setLIntegral_Icc_lt_top_of_le ENNReal.one_ne_top (fun s => ?_) T'
    simp only [exposureSDECoeffs, Finset.univ_unique, Finset.sum_singleton]
    rw [Ito.Picard.sq_coe_nnnorm_real, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem hs]; norm_num
    · rw [Set.indicator_of_notMem hs]; norm_num
  · refine setLIntegral_Icc_lt_top_of_le ENNReal.one_ne_top (fun s => ?_) T'
    rw [← lintegral_markSize_sq_eq_one hϱ hc]
    refine lintegral_mono fun e => ?_
    have hv : (exposureSDECoeffs T).γ s 0 e
        = fun _ => (Set.Icc (0 : ℝ) T).indicator (fun _ => signedSize e / 2) s :=
      funext fun _ => by simp only [exposureSDECoeffs, Pi.zero_apply, mul_zero, add_zero]
    rw [hv, pi_nnnorm_const, Ito.Picard.sq_coe_nnnorm_real]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem hs, div_pow, signedSize, mul_pow, markSide_sq, one_mul]
      nlinarith [sq_nonneg (e.2 : ℝ)]
    · rw [Set.indicator_of_notMem hs]; norm_num; positivity

/-! ### The integrands of the linear forward equation -/

section Process

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}

/-- The drift of the exposure equation along a path `X`: `−X_s` on `[0, T]`, and `0` off it. -/
noncomputable def exposureDrift (T : ℝ) (X : ℝ → Ω → ℝ) (ω : Ω) (s : ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) T).indicator (fun s => -X s ω) s

variable (Ω) in
/-- The diffusion of the exposure equation: `½` on `[0, T]`, and `0` off it. -/
noncomputable def exposureDiffusion (T : ℝ) (s : ℝ) (_ω : Ω) (_j : Fin 1) : ℝ :=
  (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) s

/-- The jump integrand of the exposure equation along a path `X`: `½ (ς q + q X_s)` on
`[0, T]`, and `0` off it. -/
noncomputable def exposureJump (T : ℝ) (X : ℝ → Ω → ℝ) (s : ℝ) (ω : Ω) (e : DealerMark) : ℝ :=
  (Set.Icc (0 : ℝ) T).indicator (fun s => (signedSize e + (e.2 : ℝ) * X s ω) / 2) s

/-! ### A right-continuous modification -/

omit [IsProbabilityMeasure P] in
/-- **A right-continuous adapted modification.** Let `X` be a jointly measurable process on
`ℝ¹`, progressively measurable, whose almost every path is right-continuous on `[0, ∞)`, over a
filtration constant before `0` whose time-`0` field contains the null sets. Then there is a
jointly measurable, adapted process `X'` with every path right-continuous at every time which
agrees with `X` at every time of `[0, ∞)`, almost surely. -/
theorem exists_rightCont_modification {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {X : ℝ → Ω → (Fin 1 → ℝ)} (hXm : Measurable (Function.uncurry X))
    (hXa : ∀ i : Fin 1, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i)
    (hXr : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))) :
    ∃ X' : ℝ → Ω → (Fin 1 → ℝ), Measurable (Function.uncurry X')
      ∧ (∀ t, Measurable[ℱ t] (X' t))
      ∧ (∀ ω t, Tendsto (fun s => X' s ω) (𝓝[>] t) (𝓝 (X' t ω)))
      ∧ ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → X' t ω = X t ω := by
  classical
  set B : Set Ω := {ω | ¬ ∀ t : ℝ, 0 ≤ t → Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))}
    with hBdef
  have hB : P B = 0 := ae_iff.1 hXr
  set N := toMeasurable P B with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable P B
  have hN0 : P N = 0 := by rw [hNdef, measure_toMeasurable]; exact hB
  have hNt : ∀ t, MeasurableSet[ℱ t] N := fun t => by
    rcases le_total 0 t with ht | ht
    · exact ℱ.mono ht _ (hnull N hNm hN0)
    · exact hℱ0 t ht _ (hnull N hNm hN0)
  have hgood : ∀ ω ∉ N, ∀ t : ℝ, 0 ≤ t → Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω)) :=
    fun ω hω => by
      by_contra h
      exact hω (subset_toMeasurable P B h)
  refine ⟨fun t ω => if ω ∈ N then 0 else X (max t 0) ω, ?_, fun t => ?_, fun ω t => ?_, ?_⟩
  · exact Measurable.ite (hNm.preimage measurable_snd) measurable_const
      (hXm.comp ((measurable_fst.max measurable_const).prodMk measurable_snd))
  · have hmax : ℱ (max t 0) ≤ ℱ t := by
      rcases le_total 0 t with ht | ht
      · rw [max_eq_left ht]
      · rw [max_eq_right ht]; exact hℱ0 t ht
    have hX : Measurable[ℱ t] (X (max t 0)) := @measurable_pi_lambda Ω (Fin 1) (fun _ => ℝ)
      (ℱ t) _ _ fun i => (((hXa i).stronglyMeasurable_eval (max t 0)).measurable).mono hmax le_rfl
    exact Measurable.ite (m := ℱ t) (hNt t) measurable_const hX
  · by_cases hω : ω ∈ N
    · simp only [hω, if_true]
      exact tendsto_const_nhds
    · simp only [hω, if_false]
      rcases lt_or_ge t 0 with ht | ht
      · rw [max_eq_right ht.le]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs
        rw [max_eq_right (le_of_lt hs)]
      · rw [max_eq_left ht]
        refine (hgood ω hω t ht).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [max_eq_left (ht.trans (le_of_lt hs))]
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω t ht
    simp only [hω, if_false, max_eq_left ht]

omit [IsProbabilityMeasure P] in
/-- A process vanishing at every time, almost surely, has zero energy. -/
theorem energy_eq_zero_of_ae_forall {H : Ω → ℝ → ℝ} (h : ∀ᵐ ω ∂P, ∀ s, H ω s = 0) :
    Brownian.Ito.energy P T H = 0 := by
  unfold Brownian.Ito.energy
  rw [lintegral_congr_ae (g := fun _ => 0) (h.mono fun ω hω => by simp [hω]), lintegral_zero]

omit [IsProbabilityMeasure P] in
/-- A marked process vanishing at every time and mark, almost surely, has zero marked energy. -/
theorem markedEnergy_eq_zero_of_ae_forall {ν : Measure DealerMark}
    {φ : Ω → ℝ → DealerMark → ℝ} (h : ∀ᵐ ω ∂P, ∀ s e, φ ω s e = 0) :
    Poisson.Compensated.markedEnergy P ν T φ = 0 := by
  unfold Poisson.Compensated.markedEnergy
  rw [lintegral_congr_ae (g := fun _ => 0) (h.mono fun ω hω => by simp [hω]), lintegral_zero]

/-! ### Existence -/

open Ito.Picard in
/-- **The exposure equation has a solution.** Let `ν` be the dealer mark measure with
`c_{±1} = (2 − ϱ)/2`, `ϱ < 2`, `D` a Lévy driver with one Brownian coordinate and mark measure
`ν`, and `ℱ` a right-continuous filtration carrying `D`, constant before `0`, whose time-`0`
field contains the null sets. For `T > 0` there is an adapted process `X` with right-continuous
paths solving

`X_t = ∫_0^t (−X_s) ds + ∫_0^t ½ dW_s + ∫_0^t ∫_E ½ (ς q + q X_s) Ñ(ds, dς, dq)`,
`t ∈ [0, T]`,

almost surely at each time. -/
theorem exists_linearFSDEJ_exposure
    (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (dealerMarks c ϱ))
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) (hT : 0 < T) :
    ∃ X : ℝ → Ω → ℝ, LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X) := by
  have hReg := isRegular_exposureSDECoeffs hϱ hc T
  have hLip := isLipschitz_exposureSDECoeffs hϱ hc T
  have hvan : ∀ s, s ∉ Set.Icc (0 : ℝ) T → ∀ x : Fin 1 → ℝ,
      (exposureSDECoeffs T).μ s x = 0 ∧ (exposureSDECoeffs T).σ s x = 0
        ∧ ∀ e, (exposureSDECoeffs T).γ s x e = 0 := fun s hs x =>
    ⟨funext fun _ => by simp [exposureSDECoeffs, hs],
      funext fun _ => funext fun _ => by simp [exposureSDECoeffs, hs],
      fun e => funext fun _ => by simp [exposureSDECoeffs, hs]⟩
  have hσc : ∀ s (x y : Fin 1 → ℝ), (exposureSDECoeffs T).σ s x = (exposureSDECoeffs T).σ s y :=
    fun _ _ _ => rfl
  generalize hC : exposureSDECoeffs T = C at hReg hLip hvan hσc
  obtain ⟨X, hXm, hXa, -, hXcad, hXS, hXsol⟩ :=
    exists_globalSolution D.W D.N ℱ hℱW hℱN C hℱ0 hnull hReg hLip 0
  obtain ⟨X', hX'm, hX'ad, hX'rc, hX'eq⟩ := exists_rightCont_modification hℱ0 hnull hXm hXa
    (hXcad.mono fun ω hω t ht => (hω t ht).1)
  have hX'a : ∀ i : Fin 1, Probability.ProgressivelyMeasurable ℱ fun ω s => X' s ω i :=
    fun i => Probability.progressivelyMeasurable_of_rightContinuous (X := fun t ω => X' t ω i)
      (fun t => (measurable_pi_apply i).comp (hX'ad t))
      (fun ω t => ((continuous_apply i).tendsto _).comp (hX'rc ω t))
  have hX'S : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X' (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ :=
    fun T' hT' => by
      rw [lintegral_congr_ae (g := fun ω =>
        ⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ?_]
      · exact hXS T' hT'
      filter_upwards [hX'eq] with ω hω
      exact iSup_congr fun t => by rw [hω t t.2.1]
  have h1 : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (fun ω s => C.μ s (X s ω) 0)
      (fun t ω => X' t ω 0) (fun s ω => C.σ s (X s ω) 0) (fun s ω e => C.γ s (X s ω) e 0) :=
    { σ_meas := fun j => measurable_sigma_comp_state C hReg hXm 0 j
      σ_prog := fun j => progressivelyMeasurable_sigma_comp_state C hReg hXa 0 j
      σ_vanish := fun ω s hs => by rw [(hvan s hs _).2.1]; rfl
      σ_sq := fun j => (lintegral_sq_sigma_lt_top_of_supL2 C hReg hLip hXm hXS 0 j hT).ne
      γ_meas := measurable_gamma_comp_state C hReg hXm 0
      γ_prog := markedProgressivelyMeasurable_gamma_comp_state C hReg hXa 0
      γ_vanish := fun ω s e hs => by rw [(hvan s hs _).2.2 e]; rfl
      γ_sq := (lintegral_sq_gamma_lt_top_of_supL2 C hReg hLip hXm hXS 0 hT).ne
      b_meas := measurable_mu_comp_state C hReg hXm 0
      b_prog := progressivelyMeasurable_comp_state hXa (f := fun s x => C.μ s x 0)
        ((measurable_pi_apply 0).comp hReg.1)
      b_vanish := fun ω s hs => by rw [(hvan s hs _).1]; rfl
      b_sq := (lintegral_sq_mu_lt_top_of_energy C hReg hLip
        (lintegral_lintegral_sq_lt_top_of_supL2 hXS) 0 hT).ne
      ξ₀_sq := memLp_const 0
      X_adapted := fun t => (measurable_pi_apply 0).comp (hX'ad t)
      X_rightCont := fun ω t => ((continuous_apply 0).tendsto _).comp (hX'rc ω t)
      eqn := fun t ht => by
        filter_upwards [eqn_sum_form D.W D.N ℱ hℱW hℱN C 0 (hXsol T) ht, hX'eq] with ω h1 h2
        rw [h2 t ht.1]
        exact h1 0 }
  have hagree : ∀ᵐ ω ∂P, ∀ s, s ∈ Set.Icc (0 : ℝ) T → X s ω = X' s ω :=
    hX'eq.mono fun ω hω s hs => (hω s hs.1).symm
  have h2 := h1.congr (b' := fun ω s => C.μ s (X' s ω) 0)
    (σ' := fun s ω => C.σ s (X' s ω) 0) (γ' := fun s ω e => C.γ s (X' s ω) e 0)
    (measurable_mu_comp_state C hReg hX'm 0)
    (progressivelyMeasurable_comp_state hX'a (f := fun s x => C.μ s x 0)
      ((measurable_pi_apply 0).comp hReg.1))
    (fun ω s hs => by rw [(hvan s hs _).1]; rfl)
    (fun j => measurable_sigma_comp_state C hReg hX'm 0 j)
    (fun j => progressivelyMeasurable_sigma_comp_state C hReg hX'a 0 j)
    (fun ω s hs => by rw [(hvan s hs _).2.1]; rfl)
    (measurable_gamma_comp_state C hReg hX'm 0)
    (markedProgressivelyMeasurable_gamma_comp_state C hReg hX'a 0)
    (fun ω s e hs => by rw [(hvan s hs _).2.2 e]; rfl)
    (energy_eq_zero_of_ae_forall (hagree.mono fun ω hω s => by
      by_cases hs : s ∈ Set.Icc (0 : ℝ) T
      · simp only [hω s hs, sub_self]
      · rw [(hvan s hs _).1, (hvan s hs _).1]; simp))
    (fun j => energy_eq_zero_of_ae_forall (Eventually.of_forall fun ω s => by
      rw [hσc s (X s ω) (X' s ω), sub_self]))
    (markedEnergy_eq_zero_of_ae_forall (hagree.mono fun ω hω s e => by
      by_cases hs : s ∈ Set.Icc (0 : ℝ) T
      · simp only [hω s hs, sub_self]
      · rw [(hvan s hs _).2.2 e, (hvan s hs _).2.2 e]; simp))
  subst hC
  exact ⟨fun t ω => X' t ω 0, h2⟩

end Process

section Enlarged

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **The exposure equation over the initially enlarged filtration.** For a Lévy driver `D` with
one Brownian coordinate and the dealer mark measure with `c_{±1} = (2 − ϱ)/2`, `ϱ < 2`, and a
σ-algebra `𝒢₀` independent of its joint natural filtration, the exposure equation has, for every
`T > 0`, a solution over `enlJoint 𝒢₀ D h𝒢₀` starting at `0`. -/
theorem exists_linearFSDEJ_exposure_enlJoint
    (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (dealerMarks c ϱ))
    (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P)
    (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) (hT : 0 < T) :
    ∃ X : ℝ → Ω → ℝ, LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X) :=
  exists_linearFSDEJ_exposure D (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun _ ht => enlJoint_le_of_nonpos D h𝒢₀ ht)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hϱ hc hT

end Enlarged

end Dissertation.WellPosedness.Existence
