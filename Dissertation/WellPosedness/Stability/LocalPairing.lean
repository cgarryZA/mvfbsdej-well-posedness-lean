/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.LocalMartingales

/-!
# The weights `G Y_{s−}` of the stochastic terms of the `G`-energy identity

The stochastic terms of the pathwise `G`-energy identity of Lemma 4.3 pair a left limit with a
stochastic differential through the coupling matrix `G`:
`⟨G δX_{s−}, δZ_s dW_s⟩ = ∑_k (G δX_{s−})_k δZ_{k,s} dW_s` and
`⟨G Σ_s dW_s, δY_{s−}⟩ = ∑_i (Gᵀ δY_{s−})_i Σ_{i,s} dW_s`, and the same with `Ñ`. The weights
`w = G Y_{s−} 1_{(0, T]}(s)` are jointly and progressively measurable, at most `(∑ |G_{ki}|) R` at
a time before which `|Y| ≤ R`, and `|w_s|² ≤ C² sup_{t ≤ T} |Y_t|²` when `|G x| ≤ C |x|`, as
`Martingale.localBrownian_weight` and `Martingale.localCompensated_weight` ask.

The pairing `⟨h, Gᵀ u⟩` of two marked integrands is integrable against `dP ⊗ ds ⊗ ν` by the
Cauchy–Schwarz inequality, `𝔼 ∫_0^T ∫_E |⟨h, Gᵀ u⟩| ν(de) ds ≤ C ‖h‖ ‖u‖` with the norms of
`L²(dP ⊗ ds ⊗ ν)`.

## Main definitions

* `Dissertation.WellPosedness.Stability.matLeftLimWeight` — the weight `G Y_{s−} 1_{(0, T]}(s)`.

## Main statements

* `Dissertation.WellPosedness.Stability.matLeftLimWeight_props` — its properties.
* `Dissertation.WellPosedness.Stability.sum_mulVec_mul_eq` — `⟨G v, y⟩ = ⟨Gᵀ y, v⟩`.
* `Dissertation.WellPosedness.Stability.lintegral_abs_dotProduct_le` — the Cauchy–Schwarz bound
  of the pairing of two marked integrands.
-/

open MeasureTheory Filter Set Matrix
open scoped ENNReal Topology

namespace Dissertation.WellPosedness.Stability

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Martingale LevyStochCalc

section Weight

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  {m n : ℕ}

/-- The weight `G Y_{s−}`: the left limits of `Y` at the times of `(0, T]`, `0` at other times,
mapped by the matrix `G`. -/
noncomputable def matLeftLimWeight (G : Matrix (Fin m) (Fin n) ℝ) (Y : Fin n → ℝ → Ω → ℝ)
    (T : ℝ) (k : Fin m) (s : ℝ) (ω : Ω) : ℝ :=
  (G *ᵥ fun i => if s ∈ Ioc (0 : ℝ) T then leftLimProc Y i s ω else 0) k

theorem matLeftLimWeight_eq (G : Matrix (Fin m) (Fin n) ℝ) (Y : Fin n → ℝ → Ω → ℝ) (k : Fin m)
    (s : ℝ) (ω : Ω) :
    matLeftLimWeight G Y T k s ω
      = ∑ i, G k i * (if s ∈ Ioc (0 : ℝ) T then Function.leftLim (fun r => Y i r ω) s else 0) :=
  rfl

/-- The properties of the weight `G Y_{s−}` that `localBrownian_weight` asks for, with `C` a
bound of `G` on `ℝⁿ`, and its vanishing off `(0, T]`. -/
theorem matLeftLimWeight_props (hℱneg : ∀ r : ℝ, r ≤ 0 → ℱ 0 ≤ ℱ r)
    (G : Matrix (Fin m) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hG : ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ C ^ 2 * (x ⬝ᵥ x))
    {Y : Fin n → ℝ → Ω → ℝ} (hYad : ∀ i, ∀ t ∈ Icc (0 : ℝ) T, Measurable[ℱ t] (Y i t))
    (hYl : ∀ i ω, ∀ t ∈ Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y i s ω) (𝓝[<] t) (𝓝 l)) :
    (∀ k, Measurable (Function.uncurry fun ω s => matLeftLimWeight G Y T k s ω))
    ∧ (∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => matLeftLimWeight G Y T k s ω)
    ∧ (∀ (R : ℝ), 0 ≤ R → ∀ k ω s, 0 ≤ s → s ≤ T →
        (∀ u, 0 ≤ u → u < s → ∀ i, |Y i u ω| ≤ R) →
          |matLeftLimWeight G Y T k s ω| ≤ (∑ k', ∑ i, |G k' i|) * R)
    ∧ (∀ ω, ∀ s ∈ Icc (0 : ℝ) T, ENNReal.ofReal (∑ k, matLeftLimWeight G Y T k s ω ^ 2)
        ≤ ENNReal.ofReal (C ^ 2) * ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2)
    ∧ ∀ k ω s, s ∉ Icc (0 : ℝ) T → matLeftLimWeight G Y T k s ω = 0 := by
  have hL := fun i => progressive_leftLim_Ioc (T := T) hℱneg (hYad i) (hYl i)
  refine ⟨fun k => ?_, fun k => ?_, ?_, ?_, ?_⟩
  · have h : Measurable (Function.uncurry fun ω s => ∑ i, G k i
        * (if s ∈ Ioc (0 : ℝ) T then Function.leftLim (fun r => Y i r ω) s else 0)) :=
      Finset.measurable_sum _ fun i _ => measurable_const.mul (hL i).1
    exact h
  · have h : Probability.ProgressivelyMeasurable ℱ fun ω s => ∑ i, G k i
        * (if s ∈ Ioc (0 : ℝ) T then Function.leftLim (fun r => Y i r ω) s else 0) :=
      progressivelyMeasurable_finset_sum _ fun i _ =>
        (Brownian.Ito.progressivelyMeasurable_const ℱ (G k i)).mul (hL i).2
    exact h
  · intro R hR k ω s hs0 hsT hb
    rw [matLeftLimWeight_eq]
    have hLb : ∀ i, |(if s ∈ Ioc (0 : ℝ) T then Function.leftLim (fun r => Y i r ω) s
        else 0)| ≤ R := fun i => by
      split_ifs with hs
      · obtain ⟨l, hl⟩ := hYl i ω s hs
        exact abs_leftLim_le hs.1 hl fun u hu hus => hb u hu hus i
      · rw [abs_zero]
        exact hR
    calc |∑ i, G k i
          * (if s ∈ Ioc (0 : ℝ) T then Function.leftLim (fun r => Y i r ω) s else 0)|
        ≤ ∑ i, |G k i| * R := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hLb i) (abs_nonneg _)
      _ = (∑ i, |G k i|) * R := by rw [Finset.sum_mul]
      _ ≤ (∑ k', ∑ i, |G k' i|) * R := by
          refine mul_le_mul_of_nonneg_right ?_ hR
          exact Finset.single_le_sum (f := fun k' => ∑ i, |G k' i|)
            (fun k' _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ k)
  · intro ω s hs
    set x : Fin n → ℝ := fun i =>
      if s ∈ Ioc (0 : ℝ) T then leftLimProc Y i s ω else 0 with hx
    have hsum : ∑ k, matLeftLimWeight G Y T k s ω ^ 2 = (G *ᵥ x) ⬝ᵥ (G *ᵥ x) := by
      simp only [dotProduct, sq]
      rfl
    rw [hsum]
    by_cases hs' : s ∈ Ioc (0 : ℝ) T
    · have hxx : x ⬝ᵥ x = ∑ i, Function.leftLim (fun r => Y i r ω) s ^ 2 := by
        simp only [dotProduct, hx, if_pos hs', sq]
        rfl
      calc ENNReal.ofReal ((G *ᵥ x) ⬝ᵥ (G *ᵥ x))
          ≤ ENNReal.ofReal (C ^ 2 * (x ⬝ᵥ x)) := ENNReal.ofReal_le_ofReal (hG x)
        _ = ENNReal.ofReal (C ^ 2)
              * ENNReal.ofReal (∑ i, Function.leftLim (fun r => Y i r ω) s ^ 2) := by
            rw [hxx, ENNReal.ofReal_mul (by positivity)]
        _ ≤ _ := by
            gcongr
            exact ofReal_sum_leftLim_sq_le hs' fun i => hYl i ω s hs'
    · have hx0 : x = 0 := funext fun i => if_neg hs'
      simp [hx0]
  · intro k ω s hs
    have hs' : s ∉ Ioc (0 : ℝ) T := fun h => hs ⟨h.1.le, h.2⟩
    have hx0 : (fun i => if s ∈ Ioc (0 : ℝ) T then leftLimProc Y i s ω else 0) = 0 :=
      funext fun i => if_neg hs'
    rw [matLeftLimWeight, hx0, mulVec_zero]
    rfl

end Weight

/-- `⟨G v, y⟩ = ⟨Gᵀ y, v⟩` in coordinates. -/
theorem sum_mulVec_mul_eq {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ)
    (y : Fin m → ℝ) : ∑ k, (G *ᵥ v) k * y k = ∑ i, (Gᵀ *ᵥ y) i * v i := by
  change (G *ᵥ v) ⬝ᵥ y = (Gᵀ *ᵥ y) ⬝ᵥ v
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose]

section Pairing

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {P : Measure Ω}
  {ν : Measure E} [SFinite P] [SFinite ν]

/-- An iterated integral over `Ω × [0, T] × E` is the integral against `dP ⊗ ds ⊗ ν`. -/
theorem lintegral_iter_eq_markedEnergyMeasure {F : Ω × ℝ × E → ℝ≥0∞} (hF : Measurable F)
    (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, F (ω, s, e) ∂ν ∂volume ∂P
      = ∫⁻ p, F p ∂(Poisson.Compensated.markedEnergyMeasure P ν T) := by
  rw [Poisson.Compensated.markedEnergyMeasure, lintegral_prod _ hF.aemeasurable]
  refine lintegral_congr fun ω => ?_
  exact (lintegral_prod (μ := volume.restrict (Icc (0 : ℝ) T)) (ν := ν)
    (fun y : ℝ × E => F (ω, y.1, y.2)) (hF.comp measurable_prodMk_left).aemeasurable).symm

/-- `|⟨h, Gᵀ u⟩| ≤ C |h| |u|` in `[0, ∞]`, for `|Gᵀ x| ≤ C |x|`. -/
theorem ofReal_abs_dotProduct_le {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hG : ∀ x : Fin m → ℝ, (Gᵀ *ᵥ x) ⬝ᵥ (Gᵀ *ᵥ x) ≤ C ^ 2 * (x ⬝ᵥ x)) (h : Fin n → ℝ)
    (u : Fin m → ℝ) :
    ENNReal.ofReal |h ⬝ᵥ (Gᵀ *ᵥ u)|
      ≤ ENNReal.ofReal C * (∑ i, (‖h i‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ)
        * (∑ k, (‖u k‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ h (Gᵀ *ᵥ u)
  have hsq : (h ⬝ᵥ (Gᵀ *ᵥ u)) ^ 2 ≤ C ^ 2 * (∑ i, h i ^ 2) * ∑ k, u k ^ 2 := by
    have e1 : ∑ i, (Gᵀ *ᵥ u) i ^ 2 = (Gᵀ *ᵥ u) ⬝ᵥ (Gᵀ *ᵥ u) := by
      simp only [dotProduct, sq]
    have e2 : u ⬝ᵥ u = ∑ k, u k ^ 2 := by simp only [dotProduct, sq]
    calc (h ⬝ᵥ (Gᵀ *ᵥ u)) ^ 2 ≤ (∑ i, h i ^ 2) * ∑ i, (Gᵀ *ᵥ u) i ^ 2 := hcs
      _ ≤ (∑ i, h i ^ 2) * (C ^ 2 * ∑ k, u k ^ 2) := by
          rw [e1, ← e2]
          exact mul_le_mul_of_nonneg_left (hG u) (Finset.sum_nonneg fun i _ => sq_nonneg _)
      _ = C ^ 2 * (∑ i, h i ^ 2) * ∑ k, u k ^ 2 := by ring
  have hab : ENNReal.ofReal |h ⬝ᵥ (Gᵀ *ᵥ u)|
      = ENNReal.ofReal ((h ⬝ᵥ (Gᵀ *ᵥ u)) ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← sq_abs, ofReal_sq_rpow_half (abs_nonneg _)]
  have hh : ENNReal.ofReal (∑ i, h i ^ 2) = ∑ i, (‖h i‖₊ : ℝ≥0∞) ^ 2 := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    exact Finset.sum_congr rfl fun i _ => (nnnorm_sq_eq_ofReal (h i)).symm
  have hu : ENNReal.ofReal (∑ k, u k ^ 2) = ∑ k, (‖u k‖₊ : ℝ≥0∞) ^ 2 := by
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
    exact Finset.sum_congr rfl fun k _ => (nnnorm_sq_eq_ofReal (u k)).symm
  rw [hab, ← hh, ← hu, ← ofReal_sq_rpow_half hC, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hsq) (by norm_num)

/-- **The pairing `⟨h, Gᵀ u⟩` of two marked integrands is integrable**:
`𝔼 ∫_0^T ∫_E |⟨h, Gᵀ u⟩| ν(de) ds ≤ C (𝔼 ∫_0^T ‖h_s‖² ds)^{1/2} (𝔼 ∫_0^T ‖u_s‖² ds)^{1/2}`,
with `‖·‖` the norm of `L²(ν)` and `|Gᵀ x| ≤ C |x|`. -/
theorem lintegral_abs_dotProduct_le {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hG : ∀ x : Fin m → ℝ, (Gᵀ *ᵥ x) ⬝ᵥ (Gᵀ *ᵥ x) ≤ C ^ 2 * (x ⬝ᵥ x))
    {H : Fin n → Ω → ℝ → E → ℝ} (hHm : ∀ i, Measurable fun p : Ω × ℝ × E => H i p.1 p.2.1 p.2.2)
    {U : Fin m → ℝ → Ω → E → ℝ} (hUm : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2)
    (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
        ENNReal.ofReal |(fun i => H i ω s e) ⬝ᵥ (Gᵀ *ᵥ fun k => U k s ω e)| ∂ν ∂volume ∂P
      ≤ ENNReal.ofReal C * (∑ i, Poisson.Compensated.markedEnergy P ν T (H i)) ^ (1 / 2 : ℝ)
        * (∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e))
          ^ (1 / 2 : ℝ) := by
  set μ := Poisson.Compensated.markedEnergyMeasure P ν T
  have hh : Measurable fun p : Ω × ℝ × E => (fun i => H i p.1 p.2.1 p.2.2 : Fin n → ℝ) :=
    measurable_pi_lambda _ hHm
  have hu : Measurable fun p : Ω × ℝ × E => (fun k => U k p.2.1 p.1 p.2.2 : Fin m → ℝ) :=
    measurable_pi_lambda _ hUm
  have hcont : Continuous fun x : (Fin n → ℝ) × (Fin m → ℝ) => |x.1 ⬝ᵥ (Gᵀ *ᵥ x.2)| :=
    continuous_abs.comp (continuous_fst.dotProduct (continuous_const.matrix_mulVec continuous_snd))
  have hF : Measurable fun p : Ω × ℝ × E => ENNReal.ofReal
      |(fun i => H i p.1 p.2.1 p.2.2) ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2.1 p.1 p.2.2)| :=
    ENNReal.measurable_ofReal.comp (hcont.measurable.comp (hh.prodMk hu))
  have hA : ∀ i, Measurable fun p : Ω × ℝ × E => (‖H i p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => (hHm i).nnnorm.coe_nnreal_ennreal.pow_const 2
  have hB : ∀ k, Measurable fun p : Ω × ℝ × E => (‖U k p.2.1 p.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    fun k => (hUm k).nnnorm.coe_nnreal_ennreal.pow_const 2
  have hAs : Measurable fun p : Ω × ℝ × E => ∑ i, (‖H i p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hA i
  have hBs : Measurable fun p : Ω × ℝ × E => ∑ k, (‖U k p.2.1 p.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun k _ => hB k
  have hEA : ∫⁻ p, ∑ i, (‖H i p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 ∂μ
      = ∑ i, Poisson.Compensated.markedEnergy P ν T (H i) := by
    rw [lintegral_finsetSum _ fun i _ => hA i]
    exact Finset.sum_congr rfl fun i _ =>
      (lintegral_iter_eq_markedEnergyMeasure (hA i) T).symm
  have hEB : ∫⁻ p, ∑ k, (‖U k p.2.1 p.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 ∂μ
      = ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) := by
    rw [lintegral_finsetSum _ fun k _ => hB k]
    exact Finset.sum_congr rfl fun k _ =>
      (lintegral_iter_eq_markedEnergyMeasure (hB k) T).symm
  rw [lintegral_iter_eq_markedEnergyMeasure (F := fun p : Ω × ℝ × E => ENNReal.ofReal
      |(fun i => H i p.1 p.2.1 p.2.2) ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2.1 p.1 p.2.2)|) hF T,
    ← hEA, ← hEB]
  calc ∫⁻ p, ENNReal.ofReal
        |(fun i => H i p.1 p.2.1 p.2.2) ⬝ᵥ (Gᵀ *ᵥ fun k => U k p.2.1 p.1 p.2.2)| ∂μ
      ≤ ∫⁻ p, ENNReal.ofReal C * (∑ i, (‖H i p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ)
          * (∑ k, (‖U k p.2.1 p.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) ∂μ :=
        lintegral_mono fun p => ofReal_abs_dotProduct_le G hC hG _ _
    _ ≤ _ := lintegral_mul_sqrt_le hAs.aemeasurable hBs.aemeasurable _

end Pairing

end Dissertation.WellPosedness.Stability
