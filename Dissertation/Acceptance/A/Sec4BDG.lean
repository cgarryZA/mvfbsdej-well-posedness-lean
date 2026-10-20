/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4BDG
import Dissertation.WellPosedness.Stability.LocalPairing
import Dissertation.WellPosedness.Robustness.CouplingNorm
import Dissertation.Acceptance.A.Sec4Difference
import Dissertation.WellPosedness.System.JumpPredictable
import Dissertation.WellPosedness.BrownianPoisson.Compensation
import Dissertation.WellPosedness.Existence.ForcingAlgebra
import Dissertation.WellPosedness.System.SolvesPredictable

/-!
# The four stochastic integrals of the `G`-energy identity of Lemma 4.3 and (4.18): proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The weights
`G δX_{s−}` and `Gᵀ δY_{s−}`, cut to `(0, T]`, are predictable, bounded before `δX` (or `δY`)
leaves a ball, and at most `‖G‖ sup_{t ≤ T} |δX_t|` (or `|δY_t|`); `⟨G v, y⟩ = ⟨Gᵀ y, v⟩` writes
the second and fourth integrands with the weight `Gᵀ δY_{s−}`. With `𝔼 sup |δX|², 𝔼 sup |δY|²`
finite (`Θ¹ − Θ² ∈ ℍ`) and the integrability of `δZ`, `δU`, `λ δσ + q^σ` and `λ δh + q^h` from
(4.15) and (4.16), `localBrownian_weight` and `localCompensated_weight` give the local integrals,
the bounds with `c₀ = 9` and the zero means. The fifth integrand is bounded by the Cauchy–Schwarz
inequality (`lintegral_abs_dotProduct_le`). The hypotheses are those of Lemma 4.3, an instance of
which is `Dissertation.Acceptance.A.lem_pert_two_data_hypotheses`.

## Main statements

* `Dissertation.Acceptance.A.eq_bdg4_XZ` — the first bound of (4.18).
* `Dissertation.Acceptance.A.eq_bdg4_sigmaY` — the second bound of (4.18).
* `Dissertation.Acceptance.A.eq_bdg4_XU` — the third bound of (4.18).
* `Dissertation.Acceptance.A.eq_bdg4_hY` — the fourth bound of (4.18).
* `Dissertation.Acceptance.A.eq_bdg4_fifth` — the integrability of the forced integrands and of
  the fifth integrand.
* `Dissertation.Acceptance.A.eq_bdg4_fifth_mean` — the predictable integrand of the fifth term,
  from the predictable left-limit tuple (`exists_markedPredictable_coeffJump_leftLim`), and its
  zero mean by (2.2) (`integral_compensated_eq_zero`).
-/

open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped ENNReal Topology

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Martingale Dissertation.WellPosedness.Spec Dissertation.Law
  LevyStochCalc

universe u v w

/-- `9 ‖G‖ ≤ c ‖G‖` in `[0, ∞]` for `c ≥ 9`. -/
theorem nine_mul_ofReal_le {c C : ℝ} (hc : 9 ≤ c) (hC : 0 ≤ C) :
    9 * ENNReal.ofReal C ≤ ENNReal.ofReal (c * C) := by
  rw [show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hc hC)

/-- `|Gᵀ x| ≤ ‖G‖ |x|`, with `‖G‖` the operator norm. -/
theorem transpose_mulVec_dotProduct_le {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) : (Gᵀ *ᵥ x) ⬝ᵥ (Gᵀ *ᵥ x) ≤ ‖GX G‖ ^ 2 * (x ⬝ᵥ x) := by
  have h := mulVec_dotProduct_le Gᵀ x
  rwa [← adjoint_GX, norm_adjoint_GX] at h

/-- **The first bound of (4.18)**, with `c₀ = 9`. -/
theorem eq_bdg4_XZ : PaperSpec.A.eq_bdg4_XZ.{u, v, w} := by
  refine ⟨9, by norm_num, fun c hc => ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ hq₁
    hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hW₁ hW₂ hsize
  have hdY := fun k => (eq_dY.{u, v, w} 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ
    h23 hG h25 lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁
    qg₂ hq₁ hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hW₁ hW₂ hsize k).2.2
  choose hZm hZp hZq hUm hUp hUq _hYeq using hdY
  obtain ⟨⟨γ₁, h₁⟩, hXl₁, -⟩ := hW₁
  obtain ⟨⟨γ₂, h₂⟩, hXl₂, -⟩ := hW₂
  have hS := hsize
  simp only [supSize, ENNReal.add_lt_top] at hS
  obtain ⟨⟨⟨hSX, -⟩, hSZ⟩, -⟩ := hS
  have hXad : ∀ i, ∀ t ∈ Icc (0 : ℝ) T,
      Measurable[enlJoint 𝒢₀ D h𝒢₀ t] (fun ω => X₁ i t ω - X₂ i t ω) := fun i t ht =>
    (h₁.X_adapted i t ht).sub (h₂.X_adapted i t ht)
  have hXr : ∀ i ω, ∀ t ∈ Ico (0 : ℝ) T,
      Tendsto (fun s => X₁ i s ω - X₂ i s ω) (𝓝[>] t) (𝓝 (X₁ i t ω - X₂ i t ω)) :=
    fun i ω t ht => (h₁.X_rightCont i ω t ht).sub (h₂.X_rightCont i ω t ht)
  have hXl : ∀ i ω, ∀ t ∈ Ioc (0 : ℝ) T,
      ∃ l : ℝ, Tendsto (fun s => X₁ i s ω - X₂ i s ω) (𝓝[<] t) (𝓝 l) := fun i ω t ht => by
    obtain ⟨l₁, e₁⟩ := hXl₁ i ω t ht
    obtain ⟨l₂, e₂⟩ := hXl₂ i ω t ht
    exact ⟨l₁ - l₂, e₁.sub e₂⟩
  obtain ⟨hwm, hwp, hwb, hwsq, hwv⟩ := matLeftLimWeight_props (ℱ := enlJoint 𝒢₀ D h𝒢₀)
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) G (norm_nonneg (GX G)) (mulVec_dotProduct_le G)
    (Y := fun i t ω => X₁ i t ω - X₂ i t ω) hXad hXl
  have key := localBrownian_weight D.W (enlJoint 𝒢₀ D h𝒢₀)
    (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) hT hXad hXr hSX hwm hwp hwb (norm_nonneg _) hwsq
    (Z := fun k s ω j => Z₁ k s ω j - Z₂ k s ω j) hZm hZp hZq
    (fun k ω s hs => Or.inl (hwv k ω s hs))
  have hfin : ENNReal.ofReal (c * ‖GX G‖)
      * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, esq (fun i => X₁ i t ω - X₂ i t ω) ∂P) ^ (1 / 2 : ℝ)
      * (∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j))
        ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hSX.ne))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hSZ.ne)
  refine ⟨key.1, fun M hM => ⟨?_, hfin, (key.2 M hM).2⟩⟩
  calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 9 * ENNReal.ofReal ‖GX G‖
          * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖X₁ i t ω - X₂ i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
            ^ (1 / 2 : ℝ)
          * (∑ k, ∑ j, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T,
              (‖Z₁ k s ω j - Z₂ k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) ^ (1 / 2 : ℝ) :=
        (key.2 M hM).1
    _ ≤ _ := mul_le_mul' (mul_le_mul' (nine_mul_ofReal_le hc (norm_nonneg _)) le_rfl) le_rfl

/-- **The second bound of (4.18)**, with `c₀ = 9`. -/
theorem eq_bdg4_sigmaY : PaperSpec.A.eq_bdg4_sigmaY.{u, v, w} := by
  refine ⟨9, by norm_num, fun c hc => ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ hq₁
    hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hW₁ hW₂ hsize
  have hdX := fun i => (eq_dX.{u, v, w} 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ
    h23 hG h25 lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁
    qg₂ hq₁ hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hW₁ hW₂ hsize i).2
  choose hσm hσp hσq _hXrest using hdX
  obtain ⟨⟨γ₁, h₁⟩, -, hYl₁⟩ := hW₁
  obtain ⟨⟨γ₂, h₂⟩, -, hYl₂⟩ := hW₂
  have hS := hsize
  simp only [supSize, ENNReal.add_lt_top] at hS
  obtain ⟨⟨⟨-, hSY⟩, -⟩, -⟩ := hS
  have hYad : ∀ k, ∀ t ∈ Icc (0 : ℝ) T,
      Measurable[enlJoint 𝒢₀ D h𝒢₀ t] (fun ω => Y₁ k t ω - Y₂ k t ω) := fun k t ht =>
    (h₁.Y_adapted k t ht).sub (h₂.Y_adapted k t ht)
  have hYr : ∀ k ω, ∀ t ∈ Ico (0 : ℝ) T,
      Tendsto (fun s => Y₁ k s ω - Y₂ k s ω) (𝓝[>] t) (𝓝 (Y₁ k t ω - Y₂ k t ω)) :=
    fun k ω t ht => (h₁.Y_rightCont k ω t ht).sub (h₂.Y_rightCont k ω t ht)
  have hYl : ∀ k ω, ∀ t ∈ Ioc (0 : ℝ) T,
      ∃ l : ℝ, Tendsto (fun s => Y₁ k s ω - Y₂ k s ω) (𝓝[<] t) (𝓝 l) := fun k ω t ht => by
    obtain ⟨l₁, e₁⟩ := hYl₁ k ω t ht
    obtain ⟨l₂, e₂⟩ := hYl₂ k ω t ht
    exact ⟨l₁ - l₂, e₁.sub e₂⟩
  obtain ⟨hwm, hwp, hwb, hwsq, hwv⟩ := matLeftLimWeight_props (ℱ := enlJoint 𝒢₀ D h𝒢₀)
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) Gᵀ (norm_nonneg (GX G))
    (transpose_mulVec_dotProduct_le G) (Y := fun k t ω => Y₁ k t ω - Y₂ k t ω) hYad hYl
  have key := localBrownian_weight D.W (enlJoint 𝒢₀ D h𝒢₀)
    (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) hT hYad hYr hSY hwm hwp hwb (norm_nonneg _) hwsq
    (Z := fun i s ω j => lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
      - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j))
    hσm hσp hσq (fun k ω s hs => Or.inl (hwv k ω s hs))
  have hσfin : ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s =>
      lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j)) < ⊤ :=
    ENNReal.sum_lt_top.2 fun i _ => ENNReal.sum_lt_top.2 fun j _ => hσq i j T hT
  have hfin : ENNReal.ofReal (c * ‖GX G‖)
      * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω) ∂P) ^ (1 / 2 : ℝ)
      * (∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s =>
          lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j)))
        ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hSY.ne))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hσfin.ne)
  simp only [sum_mulVec_mul_eq G]
  refine ⟨key.1, fun M hM => ⟨?_, hfin, (key.2 M hM).2⟩⟩
  calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 9 * ENNReal.ofReal ‖GX G‖
          * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, ∑ k, (‖Y₁ k t ω - Y₂ k t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
            ^ (1 / 2 : ℝ)
          * (∑ i, ∑ j, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T,
              (‖lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
                - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j)‖₊
                  : ℝ≥0∞) ^ 2 ∂volume ∂P) ^ (1 / 2 : ℝ) :=
        (key.2 M hM).1
    _ ≤ _ := mul_le_mul' (mul_le_mul' (nine_mul_ofReal_le hc (norm_nonneg _)) le_rfl) le_rfl

/-- **The third bound of (4.18)**, with `c₀ = 9`. -/
theorem eq_bdg4_XU : PaperSpec.A.eq_bdg4_XU.{u, v, w} := by
  refine ⟨9, by norm_num, fun c hc => ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ hq₁
    hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hW₁ hW₂ hsize
  have hdY := fun k => (eq_dY.{u, v, w} 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ
    h23 hG h25 lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁
    qg₂ hq₁ hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hW₁ hW₂ hsize k).2.2
  choose hZm hZp hZq hUm hUp hUq _hYeq using hdY
  obtain ⟨⟨γ₁, h₁⟩, hXl₁, -⟩ := hW₁
  obtain ⟨⟨γ₂, h₂⟩, hXl₂, -⟩ := hW₂
  have hS := hsize
  simp only [supSize, ENNReal.add_lt_top] at hS
  obtain ⟨⟨⟨hSX, -⟩, -⟩, hSU⟩ := hS
  have hXad : ∀ i, ∀ t ∈ Icc (0 : ℝ) T,
      Measurable[enlJoint 𝒢₀ D h𝒢₀ t] (fun ω => X₁ i t ω - X₂ i t ω) := fun i t ht =>
    (h₁.X_adapted i t ht).sub (h₂.X_adapted i t ht)
  have hXr : ∀ i ω, ∀ t ∈ Ico (0 : ℝ) T,
      Tendsto (fun s => X₁ i s ω - X₂ i s ω) (𝓝[>] t) (𝓝 (X₁ i t ω - X₂ i t ω)) :=
    fun i ω t ht => (h₁.X_rightCont i ω t ht).sub (h₂.X_rightCont i ω t ht)
  have hXl : ∀ i ω, ∀ t ∈ Ioc (0 : ℝ) T,
      ∃ l : ℝ, Tendsto (fun s => X₁ i s ω - X₂ i s ω) (𝓝[<] t) (𝓝 l) := fun i ω t ht => by
    obtain ⟨l₁, e₁⟩ := hXl₁ i ω t ht
    obtain ⟨l₂, e₂⟩ := hXl₂ i ω t ht
    exact ⟨l₁ - l₂, e₁.sub e₂⟩
  obtain ⟨hwm, hwp, hwb, hwsq, hwv⟩ := matLeftLimWeight_props (ℱ := enlJoint 𝒢₀ D h𝒢₀)
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) G (norm_nonneg (GX G)) (mulVec_dotProduct_le G)
    (Y := fun i t ω => X₁ i t ω - X₂ i t ω) hXad hXl
  have key := localCompensated_weight D.N (enlJoint 𝒢₀ D h𝒢₀)
    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) hT hXad hXr hSX hwm hwp hwb (norm_nonneg _) hwsq
    (U := fun k s ω e => U₁ k s ω e - U₂ k s ω e) hUm hUp hUq
    (fun k ω s hs => Or.inl (hwv k ω s hs))
  have hfin : ENNReal.ofReal (c * ‖GX G‖)
      * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, esq (fun i => X₁ i t ω - X₂ i t ω) ∂P) ^ (1 / 2 : ℝ)
      * (∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ k s ω e - U₂ k s ω e))
        ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hSX.ne))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hSU.ne)
  refine ⟨key.1, fun M hM => ⟨?_, hfin, (key.2 M hM).2⟩⟩
  calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 9 * ENNReal.ofReal ‖GX G‖
          * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖X₁ i t ω - X₂ i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
            ^ (1 / 2 : ℝ)
          * (∑ k, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
              (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) ^ (1 / 2 : ℝ) :=
        (key.2 M hM).1
    _ ≤ _ := mul_le_mul' (mul_le_mul' (nine_mul_ofReal_le hc (norm_nonneg _)) le_rfl) le_rfl

/-- **The fourth bound of (4.18)**, with `c₀ = 9`. -/
theorem eq_bdg4_hY : PaperSpec.A.eq_bdg4_hY.{u, v, w} := by
  refine ⟨9, by norm_num, fun c hc => ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ hq₁
    hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hW₁ hW₂ hsize
  have hdX := fun i => (eq_dX.{u, v, w} 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ
    h23 hG h25 lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁
    qg₂ hq₁ hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hW₁ hW₂ hsize i).2
  choose _hσm _hσp _hσq hrest using hdX
  choose H₀ hH₀m hH₀p hH₀q hH₀ae using fun i => (hrest i).1
  obtain ⟨⟨γ₁, h₁⟩, -, hYl₁⟩ := hW₁
  obtain ⟨⟨γ₂, h₂⟩, -, hYl₂⟩ := hW₂
  have hS := hsize
  simp only [supSize, ENNReal.add_lt_top] at hS
  obtain ⟨⟨⟨-, hSY⟩, -⟩, -⟩ := hS
  have hYad : ∀ k, ∀ t ∈ Icc (0 : ℝ) T,
      Measurable[enlJoint 𝒢₀ D h𝒢₀ t] (fun ω => Y₁ k t ω - Y₂ k t ω) := fun k t ht =>
    (h₁.Y_adapted k t ht).sub (h₂.Y_adapted k t ht)
  have hYr : ∀ k ω, ∀ t ∈ Ico (0 : ℝ) T,
      Tendsto (fun s => Y₁ k s ω - Y₂ k s ω) (𝓝[>] t) (𝓝 (Y₁ k t ω - Y₂ k t ω)) :=
    fun k ω t ht => (h₁.Y_rightCont k ω t ht).sub (h₂.Y_rightCont k ω t ht)
  have hYl : ∀ k ω, ∀ t ∈ Ioc (0 : ℝ) T,
      ∃ l : ℝ, Tendsto (fun s => Y₁ k s ω - Y₂ k s ω) (𝓝[<] t) (𝓝 l) := fun k ω t ht => by
    obtain ⟨l₁, e₁⟩ := hYl₁ k ω t ht
    obtain ⟨l₂, e₂⟩ := hYl₂ k ω t ht
    exact ⟨l₁ - l₂, e₁.sub e₂⟩
  obtain ⟨hwm, hwp, hwb, hwsq, hwv⟩ := matLeftLimWeight_props (ℱ := enlJoint 𝒢₀ D h𝒢₀)
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) Gᵀ (norm_nonneg (GX G))
    (transpose_mulVec_dotProduct_le G) (Y := fun k t ω => Y₁ k t ω - Y₂ k t ω) hYad hYl
  refine ⟨⟨H₀, hH₀m, hH₀p, hH₀q, hH₀ae⟩, fun H hHm hHp hHq _ => ?_⟩
  have key := localCompensated_weight D.N (enlJoint 𝒢₀ D h𝒢₀)
    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (fun r hr => enlJoint_le_of_nonpos D h𝒢₀ hr) hT hYad hYr hSY hwm hwp hwb (norm_nonneg _) hwsq
    (U := fun i s ω e => H i ω s e) hHm hHp hHq (fun k ω s hs => Or.inl (hwv k ω s hs))
  have hfin : ENNReal.ofReal (c * ‖GX G‖)
      * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω) ∂P) ^ (1 / 2 : ℝ)
      * (∑ i, Poisson.Compensated.markedEnergy P ν T (H i)) ^ (1 / 2 : ℝ) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hSY.ne))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ENNReal.sum_lt_top.2 fun i _ => hHq i T hT).ne)
  simp only [sum_mulVec_mul_eq G]
  refine ⟨key.1, fun M hM => ⟨?_, hfin, (key.2 M hM).2⟩⟩
  calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 9 * ENNReal.ofReal ‖GX G‖
          * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, ∑ k, (‖Y₁ k t ω - Y₂ k t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
            ^ (1 / 2 : ℝ)
          * (∑ i, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
              (‖H i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) ^ (1 / 2 : ℝ) :=
        (key.2 M hM).1
    _ ≤ _ := mul_le_mul' (mul_le_mul' (nine_mul_ofReal_le hc (norm_nonneg _)) le_rfl) le_rfl

/-- **The integrability of the forced integrands and of the fifth integrand of (4.17).** -/
theorem eq_bdg4_fifth : PaperSpec.A.eq_bdg4_fifth.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ hq₁
    hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hW₁ hW₂ hsize
  have hdX := fun i => (eq_dX.{u, v, w} 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ
    h23 hG h25 lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁
    qg₂ hq₁ hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hW₁ hW₂ hsize i).2
  have hdY := fun k => (eq_dY.{u, v, w} 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ
    h23 hG h25 lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁
    qg₂ hq₁ hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hW₁ hW₂ hsize k).2.2
  choose _hσm _hσp hσq hrest using hdX
  choose H₀ hH₀m hH₀p hH₀q hH₀ae using fun i => (hrest i).1
  choose _hZm _hZp _hZq hUm _hUp _hUq _hYeq using hdY
  have hS := hsize
  simp only [supSize, ENNReal.add_lt_top] at hS
  obtain ⟨⟨⟨-, -⟩, -⟩, hSU⟩ := hS
  refine ⟨ENNReal.sum_lt_top.2 fun i _ => ENNReal.sum_lt_top.2 fun j _ => hσq i j T hT,
    ⟨H₀, hH₀m, hH₀p, hH₀q, hH₀ae⟩, fun H hHm hHp hHq _ => ?_⟩
  have hHfin : ∑ i, Poisson.Compensated.markedEnergy P ν T (H i) < ⊤ :=
    ENNReal.sum_lt_top.2 fun i _ => hHq i T hT
  refine ⟨hHfin, lintegral_abs_dotProduct_le G (norm_nonneg _)
    (transpose_mulVec_dotProduct_le G) hHm (U := fun k s ω e => U₁ k s ω e - U₂ k s ω e) hUm T,
    ?_⟩
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hHfin.ne))
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hSU.ne)

/-- **The fifth term of (4.17)**: its predictable integrand and its zero mean by (2.2). -/
theorem eq_bdg4_fifth_mean : PaperSpec.A.eq_bdg4_fifth_mean.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ h23 hG h25
    lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁ qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ hq₁
    hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hW₁ hW₂ hsize
  have hℱN := isPoissonFiltration_enlJoint D h𝒢₀ hind₀
  have hB : CoeffBorel T C := (jointBorel_iff.mp hJ).1.toCoeffBorel
  obtain ⟨-, ⟨H₀, hH₀m, -, hH₀q, hH₀ae⟩, -⟩ := eq_bdg4_fifth.{u, v, w} 𝒢₀ ν n m d P D h𝒢₀ hind₀
    hn hm hd T hT L α β₁ β₂ G C hJ h23 hG h25 lamLow lam hlow hlow1 hlam hlam1 ξ₁ ξ₂ hξ₁ hξ₂ qb₁
    qb₂ qσ₁ qσ₂ qh₁ qh₂ qf₁ qf₂ qg₁ qg₂ hq₁ hq₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hW₁ hW₂ hsize
  obtain ⟨⟨γ₁, hp₁⟩, hXl₁, hYl₁⟩ := hW₁
  obtain ⟨⟨γ₂, hp₂⟩, hXl₂, hYl₂⟩ := hW₂
  -- predictable representatives of the two jump coefficients at the left limits
  obtain ⟨H₁, hH₁p, hH₁eq, -⟩ := exists_markedPredictable_coeffJump_leftLim (P := P) (ν := ν) hB
    hp₁.X_adapted hXl₁ hp₁.Y_adapted hYl₁ hp₁.Z_pred hp₁.U_pred
  obtain ⟨H₂, hH₂p, hH₂eq, -⟩ := exists_markedPredictable_coeffJump_leftLim (P := P) (ν := ν) hB
    hp₂.X_adapted hXl₂ hp₂.Y_adapted hYl₂ hp₂.Z_pred hp₂.U_pred
  have hIoc := ae_markedEnergyMeasure_mem_Ioc (ν := ν) (P := P) (T := T)
  refine ⟨⟨fun i ω s e => lam * (H₁ i ω s e - H₂ i ω s e) + (qh₁ i s ω e - qh₂ i s ω e),
    fun i => ?_, fun i => ?_⟩, fun H hHp hHae => ?_⟩
  · unfold Probability.MarkedPredictable at hH₁p hH₂p ⊢
    have h₁ := (hq₁.qh_pred i)
    have h₂ := (hq₂.qh_pred i)
    unfold Probability.MarkedPredictable at h₁ h₂
    letI : MeasurableSpace (Ω × ℝ × E) :=
      Probability.markedPredictableSigma (enlJoint 𝒢₀ D h𝒢₀) ν
    exact (measurable_const.mul ((hH₁p i).sub (hH₂p i))).add (h₁.sub h₂)
  · filter_upwards [hIoc] with p hp
    rw [hH₁eq i p.1 p.2.1 p.2.2 hp, hH₂eq i p.1 p.2.1 p.2.2 hp]
  -- the fifth integrand
  set ψ : Ω × ℝ × E → ℝ := fun p =>
    (fun i => H i p.1 p.2.1 p.2.2) ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k p.2.1 p.1 p.2.2 - U₂ k p.2.1 p.1 p.2.2)
    with hψdef
  have hcont : Continuous fun x : (Fin n → ℝ) × (Fin m → ℝ) => x.1 ⬝ᵥ (Gᵀ *ᵥ x.2) :=
    continuous_fst.dotProduct (continuous_const.matrix_mulVec continuous_snd)
  have hψp : Measurable[Probability.markedPredictableSigma (enlJoint 𝒢₀ D h𝒢₀) ν] ψ := by
    letI : MeasurableSpace (Ω × ℝ × E) :=
      Probability.markedPredictableSigma (enlJoint 𝒢₀ D h𝒢₀) ν
    have hHv : Measurable fun p : Ω × ℝ × E => (fun i => H i p.1 p.2.1 p.2.2 : Fin n → ℝ) :=
      measurable_pi_lambda _ fun i => hHp i
    have hUv : Measurable fun p : Ω × ℝ × E =>
        (fun k => U₁ k p.2.1 p.1 p.2.2 - U₂ k p.2.1 p.1 p.2.2 : Fin m → ℝ) :=
      measurable_pi_lambda _ fun k => (hp₁.U_pred k).sub (hp₂.U_pred k)
    exact hcont.measurable.comp (hHv.prodMk hUv)
  have hHm : ∀ i, Measurable fun p : Ω × ℝ × E => H i p.1 p.2.1 p.2.2 := fun i =>
    (hHp i).mono (Probability.markedPredictableSigma_le (enlJoint 𝒢₀ D h𝒢₀) ν) le_rfl
  have hUm : ∀ k, Measurable fun p : Ω × ℝ × E => U₁ k p.2.1 p.1 p.2.2 - U₂ k p.2.1 p.1 p.2.2 :=
    fun k =>
      ((hp₁.U_pred k).mono (Probability.markedPredictableSigma_le (enlJoint 𝒢₀ D h𝒢₀) ν) le_rfl).sub
        ((hp₂.U_pred k).mono (Probability.markedPredictableSigma_le (enlJoint 𝒢₀ D h𝒢₀) ν) le_rfl)
  -- the energy of `H`, by comparison with the representative `H₀`
  have hHq : ∀ i, Poisson.Compensated.markedEnergy P ν T (H i) < ⊤ := by
    intro i
    have hae : ∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
        H i p.1 p.2.1 p.2.2 = H₀ i p.1 p.2.1 p.2.2 := by
      filter_upwards [hHae i, hH₀ae i] with p h1 h2
      rw [h1, h2]
    have h0 := markedEnergy_sub_eq_zero_of_ae_eq (P := P) (ν := ν) (T := T) (hHm i) (hH₀m i) hae
    have hle := markedEnergy_add_le (P := P) (ν := ν) (T := T) (hH₀m i)
      (fun ω s e => H i ω s e - H₀ i ω s e)
    have e : (fun ω s e => H₀ i ω s e + (H i ω s e - H₀ i ω s e)) = H i := by
      funext ω s e
      ring
    rw [e, h0, mul_zero, add_zero] at hle
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofNat_lt_top (hH₀q i T hT))
  have hS := hsize
  simp only [supSize, ENNReal.add_lt_top] at hS
  obtain ⟨⟨⟨-, -⟩, -⟩, hSU⟩ := hS
  have hHfin : ∑ i, Poisson.Compensated.markedEnergy P ν T (H i) < ⊤ :=
    ENNReal.sum_lt_top.2 fun i _ => hHq i
  have hCS := lintegral_abs_dotProduct_le (P := P) (ν := ν) G (norm_nonneg _)
    (transpose_mulVec_dotProduct_le G) hHm (U := fun k s ω e => U₁ k s ω e - U₂ k s ω e) hUm T
  have hfinIcc : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, ‖ψ (ω, s, e)‖ₑ ∂ν ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hCS (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hHfin.ne))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hSU.ne)))
    refine lintegral_congr fun ω => lintegral_congr fun s => lintegral_congr fun e => ?_
    exact Real.enorm_eq_ofReal_abs _
  have hfin : ∫⁻ ω, (∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ‖ψ (ω, s, e)‖ₑ ∂ν) ∂P < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono_set Set.Ioc_subset_Icc_self) hfinIcc
  have hψe : Measurable[Probability.markedPredictableSigma (enlJoint 𝒢₀ D h𝒢₀) ν]
      fun x => ‖ψ x‖ₑ := by
    letI : MeasurableSpace (Ω × ℝ × E) :=
      Probability.markedPredictableSigma (enlJoint 𝒢₀ D h𝒢₀) ν
    exact hψp.enorm
  have hcomp := (Dissertation.WellPosedness.BrownianPoisson.aemeasurable_and_lintegral_compensation
    (N := D.N) hℱN T (ψ := fun x => ‖ψ x‖ₑ) hψe).2.2
  refine ⟨hψp, ?_, hfin, Dissertation.WellPosedness.BrownianPoisson.integral_compensated_eq_zero
    (N := D.N) hℱN T hψp hfin⟩
  rw [lt_top_iff_ne_top, ← lt_top_iff_ne_top]
  calc _ = ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ, ‖ψ (ω, p)‖ₑ ∂(D.N.N ω) ∂P := rfl
    _ = _ := hcomp
    _ < ⊤ := hfin

end Dissertation.Acceptance.A
