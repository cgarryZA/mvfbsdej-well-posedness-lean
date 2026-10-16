/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.RateEnergy

/-!
# The supremum upgrade of Lemma 4.3

The closure step of Lemma 4.3 of the well-posedness paper bounds the time-integrated size
`N' = 𝔼|δX_T|² + 𝔼|δY_0|² + 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²)` of the difference of two
solutions; the conclusion (4.14) is about the size with running suprema,

`N = 𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²_{L²(ν)})`.

Each coordinate of `δX` solves the linear backward equation from `δX_T` with drift
`−(λ δb + q^b)`, and each coordinate of `δY` the one with drift `λ δf + q^f`, so the `S²` bound of
Lemma 4.1 applies coordinatewise:

`𝔼 sup_{t ≤ T} |δX_t|² ≤ 3 𝔼|δξ₀|² + 3T 𝔼 ∫_0^T |λ δb + q^b|²
  + 12 𝔼 ∫_0^T (|λ δσ + q^σ|²_F + ‖λ δh + q^h‖²)`,

`𝔼 sup_{t ≤ T} |δY_t|² ≤ 3 𝔼|δY_0|² + 3T 𝔼 ∫_0^T |λ δf + q^f|² + 12 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)`.

For `λ ∈ [0, 1]` the integrands split as `|λ x + q|² ≤ 2 |x|² + 2 |q|²`, and the expected Lipschitz
bound (3.2) bounds the coefficient differences by `K N'`. Hence `N ≤ c_S (N' + P)` with `P` the
data size and `c_S = 6 (T + 4) (K + 1)`.

## Main definitions

* `supSize` — the size `N` of a difference, the left-hand side of (4.14).
* `supConst` — the constant `c_S = 6 (T + 4) (K + 1)`.

## Main statements

* `lintegral_biSup_esq_le` — the running supremum of a sum of squares is at most the sum of the
  running suprema.
* `PairDiff.lintegral_biSup_fwd_le`, `PairDiff.lintegral_biSup_bwd_le` — the `S²` bounds of `δX`
  and of `δY`.
* `PairDiff.supSize_le` — `N ≤ c_S (N' + P)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc Dissertation.WellPosedness.BrownianPoisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {d n m : ℕ}

/-- The size `N = 𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F +
‖δU‖²_{L²(ν)})` of a difference, the left-hand side of (4.14). -/
noncomputable def supSize (P : Measure Ω) (ν : Measure E) (T : ℝ) (X : Fin n → ℝ → Ω → ℝ)
    (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P
    + ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y k t ω)) ∂P
    + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
    + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)

/-- The constant `c_S = 6 (T + 4) (K + 1)` of the supremum upgrade. -/
noncomputable def supConst (T K : ℝ) : ℝ := 6 * (T + 4) * (K + 1)

/-- The constant of the supremum upgrade is nonnegative for `T, K ≥ 0`. -/
theorem supConst_nonneg {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K) : 0 ≤ supConst T K := by
  unfold supConst
  positivity

/-- The running supremum over `[0, T]` of a finite sum of squares of right-continuous processes
is, in expectation, at most the sum of the running suprema of the squares. -/
theorem lintegral_biSup_esq_le {ι : Type*} [Fintype ι] {x : ι → ℝ → Ω → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hm : ∀ i t, Measurable (x i t))
    (hrc : ∀ i ω t, Tendsto (fun s => x i s ω) (𝓝[>] t) (𝓝 (x i t ω))) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂P
      ≤ ∑ i, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖x i t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
  rw [← lintegral_finsetSum _ fun i _ =>
    measurable_biSup_sq_of_rightContinuous hT (hm i) (hrc i)]
  refine lintegral_mono fun ω => iSup₂_le fun t ht => Finset.sum_le_sum fun i _ => ?_
  exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => (‖x i t ω‖₊ : ℝ≥0∞) ^ 2) t ht

/-- **The algebra of the supremum upgrade.** With `S_X ≤ 3 ξ + 3T R_b + 12 (R_σ + R_h)`,
`S_Y ≤ 3 Y₀ + 3T R_f + 12 (J_Z + J_U)` and
`R_b + R_σ + R_h + R_f ≤ 2K (I_X + I_Y + J_Z + J_U) + 2 (Q_b + Q_σ + Q_h + Q_f)`,

`S_X + S_Y + J_Z + J_U ≤ c_S ((A + Y₀ + I_X + I_Y + J_Z + J_U)
  + (ξ + q + Q_b + Q_σ + Q_h + Q_f))`. -/
theorem le_supConst_mul {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    {SX SY ξ Y0 A IX IY JZ JU qg Qb Qσ Qh Qf Rb Rσ Rh Rf : ℝ≥0∞}
    (hSX : SX ≤ 3 * ξ + 3 * (ENNReal.ofReal T * Rb) + 12 * (Rσ + Rh))
    (hSY : SY ≤ 3 * Y0 + 3 * (ENNReal.ofReal T * Rf) + 12 * (JZ + JU))
    (hR : Rb + Rσ + Rh + Rf
      ≤ 2 * ENNReal.ofReal K * (IX + (IY + JZ + JU)) + 2 * (Qb + Qσ + Qh + Qf)) :
    SX + SY + JZ + JU ≤ ENNReal.ofReal (supConst T K)
      * ((A + Y0 + IX + IY + JZ + JU) + (ξ + qg + Qb + Qσ + Qh + Qf)) := by
  set c := ENNReal.ofReal (3 * T + 12) with hc
  set C := ENNReal.ofReal (supConst T K) with hC
  have hS : 6 * (T + 4) ≤ supConst T K := by
    unfold supConst
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 6 * (T + 4)) hK]
  have c1 : 3 * ENNReal.ofReal T ≤ c := by
    rw [hc, ← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have c2 : (12 : ℝ≥0∞) ≤ c := by
    rw [hc, ← ENNReal.ofReal_ofNat 12]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have c3 : (3 : ℝ≥0∞) ≤ C := by
    rw [hC, ← ENNReal.ofReal_ofNat 3]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have c4 : 13 + c * (2 * ENNReal.ofReal K) ≤ C := by
    rw [hc, hC, ← ENNReal.ofReal_ofNat 13, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by norm_num) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold supConst
    nlinarith
  have c5 : c * 2 ≤ C := by
    rw [hc, hC, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  clear_value c C
  set J := IY + JZ + JU with hJ
  set Q := Qb + Qσ + Qh + Qf with hQ
  calc SX + SY + JZ + JU
      ≤ (3 * ξ + 3 * (ENNReal.ofReal T * Rb) + 12 * (Rσ + Rh))
        + (3 * Y0 + 3 * (ENNReal.ofReal T * Rf) + 12 * (JZ + JU)) + JZ + JU := by gcongr
    _ = 3 * ξ + 3 * Y0 + 13 * (JZ + JU)
        + (3 * ENNReal.ofReal T * (Rb + Rf) + 12 * (Rσ + Rh)) := by ring
    _ ≤ 3 * ξ + 3 * Y0 + 13 * (IX + J) + (c * (Rb + Rf) + c * (Rσ + Rh)) := by
        refine add_le_add (add_le_add le_rfl (mul_le_mul_right ?_ 13))
          (add_le_add (mul_le_mul_left c1 _) (mul_le_mul_left c2 _))
        calc JZ + JU ≤ IY + JZ + JU := by rw [add_assoc]; exact le_add_self
          _ ≤ IX + J := le_add_self
    _ = 3 * ξ + 3 * Y0 + 13 * (IX + J) + c * (Rb + Rσ + Rh + Rf) := by ring
    _ ≤ 3 * ξ + 3 * Y0 + 13 * (IX + J) + c * (2 * ENNReal.ofReal K * (IX + J) + 2 * Q) := by
        gcongr
    _ = 3 * ξ + 3 * Y0 + (13 + c * (2 * ENNReal.ofReal K)) * (IX + J) + c * 2 * Q := by ring
    _ ≤ C * ξ + C * Y0 + C * (IX + J) + C * Q := by
        gcongr
    _ = C * (ξ + Y0 + (IX + J) + Q) := by ring
    _ ≤ C * ((A + Y0 + IX + IY + JZ + JU) + (ξ + qg + Qb + Qσ + Qh + Qf)) := by
        refine mul_le_mul_right ?_ C
        calc ξ + Y0 + (IX + J) + Q ≤ ξ + Y0 + (IX + J) + Q + (A + qg) := le_self_add
          _ = _ := by rw [hJ, hQ]; ring

namespace PairDiff

variable [IsProbabilityMeasure P] [SigmaFinite ν]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam K KT α β₁ β₂ : ℝ}
  {G : Matrix (Fin m) (Fin n) ℝ} {ξ₀ : Fin n → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
  {b : Fin n → Ω → ℝ → ℝ} {σ : Fin n → ℝ → Ω → Fin d → ℝ} {h : Fin n → ℝ → Ω → E → ℝ}
  {f : Fin m → Ω → ℝ → ℝ} {g : Fin m → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}

/-- **The `S²` bound of the forward difference.** Over a filtration whose null sets lie in its
time-`0` field, whose right-continuation is constant before `0`, and which admits a cross
witness,

`𝔼 sup_{t ≤ T} |δX_t|² ≤ 3 𝔼|δξ₀|² + 3T 𝔼 ∫_0^T |λ δb + q^b|²
  + 12 𝔼 ∫_0^T (|λ δσ + q^σ|²_F + ‖λ δh + q^h‖²)`. -/
theorem lintegral_biSup_fwd_le
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P
      ≤ 3 * ∫⁻ ω, esq (fun i => ξ₀ i ω) ∂P
        + 3 * (ENNReal.ofReal T
          * ∑ i, Brownian.Ito.energy P T (fun ω s => lam * b i ω s + qb i ω s))
        + 12 * (∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => lam * σ i s ω j + qσ i s ω j)
          + ∑ i, Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => lam * h i s ω e + qh i s ω e)) := by
  have hesq : ∫⁻ ω, esq (fun i => ξ₀ i ω) ∂P = ∑ i, ∫⁻ ω, (‖ξ₀ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    unfold esq
    exact lintegral_finsetSum' _ fun i _ =>
      ((hD.fwd i).ξ₀_sq.aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  have h0 : ∀ i, ∫⁻ ω, (‖X i 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ∫⁻ ω, (‖ξ₀ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    fun i => lintegral_congr_ae ((hD.init hT.le i).mono fun ω hω => by simp only [hω])
  have hneg : ∀ i, Brownian.Ito.energy P T (fun ω s => -(lam * b i ω s + qb i ω s))
      = Brownian.Ito.energy P T (fun ω s => lam * b i ω s + qb i ω s) := fun i => by
    simp only [Brownian.Ito.energy, nnnorm_neg]
  calc _ ≤ ∑ i, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖X i t ω‖₊ : ℝ≥0∞) ^ 2) ∂P :=
        lintegral_biSup_esq_le hT.le (fun i t => ((hD.fwd i).X_adapted t).mono (ℱ.le t) le_rfl)
          fun i => (hD.fwd i).X_rightCont
    _ ≤ ∑ i, (3 * ∫⁻ ω, (‖X i 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P
          + 3 * (ENNReal.ofReal T
            * Brownian.Ito.energy P T (fun ω s => -(lam * b i ω s + qb i ω s)))
          + 12 * ((∑ j, Brownian.Ito.energy P T (fun ω s => lam * σ i s ω j + qσ i s ω j))
            + Poisson.Compensated.markedEnergy P ν T
              (fun ω s e => lam * h i s ω e + qh i s ω e))) :=
        Finset.sum_le_sum fun i _ =>
          ((hD.fwd i).linearBSDEJ hT.le).lintegral_biSup_sq_le 𝒲 hℱ0 hnull hT
    _ = _ := by
        simp only [h0, hneg, Finset.sum_add_distrib, ← Finset.mul_sum, hesq]

/-- **The `S²` bound of the backward difference.** Over a filtration whose null sets lie in its
time-`0` field, whose right-continuation is constant before `0`, and which admits a cross
witness,

`𝔼 sup_{t ≤ T} |δY_t|² ≤ 3 𝔼|δY_0|² + 3T 𝔼 ∫_0^T |λ δf + q^f|²
  + 12 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)`. -/
theorem lintegral_biSup_bwd_le
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y k t ω)) ∂P
      ≤ 3 * ∫⁻ ω, esq (fun k => Y k 0 ω) ∂P
        + 3 * (ENNReal.ofReal T
          * ∑ k, Brownian.Ito.energy P T (fun ω s => lam * f k ω s + qf k ω s))
        + 12 * (∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)) := by
  have hYm : ∀ k t, Measurable (Y k t) := fun k t => ((hD.bwd k).Y_adapted t).mono (ℱ.le t) le_rfl
  have hesq : ∫⁻ ω, esq (fun k => Y k 0 ω) ∂P = ∑ k, ∫⁻ ω, (‖Y k 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    unfold esq
    exact lintegral_finsetSum' _ fun k _ =>
      ((hYm k 0).nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable
  calc _ ≤ ∑ k, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y k t ω‖₊ : ℝ≥0∞) ^ 2) ∂P :=
        lintegral_biSup_esq_le hT.le hYm fun k => (hD.bwd k).Y_rightCont
    _ ≤ ∑ k, (3 * ∫⁻ ω, (‖Y k 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P
          + 3 * (ENNReal.ofReal T * Brownian.Ito.energy P T (fun ω s => lam * f k ω s + qf k ω s))
          + 12 * ((∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j))
            + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e))) :=
        Finset.sum_le_sum fun k _ => (hD.bwd k).lintegral_biSup_sq_le 𝒲 hℱ0 hnull hT
    _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hesq]

/-- **The supremum upgrade of Lemma 4.3.** For the difference system at `λ ∈ [0, 1]` with
Lipschitz constant `K ≥ 0`, over a filtration whose null sets lie in its time-`0` field, whose
right-continuation is constant before `0`, and which admits a cross witness,

`N ≤ c_S (N' + P)`,   `c_S = 6 (T + 4) (K + 1)`,

with `N` the size of (4.14), `N'` the time-integrated size and `P` the data size. -/
theorem supSize_le
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hK : 0 ≤ K) :
    supSize P ν T X Y Z U ≤ ENNReal.ofReal (supConst T K)
      * (diffSize P ν T X Y Z U + dataSize P ν T ξ₀ qb qσ qh qf qg) := by
  have hSX := hD.lintegral_biSup_fwd_le 𝒲 hℱ0 hnull hT
  have hSY := hD.lintegral_biSup_bwd_le 𝒲 hℱ0 hnull hT
  have hR := hD.rateEnergy_le hT.le hlam0 hlam1
  unfold supSize diffSize dataSize
  exact le_supConst_mul hT.le hK hSX hSY (by simpa only [add_assoc] using hR)

end PairDiff

end Dissertation.WellPosedness.Stability
