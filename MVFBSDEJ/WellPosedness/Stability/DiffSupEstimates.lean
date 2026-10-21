/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.SupUpgrade
import MVFBSDEJ.WellPosedness.Stability.ForwardEstimate
import MVFBSDEJ.WellPosedness.Stability.BackwardEstimate

/-!
# The supremum bounds of Steps 3 and 4 of the proof of Lemma 4.3

For the difference system of Lemma 4.3 of the well-posedness paper at `λ ∈ [0, 1]` with Lipschitz
constants `K, K_T ≥ 0` and finite data size `P`, the `S²` bounds of `δX` and `δY` (Lemma 4.1,
coordinatewise), the rate bound (3.2) and the forward and backward estimates of the closure step
give

`𝔼 sup_{t ≤ T} |δX_t|² ≤ c_X (𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²) + P)`,

`𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²) ≤ c_Y (𝔼|δX_T|² + 𝔼 ∫_0^T |δX|² + P)`,

with `c_X = 3 + 2c + 2cK (k_F + 1)` and `c_Y = 16 k_B + 2c (K (k_B + 1) + 1)`, where `c = 3T + 12`
and `k_F`, `k_B` are the constants of the forward and backward estimates.

## Main definitions

* `fwdSupConst` — the constant `c_X`.
* `bwdSupConst` — the constant `c_Y`.

## Main statements

* `le_fwdSupConst_mul`, `le_bwdSupConst_mul` — the algebra of the two bounds.
* `PairDiff.lintegral_biSup_fwd_le_energy` — the bound on `𝔼 sup_{t ≤ T} |δX_t|²`.
* `PairDiff.lintegral_biSup_bwd_add_le` — the bound on
  `𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson

universe u v w

/-- The constant `c_X = 3 + 2c + 2cK (k_F + 1)`, `c = 3T + 12`, of the bound on
`𝔼 sup_{t ≤ T} |δX_t|²`. -/
noncomputable def fwdSupConst (T K : ℝ) : ℝ :=
  3 + 2 * (3 * T + 12) + 2 * (3 * T + 12) * K * (forwardConst T K + 1)

/-- The constant `c_Y = 16 k_B + 2c (K (k_B + 1) + 1)`, `c = 3T + 12`, of the bound on
`𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)`. -/
noncomputable def bwdSupConst (T K KT : ℝ) : ℝ :=
  16 * backwardConst T K KT + 2 * (3 * T + 12) * (K * (backwardConst T K KT + 1) + 1)

/-- **The algebra of the bound on `𝔼 sup_{t ≤ T} |δX_t|²`.** With
`S_X ≤ 3 ξ + 3T R_b + 12 (R_σ + R_h)`, `R_b + R_σ + R_h + R_f ≤ 2K (I_X + J) + 2Q`,
`I_X ≤ k_F (J + P)`, `ξ ≤ P` and `Q ≤ P`, `S_X ≤ c_X (J + P)`. -/
theorem le_fwdSupConst_mul {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    {SX ξ Rb Rσ Rh Rf IX J Q P' : ℝ≥0∞}
    (hSX : SX ≤ 3 * ξ + 3 * (ENNReal.ofReal T * Rb) + 12 * (Rσ + Rh))
    (hR : Rb + Rσ + Rh + Rf ≤ 2 * ENNReal.ofReal K * (IX + J) + 2 * Q)
    (hI : IX ≤ ENNReal.ofReal (forwardConst T K) * (J + P')) (hξ : ξ ≤ P') (hQ : Q ≤ P') :
    SX ≤ ENNReal.ofReal (fwdSupConst T K) * (J + P') := by
  set c := ENNReal.ofReal (3 * T + 12) with hc
  set k := ENNReal.ofReal K with hk
  set f := ENNReal.ofReal (forwardConst T K) with hf
  have c1 : 3 * ENNReal.ofReal T ≤ c := by
    rw [hc, ← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have c2 : (12 : ℝ≥0∞) ≤ c := by
    rw [hc, ← ENNReal.ofReal_ofNat 12]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hC : ENNReal.ofReal (fwdSupConst T K) = 3 + 2 * c + 2 * c * k * (f + 1) := by
    have h0 : 0 ≤ 3 * T + 12 := by linarith
    have hF := forwardConst_nonneg hK T
    rw [hc, hk, hf, fwdSupConst, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add hF zero_le_one, ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  clear_value c k f
  calc SX ≤ 3 * ξ + c * (Rb + Rσ + Rh + Rf) := by
        refine hSX.trans ?_
        rw [add_assoc]
        gcongr 3 * ξ + ?_
        calc 3 * (ENNReal.ofReal T * Rb) + 12 * (Rσ + Rh)
            = 3 * ENNReal.ofReal T * Rb + 12 * (Rσ + Rh) := by ring
          _ ≤ c * Rb + c * (Rσ + Rh) := by gcongr
          _ = c * (Rb + Rσ + Rh) := by ring
          _ ≤ c * (Rb + Rσ + Rh + Rf) := by gcongr c * ?_; exact le_self_add
    _ ≤ 3 * P' + c * (2 * k * (f * (J + P') + J) + 2 * P') := by
        gcongr 3 * ?_ + c * ?_
        refine hR.trans ?_
        gcongr 2 * k * (?_ + J) + 2 * ?_
    _ = (3 + 2 * c) * P' + 2 * c * k * f * (J + P') + 2 * c * k * J := by ring
    _ ≤ (3 + 2 * c) * (J + P') + 2 * c * k * f * (J + P') + 2 * c * k * (J + P') := by
        gcongr
        · exact le_add_self
        · exact le_self_add
    _ = ENNReal.ofReal (fwdSupConst T K) * (J + P') := by rw [hC]; ring

/-- **The algebra of the bound on `𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)`.** With
`S_Y ≤ 3 Y₀ + 3T R_f + 12 J_{ZU}`, `R_b + R_σ + R_h + R_f ≤ 2K (I_X + J) + 2Q`,
`Y₀, J ≤ k_B (A + I_X + P)`, `J_{ZU} ≤ J` and `Q ≤ P`, `S_Y + J_{ZU} ≤ c_Y (A + I_X + P)`. -/
theorem le_bwdSupConst_mul {T K KT : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K) (hKT : 0 ≤ KT)
    {SY Y0 Rb Rσ Rh Rf IX J JZU Q A P' : ℝ≥0∞}
    (hSY : SY ≤ 3 * Y0 + 3 * (ENNReal.ofReal T * Rf) + 12 * JZU)
    (hR : Rb + Rσ + Rh + Rf ≤ 2 * ENNReal.ofReal K * (IX + J) + 2 * Q)
    (hY0 : Y0 ≤ ENNReal.ofReal (backwardConst T K KT) * (A + IX + P'))
    (hJ : J ≤ ENNReal.ofReal (backwardConst T K KT) * (A + IX + P')) (hJZU : JZU ≤ J)
    (hQ : Q ≤ P') :
    SY + JZU ≤ ENNReal.ofReal (bwdSupConst T K KT) * (A + IX + P') := by
  set c := ENNReal.ofReal (3 * T + 12) with hc
  set k := ENNReal.ofReal K with hk
  set b := ENNReal.ofReal (backwardConst T K KT) with hb
  set W := A + IX + P' with hW
  have c1 : 3 * ENNReal.ofReal T ≤ c := by
    rw [hc, ← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hC : ENNReal.ofReal (bwdSupConst T K KT) = 16 * b + 2 * c * (k * (b + 1) + 1) := by
    have h0 : 0 ≤ 3 * T + 12 := by linarith
    have hB := backwardConst_nonneg hK hKT T
    rw [hc, hk, hb, bwdSupConst, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) zero_le_one,
      ENNReal.ofReal_mul hK, ENNReal.ofReal_add hB zero_le_one, ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  have hIX : IX ≤ W := by rw [hW]; exact (le_add_self (a := IX) (b := A)).trans le_self_add
  have hPW : P' ≤ W := by rw [hW]; exact le_add_self
  clear_value c k b W
  calc SY + JZU ≤ 3 * Y0 + 3 * (ENNReal.ofReal T * Rf) + 12 * JZU + JZU := by gcongr
    _ = 3 * Y0 + 3 * ENNReal.ofReal T * Rf + 13 * JZU := by ring
    _ ≤ 3 * Y0 + c * (Rb + Rσ + Rh + Rf) + 13 * J := by
        gcongr 3 * Y0 + ?_ + 13 * ?_
        exact mul_le_mul' c1 le_add_self
    _ ≤ 3 * (b * W) + c * (2 * k * (W + b * W) + 2 * W) + 13 * (b * W) := by
        gcongr 3 * ?_ + c * ?_ + 13 * ?_
        refine hR.trans ?_
        gcongr 2 * k * (?_ + ?_) + 2 * ?_
        exact hQ.trans hPW
    _ = (16 * b + 2 * c * (k * (b + 1) + 1)) * W := by ring
    _ = ENNReal.ofReal (bwdSupConst T K KT) * W := by rw [hC]

namespace PairDiff

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d n m : ℕ}
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

/-- The data size splits as `(𝔼|δξ₀|² + 𝔼|q^g|²) + Q`, with
`Q = 𝔼 ∫_0^T (|q^b|² + |q^σ|²_F + ‖q^h‖² + |q^f|²)`. -/
theorem dataSize_eq_add (P : Measure Ω) (ν : Measure E) (T : ℝ) (ξ₀ : Fin n → Ω → ℝ)
    (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
    (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ) :
    dataSize P ν T ξ₀ qb qσ qh qf qg
      = (∫⁻ ω, esq (fun i => ξ₀ i ω) ∂P + ∫⁻ ω, esq (fun k => qg k ω) ∂P)
        + (∑ i, Brownian.Ito.energy P T (qb i)
          + ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j)
          + ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e)
          + ∑ k, Brownian.Ito.energy P T (qf k)) := by
  unfold dataSize
  ring

/-- `J = 𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²)` is finite for the difference system. -/
theorem backEnergy_ne_top
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) :
    ∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
      + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
      + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) ≠ ⊤ :=
  ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.sum_ne_top.mpr fun k _ => ((hD.bwd k).energy_lt_top 𝒲 hT).ne,
      ENNReal.sum_ne_top.mpr fun k _ => ENNReal.sum_ne_top.mpr fun j _ => (hD.bwd k).Z_sq j⟩,
    ENNReal.sum_ne_top.mpr fun k _ => (hD.bwd k).U_sq⟩

/-- **The bound on `𝔼 sup_{t ≤ T} |δX_t|²`** (4.23). For the difference system at `λ ∈ [0, 1]`
with Lipschitz constant `K ≥ 0` and finite data size, over a filtration whose null sets lie in
its time-`0` field, whose right-continuation is constant before `0`, and which admits a cross
witness,
`𝔼 sup_{t ≤ T} |δX_t|² ≤ c_X (𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²) + P)`. -/
theorem lintegral_biSup_fwd_le_energy
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hK : 0 ≤ K)
    (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P
      ≤ ENNReal.ofReal (fwdSupConst T K)
        * (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
          + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)
          + dataSize P ν T ξ₀ qb qσ qh qf qg) := by
  have hSX := hD.lintegral_biSup_fwd_le 𝒲 hℱ0 hnull hT
  have hR := hD.rateEnergy_le hT.le hlam0 hlam1
  have hF := hD.forward_le 𝒲 hT hlam0 hlam1 hK hP
  have hJf := hD.backEnergy_ne_top 𝒲 hT
  have hIf : ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => ((hD.fwd i).energy_lt_top 𝒲 hT).ne
  have hI : ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
      ≤ ENNReal.ofReal (forwardConst T K)
        * (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
          + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)
          + dataSize P ν T ξ₀ qb qσ qh qf qg) := by
    rw [← ENNReal.toReal_le_toReal hIf
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨hJf, hP⟩)),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (forwardConst_nonneg hK T),
      ENNReal.toReal_add hJf hP]
    linarith [ENNReal.toReal_nonneg (a := ∫⁻ ω, esq (fun i => X i T ω) ∂P)]
  have hsplit := dataSize_eq_add P ν T ξ₀ qb qσ qh qf qg
  refine le_fwdSupConst_mul hT.le hK hSX hR hI ?_ ?_
  · rw [hsplit]
    exact le_self_add.trans le_self_add
  · rw [hsplit]
    exact le_add_self

/-- **The bound on `𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)`** (4.27). For the
difference system at `λ ∈ [0, 1]` with Lipschitz constants `K, K_T ≥ 0` and finite data size,
over a filtration whose null sets lie in its time-`0` field, whose right-continuation is constant
before `0`, and which admits a cross witness,
`𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²) ≤ c_Y (𝔼|δX_T|² + 𝔼 ∫_0^T |δX|² + P)`. -/
theorem lintegral_biSup_bwd_add_le
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hK : 0 ≤ K) (hKT : 0 ≤ KT)
    (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y k t ω)) ∂P
        + (∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e))
      ≤ ENNReal.ofReal (bwdSupConst T K KT)
        * (∫⁻ ω, esq (fun i => X i T ω) ∂P + ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
          + dataSize P ν T ξ₀ qb qσ qh qf qg) := by
  have hSY := hD.lintegral_biSup_bwd_le 𝒲 hℱ0 hnull hT
  have hR := hD.rateEnergy_le hT.le hlam0 hlam1
  have hB := hD.backward_le 𝒲 hT hlam0 hlam1 hK hKT hP
  have hJf := hD.backEnergy_ne_top 𝒲 hT
  have hIf : ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => ((hD.fwd i).energy_lt_top 𝒲 hT).ne
  have hAf : ∫⁻ ω, esq (fun i => X i T ω) ∂P ≠ ⊤ :=
    (lintegral_esq_lt_top fun i => (hD.fwd i).memLp_terminal hT.le).ne
  have hY0f : ∫⁻ ω, esq (fun k => Y k 0 ω) ∂P ≠ ⊤ :=
    (lintegral_esq_lt_top fun k => (hD.bwd k).memLp_initial hT.le).ne
  have hWf : ∫⁻ ω, esq (fun i => X i T ω) ∂P + ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
      + dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hAf, hIf⟩, hP⟩
  have hRf := ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := backwardConst T K KT)) hWf
  have hRr : (ENNReal.ofReal (backwardConst T K KT)
      * (∫⁻ ω, esq (fun i => X i T ω) ∂P + ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
        + dataSize P ν T ξ₀ qb qσ qh qf qg)).toReal
      = backwardConst T K KT * ((∫⁻ ω, esq (fun i => X i T ω) ∂P).toReal
        + (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)).toReal
        + (dataSize P ν T ξ₀ qb qσ qh qf qg).toReal) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (backwardConst_nonneg hK hKT T),
      ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hAf, hIf⟩) hP, ENNReal.toReal_add hAf hIf]
  have hY0 : ∫⁻ ω, esq (fun k => Y k 0 ω) ∂P ≤ ENNReal.ofReal (backwardConst T K KT)
      * (∫⁻ ω, esq (fun i => X i T ω) ∂P + ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
        + dataSize P ν T ξ₀ qb qσ qh qf qg) := by
    rw [← ENNReal.toReal_le_toReal hY0f hRf, hRr]
    linarith [ENNReal.toReal_nonneg (a := ∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
      + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
      + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e))]
  have hJ : ∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
      + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
      + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)
      ≤ ENNReal.ofReal (backwardConst T K KT)
        * (∫⁻ ω, esq (fun i => X i T ω) ∂P + ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
          + dataSize P ν T ξ₀ qb qσ qh qf qg) := by
    rw [← ENNReal.toReal_le_toReal hJf hRf, hRr]
    linarith [ENNReal.toReal_nonneg (a := ∫⁻ ω, esq (fun k => Y k 0 ω) ∂P)]
  refine le_bwdSupConst_mul hT.le hK hKT hSY hR hY0 hJ ?_ ?_
  · rw [add_assoc]
    exact le_add_self
  · rw [dataSize_eq_add P ν T ξ₀ qb qσ qh qf qg]
    exact le_add_self

end PairDiff

end MVFBSDEJ.WellPosedness.Stability
