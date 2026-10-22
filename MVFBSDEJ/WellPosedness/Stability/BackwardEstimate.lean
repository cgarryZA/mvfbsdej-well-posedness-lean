/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.BackwardEnergy
import MVFBSDEJ.WellPosedness.Stability.LipschitzRate

/-!
# The backward estimate of Lemma 4.3

Step 4 of the proof of Lemma 4.3 of the well-posedness paper bounds the backward difference
`(δY, δZ, δU)` through `δX` and the data. For the difference system,
`(λ δf + q^f)² ≤ 2 δf² + 2 (q^f)²` for `λ ∈ [0, 1]` and the expected Lipschitz bound (3.2) give
the rate bound of the weighted backward bound with `c = 2K` and `G = 2K 𝔼|δX|² + 2 𝔼|q^f|²`, and
the terminal bound (2.6) with (2.9) gives `𝔼|λ δg + q^g|² ≤ 2 K_T 𝔼|δX_T|² + 2 𝔼|q^g|²`. This is
the backward estimate `Y₀ + J ≤ k_B (A + I_X + P)` of the closure step, where `Y₀ = 𝔼|δY_0|²`,
`J = 𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²)`, `A = 𝔼|δX_T|²`, `I_X = 𝔼 ∫_0^T |δX|²` and `P` is the
data size, with `k_B = 4 (K + K_T + 1) e^{(4K + 2) T}`.

## Main definitions

* `backwardConst` — the constant `k_B = 4 (K + K_T + 1) e^{(4K + 2) T}`.

## Main statements

* `esq_mul_add_le` — `|λ x + q|² ≤ 2 |x|² + 2 |q|²` for `λ² ≤ 1`.
* `PairDiff.backward_le` — the backward estimate of Lemma 4.3.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d n m : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

/-- The constant `k_B = 4 (K + K_T + 1) e^{(4K + 2) T}` of the backward estimate. -/
noncomputable def backwardConst (T K KT : ℝ) : ℝ :=
  4 * (K + KT + 1) * Real.exp ((4 * K + 2) * T)

/-- The constant of the backward estimate is nonnegative for `K, K_T ≥ 0`. -/
theorem backwardConst_nonneg {K KT : ℝ} (hK : 0 ≤ K) (hKT : 0 ≤ KT) (T : ℝ) :
    0 ≤ backwardConst T K KT := by
  unfold backwardConst
  positivity

/-- For `λ² ≤ 1`, `|λ x + q|² ≤ 2 |x|² + 2 |q|²` for coordinate vectors, in `ℝ≥0∞`. -/
theorem esq_mul_add_le {ι : Type*} [Fintype ι] {l : ℝ} (hl : l ^ 2 ≤ 1) (x q : ι → ℝ) :
    esq (fun i => l * x i + q i) ≤ 2 * esq x + 2 * esq q := by
  unfold esq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => sq_nnnorm_mul_add_le hl _ _

namespace PairDiff

variable {lam K KT α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {ξ₀ : Fin n → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
  {b : Fin n → Ω → ℝ → ℝ} {σ : Fin n → ℝ → Ω → Fin d → ℝ} {h : Fin n → ℝ → Ω → E → ℝ}
  {f : Fin m → Ω → ℝ → ℝ} {g : Fin m → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}

/-- **The backward estimate of Lemma 4.3.** For the difference system at `λ ∈ [0, 1]` with
Lipschitz constants `K, K_T ≥ 0` and finite data size `P`, over a filtration with a cross
witness,

`𝔼|δY_0|² + 𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²) ≤ k_B (𝔼|δX_T|² + 𝔼 ∫_0^T |δX|² + P)`,

`k_B = 4 (K + K_T + 1) e^{(4K + 2) T}`: the inequality `Y₀ + J ≤ k_B (A + I_X + P)` of the
closure step. -/
theorem backward_le
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hK : 0 ≤ K)
    (hKT : 0 ≤ KT) (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) :
    (∫⁻ ω, esq (fun k => Y k 0 ω) ∂P).toReal
        + (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
          + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)).toReal
      ≤ backwardConst T K KT * ((∫⁻ ω, esq (fun i => X i T ω) ∂P).toReal
        + (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)).toReal
        + (dataSize P ν T ξ₀ qb qσ qh qf qg).toReal) := by
  obtain ⟨-, hqg, -, -, -, hqf⟩ := lt_top_of_dataSize_ne_top hP
  have hl : lam ^ 2 ≤ 1 := by nlinarith
  have hXm : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω) := fun i =>
    ((hD.fwd i).linearBSDEJ hT.le).measurable_uncurry.comp measurable_swap
  set FX : ℝ → ℝ≥0∞ := sampleEnergy P (fun i ω s => X i s ω) with hFX
  have hFXm : Measurable FX := measurable_sampleEnergy hXm
  have hFXw : ∫⁻ s in Set.Icc (0 : ℝ) T, FX s
      = ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω) := lintegral_sampleEnergy hXm T
  have hIXf : ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => ((hD.fwd i).energy_lt_top 𝒲 hT).ne
  have hQf : ∑ k, Brownian.Ito.energy P T (qf k) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun k _ => (hqf k).ne
  -- the rate bound with `c = 2K` and `G = 2K F_X + 2 F_{q^f}`
  set Gr : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (2 * K) * FX s + 2 * sampleEnergy P qf s
    with hGr
  have hGm : Measurable Gr :=
    (hFXm.const_mul _).add ((measurable_sampleEnergy hD.qf_meas).const_mul _)
  have hGw : ∫⁻ s in Set.Icc (0 : ℝ) T, Gr s
      = ENNReal.ofReal (2 * K) * ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
        + 2 * ∑ k, Brownian.Ito.energy P T (qf k) := by
    rw [lintegral_add_left (hFXm.const_mul _), lintegral_const_mul _ hFXm,
      lintegral_const_mul _ (measurable_sampleEnergy hD.qf_meas), hFXw,
      lintegral_sampleEnergy hD.qf_meas]
  have hGf : ∫⁻ s in Set.Icc (0 : ℝ) T, Gr s ≠ ⊤ := by
    rw [hGw]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIXf,
      ENNReal.mul_ne_top (by norm_num) hQf⟩
  have hrate : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      sampleEnergy P (fun k ω s => lam * f k ω s + qf k ω s) s
        ≤ ENNReal.ofReal (2 * K) * (sampleEnergy P (fun k ω s => Y k s ω) s
          + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
          + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s) + Gr s := by
    filter_upwards [hD.ae_lip] with s hs
    refine (sampleEnergy_mul_add_le (P := P) hl f qf s fun k =>
      ((hD.qf_meas k).comp (measurable_id.prodMk measurable_const)).aemeasurable).trans ?_
    calc 2 * sampleEnergy P f s + 2 * sampleEnergy P qf s
        ≤ 2 * (ENNReal.ofReal K * (FX s + (sampleEnergy P (fun k ω s => Y k s ω) s
          + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
          + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s))) + 2 * sampleEnergy P qf s := by
          gcongr
          exact le_add_self.trans hs
      _ = _ := by
        rw [hGr, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        ring
  have key := backward_energy_le (φ := fun k ω s => lam * f k ω s + qf k ω s) hD.bwd 𝒲 hT
    (by positivity : (0 : ℝ) ≤ 2 * K) hGm hGf hrate
  rw [hGw, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIXf)
      (ENNReal.mul_ne_top (by norm_num) hQf), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofNat,
    show 2 * (2 * K) + 2 = 4 * K + 2 by ring] at key
  -- the terminal bound (2.6) with (2.9)
  have hXT : ∫⁻ ω, esq (fun i => X i T ω) ∂P < ⊤ :=
    lintegral_esq_lt_top fun i => (hD.fwd i).memLp_terminal hT.le
  have hqgm : AEMeasurable (fun ω => esq (fun k => qg k ω)) P := by
    simp only [esq]
    exact Finset.aemeasurable_fun_sum _ fun k _ =>
      ((hD.qg_meas k).aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hterm : ∫⁻ ω, esq (fun k => lam * g k ω + qg k ω) ∂P
      ≤ 2 * ENNReal.ofReal KT * ∫⁻ ω, esq (fun i => X i T ω) ∂P
        + 2 * ∫⁻ ω, esq (fun k => qg k ω) ∂P := by
    calc ∫⁻ ω, esq (fun k => lam * g k ω + qg k ω) ∂P
        ≤ ∫⁻ ω, (2 * esq (fun k => g k ω) + 2 * esq (fun k => qg k ω)) ∂P :=
          lintegral_mono fun ω => esq_mul_add_le hl _ _
      _ = 2 * ∫⁻ ω, esq (fun k => g k ω) ∂P + 2 * ∫⁻ ω, esq (fun k => qg k ω) ∂P := by
          rw [lintegral_add_right' _ (hqgm.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
            lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ _ := by
          rw [mul_assoc]
          gcongr
          exact hD.lipT
  have htermr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hXT.ne,
      ENNReal.mul_ne_top (by norm_num) hqg.ne⟩) hterm
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      ENNReal.ofReal_ne_top) hXT.ne) (ENNReal.mul_ne_top (by norm_num) hqg.ne),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hKT,
    ENNReal.toReal_ofNat] at htermr
  rw [toReal_dataSize hP]
  have alg : ∀ {L a x Ξ p₁ p₂ p₃ p₄ p₅ p₆ e : ℝ}, 0 ≤ e → 0 ≤ a → 0 ≤ x → 0 ≤ p₁ → 0 ≤ p₂ →
      0 ≤ p₃ → 0 ≤ p₄ → 0 ≤ p₅ → 0 ≤ p₆ → L ≤ 2 * e * (Ξ + (2 * K * x + 2 * p₆)) →
      Ξ ≤ 2 * KT * a + 2 * p₂ →
      L ≤ 4 * (K + KT + 1) * e * (a + x + (p₁ + p₂ + p₃ + p₄ + p₅ + p₆)) := by
    intro L a x Ξ p₁ p₂ p₃ p₄ p₅ p₆ e he ha hx h1 h2 h3 h4 h5 h6 hL hΞ
    calc L ≤ 2 * e * (Ξ + (2 * K * x + 2 * p₆)) := hL
      _ ≤ 2 * e * (2 * (K + KT + 1) * (a + x + (p₁ + p₂ + p₃ + p₄ + p₅ + p₆))) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ = _ := by ring
  exact alg (Real.exp_pos _).le ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg key htermr

end PairDiff

end MVFBSDEJ.WellPosedness.Stability
