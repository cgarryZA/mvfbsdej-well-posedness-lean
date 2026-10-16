/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.ForwardEnergy
import Dissertation.WellPosedness.Stability.LipschitzRate

/-!
# The forward estimate of Lemma 4.3

Step 3 of the proof of Lemma 4.3 bounds the forward difference `δX` through `(δY, δZ, δU)` and
the data. For the difference system, `(λ δb + q^b)² ≤ 2 δb² + 2 (q^b)²` for `λ ∈ [0, 1]`, and
likewise for the diffusion and jump integrands, together with the expected Lipschitz bound (3.2)
give the rate bound of the weighted forward bound with `c = 2K` and
`G = 2K 𝔼(|δY|² + |δZ|²_F + ‖δU‖²) + 2 𝔼(|q^b|² + |q^σ|²_F + ‖q^h‖²)`. This is the forward
estimate `A + I_X ≤ k_F (J + P)` of the closure step, where `A = 𝔼|δX_T|²`,
`I_X = 𝔼 ∫_0^T |δX|²`, `J = 𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²)` and `P` is the data size, with
`k_F = 2 (K + 1) e^{(2 + 2K) T}`.

## Main definitions

* `forwardConst` — the constant `k_F = 2 (K + 1) e^{(2 + 2K) T}`.

## Main statements

* `PairDiff.forward_le` — the forward estimate of Lemma 4.3.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc Dissertation.WellPosedness.BrownianPoisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d n m : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

/-- The constant `k_F = 2 (K + 1) e^{(2 + 2K) T}` of the forward estimate. -/
noncomputable def forwardConst (T K : ℝ) : ℝ := 2 * (K + 1) * Real.exp ((2 + 2 * K) * T)

/-- The constant of the forward estimate is nonnegative for `K ≥ 0`. -/
theorem forwardConst_nonneg {K : ℝ} (hK : 0 ≤ K) (T : ℝ) : 0 ≤ forwardConst T K := by
  unfold forwardConst
  positivity

namespace PairDiff

variable {lam K KT α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {ξ₀ : Fin n → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
  {b : Fin n → Ω → ℝ → ℝ} {σ : Fin n → ℝ → Ω → Fin d → ℝ} {h : Fin n → ℝ → Ω → E → ℝ}
  {f : Fin m → Ω → ℝ → ℝ} {g : Fin m → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}

/-- **The forward estimate of Lemma 4.3.** For the difference system at `λ ∈ [0, 1]` with
Lipschitz constant `K ≥ 0` and finite data size `P`, over a filtration with a cross witness,

`𝔼|δX_T|² + 𝔼 ∫_0^T |δX|² ≤ k_F (𝔼 ∫_0^T (|δY|² + |δZ|²_F + ‖δU‖²) + P)`,

`k_F = 2 (K + 1) e^{(2 + 2K) T}`: the inequality `A + I_X ≤ k_F (J + P)` of the closure step. -/
theorem forward_le
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hK : 0 ≤ K)
    (hP : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) :
    (∫⁻ ω, esq (fun i => X i T ω) ∂P).toReal
        + (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)).toReal
      ≤ forwardConst T K * ((∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
          + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)).toReal
        + (dataSize P ν T ξ₀ qb qσ qh qf qg).toReal) := by
  obtain ⟨-, -, hqb, hqσ, hqh, -⟩ := lt_top_of_dataSize_ne_top hP
  have hl : lam ^ 2 ≤ 1 := by nlinarith
  have hYm : ∀ k, Measurable (Function.uncurry fun ω s => Y k s ω) := fun k =>
    (hD.bwd k).measurable_uncurry.comp measurable_swap
  set FJ : ℝ → ℝ≥0∞ := fun s => sampleEnergy P (fun k ω s => Y k s ω) s
    + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
    + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s with hFJ
  set FQ : ℝ → ℝ≥0∞ := fun s => sampleEnergy P qb s
    + ∑ i, sampleEnergy P (fun j ω s => qσ i s ω j) s
    + markedSampleEnergy P ν (fun i ω s e => qh i s ω e) s with hFQ
  have hFJm : Measurable FJ := measurable_sampleEnergy_add (x := fun k ω s => Y k s ω)
    (z := fun k j ω s => Z k s ω j) (u := fun k ω s e => U k s ω e) hYm
    (fun k j => (hD.bwd k).Z_meas j) fun k => (hD.bwd k).U_meas
  have hFQm : Measurable FQ := measurable_sampleEnergy_add (x := qb)
    (z := fun i j ω s => qσ i s ω j) (u := fun i ω s e => qh i s ω e) hD.qb_meas
    hD.qσ_meas hD.qh_meas
  have hFJw := lintegral_sampleEnergy_add (P := P) (ν := ν) (x := fun k ω s => Y k s ω)
    (z := fun k j ω s => Z k s ω j) (u := fun k ω s e => U k s ω e) hYm
    (fun k j => (hD.bwd k).Z_meas j) (fun k => (hD.bwd k).U_meas) T
  have hFQw := lintegral_sampleEnergy_add (P := P) (ν := ν) (x := qb)
    (z := fun i j ω s => qσ i s ω j) (u := fun i ω s e => qh i s ω e) hD.qb_meas
    hD.qσ_meas hD.qh_meas T
  have hJf : ∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
      + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
      + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.sum_ne_top.mpr fun k _ => ((hD.bwd k).energy_lt_top 𝒲 hT).ne,
        ENNReal.sum_ne_top.mpr fun k _ => ENNReal.sum_ne_top.mpr fun j _ => (hD.bwd k).Z_sq j⟩,
      ENNReal.sum_ne_top.mpr fun k _ => (hD.bwd k).U_sq⟩
  have hQf : ∑ i, Brownian.Ito.energy P T (qb i)
      + ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j)
      + ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.sum_ne_top.mpr fun i _ => (hqb i).ne,
        ENNReal.sum_ne_top.mpr fun i _ => ENNReal.sum_ne_top.mpr fun j _ => (hqσ i j).ne⟩,
      ENNReal.sum_ne_top.mpr fun i _ => (hqh i).ne⟩
  -- the rate bound with `c = 2K` and `G = 2K F_J + 2 F_Q`
  set Gr : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (2 * K) * FJ s + 2 * FQ s with hGr
  have hGm : Measurable Gr := (hFJm.const_mul _).add (hFQm.const_mul _)
  have hGw : ∫⁻ s in Set.Icc (0 : ℝ) T, Gr s = ENNReal.ofReal (2 * K)
      * (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
        + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e))
      + 2 * (∑ i, Brownian.Ito.energy P T (qb i)
        + ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j)
        + ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e)) := by
    rw [lintegral_add_left (hFJm.const_mul _), lintegral_const_mul _ hFJm,
      lintegral_const_mul _ hFQm, hFJw, hFQw]
  have hGf : ∫⁻ s in Set.Icc (0 : ℝ) T, Gr s ≠ ⊤ := by
    rw [hGw]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJf,
      ENNReal.mul_ne_top (by norm_num) hQf⟩
  have hrate : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      sampleEnergy P (fun i ω s => lam * b i ω s + qb i ω s) s
          + ∑ i, sampleEnergy P (fun j ω s => lam * σ i s ω j + qσ i s ω j) s
          + markedSampleEnergy P ν (fun i ω s e => lam * h i s ω e + qh i s ω e) s
        ≤ ENNReal.ofReal (2 * K) * sampleEnergy P (fun i ω s => X i s ω) s + Gr s := by
    filter_upwards [hD.ae_lip] with s hs
    have hb := sampleEnergy_mul_add_le (P := P) hl b qb s fun i =>
      ((hD.qb_meas i).comp (measurable_id.prodMk measurable_const)).aemeasurable
    have hσ := fun i => sampleEnergy_mul_add_le (P := P) hl (fun j ω s => σ i s ω j)
      (fun j ω s => qσ i s ω j) s fun j =>
        ((hD.qσ_meas i j).comp (measurable_id.prodMk measurable_const)).aemeasurable
    have hh := markedSampleEnergy_mul_add_le (P := P) (ν := ν) hl (fun i ω s e => h i s ω e)
      (fun i ω s e => qh i s ω e) s fun i =>
        (hD.qh_meas i).comp (by fun_prop : Measurable fun p : Ω × E => (p.1, s, p.2))
    have hsplit := add_le_add (add_le_add hb (Finset.sum_le_sum (s := Finset.univ) fun i _ => hσ i))
      hh
    refine hsplit.trans ?_
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    calc 2 * sampleEnergy P b s + 2 * sampleEnergy P qb s
          + (2 * ∑ i, sampleEnergy P (fun j ω s => σ i s ω j) s
            + 2 * ∑ i, sampleEnergy P (fun j ω s => qσ i s ω j) s)
          + (2 * markedSampleEnergy P ν (fun i ω s e => h i s ω e) s
            + 2 * markedSampleEnergy P ν (fun i ω s e => qh i s ω e) s)
        = 2 * (sampleEnergy P b s + ∑ i, sampleEnergy P (fun j ω s => σ i s ω j) s
            + markedSampleEnergy P ν (fun i ω s e => h i s ω e) s)
          + 2 * (sampleEnergy P qb s + ∑ i, sampleEnergy P (fun j ω s => qσ i s ω j) s
            + markedSampleEnergy P ν (fun i ω s e => qh i s ω e) s) := by ring
      _ ≤ 2 * (ENNReal.ofReal K * (sampleEnergy P (fun i ω s => X i s ω) s + FJ s))
          + 2 * (sampleEnergy P qb s + ∑ i, sampleEnergy P (fun j ω s => qσ i s ω j) s
            + markedSampleEnergy P ν (fun i ω s e => qh i s ω e) s) := by
        gcongr
        exact le_self_add.trans hs
      _ = _ := by
        rw [hGr, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        ring
  have key := forward_energy_le (β := fun i ω s => lam * b i ω s + qb i ω s)
    (σ := fun i s ω j => lam * σ i s ω j + qσ i s ω j)
    (γ := fun i s ω e => lam * h i s ω e + qh i s ω e) hD.fwd 𝒲 hT (by positivity) hGm hGf
    hrate
  rw [hGw, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJf)
      (ENNReal.mul_ne_top (by norm_num) hQf), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofNat] at key
  have hQ : (∑ i, Brownian.Ito.energy P T (qb i)
      + ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j)
      + ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e)).toReal
      ≤ (∑ i, Brownian.Ito.energy P T (qb i)).toReal
        + (∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j)).toReal
        + (∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e)).toReal :=
    ENNReal.toReal_add_le.trans (add_le_add ENNReal.toReal_add_le le_rfl)
  rw [toReal_dataSize hP]
  have alg : ∀ {L a J Q p₂ p₃ p₄ p₅ p₆ e : ℝ}, 0 ≤ e → 0 ≤ J → 0 ≤ a → 0 ≤ p₂ → 0 ≤ p₃ →
      0 ≤ p₄ → 0 ≤ p₅ → 0 ≤ p₆ → L ≤ e * (a + (2 * K * J + 2 * Q)) → Q ≤ p₃ + p₄ + p₅ →
      L ≤ 2 * (K + 1) * e * (J + (a + p₂ + p₃ + p₄ + p₅ + p₆)) := by
    intro L a J Q p₂ p₃ p₄ p₅ p₆ e he hJ ha h2 h3 h4 h5 h6 hL hQ
    calc L ≤ e * (a + (2 * K * J + 2 * Q)) := hL
      _ ≤ e * (2 * (K + 1) * (J + (a + p₂ + p₃ + p₄ + p₅ + p₆))) :=
          mul_le_mul_of_nonneg_left (by nlinarith) he
      _ = _ := by ring
  exact alg (Real.exp_pos _).le ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg key hQ

end PairDiff

end Dissertation.WellPosedness.Stability
