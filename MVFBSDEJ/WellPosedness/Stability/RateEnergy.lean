/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.LipschitzRate

/-!
# The energies of the realised integrands of the difference system

In the difference system (4.15)–(4.16) of Lemma 4.3 of the well-posedness paper the realised
integrands are `λ δψ + q^ψ` for `ψ ∈ {b, σ, h, f}`. For `λ ∈ [0, 1]`,
`|λ x + q|² ≤ 2 |x|² + 2 |q|²`, and the expected Lipschitz bound (3.2), integrated over the
horizon, bounds the coefficient differences by the difference itself:

`𝔼 ∫_0^T (|λ δb + q^b|² + |λ δσ + q^σ|²_F + ‖λ δh + q^h‖² + |λ δf + q^f|²)
  ≤ 2K 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²)
    + 2 𝔼 ∫_0^T (|q^b|² + |q^σ|²_F + ‖q^h‖² + |q^f|²)`.

This controls the drift and martingale parts of the running suprema in the supremum upgrade of
Lemma 4.3.

## Main statements

* `PairDiff.rateEnergy_le` — the energies of the realised integrands.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {d n m : ℕ}

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

/-- **The energies of the realised integrands.** For the difference system at `λ ∈ [0, 1]`,

`𝔼 ∫_0^T (|λ δb + q^b|² + |λ δσ + q^σ|²_F + ‖λ δh + q^h‖² + |λ δf + q^f|²)
  ≤ 2K 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²)
    + 2 𝔼 ∫_0^T (|q^b|² + |q^σ|²_F + ‖q^h‖² + |q^f|²)`. -/
theorem rateEnergy_le
    (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g qb qσ qh qf qg)
    (hT : 0 ≤ T) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    ∑ i, Brownian.Ito.energy P T (fun ω s => lam * b i ω s + qb i ω s)
        + ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => lam * σ i s ω j + qσ i s ω j)
        + ∑ i, Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => lam * h i s ω e + qh i s ω e)
        + ∑ k, Brownian.Ito.energy P T (fun ω s => lam * f k ω s + qf k ω s)
      ≤ 2 * ENNReal.ofReal K * (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
          + (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
            + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
            + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)))
        + 2 * (∑ i, Brownian.Ito.energy P T (qb i)
          + ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j)
          + ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e)
          + ∑ k, Brownian.Ito.energy P T (qf k)) := by
  have hl : lam ^ 2 ≤ 1 := by nlinarith
  have hXm : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω) := fun i =>
    ((hD.fwd i).linearBSDEJ hT).measurable_uncurry.comp measurable_swap
  have hYm : ∀ k, Measurable (Function.uncurry fun ω s => Y k s ω) := fun k =>
    (hD.bwd k).measurable_uncurry.comp measurable_swap
  -- the time integrals of the realised integrands
  have eR := lintegral_sampleEnergy_add (P := P) (ν := ν)
    (x := fun i ω s => lam * b i ω s + qb i ω s)
    (z := fun i j ω s => lam * σ i s ω j + qσ i s ω j)
    (u := fun i ω s e => lam * h i s ω e + qh i s ω e) (fun i => (hD.fwd i).b_meas)
    (fun i j => (hD.fwd i).σ_meas j) (fun i => (hD.fwd i).γ_meas) T
  have eRf := lintegral_sampleEnergy (P := P) (x := fun k ω s => lam * f k ω s + qf k ω s)
    (fun k => (hD.bwd k).φ_meas) T
  -- the time integrals of the difference and of the forcings
  set FX : ℝ → ℝ≥0∞ := sampleEnergy P (fun i ω s => X i s ω) with hFX
  set FJ : ℝ → ℝ≥0∞ := fun s => sampleEnergy P (fun k ω s => Y k s ω) s
    + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
    + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s with hFJ
  set FQ : ℝ → ℝ≥0∞ := fun s => sampleEnergy P qb s
    + ∑ i, sampleEnergy P (fun j ω s => qσ i s ω j) s
    + markedSampleEnergy P ν (fun i ω s e => qh i s ω e) s with hFQ
  have hFXm : Measurable FX := measurable_sampleEnergy hXm
  have hFJm : Measurable FJ := measurable_sampleEnergy_add (x := fun k ω s => Y k s ω)
    (z := fun k j ω s => Z k s ω j) (u := fun k ω s e => U k s ω e) hYm
    (fun k j => (hD.bwd k).Z_meas j) fun k => (hD.bwd k).U_meas
  have hFQm : Measurable FQ := measurable_sampleEnergy_add (x := qb)
    (z := fun i j ω s => qσ i s ω j) (u := fun i ω s e => qh i s ω e) hD.qb_meas
    hD.qσ_meas hD.qh_meas
  have hFfm : Measurable (sampleEnergy P qf) := measurable_sampleEnergy hD.qf_meas
  have eFX : ∫⁻ s in Set.Icc (0 : ℝ) T, FX s
      = ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω) := lintegral_sampleEnergy hXm T
  have eFJ := lintegral_sampleEnergy_add (P := P) (ν := ν) (x := fun k ω s => Y k s ω)
    (z := fun k j ω s => Z k s ω j) (u := fun k ω s e => U k s ω e) hYm
    (fun k j => (hD.bwd k).Z_meas j) (fun k => (hD.bwd k).U_meas) T
  have eFQ := lintegral_sampleEnergy_add (P := P) (ν := ν) (x := qb)
    (z := fun i j ω s => qσ i s ω j) (u := fun i ω s e => qh i s ω e) hD.qb_meas
    hD.qσ_meas hD.qh_meas T
  have eFf := lintegral_sampleEnergy (P := P) hD.qf_meas T
  -- the rate bound at almost every time
  have hrate : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      sampleEnergy P (fun i ω s => lam * b i ω s + qb i ω s) s
          + ∑ i, sampleEnergy P (fun j ω s => lam * σ i s ω j + qσ i s ω j) s
          + markedSampleEnergy P ν (fun i ω s e => lam * h i s ω e + qh i s ω e) s
          + sampleEnergy P (fun k ω s => lam * f k ω s + qf k ω s) s
        ≤ 2 * ENNReal.ofReal K * (FX s + FJ s) + 2 * (FQ s + sampleEnergy P qf s) := by
    filter_upwards [hD.ae_lip] with s hs
    have hb := sampleEnergy_mul_add_le (P := P) hl b qb s fun i =>
      ((hD.qb_meas i).comp (measurable_id.prodMk measurable_const)).aemeasurable
    have hσ := fun i => sampleEnergy_mul_add_le (P := P) hl (fun j ω s => σ i s ω j)
      (fun j ω s => qσ i s ω j) s fun j =>
        ((hD.qσ_meas i j).comp (measurable_id.prodMk measurable_const)).aemeasurable
    have hh := markedSampleEnergy_mul_add_le (P := P) (ν := ν) hl (fun i ω s e => h i s ω e)
      (fun i ω s e => qh i s ω e) s fun i =>
        (hD.qh_meas i).comp (by fun_prop : Measurable fun p : Ω × E => (p.1, s, p.2))
    have hf := sampleEnergy_mul_add_le (P := P) hl f qf s fun k =>
      ((hD.qf_meas k).comp (measurable_id.prodMk measurable_const)).aemeasurable
    refine (add_le_add (add_le_add (add_le_add hb
      (Finset.sum_le_sum (s := Finset.univ) fun i _ => hσ i)) hh) hf).trans ?_
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    calc 2 * sampleEnergy P b s + 2 * sampleEnergy P qb s
          + (2 * ∑ i, sampleEnergy P (fun j ω s => σ i s ω j) s
            + 2 * ∑ i, sampleEnergy P (fun j ω s => qσ i s ω j) s)
          + (2 * markedSampleEnergy P ν (fun i ω s e => h i s ω e) s
            + 2 * markedSampleEnergy P ν (fun i ω s e => qh i s ω e) s)
          + (2 * sampleEnergy P f s + 2 * sampleEnergy P qf s)
        = 2 * (sampleEnergy P b s + ∑ i, sampleEnergy P (fun j ω s => σ i s ω j) s
            + markedSampleEnergy P ν (fun i ω s e => h i s ω e) s + sampleEnergy P f s)
          + 2 * (FQ s + sampleEnergy P qf s) := by rw [hFQ]; ring
      _ ≤ 2 * (ENNReal.ofReal K * (FX s + FJ s)) + 2 * (FQ s + sampleEnergy P qf s) := by
        gcongr
      _ = _ := by ring
  have hm0 : Measurable fun s => FX s + FJ s := hFXm.add hFJm
  have hm1 : Measurable fun s => 2 * ENNReal.ofReal K * (FX s + FJ s) := hm0.const_mul _
  have hm2 : Measurable fun s => FQ s + sampleEnergy P qf s := hFQm.add hFfm
  calc _ = (∫⁻ s in Set.Icc (0 : ℝ) T,
          (sampleEnergy P (fun i ω s => lam * b i ω s + qb i ω s) s
            + ∑ i, sampleEnergy P (fun j ω s => lam * σ i s ω j + qσ i s ω j) s
            + markedSampleEnergy P ν (fun i ω s e => lam * h i s ω e + qh i s ω e) s))
        + ∫⁻ s in Set.Icc (0 : ℝ) T,
          sampleEnergy P (fun k ω s => lam * f k ω s + qf k ω s) s :=
        (congrArg₂ (· + ·) eR eRf).symm
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T,
          (sampleEnergy P (fun i ω s => lam * b i ω s + qb i ω s) s
            + ∑ i, sampleEnergy P (fun j ω s => lam * σ i s ω j + qσ i s ω j) s
            + markedSampleEnergy P ν (fun i ω s e => lam * h i s ω e + qh i s ω e) s
            + sampleEnergy P (fun k ω s => lam * f k ω s + qf k ω s) s) :=
        le_lintegral_add (fun s => sampleEnergy P (fun i ω s => lam * b i ω s + qb i ω s) s
            + ∑ i, sampleEnergy P (fun j ω s => lam * σ i s ω j + qσ i s ω j) s
            + markedSampleEnergy P ν (fun i ω s e => lam * h i s ω e + qh i s ω e) s)
          (fun s => sampleEnergy P (fun k ω s => lam * f k ω s + qf k ω s) s)
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T,
          (2 * ENNReal.ofReal K * (FX s + FJ s) + 2 * (FQ s + sampleEnergy P qf s)) :=
        lintegral_mono_ae hrate
    _ = _ := by
        rw [lintegral_add_left hm1, lintegral_const_mul _ hm0,
          lintegral_const_mul _ hm2, lintegral_add_left hFXm,
          lintegral_add_left hFQm, eFX, eFJ, eFQ, eFf]

end PairDiff

end MVFBSDEJ.WellPosedness.Stability
