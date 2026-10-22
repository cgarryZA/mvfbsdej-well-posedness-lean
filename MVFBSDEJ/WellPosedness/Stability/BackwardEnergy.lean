/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.SampleEnergy
import MVFBSDEJ.WellPosedness.Stability.WeightedEnergy

/-!
# The weighted backward energy bound

For solutions `(Y_k, Z_k, U_k)` of the linear backward equation with jumps, with terminal values
`ξ_k` and drifts `φ_k`, over a filtration carrying the driver with a cross witness, Itô's formula
for `e^{κt} |Y_t|²` gives in expectation, with `κ = 2c + 2` and `a = 2c + 1`,

`e^{κT} 𝔼|ξ|² = 𝔼|Y_0|² + ∫_0^T e^{κs} (κ 𝔼|Y_s|² − 2 𝔼⟨Y_s, φ_s⟩ + 𝔼|Z_s|²_F
  + 𝔼‖U_s‖²_{L²(ν)}) ds`.

Young's inequality `2 a ⟨Y, φ⟩ ≤ a² |Y|² + |φ|²` and a rate bound
`𝔼|φ_s|² ≤ c 𝔼(|Y_s|² + |Z_s|²_F + ‖U_s‖²) + G_s` bound the bracket below by
`½ 𝔼(|Y_s|² + |Z_s|²_F + ‖U_s‖²) − G_s`, since `c/a ≤ ½` and `a ≥ 1`; and `1 ≤ e^{κs} ≤ e^{κT}`
on `[0, T]` gives

`𝔼|Y_0|² + 𝔼 ∫_0^T (|Y|² + |Z|²_F + ‖U‖²) ds ≤ 2 e^{κT} (𝔼|ξ|² + ∫_0^T G_s ds)`.

Only time `0` enters: the margin `κ − a − c/a ≥ ½` keeps the `|Y|²`-integral on the left, so the
family of estimates over `[t, T]` in Step 4 of the proof of Lemma 4.3 of the well-posedness paper
is not needed. The bound controls `𝔼|Y_0|²` and the time integral, not `𝔼 sup_{t ≤ T} |Y_t|²`.

## Main statements

* `backward_energy_le` — the weighted backward bound for a family of linear backward equations.
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

/-- **The weighted backward bound.** Let `(Y_k, Z_k, U_k)` solve the linear backward equation
with terminal value `ξ_k` and drift `φ_k`, over a filtration with a cross witness. If at almost
every time `𝔼|φ_s|² ≤ c 𝔼(|Y_s|² + |Z_s|²_F + ‖U_s‖²) + G_s` with `c ≥ 0` and `G` of finite
integral, then

`𝔼|Y_0|² + 𝔼 ∫_0^T (|Y|² + |Z|²_F + ‖U‖²) ds ≤ 2 e^{(2c+2)T} (𝔼|ξ|² + ∫_0^T G_s ds)`. -/
theorem backward_energy_le {ξ : Fin m → Ω → ℝ} {φ : Fin m → Ω → ℝ → ℝ}
    {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
    (hY : ∀ k, LinearBSDEJ D ℱ hℱW hℱN T (ξ k) (φ k) (Y k) (Z k) (U k))
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) {c : ℝ} (hc : 0 ≤ c) {G : ℝ → ℝ≥0∞}
    (hGm : Measurable G) (hG : ∫⁻ s in Set.Icc (0 : ℝ) T, G s ≠ ⊤)
    (hrate : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      sampleEnergy P φ s ≤ ENNReal.ofReal c * (sampleEnergy P (fun k ω s => Y k s ω) s
        + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
        + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s) + G s) :
    (∫⁻ ω, esq (fun k => Y k 0 ω) ∂P).toReal
        + (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
          + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)).toReal
      ≤ 2 * Real.exp ((2 * c + 2) * T) * ((∫⁻ ω, esq (fun k => ξ k ω) ∂P).toReal
        + (∫⁻ s in Set.Icc (0 : ℝ) T, G s).toReal) := by
  classical
  set κ : ℝ := 2 * c + 2 with hκ
  set R : Fin m → ℝ → ℝ := fun k s => κ * ∫ ω, Y k s ω * Y k s ω ∂P
    + 2 * ∫ ω, Y k s ω * -φ k ω s ∂P
    + (∑ j : Fin d, (∫⁻ ω, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
    + (∫⁻ ω, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal with hR
  have hYm : ∀ k, Measurable (Function.uncurry fun ω s => Y k s ω) := fun k =>
    (hY k).measurable_uncurry.comp measurable_swap
  set FJ : ℝ → ℝ≥0∞ := fun s => sampleEnergy P (fun k ω s => Y k s ω) s
    + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
    + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s with hFJ
  have hFJm : Measurable FJ := measurable_sampleEnergy_add (x := fun k ω s => Y k s ω)
    (z := fun k j ω s => Z k s ω j) (u := fun k ω s e => U k s ω e) hYm
    (fun k j => (hY k).Z_meas j) fun k => (hY k).U_meas
  have hFJw := lintegral_sampleEnergy_add (P := P) (ν := ν) (x := fun k ω s => Y k s ω)
    (z := fun k j ω s => Z k s ω j) (u := fun k ω s e => U k s ω e) hYm
    (fun k j => (hY k).Z_meas j) (fun k => (hY k).U_meas) T
  have hFJf : ∫⁻ s in Set.Icc (0 : ℝ) T, FJ s ≠ ⊤ := by
    rw [hFJw]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.sum_ne_top.mpr fun k _ => ((hY k).energy_lt_top 𝒲 hT).ne,
        ENNReal.sum_ne_top.mpr fun k _ => ENNReal.sum_ne_top.mpr fun j _ => (hY k).Z_sq j⟩,
      ENNReal.sum_ne_top.mpr fun k _ => (hY k).U_sq⟩
  -- the pointwise bound on the time integrand
  have hpt : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (FJ s).toReal / 2 - Real.exp (κ * T) * (G s).toReal ≤ Real.exp (κ * s) * ∑ k, R k s := by
    have hYs : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ k, MemLp (Y k s) 2 P :=
      ae_all_iff.mpr fun k => Ito.SecondMoment.ae_memLp_two_eval (hYm k)
        ((hY k).energy_lt_top 𝒲 hT)
    have hφs : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        ∀ k, MemLp (fun ω => φ k ω s) 2 P :=
      ae_all_iff.mpr fun k => Ito.SecondMoment.ae_memLp_two_eval (hY k).φ_meas
        (hY k).φ_sq.lt_top
    filter_upwards [ae_restrict_mem measurableSet_Icc, hYs, hφs, hrate,
      ae_lt_top hFJm hFJf, ae_lt_top hGm hG] with s hs hYs hφs hrs hFJs hGs
    have hRf : ENNReal.ofReal c * FJ s + G s ≠ ⊤ :=
      (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFJs, hGs⟩).ne
    have hYZf := (ENNReal.add_ne_top.mp hFJs.ne).1
    have hUf := (ENNReal.add_ne_top.mp hFJs.ne).2
    have hYf := (ENNReal.add_ne_top.mp hYZf).1
    have hZf := (ENNReal.add_ne_top.mp hYZf).2
    have hZf' : ∀ k, ∀ j ∈ Finset.univ, ∫⁻ ω, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P ≠ ⊤ := fun k =>
      ENNReal.sum_ne_top.mp (ENNReal.sum_ne_top.mp hZf k (Finset.mem_univ _))
    -- the real form of the rate bound and of `F_J`
    have hreal := ENNReal.toReal_mono hRf hrs
    rw [ENNReal.toReal_add (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFJs).ne hGs.ne,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, toReal_sampleEnergy hφs] at hreal
    have hFJr : (FJ s).toReal = ∑ k, ∫ ω, Y k s ω * Y k s ω ∂P
        + ∑ k, ∑ j : Fin d, (∫⁻ ω, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
        + ∑ k, (∫⁻ ω, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal := by
      rw [hFJ, ENNReal.toReal_add hYZf hUf, ENNReal.toReal_add hYf hZf,
        toReal_sampleEnergy hYs,
        ENNReal.toReal_sum fun k _ => ENNReal.sum_ne_top.mp hZf k (Finset.mem_univ _)]
      unfold markedSampleEnergy at hUf ⊢
      rw [ENNReal.toReal_sum fun k _ => ENNReal.sum_ne_top.mp hUf k (Finset.mem_univ _)]
      simp only [sampleEnergy, ENNReal.toReal_sum (hZf' _)]
    rw [hFJr] at hreal ⊢
    -- Young's inequality on the drift pairing, with `a = 2c + 1`
    have hYo : ∀ k, -((2 * c + 1) * (2 * ∫ ω, Y k s ω * -φ k ω s ∂P))
        ≤ (2 * c + 1) ^ 2 * ∫ ω, Y k s ω * Y k s ω ∂P + ∫ ω, φ k ω s * φ k ω s ∂P := fun k => by
      have := two_mul_integral_mul_le (hYs k) (hφs k) (2 * c + 1)
      simp only [mul_neg, integral_neg]
      linarith
    have hYos := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hYo k
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hYos
    simp only [← Finset.mul_sum, Finset.sum_neg_distrib] at hYos
    have hsum : ∑ k, R k s = κ * ∑ k, ∫ ω, Y k s ω * Y k s ω ∂P
        + 2 * ∑ k, ∫ ω, Y k s ω * -φ k ω s ∂P
        + ∑ k, ∑ j : Fin d, (∫⁻ ω, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
        + ∑ k, (∫⁻ ω, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal := by
      simp only [hR, Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsum]
    have hy0 : 0 ≤ ∑ k, ∫ ω, Y k s ω * Y k s ω ∂P :=
      Finset.sum_nonneg fun k _ => integral_nonneg fun ω => mul_self_nonneg _
    have hz0 : 0 ≤ ∑ k, ∑ j : Fin d, (∫⁻ ω, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have hu0 : 0 ≤ ∑ k, (∫⁻ ω, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal :=
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have hg0 : 0 ≤ (G s).toReal := ENNReal.toReal_nonneg
    have he1 : 1 ≤ Real.exp (κ * s) := Real.one_le_exp (by nlinarith [hs.1])
    have heT : Real.exp (κ * s) ≤ Real.exp (κ * T) := Real.exp_le_exp.mpr (by nlinarith [hs.2])
    generalize ∑ k, ∫ ω, Y k s ω * Y k s ω ∂P = y at hreal hYos hy0 ⊢
    generalize ∑ k, ∫ ω, Y k s ω * -φ k ω s ∂P = S at hYos ⊢
    generalize ∑ k, ∑ j : Fin d, (∫⁻ ω, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal = z at hreal hz0 ⊢
    generalize ∑ k, (∫⁻ ω, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal = u at hreal hu0 ⊢
    generalize ∑ k, ∫ ω, φ k ω s * φ k ω s ∂P = F at hreal hYos
    generalize (G s).toReal = g at hreal hg0 ⊢
    generalize Real.exp (κ * s) = es at he1 heT ⊢
    have h1 : (2 * c + 1) * ((y + z + u) / 2 - g) ≤ (2 * c + 1) * (κ * y + 2 * S + z + u) := by
      rw [hκ]
      nlinarith [mul_nonneg hc hg0]
    have h2 := le_of_mul_le_mul_left h1 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left h2 (zero_le_one.trans he1),
      mul_nonneg (sub_nonneg.mpr he1) (by positivity : 0 ≤ (y + z + u) / 2),
      mul_nonneg (sub_nonneg.mpr heT) hg0]
  -- integration in time
  have hRi : ∀ k, IntegrableOn (fun s => Real.exp (κ * s) * R k s) (Set.Icc (0 : ℝ) T) :=
    fun k => (hY k).integrableOn_exp_mul_rate 𝒲 κ hT
  have hFJi : IntegrableOn (fun s => (FJ s).toReal) (Set.Icc (0 : ℝ) T) :=
    integrable_toReal_of_lintegral_ne_top hFJm.aemeasurable hFJf
  have hGi : IntegrableOn (fun s => (G s).toReal) (Set.Icc (0 : ℝ) T) :=
    integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hG
  have hLi : IntegrableOn (fun s => Real.exp (κ * s) * ∑ k, R k s) (Set.Icc (0 : ℝ) T) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun k _ => hRi k
  have hint : (∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
        + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)).toReal / 2
      - Real.exp (κ * T) * (∫⁻ s in Set.Icc (0 : ℝ) T, G s).toReal
      ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (κ * s) * ∑ k, R k s := by
    refine le_trans (le_of_eq ?_) (integral_mono_ae
      (f := fun s => (FJ s).toReal / 2 - Real.exp (κ * T) * (G s).toReal)
      ((hFJi.div_const 2).sub (hGi.const_mul _)) hLi hpt)
    rw [integral_sub (hFJi.div_const 2) (hGi.const_mul _), integral_div, integral_const_mul,
      integral_toReal hFJm.aemeasurable (ae_lt_top hFJm hFJf),
      integral_toReal hGm.aemeasurable (ae_lt_top hGm hG), hFJw]
  -- the summed weighted identity
  have hid : Real.exp (κ * T) * ∑ k, ∫ ω, Y k T ω * Y k T ω ∂P
      = ∑ k, ∫ ω, Y k 0 ω * Y k 0 ω ∂P
        + ∫ s in Set.Icc (0 : ℝ) T, Real.exp (κ * s) * ∑ k, R k s := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun k _ => hRi k, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => (hY k).exp_mul_integral_mul_self_eq 𝒲 κ hT
  have hY0 : (∫⁻ ω, esq (fun k => Y k 0 ω) ∂P).toReal = ∑ k, ∫ ω, Y k 0 ω * Y k 0 ω ∂P :=
    toReal_lintegral_esq fun k => (hY k).memLp_initial hT.le
  have hΞ : (∫⁻ ω, esq (fun k => ξ k ω) ∂P).toReal = ∑ k, ∫ ω, Y k T ω * Y k T ω ∂P := by
    rw [toReal_lintegral_esq fun k => (hY k).ξ_sq]
    refine Finset.sum_congr rfl fun k _ => integral_congr_ae ?_
    filter_upwards [(hY k).ae_eq_terminal hT.le] with ω hω
    rw [hω]
  have hy0 : 0 ≤ ∑ k, ∫ ω, Y k 0 ω * Y k 0 ω ∂P :=
    Finset.sum_nonneg fun k _ => integral_nonneg fun ω => mul_self_nonneg _
  rw [hY0, hΞ]
  nlinarith [hid, hint, hy0]

end MVFBSDEJ.WellPosedness.Stability
