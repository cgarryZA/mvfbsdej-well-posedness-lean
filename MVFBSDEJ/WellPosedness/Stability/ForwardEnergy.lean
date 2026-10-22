/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.SampleEnergy
import MVFBSDEJ.WellPosedness.Stability.WeightedEnergy

/-!
# The weighted forward energy bound

For solutions `X_i` of the linear forward equation with jumps, with drifts `β_i`, diffusion
vectors `σ_i` and jump integrands `γ_i`, over a filtration carrying the driver with a cross
witness, the weighted second-moment identity at the weight `e^{−(2 + c) s}` has the time
integrand

`e^{−(2+c)s} (−(2 + c) 𝔼|X_s|² + 2 𝔼⟨X_s, β_s⟩ + 𝔼|σ_s|²_F + 𝔼‖γ_s‖²_{L²(ν)})`.

Young's inequality `2 ⟨X, β⟩ ≤ |X|² + |β|²` and a rate bound
`𝔼|β_s|² + 𝔼|σ_s|²_F + 𝔼‖γ_s‖² ≤ c 𝔼|X_s|² + G_s` bound the bracket by `−𝔼|X_s|² + G_s`, and
`e^{−(2+c)T} ≤ e^{−(2+c)s} ≤ 1` on `[0, T]` gives

`𝔼|X_T|² + 𝔼 ∫_0^T |X_s|² ds ≤ e^{(2+c)T} (𝔼|X_0|² + ∫_0^T G_s ds)`:

the weight absorbs the linear term, so no Grönwall lemma is needed. Step 3 of the proof of
Lemma 4.3 of the well-posedness paper bounds `𝔼 sup_{t ≤ T} |X_t|²` by BDG and Grönwall; this
bound controls `𝔼|X_T|²` and the time integral instead, which is what the closure step uses.

## Main statements

* `forward_energy_le` — the weighted forward bound for a family of linear forward equations.
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

/-- **The weighted forward bound.** Let `X_i` solve the linear forward equation from `ξ₀_i` with
drift `β_i`, diffusion vector `σ_i` and jump integrand `γ_i`, over a filtration with a cross
witness. If at almost every time `𝔼|β_s|² + 𝔼|σ_s|²_F + 𝔼‖γ_s‖² ≤ c 𝔼|X_s|² + G_s` with `c ≥ 0`
and `G` of finite integral, then

`𝔼|X_T|² + 𝔼 ∫_0^T |X_s|² ds ≤ e^{(2+c)T} (𝔼|ξ₀|² + ∫_0^T G_s ds)`. -/
theorem forward_energy_le {ξ₀ : Fin n → Ω → ℝ} {β : Fin n → Ω → ℝ → ℝ}
    {X : Fin n → ℝ → Ω → ℝ} {σ : Fin n → ℝ → Ω → Fin d → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}
    (hX : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (ξ₀ i) (β i) (X i) (σ i) (γ i))
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) {c : ℝ} (hc : 0 ≤ c) {G : ℝ → ℝ≥0∞}
    (hGm : Measurable G) (hG : ∫⁻ s in Set.Icc (0 : ℝ) T, G s ≠ ⊤)
    (hrate : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      sampleEnergy P β s + ∑ i, sampleEnergy P (fun j ω s => σ i s ω j) s
          + markedSampleEnergy P ν (fun i ω s e => γ i s ω e) s
        ≤ ENNReal.ofReal c * sampleEnergy P (fun i ω s => X i s ω) s + G s) :
    (∫⁻ ω, esq (fun i => X i T ω) ∂P).toReal
        + (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)).toReal
      ≤ Real.exp ((2 + c) * T) * ((∫⁻ ω, esq (fun i => ξ₀ i ω) ∂P).toReal
        + (∫⁻ s in Set.Icc (0 : ℝ) T, G s).toReal) := by
  classical
  set w : ℝ := -(2 + c) with hw
  set R : Fin n → ℝ → ℝ := fun i s => w * ∫ ω, X i s ω * X i s ω ∂P
    + 2 * ∫ ω, X i s ω * β i ω s ∂P
    + (∑ j : Fin d, (∫⁻ ω, (‖σ i s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
    + (∫⁻ ω, ∫⁻ e, (‖γ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal with hR
  set FX : ℝ → ℝ≥0∞ := sampleEnergy P (fun i ω s => X i s ω) with hFX
  have hXm : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω) := fun i =>
    ((hX i).linearBSDEJ hT.le).measurable_uncurry.comp measurable_swap
  have hFXm : Measurable FX := measurable_sampleEnergy hXm
  have hFXw : ∫⁻ s in Set.Icc (0 : ℝ) T, FX s = ∑ i, Brownian.Ito.energy P T
      (fun ω s => X i s ω) := lintegral_sampleEnergy hXm T
  have hFXf : ∫⁻ s in Set.Icc (0 : ℝ) T, FX s ≠ ⊤ := by
    rw [hFXw]
    exact ENNReal.sum_ne_top.mpr fun i _ => ((hX i).energy_lt_top 𝒲 hT).ne
  -- the pointwise bound on the time integrand
  have hpt : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Real.exp (w * s) * ∑ i, R i s ≤ -Real.exp (w * T) * (FX s).toReal + (G s).toReal := by
    have hXs : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i, MemLp (X i s) 2 P :=
      ae_all_iff.mpr fun i => Ito.SecondMoment.ae_memLp_two_eval (hXm i)
        ((hX i).energy_lt_top 𝒲 hT)
    have hβs : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        ∀ i, MemLp (fun ω => β i ω s) 2 P :=
      ae_all_iff.mpr fun i => Ito.SecondMoment.ae_memLp_two_eval (hX i).b_meas
        (hX i).b_sq.lt_top
    filter_upwards [ae_restrict_mem measurableSet_Icc, hXs, hβs, hrate,
      ae_lt_top hFXm hFXf, ae_lt_top hGm hG] with s hs hXs hβs hrs hFXs hGs
    have hRf : ENNReal.ofReal c * FX s + G s ≠ ⊤ :=
      (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFXs, hGs⟩).ne
    have hLf := (hrs.trans_lt (lt_top_iff_ne_top.mpr hRf)).ne
    have hβσf := (ENNReal.add_ne_top.mp hLf).1
    have hγf := (ENNReal.add_ne_top.mp hLf).2
    have hβf := (ENNReal.add_ne_top.mp hβσf).1
    have hσf := (ENNReal.add_ne_top.mp hβσf).2
    have hσf' : ∀ i, ∀ j ∈ Finset.univ, ∫⁻ ω, (‖σ i s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P ≠ ⊤ := fun i =>
      ENNReal.sum_ne_top.mp (ENNReal.sum_ne_top.mp hσf i (Finset.mem_univ _))
    -- the real form of the rate bound
    have hreal := ENNReal.toReal_mono hRf hrs
    rw [ENNReal.toReal_add hβσf hγf, ENNReal.toReal_add hβf hσf,
      ENNReal.toReal_sum fun i _ => ENNReal.sum_ne_top.mp hσf i (Finset.mem_univ _),
      ENNReal.toReal_add (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFXs).ne hGs.ne,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hc, toReal_sampleEnergy hβs] at hreal
    unfold markedSampleEnergy at hreal hγf
    rw [ENNReal.toReal_sum fun i _ => ENNReal.sum_ne_top.mp hγf i (Finset.mem_univ _)] at hreal
    simp only [sampleEnergy] at hreal
    simp only [ENNReal.toReal_sum (hσf' _)] at hreal
    rw [hFX, toReal_sampleEnergy hXs] at hreal ⊢
    -- Young's inequality on the drift pairing
    have hY : ∀ i, 2 * ∫ ω, X i s ω * β i ω s ∂P
        ≤ ∫ ω, X i s ω * X i s ω ∂P + ∫ ω, β i ω s * β i ω s ∂P := fun i => by
      simpa using two_mul_integral_mul_le (hXs i) (hβs i) 1
    have hsum : ∑ i, R i s = w * ∑ i, ∫ ω, X i s ω * X i s ω ∂P
        + ∑ i, 2 * ∫ ω, X i s ω * β i ω s ∂P
        + ∑ i, ∑ j : Fin d, (∫⁻ ω, (‖σ i s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
        + ∑ i, (∫⁻ ω, ∫⁻ e, (‖γ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal := by
      simp only [hR, Finset.sum_add_distrib, Finset.mul_sum]
    have hYs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hY i
    rw [Finset.sum_add_distrib] at hYs
    have hrate' : ∑ i, R i s ≤ -∑ i, ∫ ω, X i s ω * X i s ω ∂P + (G s).toReal := by
      rw [hsum, hw]
      linarith
    have ha : 0 ≤ ∑ i, ∫ ω, X i s ω * X i s ω ∂P :=
      Finset.sum_nonneg fun i _ => integral_nonneg fun ω => mul_self_nonneg _
    have hg : 0 ≤ (G s).toReal := ENNReal.toReal_nonneg
    have hw0 : w ≤ 0 := by rw [hw]; linarith
    have he1 : Real.exp (w * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hs.1])
    have heT : Real.exp (w * T) ≤ Real.exp (w * s) :=
      Real.exp_le_exp.mpr (by nlinarith [hs.2])
    have hepos : 0 ≤ Real.exp (w * s) := (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left hrate' hepos, mul_nonneg (sub_nonneg.mpr heT) ha,
      mul_nonneg (sub_nonneg.mpr he1) hg]
  -- integration in time
  have hRi : ∀ i, IntegrableOn (fun s => Real.exp (w * s) * R i s) (Set.Icc (0 : ℝ) T) :=
    fun i => (hX i).integrableOn_exp_mul_rate 𝒲 w hT
  have hFXi : IntegrableOn (fun s => (FX s).toReal) (Set.Icc (0 : ℝ) T) :=
    integrable_toReal_of_lintegral_ne_top hFXm.aemeasurable hFXf
  have hGi : IntegrableOn (fun s => (G s).toReal) (Set.Icc (0 : ℝ) T) :=
    integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hG
  have hLi : IntegrableOn (fun s => Real.exp (w * s) * ∑ i, R i s) (Set.Icc (0 : ℝ) T) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun i _ => hRi i
  have hint : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (w * s) * ∑ i, R i s
      ≤ -Real.exp (w * T) * (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)).toReal
        + (∫⁻ s in Set.Icc (0 : ℝ) T, G s).toReal := by
    refine (integral_mono_ae (g := fun s => -Real.exp (w * T) * (FX s).toReal + (G s).toReal)
      hLi ((hFXi.const_mul _).add hGi) hpt).trans_eq ?_
    rw [integral_add (hFXi.const_mul _) hGi, integral_const_mul,
      integral_toReal hFXm.aemeasurable (ae_lt_top hFXm hFXf),
      integral_toReal hGm.aemeasurable (ae_lt_top hGm hG), hFXw]
  -- the summed weighted identity
  have hid : Real.exp (w * T) * ∑ i, ∫ ω, X i T ω * X i T ω ∂P
      = ∑ i, ∫ ω, X i 0 ω * X i 0 ω ∂P
        + ∫ s in Set.Icc (0 : ℝ) T, Real.exp (w * s) * ∑ i, R i s := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun i _ => hRi i, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (hX i).exp_mul_integral_mul_self_eq 𝒲 w hT
  have hA : (∫⁻ ω, esq (fun i => X i T ω) ∂P).toReal = ∑ i, ∫ ω, X i T ω * X i T ω ∂P :=
    toReal_lintegral_esq fun i => (hX i).memLp_terminal hT.le
  have hΞ : (∫⁻ ω, esq (fun i => ξ₀ i ω) ∂P).toReal = ∑ i, ∫ ω, X i 0 ω * X i 0 ω ∂P := by
    rw [toReal_lintegral_esq fun i => (hX i).ξ₀_sq]
    refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
    filter_upwards [(hX i).initial_ae_eq hT.le] with ω hω
    rw [hω]
  have hexp : Real.exp ((2 + c) * T) * Real.exp (w * T) = 1 := by
    rw [← Real.exp_add, hw, ← add_mul, add_neg_cancel, zero_mul, Real.exp_zero]
  rw [hA, hΞ]
  have hle : Real.exp (w * T) * (∑ i, ∫ ω, X i T ω * X i T ω ∂P
      + (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)).toReal)
      ≤ ∑ i, ∫ ω, X i 0 ω * X i 0 ω ∂P + (∫⁻ s in Set.Icc (0 : ℝ) T, G s).toReal := by
    rw [mul_add]
    linarith
  calc ∑ i, ∫ ω, X i T ω * X i T ω ∂P + (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)).toReal
      = Real.exp ((2 + c) * T) * (Real.exp (w * T) * (∑ i, ∫ ω, X i T ω * X i T ω ∂P
        + (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)).toReal)) := by
        rw [← mul_assoc, hexp, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

end MVFBSDEJ.WellPosedness.Stability
