/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.BrownianPoisson.MeasurableDrift
import MVFBSDEJ.WellPosedness.Stability.WeightedEnergy

/-!
# The energy bound of a linear backward equation at every time

For a solution `(Y, Z, U)` of the linear backward equation with drift `φ` over a filtration
carrying the driver with a cross witness, the weighted second-moment identities at weight `e^s`
at the horizons `t` and `T` differ by the integral of their rate over `(t, T]`. Young's inequality
`𝔼[Y_s²] − 2 𝔼[Y_s φ_s] ≥ −𝔼[φ_s²]` and `1 ≤ e^s ≤ e^T` on `[t, T]` then give, for every
`t ∈ [0, T]`,

`𝔼[Y_t²] + 𝔼 ∫_t^T (|Z_s|² + ∫_E U_s(e)² ν(de)) ds ≤ e^T (𝔼[ξ²] + 𝔼 ∫_0^T φ_s² ds)`,

the bound at every time in the proof of Lemma 4.1 of the well-posedness paper.

## Main statements

* `toReal_lintegral_setLIntegral_eq` — a window energy is the time integral of the sample
  energies.
* `LinearBSDEJ.exp_mul_integral_mul_self_eq_at` — the weighted identity at a time of `[0, T]`.
* `LinearBSDEJ.lintegral_sq_at_add_energy_le` — the bound at every time.
* `brownianPoisson_energy_at_vec_of_measurable` — the same in `ℝᵐ`, for a jointly measurable
  drift and a solution given on `[0, T]` only.
* `brownianPoisson_supE_vec_of_measurable` — the bound on
  `sup_{t ≤ T} 𝔼|Y_t|² + 𝔼 ∫_0^T (|Z_s|²_F + ‖U_s‖²) ds` by `2 e^T (𝔼|ξ|² + 𝔼 ∫_0^T |φ_s|² ds)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.BrownianPoisson

open LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

section Window

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- A window energy over a measurable set of times `S` is the time integral over `S` of the
sample energies. -/
theorem toReal_lintegral_setLIntegral_eq [SFinite P] {F : Ω → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) {S : Set ℝ}
    (hfin : ∫⁻ ω, ∫⁻ s in S, F ω s ∂volume ∂P < ⊤) :
    (∫⁻ ω, ∫⁻ s in S, F ω s ∂volume ∂P).toReal = ∫ s in S, (∫⁻ ω, F ω s ∂P).toReal := by
  have hswap : ∫⁻ ω, ∫⁻ s in S, F ω s ∂volume ∂P = ∫⁻ s in S, ∫⁻ ω, F ω s ∂P ∂volume :=
    lintegral_lintegral_swap (μ := P) (ν := volume.restrict S) hF.aemeasurable
  have hm : Measurable fun s => ∫⁻ ω, F ω s ∂P := hF.lintegral_prod_left
  rw [hswap, integral_toReal hm.aemeasurable]
  exact ae_lt_top hm (by rw [← hswap]; exact hfin.ne)

/-- A double lower integral over the sample point and a set of times is the lower integral over
the product measure. -/
theorem lintegral_setLIntegral_eq_prod [SFinite P] {F : Ω × ℝ → ℝ≥0∞} (hF : Measurable F)
    (S : Set ℝ) :
    ∫⁻ ω, ∫⁻ s in S, F (ω, s) ∂volume ∂P = ∫⁻ p, F p ∂(P.prod (volume.restrict S)) :=
  (lintegral_prod _ hF.aemeasurable).symm

end Window

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {T : ℝ} {ξ : Ω → ℝ} {φ : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
  {U : ℝ → Ω → E → ℝ}

namespace LinearBSDEJ

/-- **The weighted second-moment identity at a time `t ∈ [0, T]`** of a solution of the linear
backward equation, over a filtration with a cross witness. -/
theorem exp_mul_integral_mul_self_eq_at (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U)
    (𝒲 : D.CrossWitness ℱ) (β : ℝ) (hT : 0 < T) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    Real.exp (β * t) * ∫ ω, Y t ω * Y t ω ∂P
      = ∫ ω, Y 0 ω * Y 0 ω ∂P + ∫ s in Set.Icc (0 : ℝ) t, Real.exp (β * s)
          * (β * ∫ ω, Y s ω * Y s ω ∂P + 2 * ∫ ω, Y s ω * -φ ω s ∂P
            + (∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
            + (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) := by
  rcases ht.eq_or_lt with h0 | h0
  · subst h0
    rw [integral_Icc_eq_integral_Ioc, Set.Ioc_self, setIntegral_empty, mul_zero, Real.exp_zero,
      one_mul, add_zero]
  have key := Ito.SecondMoment.integral_exp_mul_self_eq_of_isItoLevyProcess
    (h.isItoLevyProcess_clampT hT) 𝒲 h.stronglyMeasurable_initial (h.memLp_initial hT.le)
    h.φ_meas.neg (continuous_neg.comp_progressivelyMeasurable neg_zero h.φ_prog)
    (fun T' _ => neg_drift_sq_int_global h.φ_vanish h.φ_sq T') β h0
  rw [clampT_apply_of_le htT] at key
  rw [key]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  simp only [clampT_apply_of_le (hs.2.trans htT)]

/-- **The bound at every time**, in the separated form: for a solution of the linear backward
equation over a filtration with a cross witness and every `t ∈ [0, T]`,
`𝔼[Y_t²] + (∑_j 𝔼 ∫_{(t, T]} Z_j(s)² ds + 𝔼 ∫_{(t, T]} ∫_E U_s(e)² ν(de) ds)
  ≤ e^T (𝔼[ξ²] + 𝔼 ∫_0^T φ_s² ds)`. -/
theorem lintegral_sq_at_add_energy_le_Ioc (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        + ((∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Ioc t T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Ioc t T, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      ≤ ENNReal.ofReal (Real.exp T)
        * (∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P + Brownian.Ito.energy P T φ) := by
  classical
  obtain ⟨ht0, htT⟩ := ht
  have hI := h.isItoLevyProcess_clampT hT
  have hbm : Measurable (Function.uncurry fun ω s => -φ ω s) := h.φ_meas.neg
  have hbq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖-φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun T' _ =>
    neg_drift_sq_int_global h.φ_vanish h.φ_sq T'
  have hX₀2 := h.memLp_initial hT.le
  have hYs : ∀ s ∈ Set.Icc (0 : ℝ) T, MemLp (Y s) 2 P := fun s hs => by
    have := Ito.SecondMoment.memLp_two_of_isItoLevyProcess hI hX₀2 hbm hbq hs.1
    rwa [clampT_apply_of_le hs.2] at this
  have hφm2 : Measurable (Function.uncurry fun ω s => (‖φ ω s‖₊ : ℝ≥0∞) ^ 2) :=
    h.φ_meas.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hZm2 := fun j => Ito.SecondMoment.measurable_uncurry_sq_diffusion hI j
  have hUm2 := Ito.SecondMoment.measurable_uncurry_lintegral_sq_jump hI
  have hsub : Set.Ioc t T ⊆ Set.Icc (0 : ℝ) T := fun s hs => ⟨ht0.trans hs.1.le, hs.2⟩
  have hZf : ∀ j : Fin d,
      ∫⁻ ω, ∫⁻ s in Set.Ioc t T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun j =>
    lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono_set hsub) (h.Z_sq j).lt_top
  have hUf : ∫⁻ ω, ∫⁻ s in Set.Ioc t T, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono_set hsub) h.U_sq.lt_top
  -- the rates, integrable on `[0, T]`
  have hC : IntegrableOn (fun s => ∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      (Set.Icc (0 : ℝ) T) :=
    integrable_finsetSum _ fun j _ =>
      Ito.SecondMoment.integrableOn_toReal_lintegral (hZm2 j) (h.Z_sq j).lt_top
  have hG : IntegrableOn (fun s => (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)
      (Set.Icc (0 : ℝ) T) :=
    Ito.SecondMoment.integrableOn_toReal_lintegral hUm2 h.U_sq.lt_top
  have hF : IntegrableOn (fun s => (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      (Set.Icc (0 : ℝ) T) :=
    Ito.SecondMoment.integrableOn_toReal_lintegral hφm2 h.φ_sq.lt_top
  have hR := h.integrableOn_exp_mul_rate 𝒲 1 hT
  -- the identities at `T` and at `t`, and their difference
  have kT := h.exp_mul_integral_mul_self_eq 𝒲 1 hT
  have kt := h.exp_mul_integral_mul_self_eq_at 𝒲 1 hT ht0 htT
  have hsplit : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (1 * s)
        * (1 * ∫ ω, Y s ω * Y s ω ∂P + 2 * ∫ ω, Y s ω * -φ ω s ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)
      = (∫ s in Set.Icc (0 : ℝ) t, Real.exp (1 * s)
        * (1 * ∫ ω, Y s ω * Y s ω ∂P + 2 * ∫ ω, Y s ω * -φ ω s ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal))
        + ∫ s in Set.Ioc t T, Real.exp (1 * s)
        * (1 * ∫ ω, Y s ω * Y s ω ∂P + 2 * ∫ ω, Y s ω * -φ ω s ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) := by
    rw [← Set.Icc_union_Ioc_eq_Icc ht0 htT]
    refine setIntegral_union (Set.disjoint_left.mpr fun x hx hx' => not_lt.mpr hx.2 hx'.1)
      measurableSet_Ioc (hR.mono_set (Set.Icc_subset_Icc le_rfl htT)) (hR.mono_set hsub)
  -- the rate dominates the energy rates, less `e^T` times the drift rate, on `(t, T]`
  have hmono : ∫ s in Set.Ioc t T,
      ((∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
        + (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal
        - Real.exp T * (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      ≤ ∫ s in Set.Ioc t T, Real.exp (1 * s)
        * (1 * ∫ ω, Y s ω * Y s ω ∂P + 2 * ∫ ω, Y s ω * -φ ω s ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) := by
    refine integral_mono_ae (((hC.add hG).sub (hF.const_mul _)).mono_set hsub)
      (hR.mono_set hsub) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae_restrict_of_subset hsub
      (Ito.SecondMoment.ae_memLp_two_eval (P := P) h.φ_meas h.φ_sq.lt_top)] with s hs hφs
    have hsI : s ∈ Set.Icc (0 : ℝ) T := hsub hs
    have hyoung := neg_integral_mul_self_le (hYs s hsI) hφs
    rw [Ito.SecondMoment.integral_mul_self_eq_toReal hφs] at hyoung
    have hC0 : 0 ≤ ∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal :=
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    have hG0 : 0 ≤ (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal := ENNReal.toReal_nonneg
    have hF0 : 0 ≤ (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal := ENNReal.toReal_nonneg
    have he1 : 1 ≤ Real.exp (1 * s) := Real.one_le_exp (by linarith [hsI.1])
    have heT : Real.exp (1 * s) ≤ Real.exp T := Real.exp_le_exp.mpr (by linarith [hsI.2])
    generalize (∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal) = c at hC0 ⊢
    generalize (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal = g at hG0 ⊢
    generalize (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal = f at hF0 hyoung ⊢
    generalize ∫ ω, Y s ω * Y s ω ∂P = a at hyoung ⊢
    generalize ∫ ω, Y s ω * -φ ω s ∂P = b at hyoung ⊢
    generalize Real.exp (1 * s) = es at he1 heT ⊢
    have k1 : 0 ≤ (es - 1) * (c + g) := mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ (Real.exp T - es) * f := mul_nonneg (by linarith) hF0
    have k3 : 0 ≤ es * (1 * a + 2 * b + f) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  -- the energy integrals over `(t, T]`
  have hCint : ∫ s in Set.Ioc t T, ∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
      = ∑ j : Fin d,
        (∫⁻ ω, ∫⁻ s in Set.Ioc t T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
    rw [integral_finsetSum _ fun j _ =>
      (Ito.SecondMoment.integrableOn_toReal_lintegral (hZm2 j) (h.Z_sq j).lt_top).mono_set hsub]
    exact Finset.sum_congr rfl fun j _ =>
      (toReal_lintegral_setLIntegral_eq (hZm2 j) (hZf j)).symm
  have hGint : ∫ s in Set.Ioc t T, (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal
      = (∫⁻ ω, ∫⁻ s in Set.Ioc t T, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal :=
    (toReal_lintegral_setLIntegral_eq hUm2 hUf).symm
  have hFint : ∫ s in Set.Ioc t T, (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
      ≤ (Brownian.Ito.energy P T φ).toReal := by
    rw [Brownian.Ito.energy, Ito.SecondMoment.toReal_lintegral_lintegral_eq hφm2 h.φ_sq.lt_top]
    exact setIntegral_mono_set hF (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      (Eventually.of_forall hsub)
  have hlower : ∫ s in Set.Ioc t T,
      ((∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
        + (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal
        - Real.exp T * (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      = (∑ j : Fin d,
          (∫⁻ ω, ∫⁻ s in Set.Ioc t T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
        + (∫⁻ ω, ∫⁻ s in Set.Ioc t T, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal
        - Real.exp T * ∫ s in Set.Ioc t T, (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal := by
    have hCG : IntegrableOn (fun s =>
        (∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) (Set.Ioc t T) :=
      (hC.add hG).mono_set hsub
    have hFc : IntegrableOn (fun s => Real.exp T * (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
        (Set.Ioc t T) :=
      IntegrableOn.mono_set (hF.const_mul (Real.exp T)) hsub
    rw [integral_sub hCG hFc,
      integral_add (hC.mono_set hsub) (hG.mono_set hsub), integral_const_mul, hCint, hGint]
  -- the real inequality
  have hYT : MemLp (Y T) 2 P := hYs T ⟨hT.le, le_rfl⟩
  have hYt : MemLp (Y t) 2 P := hYs t ⟨ht0, htT⟩
  rw [Ito.SecondMoment.integral_mul_self_eq_toReal hYT, one_mul] at kT
  rw [Ito.SecondMoment.integral_mul_self_eq_toReal hYt, one_mul] at kt
  rw [hlower] at hmono
  have hreal : (∫⁻ ω, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
      + ((∑ j : Fin d,
          (∫⁻ ω, ∫⁻ s in Set.Ioc t T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
        + (∫⁻ ω, ∫⁻ s in Set.Ioc t T, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal)
      ≤ Real.exp T * ((∫⁻ ω, (‖Y T ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
        + (Brownian.Ito.energy P T φ).toReal) := by
    rw [hsplit] at kT
    have hA0 : 0 ≤ (∫⁻ ω, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal := ENNReal.toReal_nonneg
    have het : 1 ≤ Real.exp t := Real.one_le_exp ht0
    have hA : (∫⁻ ω, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
        ≤ Real.exp t * (∫⁻ ω, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal := le_mul_of_one_le_left hA0 het
    have hFe := mul_le_mul_of_nonneg_left hFint (Real.exp_pos T).le
    linarith
  -- back to `ℝ≥0∞`
  have hξT : ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ∫⁻ ω, (‖Y T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [h.ae_eq_terminal hT.le] with ω hω
    rw [hω]
  rw [hξT]
  have hYtf : ∫⁻ ω, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≠ ⊤ :=
    (Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two hYt).ne
  have hYTf : ∫⁻ ω, (‖Y T ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≠ ⊤ :=
    (Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two hYT).ne
  have hZf' : ∀ j ∈ Finset.univ,
      ∫⁻ ω, ∫⁻ s in Set.Ioc t T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ :=
    fun j _ => (hZf j).ne
  have hS : (∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Ioc t T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      + ∫⁻ ω, ∫⁻ s in Set.Ioc t T, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr hZf', hUf.ne⟩
  have hRf : ENNReal.ofReal (Real.exp T)
      * (∫⁻ ω, (‖Y T ω‖₊ : ℝ≥0∞) ^ 2 ∂P + Brownian.Ito.energy P T φ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr ⟨hYTf, h.φ_sq⟩)
  rw [← ENNReal.toReal_le_toReal (ENNReal.add_ne_top.mpr ⟨hYtf, hS⟩) hRf, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos T).le, ENNReal.toReal_add hYTf h.φ_sq,
    ENNReal.toReal_add hYtf hS,
    ENNReal.toReal_add (ENNReal.sum_ne_top.mpr hZf') hUf.ne, ENNReal.toReal_sum hZf']
  exact hreal

/-- **The bound at every time**: for a solution of the linear backward equation over a filtration
with a cross witness and every `t ∈ [0, T]`,
`𝔼[Y_t²] + 𝔼 ∫_t^T (|Z_s|² + ∫_E U_s(e)² ν(de)) ds ≤ e^T (𝔼[ξ²] + 𝔼 ∫_0^T φ_s² ds)`. -/
theorem lintegral_sq_at_add_energy_le (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        + ∫⁻ ω, ∫⁻ s in Set.Icc t T, (Stability.esq (Z s ω)
          + ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp T)
        * (∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P + Brownian.Ito.energy P T φ) := by
  classical
  have hI := h.isItoLevyProcess_clampT hT
  have hZm2 := fun j => Ito.SecondMoment.measurable_uncurry_sq_diffusion hI j
  have hUm2 := Ito.SecondMoment.measurable_uncurry_lintegral_sq_jump hI
  have hUm2' : Measurable fun p : Ω × ℝ => ∫⁻ e, (‖U p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν := hUm2
  have hZm2' : ∀ j, Measurable fun p : Ω × ℝ => (‖Z p.2 p.1 j‖₊ : ℝ≥0∞) ^ 2 := hZm2
  have hres : volume.restrict (Set.Icc t T) = volume.restrict (Set.Ioc t T) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  refine le_trans (le_of_eq ?_) (h.lintegral_sq_at_add_energy_le_Ioc 𝒲 hT ht)
  congr 1
  simp only [Stability.esq]
  rw [hres]
  rw [lintegral_setLIntegral_eq_prod (F := fun p : Ω × ℝ => ∑ j : Fin d,
      (‖Z p.2 p.1 j‖₊ : ℝ≥0∞) ^ 2 + ∫⁻ e, (‖U p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      ((Finset.measurable_sum _ fun j _ => hZm2' j).add hUm2'),
    lintegral_add_right (fun p : Ω × ℝ => ∑ j : Fin d, (‖Z p.2 p.1 j‖₊ : ℝ≥0∞) ^ 2) hUm2',
    lintegral_finsetSum _ fun j _ => hZm2' j,
    lintegral_setLIntegral_eq_prod (F := fun p : Ω × ℝ => ∫⁻ e, (‖U p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      hUm2']
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (lintegral_setLIntegral_eq_prod (F := fun p : Ω × ℝ => (‖Z p.2 p.1 j‖₊ : ℝ≥0∞) ^ 2)
    (hZm2' j) _).symm

end LinearBSDEJ

/-- **The bound at every time in `ℝᵐ`, for a jointly measurable drift** (the proof of Lemma 4.1),
under the hypotheses of `brownianPoisson_estimate_vec_of_measurable`: for every `t ∈ [0, T]`,
`𝔼|Y_t|² + 𝔼 ∫_t^T (|Z_s|²_F + ‖U_s‖²_{L²(ν)}) ds ≤ e^T (𝔼|ξ|² + 𝔼 ∫_0^T |φ_s|² ds)`. -/
theorem brownianPoisson_energy_at_vec_of_measurable [ℱ.IsRightContinuous]
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    {m : ℕ} {ξ : Fin m → Ω → ℝ} {φ : Fin m → Ω → ℝ → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
    {Z : Fin m → ℝ → Ω → (Fin d → ℝ)} {U : Fin m → ℝ → Ω → E → ℝ}
    (hZm : ∀ k (i : Fin d), Measurable (Function.uncurry fun ω s => Z k s ω i))
    (hZp : ∀ k (i : Fin d), Probability.ProgressivelyMeasurable ℱ fun ω s => Z k s ω i)
    (hZv : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) T → Z k s ω = 0)
    (hZs : ∀ k (i : Fin d), Brownian.Ito.energy P T (fun ω s => Z k s ω i) ≠ ⊤)
    (hUm : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2)
    (hUp : ∀ k, Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U k s ω e)
    (hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → U k s ω e = 0)
    (hUs : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) ≠ ⊤)
    (hφm : ∀ k, Measurable (Function.uncurry (φ k)))
    (hφs : ∀ k, Brownian.Ito.energy P T (φ k) ≠ ⊤) (hξ : ∀ k, MemLp (ξ k) 2 P)
    (hYa : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (Y k t))
    (hYr : ∀ k ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => Y k s ω) (𝓝[>] t) (𝓝 (Y k t ω)))
    (heq : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      Y k t ω = ξ k ω + (∫ s in Set.Icc t T, φ k ω s)
        - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW (Z k) (hZm k)
              (hZp k) (sq_int_global_of_vanishing (hZv k) (hZs k)) T ω
            - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW (Z k)
              (hZm k) (hZp k) (sq_int_global_of_vanishing (hZv k) (hZs k)) t ω)
        - (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U k s ω' e) (hUm k)
              (hUp k) (marked_sq_int_global_of_vanishing (hUv k) (hUs k)) T ω
            - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U k s ω' e)
              (hUm k) (hUp k) (marked_sq_int_global_of_vanishing (hUv k) (hUs k)) t ω))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, Stability.esq (fun k => Y k t ω) ∂P
        + ∫⁻ ω, ∫⁻ s in Set.Icc t T, (∑ k, Stability.esq (Z k s ω)
          + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp T)
        * (∫⁻ ω, Stability.esq (fun k => ξ k ω) ∂P + ∑ k, Brownian.Ito.energy P T (φ k)) := by
  classical
  have key : ∀ k, ∫⁻ ω, (‖Y k t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      + ∫⁻ ω, ∫⁻ s in Set.Icc t T, (Stability.esq (Z k s ω)
        + ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp T)
        * (∫⁻ ω, (‖ξ k ω‖₊ : ℝ≥0∞) ^ 2 ∂P + Brownian.Ito.energy P T (φ k)) := by
    intro k
    obtain ⟨ψ, Y', hlin, hE, -, hY'⟩ := exists_linearBSDEJ_of_measurable hℱ0 hnull hT (hZm k)
      (hZp k) (hZv k) (hZs k) (hUm k) (hUp k) (hUv k) (hUs k) (hφm k) (hφs k) (hξ k) (hYa k)
      (hYr k) (heq k)
    have h := hlin.lintegral_sq_at_add_energy_le 𝒲 hT ht
    rwa [hY' t ht, hE] at h
  -- measurability of the integrands
  have hYm : ∀ k, Measurable (Y k t) := fun k => (hYa k t ht).mono (ℱ.le t) le_rfl
  have hZm2 : ∀ k, Measurable fun p : Ω × ℝ => Stability.esq (Z k p.2 p.1) := fun k =>
    Finset.measurable_sum _ fun j _ => ((hZm k j).nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hUm2 : ∀ k, Measurable fun p : Ω × ℝ => ∫⁻ e, (‖U k p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
    fun k => Measurable.lintegral_prod_right' (f := fun q : (Ω × ℝ) × E =>
      (‖U k q.1.2 q.1.1 q.2‖₊ : ℝ≥0∞) ^ 2)
      (((hUm k).comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk
        measurable_snd))).nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hY : ∫⁻ ω, Stability.esq (fun k => Y k t ω) ∂P
      = ∑ k, ∫⁻ ω, (‖Y k t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    simp only [Stability.esq]
    exact lintegral_finsetSum _ fun k _ => (hYm k).nnnorm.coe_nnreal_ennreal.pow_const 2
  have hξs : ∫⁻ ω, Stability.esq (fun k => ξ k ω) ∂P
      = ∑ k, ∫⁻ ω, (‖ξ k ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    simp only [Stability.esq]
    exact lintegral_finsetSum' _ fun k _ =>
      (hξ k).aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hZU : ∫⁻ ω, ∫⁻ s in Set.Icc t T, (∑ k, Stability.esq (Z k s ω)
        + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P
      = ∑ k, ∫⁻ ω, ∫⁻ s in Set.Icc t T, (Stability.esq (Z k s ω)
        + ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P := by
    rw [lintegral_setLIntegral_eq_prod (F := fun p : Ω × ℝ => ∑ k, Stability.esq (Z k p.2 p.1)
      + ∑ k, ∫⁻ e, (‖U k p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      ((Finset.measurable_sum _ fun k _ => hZm2 k).add (Finset.measurable_sum _ fun k _ => hUm2 k))]
    simp only [← Finset.sum_add_distrib]
    have hZU2 : ∀ k, Measurable fun p : Ω × ℝ => Stability.esq (Z k p.2 p.1)
        + ∫⁻ e, (‖U k p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν := fun k => (hZm2 k).add (hUm2 k)
    rw [lintegral_finsetSum _ fun k _ => hZU2 k]
    exact Finset.sum_congr rfl fun k _ =>
      (lintegral_setLIntegral_eq_prod (F := fun p : Ω × ℝ => Stability.esq (Z k p.2 p.1)
        + ∫⁻ e, (‖U k p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ((hZm2 k).add (hUm2 k)) _).symm
  rw [hY, hZU, hξs, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => key k

/-- The energies of `Z` and `U` on `[0, T]`, summed over the coordinates, as one double integral. -/
theorem lintegral_setLIntegral_energy_eq {m : ℕ} {Z : Fin m → ℝ → Ω → (Fin d → ℝ)}
    {U : Fin m → ℝ → Ω → E → ℝ}
    (hZm : ∀ k (i : Fin d), Measurable (Function.uncurry fun ω s => Z k s ω i))
    (hUm : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (∑ k, Stability.esq (Z k s ω)
        + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P
      = (∑ k, ∑ j : Fin d, Brownian.Ito.energy P T (fun ω s => Z k s ω j))
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) := by
  have hZm2 : ∀ k (j : Fin d), Measurable fun p : Ω × ℝ => (‖Z k p.2 p.1 j‖₊ : ℝ≥0∞) ^ 2 :=
    fun k j => (hZm k j).nnnorm.coe_nnreal_ennreal.pow_const 2
  have hUm2 : ∀ k, Measurable fun p : Ω × ℝ => ∫⁻ e, (‖U k p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
    fun k => Measurable.lintegral_prod_right' (f := fun q : (Ω × ℝ) × E =>
      (‖U k q.1.2 q.1.1 q.2‖₊ : ℝ≥0∞) ^ 2)
      (((hUm k).comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk
        measurable_snd))).nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hZs : ∀ k, Measurable fun p : Ω × ℝ => ∑ j : Fin d, (‖Z k p.2 p.1 j‖₊ : ℝ≥0∞) ^ 2 :=
    fun k => Finset.measurable_sum _ fun j _ => hZm2 k j
  simp only [Stability.esq]
  rw [lintegral_setLIntegral_eq_prod (F := fun p : Ω × ℝ =>
      ∑ k, ∑ j : Fin d, (‖Z k p.2 p.1 j‖₊ : ℝ≥0∞) ^ 2
        + ∑ k, ∫⁻ e, (‖U k p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      ((Finset.measurable_sum _ fun k _ => hZs k).add (Finset.measurable_sum _ fun k _ => hUm2 k)),
    lintegral_add_right (fun p : Ω × ℝ => ∑ k, ∑ j : Fin d, (‖Z k p.2 p.1 j‖₊ : ℝ≥0∞) ^ 2)
      (Finset.measurable_sum _ fun k _ => hUm2 k),
    lintegral_finsetSum _ fun k _ => hZs k, lintegral_finsetSum _ fun k _ => hUm2 k]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [lintegral_finsetSum _ fun j _ => hZm2 k j]
    exact Finset.sum_congr rfl fun j _ =>
      (lintegral_setLIntegral_eq_prod (F := fun p : Ω × ℝ => (‖Z k p.2 p.1 j‖₊ : ℝ≥0∞) ^ 2)
        (hZm2 k j) _).symm
  · exact Finset.sum_congr rfl fun k _ =>
      (lintegral_setLIntegral_eq_prod (F := fun p : Ω × ℝ =>
        ∫⁻ e, (‖U k p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν) (hUm2 k) _).symm

/-- **The bound (4.6) in `ℝᵐ`, for a jointly measurable drift** (the proof of Lemma 4.1), under
the hypotheses of `brownianPoisson_estimate_vec_of_measurable`:
`sup_{t ≤ T} 𝔼|Y_t|² + 𝔼 ∫_0^T (|Z_s|²_F + ‖U_s‖²_{L²(ν)}) ds
  ≤ 2 e^T (𝔼|ξ|² + 𝔼 ∫_0^T |φ_s|² ds)`. -/
theorem brownianPoisson_supE_vec_of_measurable [ℱ.IsRightContinuous]
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    {m : ℕ} {ξ : Fin m → Ω → ℝ} {φ : Fin m → Ω → ℝ → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
    {Z : Fin m → ℝ → Ω → (Fin d → ℝ)} {U : Fin m → ℝ → Ω → E → ℝ}
    (hZm : ∀ k (i : Fin d), Measurable (Function.uncurry fun ω s => Z k s ω i))
    (hZp : ∀ k (i : Fin d), Probability.ProgressivelyMeasurable ℱ fun ω s => Z k s ω i)
    (hZv : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) T → Z k s ω = 0)
    (hZs : ∀ k (i : Fin d), Brownian.Ito.energy P T (fun ω s => Z k s ω i) ≠ ⊤)
    (hUm : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2)
    (hUp : ∀ k, Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U k s ω e)
    (hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → U k s ω e = 0)
    (hUs : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) ≠ ⊤)
    (hφm : ∀ k, Measurable (Function.uncurry (φ k)))
    (hφs : ∀ k, Brownian.Ito.energy P T (φ k) ≠ ⊤) (hξ : ∀ k, MemLp (ξ k) 2 P)
    (hYa : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (Y k t))
    (hYr : ∀ k ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => Y k s ω) (𝓝[>] t) (𝓝 (Y k t ω)))
    (heq : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      Y k t ω = ξ k ω + (∫ s in Set.Icc t T, φ k ω s)
        - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW (Z k) (hZm k)
              (hZp k) (sq_int_global_of_vanishing (hZv k) (hZs k)) T ω
            - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW (Z k)
              (hZm k) (hZp k) (sq_int_global_of_vanishing (hZv k) (hZs k)) t ω)
        - (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U k s ω' e) (hUm k)
              (hUp k) (marked_sq_int_global_of_vanishing (hUv k) (hUs k)) T ω
            - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U k s ω' e)
              (hUm k) (hUp k) (marked_sq_int_global_of_vanishing (hUv k) (hUs k)) t ω)) :
    (⨆ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, Stability.esq (fun k => Y k t ω) ∂P)
        + ((∑ k, ∑ j : Fin d, Brownian.Ito.energy P T (fun ω s => Z k s ω j))
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e))
      ≤ ENNReal.ofReal (2 * Real.exp T)
        * (∫⁻ ω, Stability.esq (fun k => ξ k ω) ∂P + ∑ k, Brownian.Ito.energy P T (φ k)) := by
  have key := fun t (ht : t ∈ Set.Icc (0 : ℝ) T) =>
    brownianPoisson_energy_at_vec_of_measurable 𝒲 hℱ0 hnull hT hZm hZp hZv hZs hUm hUp hUv hUs
      hφm hφs hξ hYa hYr heq ht
  have h1 : (⨆ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, Stability.esq (fun k => Y k t ω) ∂P)
      ≤ ENNReal.ofReal (Real.exp T)
        * (∫⁻ ω, Stability.esq (fun k => ξ k ω) ∂P + ∑ k, Brownian.Ito.energy P T (φ k)) :=
    iSup₂_le fun t ht => le_self_add.trans (key t ht)
  have h2 := le_add_self.trans (key 0 ⟨le_rfl, hT.le⟩)
  rw [lintegral_setLIntegral_energy_eq hZm hUm] at h2
  calc _ ≤ ENNReal.ofReal (Real.exp T)
          * (∫⁻ ω, Stability.esq (fun k => ξ k ω) ∂P + ∑ k, Brownian.Ito.energy P T (φ k))
        + ENNReal.ofReal (Real.exp T)
          * (∫⁻ ω, Stability.esq (fun k => ξ k ω) ∂P + ∑ k, Brownian.Ito.energy P T (φ k)) :=
        add_le_add h1 h2
    _ = _ := by
        rw [← two_mul, ← mul_assoc, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

end MVFBSDEJ.WellPosedness.BrownianPoisson
