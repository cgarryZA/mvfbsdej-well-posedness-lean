/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.EnergyAt

/-!
# The weighted energy inequality of a linear backward equation at every time

For a solution `(Y, Z, U)` of the linear backward equation with drift `φ` over a filtration
carrying the driver with a cross witness, the weighted second-moment identities at weight `e^s`
at the horizons `t` and `T` differ by the integral of their rate over `(t, T]`, and Young's
inequality `𝔼[Y_s²] − 2 𝔼[Y_s φ_s] ≥ −𝔼[φ_s²]` cancels the `𝔼[Y_s²]` term: for every
`t ∈ [0, T]`,

`𝔼 e^t Y_t² + 𝔼 ∫_t^T e^s (|Z_s|² + ∫_E U_s(e)² ν(de)) ds ≤ 𝔼 e^T ξ² + 𝔼 ∫_t^T e^s φ_s² ds`,

the weighted inequality in the proof of Lemma 4.1 of the well-posedness paper, from which the
bound at every time follows by `1 ≤ e^s ≤ e^T`.

## Main statements

* `setLIntegral_exp_mul_le` — a weighted window energy over `(t, T]` is at most `e^T` times the
  energy over `[0, T]`.
* `LinearBSDEJ.exp_lintegral_sq_at_add_energy_le_Ioc` — the weighted inequality, over `(t, T]`.
* `LinearBSDEJ.exp_lintegral_sq_at_add_energy_le` — the same over `[t, T]`.
* `brownianPoisson_weighted_at_vec_of_measurable` — the same in `ℝᵐ`, for a jointly measurable
  drift and a solution given on `[0, T]` only.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.BrownianPoisson

open LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

section Window

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- A window energy weighted by `e^s` over `(t, T]`, `0 ≤ t`, is at most `e^T` times the energy
over `[0, T]`. -/
theorem setLIntegral_exp_mul_le {g : Ω → ℝ → ℝ≥0∞} {t T : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, ∫⁻ s in Set.Ioc t T, ENNReal.ofReal (Real.exp s) * g ω s ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp T) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, g ω s ∂volume ∂P := by
  have hsub : Set.Ioc t T ⊆ Set.Icc (0 : ℝ) T := fun s hs => ⟨ht.trans hs.1.le, hs.2⟩
  calc ∫⁻ ω, ∫⁻ s in Set.Ioc t T, ENNReal.ofReal (Real.exp s) * g ω s ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Ioc t T, ENNReal.ofReal (Real.exp T) * g ω s ∂volume ∂P :=
        lintegral_mono fun ω => setLIntegral_mono' measurableSet_Ioc fun s hs =>
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hs.2)) _
    _ = ENNReal.ofReal (Real.exp T) * ∫⁻ ω, ∫⁻ s in Set.Ioc t T, g ω s ∂volume ∂P := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun ω => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp T) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, g ω s ∂volume ∂P := by
        gcongr

/-- A finite window energy weighted by `e^s` is the time integral of the weighted sample
energies. -/
theorem toReal_lintegral_setLIntegral_exp_mul_eq [SFinite P] {F : Ω → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) {S : Set ℝ} (hS : MeasurableSet S)
    (hfin : ∫⁻ ω, ∫⁻ s in S, ENNReal.ofReal (Real.exp s) * F ω s ∂volume ∂P < ⊤) :
    (∫⁻ ω, ∫⁻ s in S, ENNReal.ofReal (Real.exp s) * F ω s ∂volume ∂P).toReal
      = ∫ s in S, Real.exp s * (∫⁻ ω, F ω s ∂P).toReal := by
  have hG : Measurable (Function.uncurry fun ω s => ENNReal.ofReal (Real.exp s) * F ω s) :=
    (Real.measurable_exp.ennreal_ofReal.comp measurable_snd).mul hF
  rw [toReal_lintegral_setLIntegral_eq hG hfin]
  refine setIntegral_congr_fun hS fun s _ => ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos s).le]

/-- A double lower integral over the sample point and a set of times of a finite sum of jointly
measurable integrands is the sum of the double lower integrals. -/
theorem lintegral_setLIntegral_finsetSum [SFinite P] {ι : Type*} [Fintype ι]
    {F : ι → Ω × ℝ → ℝ≥0∞} (hF : ∀ k, Measurable (F k)) (S : Set ℝ) :
    ∫⁻ ω, ∫⁻ s in S, ∑ k, F k (ω, s) ∂volume ∂P
      = ∑ k, ∫⁻ ω, ∫⁻ s in S, F k (ω, s) ∂volume ∂P := by
  rw [lintegral_setLIntegral_eq_prod (F := fun p => ∑ k, F k p)
    (Finset.measurable_sum _ fun k _ => hF k), lintegral_finsetSum _ fun k _ => hF k]
  exact Finset.sum_congr rfl fun k _ => (lintegral_setLIntegral_eq_prod (hF k) S).symm

/-- A double lower integral over the sample point and a set of times of a sum of two jointly
measurable integrands is the sum of the double lower integrals. -/
theorem lintegral_setLIntegral_add [SFinite P] {F G : Ω × ℝ → ℝ≥0∞} (hF : Measurable F)
    (hG : Measurable G) (S : Set ℝ) :
    ∫⁻ ω, ∫⁻ s in S, (F (ω, s) + G (ω, s)) ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in S, F (ω, s) ∂volume ∂P + ∫⁻ ω, ∫⁻ s in S, G (ω, s) ∂volume ∂P := by
  rw [lintegral_setLIntegral_eq_prod (F := fun p => F p + G p) (hF.add hG),
    lintegral_add_right _ hG, lintegral_setLIntegral_eq_prod hF S,
    lintegral_setLIntegral_eq_prod hG S]

end Window

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {T : ℝ} {ξ : Ω → ℝ} {φ : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
  {U : ℝ → Ω → E → ℝ}

namespace LinearBSDEJ

/-- **The weighted inequality at every time**, in the separated form over `(t, T]`: for a
solution of the linear backward equation over a filtration with a cross witness and every
`t ∈ [0, T]`,
`e^t 𝔼[Y_t²] + (∑_j 𝔼 ∫_{(t, T]} e^s Z_j(s)² ds + 𝔼 ∫_{(t, T]} e^s ∫_E U_s(e)² ν(de) ds)
  ≤ e^T 𝔼[ξ²] + 𝔼 ∫_{(t, T]} e^s φ_s² ds`. -/
theorem exp_lintegral_sq_at_add_energy_le_Ioc (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ENNReal.ofReal (Real.exp t) * ∫⁻ ω, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        + ((∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Ioc t T,
            ENNReal.ofReal (Real.exp s) * (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Ioc t T,
            ENNReal.ofReal (Real.exp s) * ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      ≤ ENNReal.ofReal (Real.exp T) * ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        + ∫⁻ ω, ∫⁻ s in Set.Ioc t T,
          ENNReal.ofReal (Real.exp s) * (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
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
  -- the weighted window energies are finite
  have hZf : ∀ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Ioc t T,
      ENNReal.ofReal (Real.exp s) * (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun j =>
    (setLIntegral_exp_mul_le ht0).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h.Z_sq j).lt_top)
  have hUf : ∫⁻ ω, ∫⁻ s in Set.Ioc t T,
      ENNReal.ofReal (Real.exp s) * ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    (setLIntegral_exp_mul_le ht0).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h.U_sq.lt_top)
  have hφf : ∫⁻ ω, ∫⁻ s in Set.Ioc t T,
      ENNReal.ofReal (Real.exp s) * (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    (setLIntegral_exp_mul_le ht0).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h.φ_sq.lt_top)
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
  have hexpI : ∀ {f : ℝ → ℝ}, IntegrableOn f (Set.Icc (0 : ℝ) T) →
      IntegrableOn (fun s => Real.exp s * f s) (Set.Ioc t T) := fun {f} hf =>
    (IntegrableOn.continuousOn_mul Real.continuous_exp.continuousOn
      (hf.mono_set (Set.Icc_subset_Icc ht0 le_rfl)) isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
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
  -- Young's inequality on `(t, T]`
  have hmono : ∫ s in Set.Ioc t T,
      (Real.exp s * ∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
        + Real.exp s * (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal
        - Real.exp s * (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      ≤ ∫ s in Set.Ioc t T, Real.exp (1 * s)
        * (1 * ∫ ω, Y s ω * Y s ω ∂P + 2 * ∫ ω, Y s ω * -φ ω s ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) := by
    refine integral_mono_ae (((hexpI hC).add (hexpI hG)).sub (hexpI hF))
      (hR.mono_set hsub) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae_restrict_of_subset hsub
      (Ito.SecondMoment.ae_memLp_two_eval (P := P) h.φ_meas h.φ_sq.lt_top)] with s hs hφs
    have hsI : s ∈ Set.Icc (0 : ℝ) T := hsub hs
    have hyoung := neg_integral_mul_self_le (hYs s hsI) hφs
    rw [Ito.SecondMoment.integral_mul_self_eq_toReal hφs] at hyoung
    rw [one_mul, one_mul, ← mul_add, ← mul_sub]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos s).le
  -- the weighted energies as time integrals
  have hZm2' : ∀ j : Fin d, Measurable (Function.uncurry fun ω s =>
      (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2) := hZm2
  have eZ : ∀ j : Fin d, (∫⁻ ω, ∫⁻ s in Set.Ioc t T,
        ENNReal.ofReal (Real.exp s) * (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal
      = ∫ s in Set.Ioc t T, Real.exp s * (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal := fun j =>
    toReal_lintegral_setLIntegral_exp_mul_eq (hZm2' j) measurableSet_Ioc (hZf j)
  have eU : (∫⁻ ω, ∫⁻ s in Set.Ioc t T,
        ENNReal.ofReal (Real.exp s) * ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal
      = ∫ s in Set.Ioc t T, Real.exp s
        * (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal :=
    toReal_lintegral_setLIntegral_exp_mul_eq hUm2 measurableSet_Ioc hUf
  have eφ : (∫⁻ ω, ∫⁻ s in Set.Ioc t T,
        ENNReal.ofReal (Real.exp s) * (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal
      = ∫ s in Set.Ioc t T, Real.exp s * (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal :=
    toReal_lintegral_setLIntegral_exp_mul_eq hφm2 measurableSet_Ioc hφf
  have hlower : ∫ s in Set.Ioc t T,
      (Real.exp s * ∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
        + Real.exp s * (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal
        - Real.exp s * (∫⁻ ω, (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      = (∑ j : Fin d, (∫⁻ ω, ∫⁻ s in Set.Ioc t T,
          ENNReal.ofReal (Real.exp s) * (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
        + (∫⁻ ω, ∫⁻ s in Set.Ioc t T,
          ENNReal.ofReal (Real.exp s) * ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal
        - (∫⁻ ω, ∫⁻ s in Set.Ioc t T,
          ENNReal.ofReal (Real.exp s) * (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
    have hZj : ∀ j : Fin d, IntegrableOn (fun s => Real.exp s
        * (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal) (Set.Ioc t T) := fun j =>
      hexpI (Ito.SecondMoment.integrableOn_toReal_lintegral (hZm2 j) (h.Z_sq j).lt_top)
    have hsum : (fun s => Real.exp s * ∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
        = fun s => ∑ j : Fin d, Real.exp s * (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal := by
      funext s
      rw [Finset.mul_sum]
    have hAB : IntegrableOn (fun s =>
        Real.exp s * ∑ j : Fin d, (∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
          + Real.exp s * (∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) (Set.Ioc t T) :=
      (hexpI hC).add (hexpI hG)
    rw [integral_sub hAB (hexpI hF), integral_add (hexpI hC) (hexpI hG), hsum,
      integral_finsetSum _ fun j _ => hZj j, eU, eφ]
    simp only [eZ]
  -- the real inequality
  have hYT : MemLp (Y T) 2 P := hYs T ⟨hT.le, le_rfl⟩
  have hYt : MemLp (Y t) 2 P := hYs t ⟨ht0, htT⟩
  rw [Ito.SecondMoment.integral_mul_self_eq_toReal hYT, one_mul] at kT
  rw [Ito.SecondMoment.integral_mul_self_eq_toReal hYt, one_mul] at kt
  rw [hlower] at hmono
  have hreal : Real.exp t * (∫⁻ ω, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
      + ((∑ j : Fin d, (∫⁻ ω, ∫⁻ s in Set.Ioc t T,
          ENNReal.ofReal (Real.exp s) * (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
        + (∫⁻ ω, ∫⁻ s in Set.Ioc t T,
          ENNReal.ofReal (Real.exp s) * ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal)
      ≤ Real.exp T * (∫⁻ ω, (‖Y T ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
        + (∫⁻ ω, ∫⁻ s in Set.Ioc t T,
          ENNReal.ofReal (Real.exp s) * (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
    rw [hsplit] at kT
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
  have hZf' : ∀ j ∈ Finset.univ, ∫⁻ ω, ∫⁻ s in Set.Ioc t T,
      ENNReal.ofReal (Real.exp s) * (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ :=
    fun j _ => (hZf j).ne
  have hS := ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr hZf', hUf.ne⟩
  have hL := ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := Real.exp t)) hYtf, hS⟩
  have hRf := ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := Real.exp T)) hYTf, hφf.ne⟩
  rw [← ENNReal.toReal_le_toReal hL hRf, ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYtf) hS,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hYTf) hφf.ne,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos t).le,
    ENNReal.toReal_ofReal (Real.exp_pos T).le,
    ENNReal.toReal_add (ENNReal.sum_ne_top.mpr hZf') hUf.ne, ENNReal.toReal_sum hZf']
  exact hreal

/-- **The weighted inequality at every time**: for a solution of the linear backward equation
over a filtration with a cross witness and every `t ∈ [0, T]`,
`e^t 𝔼[Y_t²] + 𝔼 ∫_t^T e^s (|Z_s|² + ∫_E U_s(e)² ν(de)) ds ≤ e^T 𝔼[ξ²] + 𝔼 ∫_t^T e^s φ_s² ds`. -/
theorem exp_lintegral_sq_at_add_energy_le (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ENNReal.ofReal (Real.exp t) * ∫⁻ ω, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        + ∫⁻ ω, ∫⁻ s in Set.Icc t T, ENNReal.ofReal (Real.exp s) * (Stability.esq (Z s ω)
          + ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp T) * ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        + ∫⁻ ω, ∫⁻ s in Set.Icc t T,
          ENNReal.ofReal (Real.exp s) * (‖φ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  classical
  have hI := h.isItoLevyProcess_clampT hT
  have hw : Measurable fun p : Ω × ℝ => ENNReal.ofReal (Real.exp p.2) :=
    Real.measurable_exp.ennreal_ofReal.comp measurable_snd
  have hZm2 : ∀ j, Measurable fun p : Ω × ℝ =>
      ENNReal.ofReal (Real.exp p.2) * (‖Z p.2 p.1 j‖₊ : ℝ≥0∞) ^ 2 := fun j =>
    hw.mul (Ito.SecondMoment.measurable_uncurry_sq_diffusion hI j)
  have hUm2 : Measurable fun p : Ω × ℝ =>
      ENNReal.ofReal (Real.exp p.2) * ∫⁻ e, (‖U p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
    hw.mul (Ito.SecondMoment.measurable_uncurry_lintegral_sq_jump hI)
  have hres : volume.restrict (Set.Icc t T) = volume.restrict (Set.Ioc t T) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  have e : ∫⁻ ω, ∫⁻ s in Set.Icc t T, ENNReal.ofReal (Real.exp s) * (Stability.esq (Z s ω)
        + ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P
      = (∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Ioc t T,
          ENNReal.ofReal (Real.exp s) * (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Ioc t T,
          ENNReal.ofReal (Real.exp s) * ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
    simp only [Stability.esq, mul_add, Finset.mul_sum]
    rw [hres, lintegral_setLIntegral_add (Finset.measurable_sum _ fun j _ => hZm2 j) hUm2,
      lintegral_setLIntegral_finsetSum hZm2]
  rw [e, hres]
  exact h.exp_lintegral_sq_at_add_energy_le_Ioc 𝒲 hT ht

end LinearBSDEJ

/-- **The weighted inequality at every time in `ℝᵐ`, for a jointly measurable drift** (the proof
of Lemma 4.1), under the hypotheses of `brownianPoisson_estimate_vec_of_measurable`: for every
`t ∈ [0, T]`,
`𝔼 e^t |Y_t|² + 𝔼 ∫_t^T e^s (|Z_s|²_F + ‖U_s‖²_{L²(ν)}) ds ≤ 𝔼 e^T |ξ|² + 𝔼 ∫_t^T e^s |φ_s|² ds`. -/
theorem brownianPoisson_weighted_at_vec_of_measurable [ℱ.IsRightContinuous]
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
    ENNReal.ofReal (Real.exp t) * ∫⁻ ω, Stability.esq (fun k => Y k t ω) ∂P
        + ∫⁻ ω, ∫⁻ s in Set.Icc t T, ENNReal.ofReal (Real.exp s) * (∑ k, Stability.esq (Z k s ω)
          + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp T) * ∫⁻ ω, Stability.esq (fun k => ξ k ω) ∂P
        + ∫⁻ ω, ∫⁻ s in Set.Icc t T,
          ENNReal.ofReal (Real.exp s) * Stability.esq (fun k => φ k ω s) ∂volume ∂P := by
  classical
  have hsub : Set.Icc t T ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc ht.1 le_rfl
  have key : ∀ k, ENNReal.ofReal (Real.exp t) * ∫⁻ ω, (‖Y k t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      + ∫⁻ ω, ∫⁻ s in Set.Icc t T, ENNReal.ofReal (Real.exp s) * (Stability.esq (Z k s ω)
        + ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp T) * ∫⁻ ω, (‖ξ k ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        + ∫⁻ ω, ∫⁻ s in Set.Icc t T,
          ENNReal.ofReal (Real.exp s) * (‖φ k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    intro k
    obtain ⟨ψ, Y', hlin, -, hψ, hY'⟩ := exists_linearBSDEJ_of_measurable hℱ0 hnull hT (hZm k)
      (hZp k) (hZv k) (hZs k) (hUm k) (hUp k) (hUv k) (hUs k) (hφm k) (hφs k) (hξ k) (hYa k)
      (hYr k) (heq k)
    have h := hlin.exp_lintegral_sq_at_add_energy_le 𝒲 hT ht
    have hφψ : ∫⁻ ω, ∫⁻ s in Set.Icc t T,
          ENNReal.ofReal (Real.exp s) * (‖ψ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        = ∫⁻ ω, ∫⁻ s in Set.Icc t T,
          ENNReal.ofReal (Real.exp s) * (‖φ k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hψ] with ω hω
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hω] with s hs
      rw [hs]
    rwa [hY' t ht, hφψ] at h
  -- measurability of the integrands
  have hw : Measurable fun p : Ω × ℝ => ENNReal.ofReal (Real.exp p.2) :=
    Real.measurable_exp.ennreal_ofReal.comp measurable_snd
  have hYm : ∀ k, Measurable (Y k t) := fun k => (hYa k t ht).mono (ℱ.le t) le_rfl
  have hZm2 : ∀ k, Measurable fun p : Ω × ℝ => Stability.esq (Z k p.2 p.1) := fun k =>
    Finset.measurable_sum _ fun j _ => ((hZm k j).nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hUm2 : ∀ k, Measurable fun p : Ω × ℝ => ∫⁻ e, (‖U k p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
    fun k => Measurable.lintegral_prod_right' (f := fun q : (Ω × ℝ) × E =>
      (‖U k q.1.2 q.1.1 q.2‖₊ : ℝ≥0∞) ^ 2)
      (((hUm k).comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk
        measurable_snd))).nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hφm2 : ∀ k, Measurable fun p : Ω × ℝ => (‖φ k p.1 p.2‖₊ : ℝ≥0∞) ^ 2 := fun k =>
    (hφm k).nnnorm.coe_nnreal_ennreal.pow_const 2
  have hY : ∫⁻ ω, Stability.esq (fun k => Y k t ω) ∂P
      = ∑ k, ∫⁻ ω, (‖Y k t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    simp only [Stability.esq]
    exact lintegral_finsetSum _ fun k _ => (hYm k).nnnorm.coe_nnreal_ennreal.pow_const 2
  have hξs : ∫⁻ ω, Stability.esq (fun k => ξ k ω) ∂P
      = ∑ k, ∫⁻ ω, (‖ξ k ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    simp only [Stability.esq]
    exact lintegral_finsetSum' _ fun k _ =>
      (hξ k).aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hZU : ∫⁻ ω, ∫⁻ s in Set.Icc t T, ENNReal.ofReal (Real.exp s) * (∑ k, Stability.esq (Z k s ω)
        + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P
      = ∑ k, ∫⁻ ω, ∫⁻ s in Set.Icc t T, ENNReal.ofReal (Real.exp s) * (Stability.esq (Z k s ω)
        + ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P := by
    simp only [← Finset.sum_add_distrib, Finset.mul_sum]
    exact lintegral_setLIntegral_finsetSum (F := fun k p => ENNReal.ofReal (Real.exp p.2)
      * (Stability.esq (Z k p.2 p.1) + ∫⁻ e, (‖U k p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν))
      (fun k => hw.mul ((hZm2 k).add (hUm2 k))) _
  have hφe : ∫⁻ ω, ∫⁻ s in Set.Icc t T,
        ENNReal.ofReal (Real.exp s) * Stability.esq (fun k => φ k ω s) ∂volume ∂P
      = ∑ k, ∫⁻ ω, ∫⁻ s in Set.Icc t T,
        ENNReal.ofReal (Real.exp s) * (‖φ k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    simp only [Stability.esq, Finset.mul_sum]
    exact lintegral_setLIntegral_finsetSum (F := fun k p => ENNReal.ofReal (Real.exp p.2)
      * (‖φ k p.1 p.2‖₊ : ℝ≥0∞) ^ 2) (fun k => hw.mul (hφm2 k)) _
  rw [hY, hZU, hξs, hφe, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => key k

end Dissertation.WellPosedness.BrownianPoisson
