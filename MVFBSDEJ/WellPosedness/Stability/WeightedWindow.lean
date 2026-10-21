/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.MomentAt

/-!
# The weighted second-moment identity of the linear backward equation on a window

For a solution `(Y, Z, U)` of the linear backward equation with terminal value `ξ` and drift `φ`
over a filtration carrying the driver with a cross witness, every `β ∈ ℝ` and every
`t ∈ [0, T]`,

`e^{βt} 𝔼[Y_t²] + 𝔼 ∫_t^T e^{βs} (β Y_s² + |Z_s|² + ∫_E U_s(e)² ν(de)) ds
  = e^{βT} 𝔼[ξ²] + 2 𝔼 ∫_t^T e^{βs} Y_s φ_s ds`,

both integrands being integrable for `P ⊗ ds` on `Ω × [t, T]`. It is the difference of the
weighted identities at the horizons `t` and `T`, read on the window `Ω × [t, T]`; Itô's formula
for `e^{κt} |δY_t|²` in Step 4 of the proof of Lemma 4.3 of the well-posedness paper is its sum
over the coordinates.

## Main statements

* `integral_window_split` — an integral for `P ⊗ ds` on `[0, T]` splits at `t ∈ [0, T]`.
* `LinearBSDEJ.exp_mul_window_eq` — the weighted identity on `Ω × [t, T]`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc MVFBSDEJ.WellPosedness.BrownianPoisson

universe u v w

section Split

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]

/-- **An integral on the window `Ω × [0, T]` splits at `t ∈ [0, T]`.** A function integrable for
`P ⊗ ds` on `[0, T]` is integrable on `[0, t]` and on `[t, T]`, and its integral is the sum of
the two. -/
theorem integral_window_split {F : Ω × ℝ → ℝ} {T t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hF : Integrable F (P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))) :
    Integrable F (P.prod (volume.restrict (Set.Icc (0 : ℝ) t)))
      ∧ Integrable F (P.prod (volume.restrict (Set.Icc t T)))
      ∧ ∫ q, F q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
        = ∫ q, F q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) t)))
          + ∫ q, F q ∂(P.prod (volume.restrict (Set.Icc t T))) := by
  have hres : volume.restrict (Set.Icc (0 : ℝ) T)
      = volume.restrict (Set.Icc (0 : ℝ) t) + volume.restrict (Set.Icc t T) := by
    rw [← Set.Icc_union_Ioc_eq_Icc ht.1 ht.2,
      Measure.restrict_union (Set.disjoint_left.mpr fun x hx hx' => not_lt.mpr hx.2 hx'.1)
        measurableSet_Ioc, Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume))]
  rw [hres, Measure.prod_add] at hF ⊢
  exact ⟨hF.left_of_add_measure, hF.right_of_add_measure,
    integral_add_measure hF.left_of_add_measure hF.right_of_add_measure⟩

end Split

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}
  {ξ : Ω → ℝ} {φ : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}

/-- **The weighted identity of a solution of the linear backward equation on `[0, τ]`**, for
`P ⊗ ds`: `e^{βτ} 𝔼[Y_τ²] = 𝔼[Y_0²]` plus the integral over `Ω × [0, τ]` of the integrable
function `β e^{βs} Y_s² + e^{βs} (2 Y_s (−φ_s) + |Z_s|² + ∫_E U_s(e)² ν(de))`. -/
theorem _root_.MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.exp_mul_prod_eq
    (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (β : ℝ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    Integrable (fun q : Ω × ℝ => β * Real.exp (β * q.2) * (Y q.2 q.1 * Y q.2 q.1)
        + Real.exp (β * q.2) * (Y q.2 q.1 * -φ q.1 q.2 + Y q.2 q.1 * -φ q.1 q.2
          + ∑ j, Z q.2 q.1 j * Z q.2 q.1 j + ∫ e, U q.2 q.1 e * U q.2 q.1 e ∂ν))
        (P.prod (volume.restrict (Set.Icc (0 : ℝ) τ)))
      ∧ Real.exp (β * τ) * ∫ ω, Y τ ω * Y τ ω ∂P = ∫ ω, Y 0 ω * Y 0 ω ∂P
        + ∫ q, (β * Real.exp (β * q.2) * (Y q.2 q.1 * Y q.2 q.1)
          + Real.exp (β * q.2) * (Y q.2 q.1 * -φ q.1 q.2 + Y q.2 q.1 * -φ q.1 q.2
            + ∑ j, Z q.2 q.1 j * Z q.2 q.1 j + ∫ e, U q.2 q.1 e * U q.2 q.1 e ∂ν))
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) τ))) := by
  have hf := h.linearFSDEJ (ξ₀ := Y 0) EventuallyEq.rfl hT.le
  have hsub : Set.Icc (0 : ℝ) τ ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl hτ.2
  have hwc : Continuous fun s : ℝ => Real.exp (β * s) := by fun_prop
  have hw'c : Continuous fun s : ℝ => β * Real.exp (β * s) := by fun_prop
  have hw : ∀ x ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s => Real.exp (β * s)) (β * Real.exp (β * x)) x := fun x _ => by
    have := ((hasDerivAt_id x).const_mul β).exp
    simpa only [mul_one, id, mul_comm] using this
  have key := mul_eq_add_setIntegral_of_hasDerivAt (LinearFSDEJ.integrableOn_rate hf hf 𝒲 hT)
    (fun s hs => LinearFSDEJ.integral_mul_eq_at hf hf 𝒲 hT hs) hwc.continuousOn hw
    hw'c.continuousOn hτ
  obtain ⟨hI1, hE1⟩ := LinearFSDEJ.setIntegral_weight_eq
    (LinearFSDEJ.integrable_mul_prod_at hf hf 𝒲 hT hτ.2) hw'c.continuousOn
  obtain ⟨hI2, hE2⟩ := LinearFSDEJ.setIntegral_weight_rate_eq hf hf 𝒲 hT hτ.2 hwc.continuousOn
  have hA : IntegrableOn (fun s => β * Real.exp (β * s) * ∫ ω, Y s ω * Y s ω ∂P)
      (Set.Icc (0 : ℝ) τ) :=
    IntegrableOn.continuousOn_mul hw'c.continuousOn
      (LinearFSDEJ.integrable_mul_prod_at hf hf 𝒲 hT hτ.2).integral_prod_right isCompact_Icc
  have hB : IntegrableOn (fun s => Real.exp (β * s)
      * (∫ ω, (Y s ω * -φ ω s + Y s ω * -φ ω s) ∂P
        + ∑ j, ∫ ω, Z s ω j * Z s ω j ∂P + ∫ ω, ∫ e, U s ω e * U s ω e ∂ν ∂P))
      (Set.Icc (0 : ℝ) τ) :=
    IntegrableOn.continuousOn_mul hwc.continuousOn
      ((LinearFSDEJ.integrableOn_rate hf hf 𝒲 hT).mono_set hsub) isCompact_Icc
  refine ⟨hI1.add hI2, ?_⟩
  rw [mul_zero, Real.exp_zero, one_mul] at key
  dsimp only at hE1 hE2
  rw [key, integral_add hA hB, hE1, hE2, integral_add hI1 hI2]

/-- **The weighted identity of a solution of the linear backward equation on `Ω × [t, T]`.** For
a solution over a filtration with a cross witness, `β ∈ ℝ` and `t ∈ [0, T]`, the integrands
`e^{βs} (β Y_s² + |Z_s|² + ∫_E U_s(e)² ν(de))` and `e^{βs} Y_s φ_s` are integrable for `P ⊗ ds`
on `[t, T]`, and
`e^{βt} 𝔼[Y_t²] + 𝔼 ∫_t^T e^{βs} (β Y_s² + |Z_s|² + ∫_E U_s(e)² ν(de)) ds
  = e^{βT} 𝔼[ξ²] + 2 𝔼 ∫_t^T e^{βs} Y_s φ_s ds`. -/
theorem _root_.MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.exp_mul_window_eq
    (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (β : ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Integrable (fun q : Ω × ℝ => Real.exp (β * q.2) * (β * Y q.2 q.1 ^ 2
        + ∑ j, Z q.2 q.1 j ^ 2 + ∫ e, U q.2 q.1 e ^ 2 ∂ν))
        (P.prod (volume.restrict (Set.Icc t T)))
      ∧ Integrable (fun q : Ω × ℝ => Real.exp (β * q.2) * (Y q.2 q.1 * φ q.1 q.2))
        (P.prod (volume.restrict (Set.Icc t T)))
      ∧ Real.exp (β * t) * ∫ ω, Y t ω ^ 2 ∂P
          + ∫ q, Real.exp (β * q.2) * (β * Y q.2 q.1 ^ 2 + ∑ j, Z q.2 q.1 j ^ 2
            + ∫ e, U q.2 q.1 e ^ 2 ∂ν) ∂(P.prod (volume.restrict (Set.Icc t T)))
        = Real.exp (β * T) * ∫ ω, ξ ω ^ 2 ∂P
          + 2 * ∫ q, Real.exp (β * q.2) * (Y q.2 q.1 * φ q.1 q.2)
            ∂(P.prod (volume.restrict (Set.Icc t T))) := by
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  obtain ⟨hIT, hET⟩ := h.exp_mul_prod_eq 𝒲 hT β hTm
  obtain ⟨-, hEt⟩ := h.exp_mul_prod_eq 𝒲 hT β ht
  obtain ⟨-, hIw, hsplit⟩ := integral_window_split ht hIT
  -- the product `Y φ` and its weight on `[t, T]`
  have hYm : Measurable (Function.uncurry fun ω s => Y s ω) :=
    h.measurable_uncurry.comp measurable_swap
  have hYφ : Integrable (fun q : Ω × ℝ => Y q.2 q.1 * φ q.1 q.2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    integrable_mul_prod (f := fun ω s => Y s ω) hYm h.φ_meas (h.energy_lt_top 𝒲 hT)
      h.φ_sq.lt_top
  have hYφw : Integrable (fun q : Ω × ℝ => Real.exp (β * q.2) * (Y q.2 q.1 * φ q.1 q.2))
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    (LinearFSDEJ.setIntegral_weight_eq hYφ (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).continuousOn).1
  obtain ⟨-, hH, -⟩ := integral_window_split ht hYφw
  -- the integrand of the identity is the energy integrand less twice the pairing
  have hFG : (fun q : Ω × ℝ => β * Real.exp (β * q.2) * (Y q.2 q.1 * Y q.2 q.1)
        + Real.exp (β * q.2) * (Y q.2 q.1 * -φ q.1 q.2 + Y q.2 q.1 * -φ q.1 q.2
          + ∑ j, Z q.2 q.1 j * Z q.2 q.1 j + ∫ e, U q.2 q.1 e * U q.2 q.1 e ∂ν))
      = fun q : Ω × ℝ => Real.exp (β * q.2) * (β * Y q.2 q.1 ^ 2
          + ∑ j, Z q.2 q.1 j ^ 2 + ∫ e, U q.2 q.1 e ^ 2 ∂ν)
        - 2 * (Real.exp (β * q.2) * (Y q.2 q.1 * φ q.1 q.2)) := by
    funext q
    simp only [sq]
    ring
  rw [hFG] at hIw hsplit hET hEt
  have hG : Integrable (fun q : Ω × ℝ => Real.exp (β * q.2) * (β * Y q.2 q.1 ^ 2
      + ∑ j, Z q.2 q.1 j ^ 2 + ∫ e, U q.2 q.1 e ^ 2 ∂ν))
      (P.prod (volume.restrict (Set.Icc t T))) := by
    have := hIw.add (hH.const_mul 2)
    refine this.congr (Eventually.of_forall fun q => ?_)
    simp only [Pi.add_apply]
    ring
  refine ⟨hG, hH, ?_⟩
  have hξ : ∫ ω, Y T ω * Y T ω ∂P = ∫ ω, ξ ω ^ 2 ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [h.ae_eq_terminal hT.le] with ω hω
    rw [hω, sq]
  have hYt : ∫ ω, Y t ω * Y t ω ∂P = ∫ ω, Y t ω ^ 2 ∂P :=
    integral_congr_ae (Eventually.of_forall fun ω => (sq (Y t ω)).symm)
  rw [integral_sub hG (hH.const_mul 2), integral_const_mul] at hsplit
  rw [hsplit, hξ] at hET
  rw [hYt] at hEt
  linarith

end MVFBSDEJ.WellPosedness.Stability
