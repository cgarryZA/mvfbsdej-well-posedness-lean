/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.Dealer.Zero

/-!
# Example 5.5: the linear equation of the specialisation

In the specialisation of the exposure-sensitive dealer system the forward component at zero
interaction solves the linear equation

`X_t = ∫_0^t (−X_s ds + ½ dW_s) + ½ ∫_0^t ∫_E (η_c(e) + η_x(e) X_{s−}) Ñ(ds, de)`,

with `η_c, η_x` representatives of `h_c, h_x`. A solution meets its left limits for
`dP ⊗ ds`, so for two solutions the difference `D` has the rate `−2 D² + ¼ D² ‖h_x‖²`, which is
`−(7/4) D² ≤ 0` when `‖h_x‖ = 1`: solutions are unique.

## Main definitions

* `DealerLinear` — the linear equation.

## Main statements

* `LinearFSDEJ.ae_leftLimProc_eq` — a solution of a linear forward equation meets its left limits
  for `dP ⊗ ds` on `[0, T]`.
* `energy_eq_zero_of_ae_ae`, `markedEnergy_eq_zero_of_ae_ae` — zero energy from vanishing at
  almost every time, almost surely.
* `DealerLinear.unique` — two solutions are indistinguishable on `[0, T]`.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped RealInnerProductSpace ENNReal NNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.BrownianPoisson LevyStochCalc

universe u v w

/-! ### Zero energy from vanishing at almost every time -/

section ZeroEnergy

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  [SFinite P] {ν : Measure E} {T : ℝ}

/-- **Zero energy from vanishing at almost every time.** A jointly measurable integrand that
vanishes almost surely at almost every time of `[0, T]` has zero energy on `[0, T]`. -/
theorem energy_eq_zero_of_ae_ae {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (h : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, H ω s = 0) :
    Brownian.Ito.energy P T H = 0 := by
  have hm' : Measurable (Function.uncurry fun ω s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2) :=
    (hm.nnnorm.coe_nnreal_ennreal).pow_const 2
  unfold Brownian.Ito.energy
  rw [lintegral_lintegral_swap hm'.aemeasurable]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [h] with s hs
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hs] with ω hω
  simp [hω]

/-- **Zero marked energy from vanishing at almost every time.** A jointly measurable marked
integrand that vanishes `ν`-almost everywhere, almost surely, at almost every time of `[0, T]` has
zero marked energy on `[0, T]`. -/
theorem markedEnergy_eq_zero_of_ae_ae [SFinite ν] {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (h : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, ∀ᵐ e ∂ν, φ ω s e = 0) :
    Poisson.Compensated.markedEnergy P ν T φ = 0 := by
  have hm' : Measurable fun p : Ω × ℝ × E => (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    (hm.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hin : Measurable (Function.uncurry fun ω s => ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) := by
    have h1 : Measurable fun q : (Ω × ℝ) × E => (‖φ q.1.1 q.1.2 q.2‖₊ : ℝ≥0∞) ^ 2 :=
      hm'.comp MeasurableEquiv.prodAssoc.measurable
    exact h1.lintegral_prod_right'
  unfold Poisson.Compensated.markedEnergy
  rw [lintegral_lintegral_swap hin.aemeasurable]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [h] with s hs
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hs] with ω hω
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hω] with e he
  simp [he]

end ZeroEnergy

/-! ### Left limits of a solution of a linear forward equation -/

section LeftLim

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}
  {ξ₀ : Ω → ℝ} {b : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ} {σ : ℝ → Ω → (Fin d → ℝ)}
  {γ : ℝ → Ω → E → ℝ}

/-- A solution of a linear forward equation is jointly measurable in the sample point and the
time. -/
theorem _root_.Dissertation.WellPosedness.Stability.LinearFSDEJ.measurable_uncurry_swap
    (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) :
    Measurable (Function.uncurry fun ω s => X s ω) :=
  (Probability.measurable_uncurry_of_rightContinuous h.X_adapted h.X_rightCont).comp
    measurable_swap

/-- **A solution of a linear forward equation meets its left limits** for `dP ⊗ ds`-almost every
`(ω, s) ∈ Ω × [0, T]`. -/
theorem _root_.Dissertation.WellPosedness.Stability.LinearFSDEJ.ae_leftLimProc_eq
    (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) (hT : 0 ≤ T) :
    ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T),
      leftLimProc (fun _ : Fin 1 => X) 0 p.2 p.1 = X p.2 p.1 := by
  have h1 := System.ae_leftLimProc_eq (P := P) (T := T) (X := fun _ : Fin 1 => X)
    (fun _ => h.measurable_uncurry_swap)
    ((h.ae_leftLim hT).mono fun ω hω _ => ⟨h.X_rightCont ω, hω⟩)
  filter_upwards [h1] with p hp
  exact hp 0

/-- **A solution of a linear forward equation meets its left limits at almost every time**,
almost surely. -/
theorem _root_.Dissertation.WellPosedness.Stability.LinearFSDEJ.ae_ae_leftLimProc_eq
    (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ) (hT : 0 ≤ T) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      leftLimProc (fun _ : Fin 1 => X) 0 s ω = X s ω :=
  ae_ae_of_ae_prod_Icc (h.ae_leftLimProc_eq hT)

end LeftLim

/-! ### The linear equation -/

section Linear

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {ηc ηx : E → ℝ}

variable (D ℱ hℱW hℱN) in
/-- The linear equation of the specialisation of the dealer market,
`X_t = ∫_0^t (−X_s ds + ½ dW_s) + ½ ∫_0^t ∫_E (η_c(e) + η_x(e) X_{s−}) Ñ(ds, de)` on `[0, T]`,
the drift and diffusion taken on `[0, T]` and the jump integrand on `(0, T]`. -/
def DealerLinear (T : ℝ) (ηc ηx : E → ℝ) (X : ℝ → Ω → ℝ) : Prop :=
  LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0)
    (fun ω s => (Set.Icc (0 : ℝ) T).indicator (fun s => -X s ω) s) X
    (fun s _ _ => (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) s)
    (fun s ω e => (Set.Ioc (0 : ℝ) T).indicator
      (fun s => 1 / 2 * (ηc e + ηx e * leftLimProc (fun _ : Fin 1 => X) 0 s ω)) s)

omit [IsProbabilityMeasure P] in
/-- For `P ⊗ ds` on `[0, T]`, almost every point has its time in `(0, T)`. -/
theorem ae_snd_mem_Ioo [SFinite P] :
    ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), q.2 ∈ Set.Ioo (0 : ℝ) T := by
  refine Measure.quasiMeasurePreserving_snd.ae ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [(Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := T)).mem_iff] with s hs hsI
  exact hs.mpr hsI

/-- **The linear equation has at most one solution.** Over a filtration with a cross witness, for
`T > 0` and `η_x` with `∫_E η_x² dν = 1`, two solutions of the linear equation are
indistinguishable on `[0, T]`. -/
theorem DealerLinear.unique {X₁ X₂ : ℝ → Ω → ℝ} (h₁ : DealerLinear D ℱ hℱW hℱN T ηc ηx X₁)
    (h₂ : DealerLinear D ℱ hℱW hℱN T ηc ηx X₂) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    (hηx : ∫ e, ηx e ^ 2 ∂ν = 1) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ t ω = X₂ t ω := by
  have hl₁ := h₁.ae_leftLimProc_eq hT.le
  have hl₂ := h₂.ae_leftLimProc_eq hT.le
  -- the rate of the difference is nonpositive
  have hr : ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      2 * (X₂ q.2 q.1 - (fun _ => (1 : ℝ)) q.2 * X₁ q.2 q.1)
          * ((Set.Icc (0 : ℝ) T).indicator (fun s => -X₂ s q.1) q.2
            - (fun _ => (0 : ℝ)) q.2 * X₁ q.2 q.1
            - (fun _ => (1 : ℝ)) q.2 * (Set.Icc (0 : ℝ) T).indicator (fun s => -X₁ s q.1) q.2)
        + ∑ j : Fin 1, ((Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) q.2
            - (fun _ => (1 : ℝ)) q.2 * (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) q.2)
          ^ 2
        + ∫ e, ((Set.Ioc (0 : ℝ) T).indicator
              (fun s => 1 / 2 * (ηc e + ηx e * leftLimProc (fun _ : Fin 1 => X₂) 0 s q.1)) q.2
            - (fun _ => (1 : ℝ)) q.2 * (Set.Ioc (0 : ℝ) T).indicator
              (fun s => 1 / 2 * (ηc e + ηx e * leftLimProc (fun _ : Fin 1 => X₁) 0 s q.1)) q.2)
          ^ 2 ∂ν ≤ 0 := by
    filter_upwards [hl₁, hl₂, ae_snd_mem_Ioo] with q hq₁ hq₂ hqI
    have hIcc : q.2 ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self hqI
    have hIoc : q.2 ∈ Set.Ioc (0 : ℝ) T := Set.Ioo_subset_Ioc_self hqI
    simp only [Set.indicator_of_mem hIcc, Set.indicator_of_mem hIoc, hq₁, hq₂, one_mul,
      zero_mul, sub_zero, sub_self, Fin.sum_univ_one]
    have hj : ∫ e, (1 / 2 * (ηc e + ηx e * X₂ q.2 q.1) - 1 / 2 * (ηc e + ηx e * X₁ q.2 q.1)) ^ 2
        ∂ν = (X₂ q.2 q.1 - X₁ q.2 q.1) ^ 2 / 4 := by
      have e : (fun e => (1 / 2 * (ηc e + ηx e * X₂ q.2 q.1)
          - 1 / 2 * (ηc e + ηx e * X₁ q.2 q.1)) ^ 2)
          = fun e => (X₂ q.2 q.1 - X₁ q.2 q.1) ^ 2 / 4 * ηx e ^ 2 := by
        funext e
        ring
      rw [e, integral_const_mul, hηx, mul_one]
    rw [hj]
    nlinarith [sq_nonneg (X₂ q.2 q.1 - X₁ q.2 q.1)]
  -- the second moment of the difference vanishes at every time
  have hF : ∀ t ∈ Set.Icc (0 : ℝ) T, X₂ t =ᵐ[P] X₁ t := by
    intro t ht
    obtain ⟨-, heq⟩ := LinearFSDEJ.integral_residual_sq_eq h₁ h₂ 𝒲 hT (p := fun _ => 1)
      (p' := fun _ => 0) continuousOn_const (fun x _ => hasDerivAt_const x 1) continuousOn_const ht
    have hle := integral_nonpos_of_ae
      (ae_mono (LinearFSDEJ.prod_restrict_Icc_le (P := P) ht.2) hr)
    have h0 : ∫ ω, (X₂ t ω - 1 * X₁ t ω) ^ 2 ∂P = 0 := by
      have hge : 0 ≤ ∫ ω, (X₂ t ω - 1 * X₁ t ω) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
      simp only [sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, integral_zero, zero_add] at heq
      linarith
    have hint' : Integrable (fun ω => (X₂ t ω - 1 * X₁ t ω) ^ 2) P :=
      ((h₂.memLp_apply ht).sub ((h₁.memLp_apply ht).const_mul 1)).integrable_sq
    filter_upwards [(integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint').mp h0] with ω hω
    have : (X₂ t ω - 1 * X₁ t ω) ^ 2 = 0 := hω
    have := pow_eq_zero_iff two_ne_zero |>.mp this
    linarith
  have hfin := ae_forall_Icc_eq_of_ae_rightContinuous hT.le hF (ae_of_all _ h₂.X_rightCont)
    (ae_of_all _ h₁.X_rightCont)
  filter_upwards [hfin] with ω hω t ht
  exact (hω t ht).symm

end Linear

end Dissertation.WellPosedness.Existence
