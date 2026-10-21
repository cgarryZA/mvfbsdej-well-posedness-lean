/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Enlarged.Driver
import MVFBSDEJ.WellPosedness.Enlarged.Pairing
import MVFBSDEJ.WellPosedness.Enlarged.Characters

/-!
# The orthogonal complement of the joint ranges over the enlarged filtration

Let `D = (W, N)` be a Lévy driver with joint natural filtration `ℱ`, let `𝒢₀` be independent of
`⨆ t, ℱ_t`, and let `ℱᵉⁿˡ = enlJoint 𝒢₀ D h𝒢₀` be the usual augmentation of `t ↦ ℱ_t ⊔ 𝒢₀`.
A square-integrable weight `r`, measurable for `ℱᵉⁿˡ_T`, orthogonal to every bounded
`ℱᵉⁿˡ_0`-measurable weight, to the Itô integrals against every Brownian coordinate and to the
compensated integral of every admissible integrand over `[0, T]`, vanishes almost everywhere.

The independence of `𝒢₀` from the noise makes the driver a Lévy driver for `ℱᵉⁿˡ`. The weight
`r` is measurable for the augmentation of `ℱ_{T+1} ⊔ 𝒢₀`, and the orthogonality to the
compensated integrals carries over to the horizon `T + 1`. For a character
`g = e^{i ∑ u_A 1_A}` of finitely many indicators of sets of `𝒢₀`, the real and imaginary parts
of `g` are bounded and `ℱᵉⁿˡ_0`-measurable, so `E[r g] = 0`, and the grid induction started from
`g` gives

`E[e^{i ∑ w_p W_{t_p}} · e^{i ∑ v_B N(B)} · e^{i ∑ u_A 1_A} · r] = 0`

for every Brownian cylinder character and window character before `T + 1`. These products
separate on the augmentation of `ℱ_{T+1} ⊔ 𝒢₀`, so `r` vanishes.

## Main statements

* `integral_mul_eq_zero_of_perp_real` — a weight orthogonal to every bounded real weight
  measurable for a σ-algebra is orthogonal to every character of a real function measurable for
  it.
* `ae_eq_zero_of_perp_enl` — the orthogonal complement of the time-`0` weights and of the joint
  ranges over the enlarged filtration is trivial.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MVFBSDEJ.WellPosedness.Enlarged

open LevyStochCalc LevyStochCalc.Driver LevyStochCalc.Probability
open LevyStochCalc.Brownian.Ito LevyStochCalc.Poisson.Compensated

universe u v w

section Real

variable {Ω : Type u} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- A square-integrable weight orthogonal to every bounded real weight strongly measurable for a
sub-σ-algebra `m` integrates to zero against `e^{iθ}` for every real `θ` measurable for `m`. -/
theorem integral_mul_eq_zero_of_perp_real (hm : m ≤ mΩ) {r : Ω → ℝ} (hr2 : MemLp r 2 P)
    (hr0 : ∀ g : Ω → ℝ, StronglyMeasurable[m] g → (∃ C, ∀ ω, |g ω| ≤ C) →
      ∫ ω, r ω * g ω ∂P = 0)
    {θ : Ω → ℝ} (hθ : Measurable[m] θ) :
    ∫ ω, ((r ω : ℝ) : ℂ) * Complex.exp (((θ ω : ℝ) : ℂ) * Complex.I) ∂P = 0 := by
  have hcos : Measurable[m] fun ω => Real.cos (θ ω) := Real.continuous_cos.measurable.comp hθ
  have hsin : Measurable[m] fun ω => Real.sin (θ ω) := Real.continuous_sin.measurable.comp hθ
  have hr1 : Integrable r P := hr2.integrable (by norm_num)
  have hcI : Integrable (fun ω => r ω * Real.cos (θ ω)) P :=
    hr1.mul_bdd (hcos.mono hm le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hsI : Integrable (fun ω => r ω * Real.sin (θ ω)) P :=
    hr1.mul_bdd (hsin.mono hm le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hc0 := hr0 _ hcos.stronglyMeasurable ⟨1, fun ω => Real.abs_cos_le_one _⟩
  have hs0 := hr0 _ hsin.stronglyMeasurable ⟨1, fun ω => Real.abs_sin_le_one _⟩
  have hrw : (fun ω => ((r ω : ℝ) : ℂ) * Complex.exp (((θ ω : ℝ) : ℂ) * Complex.I))
      = fun ω => ((r ω * Real.cos (θ ω) : ℝ) : ℂ)
        + ((r ω * Real.sin (θ ω) : ℝ) : ℂ) * Complex.I := by
    funext ω
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [hrw, integral_add hcI.ofReal (hsI.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, hc0, hs0]
  simp

end Real

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- **The orthogonal complement over the enlarged filtration is trivial.** For `𝒢₀` independent
of the joint natural filtration of a Lévy driver, a square-integrable weight measurable for the
enlarged filtration at the horizon `T`, orthogonal to every bounded real weight measurable at
time `0`, to every coordinate's Itô integrals and to the compensated integral of every admissible
integrand over `[0, T]`, vanishes almost everywhere. -/
theorem ae_eq_zero_of_perp_enl (D : LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (hd : 0 < d) {T : ℝ} (hT : 0 < T)
    {r : Ω → ℝ} (hr2 : MemLp r 2 P) (hrm : AEStronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ T] r P)
    (hr0 : ∀ g : Ω → ℝ, StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] g → (∃ C, ∀ ω, |g ω| ≤ C) →
      ∫ ω, r ω * g ω ∂P = 0)
    (hrB : ∀ (i : Fin d) (G : HorizonIntegrand P (enlJoint 𝒢₀ D h𝒢₀) T),
      ∫ ω, r ω * G.integral (D.W.W i) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀ i) ω ∂P = 0)
    (hrN : ∀ K : MarkedHorizonIntegrand P ν (enlJoint 𝒢₀ D h𝒢₀) T,
      ∫ ω, r ω * K.integral D.N (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) ω ∂P = 0) :
    r =ᵐ[P] 0 := by
  have hW := isBrownianFiltration_enlJoint D h𝒢₀ hind₀
  have hN := isPoissonFiltration_enlJoint D h𝒢₀ hind₀
  have hTR : T ≤ T + 1 := by linarith
  have hR : (0 : ℝ) < T + 1 := by linarith
  have hperp : ∀ i : Fin d, PerpItoIntegrals (D.W.W i) (enlJoint 𝒢₀ D h𝒢₀) (hW i)
      fun ω => ((r ω : ℝ) : ℂ) := by
    intro i
    refine ⟨fun K hm hp hq t ht => ?_⟩
    have hreal := integral_mul_stochasticIntegral_eq_zero (D.W.W i) (hW i) hT hr2 hrm (hrB i)
      K hm hp hq ht
    have hcast : (fun ω => ((r ω : ℝ) : ℂ) * ((stochasticIntegralBrownian (D.W.W i)
          (enlJoint 𝒢₀ D h𝒢₀) (hW i) K hm hp hq t ω : ℝ) : ℂ))
        = fun ω => ((r ω * stochasticIntegralBrownian (D.W.W i) (enlJoint 𝒢₀ D h𝒢₀) (hW i)
          K hm hp hq t ω : ℝ) : ℂ) := by
      funext ω
      rw [Complex.ofReal_mul]
    rw [hcast, integral_complex_ofReal, hreal, Complex.ofReal_zero]
  have hrNR : ∀ K : MarkedHorizonIntegrand P ν (enlJoint 𝒢₀ D h𝒢₀) (T + 1),
      ∫ ω, r ω * K.integral D.N hN ω ∂P = 0 := fun K =>
    Poisson.Compensated.integral_mul_integral_eq_zero D.N hN hT hr2 hrm hrN hTR K
  have hrmR : AEStronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ (T + 1)] r P :=
    hrm.mono ((enlJoint 𝒢₀ D h𝒢₀).mono hTR)
  have hr2C : MemLp (fun ω => ((r ω : ℝ) : ℂ)) 2 P := by
    refine ⟨Complex.continuous_ofReal.comp_aestronglyMeasurable hr2.1, ?_⟩
    rw [eLpNorm_congr_norm_ae (Eventually.of_forall fun ω => Complex.norm_real (r ω))]
    exact hr2.2
  have hrmC : AEStronglyMeasurable[aug (D.filtration (T + 1) ⊔ 𝒢₀) mΩ P]
      (fun ω => ((r ω : ℝ) : ℂ)) P :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hrm).mono
      (enlJoint_le_aug_succ D h𝒢₀ hT.le)
  have hzero := ae_eq_zero_of_integral_char_enl D h𝒢₀ (T + 1) (hr2C.integrable (by norm_num))
    hrmC fun F G H w v u => ?_
  · filter_upwards [hzero] with ω hω
    have hc : ((r ω : ℝ) : ℂ) = 0 := hω
    exact_mod_cast hc
  have hθ : Measurable[𝒢₀] fun ω => ∑ A : H,
      ((A : {A : Set Ω // MeasurableSet[𝒢₀] A}) : Set Ω).indicator (fun _ => (1 : ℝ)) ω
        * u A :=
    Finset.measurable_sum _ fun A _ => (measurable_const.indicator A.1.2).mul_const (u A)
  have hθ₀ : Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] fun ω => ∑ A : H,
      ((A : {A : Set Ω // MeasurableSet[𝒢₀] A}) : Set Ω).indicator (fun _ => (1 : ℝ)) ω
        * u A :=
    hθ.mono (le_enlJoint_zero D h𝒢₀) le_rfl
  have hgm : StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] fun ω =>
      Complex.exp (((∑ A : H, ((A : {A : Set Ω // MeasurableSet[𝒢₀] A}) : Set Ω).indicator
        (fun _ => (1 : ℝ)) ω * u A : ℝ) : ℂ) * Complex.I) :=
    (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp hθ₀).mul_const
      Complex.I)).stronglyMeasurable
  have hrg := integral_mul_eq_zero_of_perp_real ((enlJoint 𝒢₀ D h𝒢₀).le 0) hr2 hr0 hθ₀
  exact pairing_char_joint_mul_eq_zero D.W D.N (enlJoint 𝒢₀ D h𝒢₀) hd hW
    (fun hc => isBrownianFiltration_combineBM_enlJoint D h𝒢₀ hind₀ hc) hN
    (fun _ ht => enlJoint_le_of_nonpos D h𝒢₀ ht)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hR hr2 hrmR hperp hrNR hgm
    (Mg := 1) (fun ω => le_of_eq (Complex.norm_exp_ofReal_mul_I _)) hrg F G w v

end MVFBSDEJ.WellPosedness.Enlarged
