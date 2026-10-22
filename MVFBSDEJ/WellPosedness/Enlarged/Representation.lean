/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Enlarged.Range
import MVFBSDEJ.WellPosedness.Enlarged.Complement
import MVFBSDEJ.WellPosedness.Enlarged.CrossWitness

/-!
# Martingale representation over the enlarged filtration

Let `D = (W, N)` be a Lévy driver with joint natural filtration `ℱ`, let `𝒢₀` be independent of
`⨆ t, ℱ_t`, and let `ℱᵉⁿˡ = enlJoint 𝒢₀ D h𝒢₀` be the usual augmentation of `t ↦ ℱ_t ⊔ 𝒢₀`.
Every square-integrable `ℱᵉⁿˡ_T`-measurable `ζ` is

`ζ = E[ζ | ℱᵉⁿˡ_0] + ∑ i ∫₀ᵀ Gⁱ dWⁱ + ∫₀ᵀ ∫ K dÑ`

for integrands `G`, `K` admissible for `ℱᵉⁿˡ`: the remainder `ζ - E[ζ | ℱᵉⁿˡ_0]` is orthogonal
to every bounded `ℱᵉⁿˡ_0`-measurable weight, the joint range over `ℱᵉⁿˡ` is closed, and the only
weight orthogonal to the time-`0` weights and to the joint range is zero. On a countably
generated mark space the last step is carried out for the driver with its marks coded into
`ℕ → Bool`, which has the same enlarged filtration and each of whose joint integrals is almost
surely a joint integral of `D`. The initial value `E[ζ | ℱᵉⁿˡ_0]` is random in general. Since
`ℱᵉⁿˡ` is right-continuous, the conditional expectation of such a `ζ` at a time `t ≤ T` is
`E[ζ | ℱᵉⁿˡ_0]` plus the joint integral over `[0, t]` of the same integrands.

## Main statements

* `exists_jointIntegral_enlJoint` — the martingale representation over the enlarged filtration.
* `condExp_enlJoint_eq_jointIntegralProcess` — the conditional expectations of a represented
  weight before the horizon.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MVFBSDEJ.WellPosedness.Enlarged

open LevyStochCalc LevyStochCalc.Driver LevyStochCalc.Driver.LevyDriver
open LevyStochCalc.Brownian.Ito LevyStochCalc.Poisson.Compensated

universe u v w

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {d : ℕ}

/-- **Martingale representation over the enlarged filtration.** For `𝒢₀` independent of the
joint natural filtration of a Lévy driver, every square-integrable weight `ζ` measurable for the
enlarged filtration at the horizon `T > 0` is its conditional expectation given the time-`0`
field plus a joint integral over `[0, T]` of integrands admissible for the enlarged filtration. -/
theorem exists_jointIntegral_enlJoint [MeasurableSpace.CountablyGenerated E]
    (D : LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (hd : 0 < d) {T : ℝ} (hT : 0 < T)
    {ζ : Ω → ℝ} (hζ2 : MemLp ζ 2 P) (hζm : AEStronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ T] ζ P) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P (enlJoint 𝒢₀ D h𝒢₀) T)
      (K : MarkedHorizonIntegrand P ν (enlJoint 𝒢₀ D h𝒢₀) T),
      ζ =ᵐ[P] fun ω => P[ζ | enlJoint 𝒢₀ D h𝒢₀ 0] ω
        + jointIntegral (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
            (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) G K ω := by
  have hm₀ : enlJoint 𝒢₀ D h𝒢₀ 0 ≤ mΩ := (enlJoint 𝒢₀ D h𝒢₀).le 0
  haveI : SigmaFinite (P.trim hm₀) := by infer_instance
  set c : Ω → ℝ := P[ζ | enlJoint 𝒢₀ D h𝒢₀ 0] with hcdef
  have hc2 : MemLp c 2 P := hζ2.condExp (by norm_num)
  have hcm : StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] c := stronglyMeasurable_condExp
  have hZ2 : MemLp (fun ω => ζ ω - c ω) 2 P := hζ2.sub hc2
  have hZm : AEStronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ T] (fun ω => ζ ω - c ω) P :=
    hζm.sub (hcm.mono ((enlJoint 𝒢₀ D h𝒢₀).mono hT.le)).aestronglyMeasurable
  have hZ0 : ∀ g : Ω → ℝ, StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] g →
      (∃ C, ∀ ω, |g ω| ≤ C) → ∫ ω, (ζ ω - c ω) * g ω ∂P = 0 := by
    rintro g hgm ⟨C, hgC⟩
    have hgae : AEStronglyMeasurable g P := (hgm.mono hm₀).aestronglyMeasurable
    have hbd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ C :=
      Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgC ω
    have hζg : Integrable (fun ω => ζ ω * g ω) P :=
      (hζ2.integrable (by norm_num)).mul_bdd hgae hbd
    have hcg : Integrable (fun ω => c ω * g ω) P :=
      (hc2.integrable (by norm_num)).mul_bdd hgae hbd
    have hpull : P[ζ * g | enlJoint 𝒢₀ D h𝒢₀ 0] =ᵐ[P] c * g :=
      condExp_mul_of_aestronglyMeasurable_right hgm.aestronglyMeasurable hζg
        (hζ2.integrable (by norm_num))
    have hcgζg : ∫ ω, c ω * g ω ∂P = ∫ ω, ζ ω * g ω ∂P := by
      have h1 : ∫ ω, c ω * g ω ∂P = ∫ ω, (P[ζ * g | enlJoint 𝒢₀ D h𝒢₀ 0]) ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hpull] with ω e
        rw [e, Pi.mul_apply]
      rw [h1, integral_condExp hm₀]
      rfl
    have hrw : (fun ω => (ζ ω - c ω) * g ω) = fun ω => ζ ω * g ω - c ω * g ω := by
      funext ω; ring
    rw [hrw, integral_sub hζg hcg, hcgζg, sub_self]
  have hf := MarkCoding.filtration_codedDriver D
  have hind₀' : Indep 𝒢₀ (⨆ t, (MarkCoding.codedDriver D).filtration t) P := by
    rw [hf]
    exact hind₀
  have henl : enlJoint 𝒢₀ (MarkCoding.codedDriver D) h𝒢₀ = enlJoint 𝒢₀ D h𝒢₀ := by
    simp only [enlJoint, initJoint, hf]
  obtain ⟨G, K, hZeq⟩ := exists_jointIntegral_of_perp_zero
    (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (isPoissonFiltration_enlJoint D h𝒢₀ hind₀)
    (crossWitnessEnl D h𝒢₀ hind₀) hT
    (fun _ hr2 hrm hr0 hrB hrN => MarkCoding.ae_eq_zero_of_perp_of_mapMarks
      (MeasurableSpace.measurable_mapNatBool E) henl
      (fun _ hr2 hrm hr0 hrB hrN => ae_eq_zero_of_perp_enl (MarkCoding.codedDriver D) h𝒢₀
        hind₀' hd hT hr2 hrm hr0 hrB hrN)
      hr2 hrm hr0 hrB hrN)
    hZ2 hZm hZ0
  refine ⟨G, K, ?_⟩
  filter_upwards [hZeq] with ω e
  rw [← e]
  ring

/-- **Conditional expectations of a represented weight.** If `ζ` is its conditional expectation
given the time-`0` field of the enlarged filtration plus a joint integral over `[0, T]`, then at
every time `t ≤ T` its conditional expectation given the enlarged filtration is that time-`0`
conditional expectation plus the joint integral over `[0, t]` of the same integrands. -/
theorem condExp_enlJoint_eq_jointIntegralProcess (D : LevyDriver.{u, v, w} P d ν)
    (h𝒢₀ : 𝒢₀ ≤ mΩ) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) {T : ℝ} {ζ : Ω → ℝ}
    (G : ∀ _ : Fin d, HorizonIntegrand P (enlJoint 𝒢₀ D h𝒢₀) T)
    (K : MarkedHorizonIntegrand P ν (enlJoint 𝒢₀ D h𝒢₀) T)
    (hζ : ζ =ᵐ[P] fun ω => P[ζ | enlJoint 𝒢₀ D h𝒢₀ 0] ω
      + jointIntegral (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
          (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) G K ω)
    {t : ℝ} (htT : t ≤ T) :
    P[ζ | enlJoint 𝒢₀ D h𝒢₀ t] =ᵐ[P] fun ω => P[ζ | enlJoint 𝒢₀ D h𝒢₀ 0] ω
      + jointIntegralProcess (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
          (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) G K t ω := by
  set hW := isBrownianFiltration_enlJoint D h𝒢₀ hind₀
  set hN := isPoissonFiltration_enlJoint D h𝒢₀ hind₀
  set c : Ω → ℝ := P[ζ | enlJoint 𝒢₀ D h𝒢₀ 0] with hcdef
  have h0t : enlJoint 𝒢₀ D h𝒢₀ 0 ≤ enlJoint 𝒢₀ D h𝒢₀ t := by
    rcases le_total t 0 with ht | ht
    · exact enlJoint_le_of_nonpos D h𝒢₀ ht
    · exact (enlJoint 𝒢₀ D h𝒢₀).mono ht
  have hcint : Integrable c P := integrable_condExp
  have hJint : Integrable (jointIntegral hW hN G K) P :=
    (memLp_jointIntegral hW hN G K).integrable (by norm_num)
  have hcm : StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ t] c :=
    (stronglyMeasurable_condExp (m := enlJoint 𝒢₀ D h𝒢₀ 0) (μ := P) (f := ζ)).mono h0t
  have hcc : P[c | enlJoint 𝒢₀ D h𝒢₀ t] = c :=
    condExp_of_stronglyMeasurable ((enlJoint 𝒢₀ D h𝒢₀).le t) hcm hcint
  have hrc : (enlJoint 𝒢₀ D h𝒢₀).rightCont = enlJoint 𝒢₀ D h𝒢₀ :=
    MeasureTheory.Filtration.IsRightContinuous.eq
  have hJ := condExp_jointIntegral_rightCont hW hN G K htT
  rw [hrc] at hJ
  refine (condExp_congr_ae hζ).trans ?_
  refine (condExp_add hcint hJint _).trans ?_
  rw [hcc]
  filter_upwards [hJ] with ω e
  rw [Pi.add_apply, e]

end MVFBSDEJ.WellPosedness.Enlarged
