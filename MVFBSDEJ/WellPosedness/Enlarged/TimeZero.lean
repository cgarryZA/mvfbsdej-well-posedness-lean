/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.JointPRPProcess

/-!
# The joint integral at time zero

Let `ℱ` be a filtration carrying a Lévy driver `D = (W, N)`: every Brownian coordinate is a
Brownian motion and `N` is a Poisson random measure for `ℱ`. The Itô integral and the compensated
integral vanish almost surely at every time `t ≤ 0`, so the joint integral process
`t ↦ ∑ i ∫₀ᵗ Gⁱ dWⁱ + ∫₀ᵗ ∫ K dÑ` vanishes almost surely at time `0`. For `T ≥ 0` the joint
integral over `[0, T]` conditions at time `0`, for the right-continuous version of `ℱ`, to the
value of that process at `0`, and for `T < 0` it vanishes; either way it is orthogonal in `L²`
to every bounded weight measurable for `ℱ₀`:

`E[g · (∑ i ∫₀ᵀ Gⁱ dWⁱ + ∫₀ᵀ ∫ K dÑ)] = 0`   for `g` bounded and `ℱ₀`-measurable.

For the trivial weight `g = 1` this is the vanishing of the mean of the joint integral.

## Main statements

* `jointIntegralProcess_ae_zero_of_nonpos` — the joint integral process vanishes almost surely
  at every nonpositive time.
* `jointIntegralProcess_zero_ae` — it vanishes almost surely at time `0`.
* `integral_mul_jointIntegral_eq_zero` — the joint integral is orthogonal to every bounded
  `ℱ₀`-measurable weight.
-/

open MeasureTheory ProbabilityTheory

namespace MVFBSDEJ.WellPosedness.Enlarged

open LevyStochCalc LevyStochCalc.Driver LevyStochCalc.Driver.LevyDriver
open LevyStochCalc.Brownian.Ito LevyStochCalc.Poisson.Compensated

universe u v w

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyDriver.{u, v, w} P d ν} {ℱ : MeasureTheory.Filtration ℝ mΩ} {T : ℝ}
  (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
  (hℱN : Poisson.IsPoissonFiltration D.N ℱ)

/-- The joint integral process vanishes almost surely at every nonpositive time. -/
theorem jointIntegralProcess_ae_zero_of_nonpos (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T)
    (K : MarkedHorizonIntegrand P ν ℱ T) {t : ℝ} (ht : t ≤ 0) :
    jointIntegralProcess hcoord hℱN G K t =ᵐ[P] 0 := by
  have hB : ∀ i : Fin d, horizonProcess (D.W.W i) (hcoord i) (G i) t =ᵐ[P] 0 := fun i =>
    stochasticIntegralBrownian_ae_zero_of_nonpos (D.W.W i) ℱ (hcoord i) _ _ _ _ ht
  have hN : markedHorizonProcess D.N hℱN K t =ᵐ[P] 0 :=
    (stochasticIntegral_ae_eq_process D.N ℱ hℱN _ _ _ _ t).trans
      (process_ae_zero_of_nonpos D.N ℱ hℱN _ _ _ _ ht)
  filter_upwards [hN, Filter.eventually_all.2 hB] with ω e1 e2
  simp only [jointIntegralProcess, Pi.zero_apply]
  rw [e1, Pi.zero_apply, add_zero]
  exact Finset.sum_eq_zero fun i _ => e2 i

/-- The joint integral process vanishes almost surely at time `0`. -/
theorem jointIntegralProcess_zero_ae (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T)
    (K : MarkedHorizonIntegrand P ν ℱ T) :
    jointIntegralProcess hcoord hℱN G K 0 =ᵐ[P] 0 :=
  jointIntegralProcess_ae_zero_of_nonpos hcoord hℱN G K le_rfl

/-- The joint integral is orthogonal to every bounded weight measurable at time `0`:
`E[g · (∑ i ∫₀ᵀ Gⁱ dWⁱ + ∫₀ᵀ ∫ K dÑ)] = 0` for `g` bounded and strongly `ℱ₀`-measurable. -/
theorem integral_mul_jointIntegral_eq_zero (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T)
    (K : MarkedHorizonIntegrand P ν ℱ T) {g : Ω → ℝ} (hgm : StronglyMeasurable[ℱ 0] g)
    {C : ℝ} (hgC : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω * jointIntegral hcoord hℱN G K ω ∂P = 0 := by
  rcases le_or_gt T 0 with hT | hT
  · have h0 := jointIntegralProcess_ae_zero_of_nonpos hcoord hℱN G K hT
    rw [jointIntegralProcess_horizon] at h0
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h0] with ω hω
    rw [hω, Pi.zero_apply, mul_zero]
  · set J := jointIntegral hcoord hℱN G K with hJdef
    haveI : SigmaFinite (P.trim (ℱ.rightCont.le 0)) := by infer_instance
    have hJint : Integrable J P := (memLp_jointIntegral hcoord hℱN G K).integrable (by norm_num)
    have hgm' : StronglyMeasurable[ℱ.rightCont 0] g := hgm.mono (ℱ.le_rightCont 0)
    have hprod : Integrable (g * J) P :=
      hJint.bdd_mul (hgm.mono (ℱ.le 0)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgC ω)
    have hpull := condExp_mul_of_stronglyMeasurable_left hgm' hprod hJint
    have hcond : P[J | ℱ.rightCont 0] =ᵐ[P] 0 :=
      (condExp_jointIntegral_rightCont hcoord hℱN G K hT.le).trans
        (jointIntegralProcess_zero_ae hcoord hℱN G K)
    change ∫ ω, (g * J) ω ∂P = 0
    rw [← integral_condExp (ℱ.rightCont.le 0)]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hpull, hcond] with ω e1 e2
    rw [e1, Pi.mul_apply, e2, Pi.zero_apply, mul_zero]

end MVFBSDEJ.WellPosedness.Enlarged
