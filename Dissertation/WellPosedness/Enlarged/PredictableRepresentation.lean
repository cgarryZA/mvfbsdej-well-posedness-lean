/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Enlarged.Representation
import Dissertation.WellPosedness.Enlarged.RepresentationUnique
import LevyStochCalc.Brownian.PredictableIntegrand
import LevyStochCalc.Poisson.PredictableIntegrand

/-!
# Predictable integrands over the enlarged filtration

Let `D = (W, N)` be a Lévy driver with `d` Brownian coordinates, let `𝒢₀` be independent of its
joint natural filtration, and let `ℱ = enlJoint 𝒢₀ D h𝒢₀` be the usual augmentation of
`t ↦ ℱᴰ_t ⊔ 𝒢₀`, `T > 0`. Integrands `(G, K)` admissible for `ℱ` over `[0, T]` may be replaced by
predictable ones with almost surely the same joint integral `∑ i ∫₀ᵀ Gⁱ dWⁱ + ∫₀ᵀ ∫_E K dÑ`. This
turns the representation `exists_jointIntegral_enlJoint` of a square-integrable terminal variable,
whose integrands are admissible, into one with predictable integrands, as in the Brownian–Poisson
predictable representation property of §2 of the paper.

## Main statements

* `exists_predictable_of_jointIntegral_enlJoint` — predictable integrands with the same joint
  integral.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness.Enlarged

open LevyStochCalc LevyStochCalc.Driver LevyStochCalc.Driver.LevyDriver
open LevyStochCalc.Brownian.Ito LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

universe u v w

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {d : ℕ}

/-- **Predictable integrands with the same joint integral.** For `T > 0`, integrands admissible
for the enlarged filtration may be replaced by predictable ones with almost surely the same joint
integral over `[0, T]`. -/
theorem exists_predictable_of_jointIntegral_enlJoint (D : LevyDriver.{u, v, w} P d ν)
    (h𝒢₀ : 𝒢₀ ≤ mΩ) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) {T : ℝ} (hT : 0 < T)
    (G : ∀ _ : Fin d, HorizonIntegrand P (enlJoint 𝒢₀ D h𝒢₀) T)
    (K : MarkedHorizonIntegrand P ν (enlJoint 𝒢₀ D h𝒢₀) T) :
    ∃ (G' : ∀ _ : Fin d, HorizonIntegrand P (enlJoint 𝒢₀ D h𝒢₀) T)
      (K' : MarkedHorizonIntegrand P ν (enlJoint 𝒢₀ D h𝒢₀) T),
      (∀ i, Predictable (enlJoint 𝒢₀ D h𝒢₀) (G' i).toFun)
        ∧ MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) ν K'.toFun
        ∧ jointIntegral (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
            (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) G' K'
          =ᵐ[P] jointIntegral (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
            (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) G K := by
  choose G' hG'pred hG'int using fun i : Fin d => exists_predictable_horizonIntegrand (D.W.W i)
    (isBrownianFiltration_enlJoint D h𝒢₀ hind₀ i)
    (fun _ ht => enlJoint_le_of_nonpos D h𝒢₀ ht) hT (G i)
  obtain ⟨K', hK'pred, hK'int⟩ := exists_markedPredictable_markedHorizonIntegrand D.N
    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) hT K
  refine ⟨G', K', hG'pred, hK'pred, ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ i : Fin d,
      (G' i).integral (D.W.W i) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀ i) ω
        = (G i).integral (D.W.W i) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀ i) ω :=
    ae_all_iff.mpr hG'int
  filter_upwards [hall, hK'int] with ω h1 h2
  change Brownian.Multidim.MultidimBrownianMotion.vectorIntegral D.W
      (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) G' ω
      + K'.integral D.N (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) ω
    = Brownian.Multidim.MultidimBrownianMotion.vectorIntegral D.W
      (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) G ω
      + K.integral D.N (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) ω
  rw [h2]
  exact congrArg (· + K.integral D.N (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) ω)
    (Finset.sum_congr rfl fun i _ => h1 i)

end Dissertation.WellPosedness.Enlarged
