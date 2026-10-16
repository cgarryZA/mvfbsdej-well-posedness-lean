/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.P2
import Dissertation.Law.Wasserstein

/-!
# Pushforward along a map that does not increase distances

Pushing a coupling forward coordinatewise along a measurable map `P` produces a coupling of the
pushforward laws, and when `P` satisfies `‖P x - P y‖ ≤ ‖x - y‖` this transformation does not
increase the quadratic transport cost. Taking the infimum over couplings gives the corresponding
bound for the squared 2-Wasserstein distance; a coordinate projection of a product of normed
spaces is one such map.

## Main statements

* `Dissertation.Law.isCoupling_map_prodMap`: the coordinatewise pushforward of a coupling is a
  coupling of the pushforward laws.
* `Dissertation.Law.w2sq_map_le_of_norm_sub_le`: a measurable map that does not increase
  distances does not increase the squared 2-Wasserstein distance of the laws.
* `Dissertation.Law.w2_map_le_of_norm_sub_le`: the same bound for the real-valued distance, under
  the hypothesis that the squared distance of the two laws is finite.
* `Dissertation.Law.w2P_map_le_of_norm_sub_le`: the same bound for two laws of finite second
  moment.
-/

namespace Dissertation.Law

open MeasureTheory
open scoped ENNReal

section Pushforward

variable {E : Type*} [MeasurableSpace E] {F : Type*} [MeasurableSpace F]

/-- The coordinatewise pushforward of a coupling along a measurable map is a coupling of the
pushforward laws. -/
theorem isCoupling_map_prodMap {μ ν : Measure E} {γ : Measure (E × E)} (hγ : IsCoupling μ ν γ)
    {P : E → F} (hP : Measurable P) :
    IsCoupling (μ.map P) (ν.map P) (γ.map fun p => (P p.1, P p.2)) := by
  obtain ⟨h1, h2⟩ := hγ
  have hm : Measurable fun p : E × E => (P p.1, P p.2) :=
    (hP.comp measurable_fst).prodMk (hP.comp measurable_snd)
  refine ⟨?_, ?_⟩
  · rw [Measure.fst, Measure.map_map measurable_fst hm, ← h1, Measure.fst,
      Measure.map_map hP measurable_fst]
    rfl
  · rw [Measure.snd, Measure.map_map measurable_snd hm, ← h2, Measure.snd,
      Measure.map_map hP measurable_snd]
    rfl

end Pushforward

section Contraction

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

/-- A measurable map that does not increase distances does not increase the squared
2-Wasserstein distance of the laws. -/
theorem w2sq_map_le_of_norm_sub_le {P : E → F} (hP : Measurable P)
    (hlip : ∀ x y, ‖P x - P y‖ ≤ ‖x - y‖) (μ ν : Measure E) :
    w2sq (μ.map P) (ν.map P) ≤ w2sq μ ν := by
  refine le_iInf₂ fun γ hγ => ?_
  have hm : Measurable fun p : E × E => (P p.1, P p.2) :=
    (hP.comp measurable_fst).prodMk (hP.comp measurable_snd)
  refine (w2sq_le_transportCostSq (isCoupling_map_prodMap hγ hP)).trans ?_
  rw [transportCostSq, transportCostSq, lintegral_map measurable_normSq_sub hm]
  refine lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_
  have h := hlip p.1 p.2
  have h0 : (0 : ℝ) ≤ ‖P p.1 - P p.2‖ := norm_nonneg _
  nlinarith [h, h0]

/-- A measurable map that does not increase distances does not increase the 2-Wasserstein
distance of two laws at finite squared distance. -/
theorem w2_map_le_of_norm_sub_le {P : E → F} (hP : Measurable P)
    (hlip : ∀ x y, ‖P x - P y‖ ≤ ‖x - y‖) (μ ν : Measure E) (hfin : w2sq μ ν ≠ ⊤) :
    w2 (μ.map P) (ν.map P) ≤ w2 μ ν :=
  Real.sqrt_le_sqrt (ENNReal.toReal_mono hfin (w2sq_map_le_of_norm_sub_le hP hlip μ ν))

end Contraction

/-! ### Pushforward of the laws of finite second moment -/

section ContractionP2

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F]
  [BorelSpace F] [SecondCountableTopology F]

/-- A measurable map that does not increase distances does not increase the 2-Wasserstein
distance of two laws of finite second moment. -/
theorem w2P_map_le_of_norm_sub_le (μ ν : P2 E) {P : E → F} (hP : Measurable P)
    (hnorm : ∀ x, ‖P x‖ ≤ ‖x‖) (hlip : ∀ x y, ‖P x - P y‖ ≤ ‖x - y‖) :
    w2P (μ.map hP hnorm) (ν.map hP hnorm) ≤ w2P μ ν :=
  w2_map_le_of_norm_sub_le hP hlip μ.law ν.law (w2sq_ne_top μ ν)

end ContractionP2

end Dissertation.Law
