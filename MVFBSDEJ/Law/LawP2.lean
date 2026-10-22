/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Function.L2Space
import MVFBSDEJ.Law.P2
import MVFBSDEJ.Law.Synchronous

/-!
# The law of a square-integrable random element

A random element `Θ` of a normed space `F` with `𝔼‖Θ‖² < ∞` has a law of finite second moment,
the image measure `P ∘ Θ⁻¹`. The map `lawP2 P` sends a random element to that law, as an element
of `P2 F`, and to the Dirac mass at the origin when `Θ` is not square integrable; the diagonal
inputs `(Θ, Law Θ)`, `Θ ∈ L²(Ω; F)`, of the well-posedness paper are the pairs
`(Θ, lawP2 P Θ)`. The law depends only on the almost-everywhere class of `Θ`, and the
synchronous coupling of two random elements on one probability space gives the coupling bound
(2.8):

`W₂(Law Θ, Law Θ')² ≤ 𝔼‖Θ − Θ'‖²`.

## Main definitions

* `MVFBSDEJ.Law.lawP2`: the law of a random element, as a law of finite second moment.

## Main statements

* `MVFBSDEJ.Law.secondMoment_map_eq`: the second moment of an image measure.
* `MVFBSDEJ.Law.lawP2_law`: for a square-integrable random element the underlying measure of
  `lawP2 P Θ` is the image measure `P.map Θ`.
* `MVFBSDEJ.Law.lawP2_of_not_memLp`: off `L²` the value is the Dirac mass at the origin.
* `MVFBSDEJ.Law.lawP2_congr`: the law depends only on the almost-everywhere class.
* `MVFBSDEJ.Law.w2P_lawP2_sq_le`: the coupling bound (2.8).
* `MVFBSDEJ.Law.ofReal_w2P_lawP2_sq_le`: the coupling bound as a lower integral.
-/

namespace MVFBSDEJ.Law

open MeasureTheory
open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F]

/-- Two laws of finite second moment with the same underlying measure are equal. -/
theorem P2.ext_law {μ μ' : P2 F} (h : μ.law = μ'.law) : μ = μ' := by
  cases μ
  cases μ'
  cases h
  rfl

variable [BorelSpace F] {Ω : Type*} {m : MeasurableSpace Ω}

/-- The second moment of the image of a measure under an almost everywhere measurable map is
the expected squared norm of the map. -/
theorem secondMoment_map_eq (P : Measure Ω) {Θ : Ω → F} (hΘ : AEMeasurable Θ P) :
    secondMoment (P.map Θ) = ∫⁻ ω, ENNReal.ofReal (‖Θ ω‖ ^ 2) ∂P :=
  lintegral_map' (by fun_prop) hΘ

/-- The image of a measure under a square-integrable map has finite second moment. -/
theorem secondMoment_map_ne_top {P : Measure Ω} {Θ : Ω → F} (hΘ : MemLp Θ 2 P) :
    secondMoment (P.map Θ) ≠ ⊤ := by
  rw [secondMoment_map_eq P hΘ.aestronglyMeasurable.aemeasurable]
  exact (hΘ.integrable_norm_pow two_ne_zero).lintegral_lt_top.ne

/-- The law of a random element `Θ` of `F` under a probability measure `P`, as a law of finite
second moment: the image measure `P.map Θ` when `Θ` is square integrable, and the Dirac mass at
the origin otherwise. -/
noncomputable def lawP2 (P : Measure Ω) [IsProbabilityMeasure P] (Θ : Ω → F) : P2 F := by
  classical
  exact if h : MemLp Θ 2 P then
    { law := P.map Θ
      isProbabilityMeasure :=
        Measure.isProbabilityMeasure_map h.aestronglyMeasurable.aemeasurable
      secondMoment_ne_top := secondMoment_map_ne_top h }
  else P2.dirac 0

variable {P : Measure Ω} [IsProbabilityMeasure P] {Θ Θ' : Ω → F}

/-- The law of a square-integrable random element is its image measure. -/
theorem lawP2_law (hΘ : MemLp Θ 2 P) : (lawP2 P Θ).law = P.map Θ := by
  unfold lawP2
  rw [dif_pos hΘ]

/-- Off `L²` the law is the Dirac mass at the origin. -/
theorem lawP2_of_not_memLp (hΘ : ¬ MemLp Θ 2 P) : lawP2 P Θ = P2.dirac 0 := by
  unfold lawP2
  rw [dif_neg hΘ]

/-- The law of a random element depends only on its almost-everywhere class. -/
theorem lawP2_congr (h : Θ =ᵐ[P] Θ') : lawP2 P Θ = lawP2 P Θ' := by
  by_cases hΘ : MemLp Θ 2 P
  · have hΘ' : MemLp Θ' 2 P := (memLp_congr_ae h).mp hΘ
    exact P2.ext_law (by rw [lawP2_law hΘ, lawP2_law hΘ', Measure.map_congr h])
  · have hΘ' : ¬ MemLp Θ' 2 P := fun h' => hΘ ((memLp_congr_ae h).mpr h')
    rw [lawP2_of_not_memLp hΘ, lawP2_of_not_memLp hΘ']

variable [SecondCountableTopology F]

/-- **The coupling bound (2.8).** For square-integrable random elements `Θ, Θ'` on one
probability space, `W₂(Law Θ, Law Θ')² ≤ 𝔼‖Θ − Θ'‖²`. -/
theorem w2P_lawP2_sq_le (hΘ : MemLp Θ 2 P) (hΘ' : MemLp Θ' 2 P) :
    w2P (lawP2 P Θ) (lawP2 P Θ') ^ 2 ≤ ∫ ω, ‖Θ ω - Θ' ω‖ ^ 2 ∂P := by
  have ha := hΘ.aestronglyMeasurable.aemeasurable
  have ha' := hΘ'.aestronglyMeasurable.aemeasurable
  have hsub : (fun ω => ‖Θ ω - Θ' ω‖ ^ 2)
      =ᵐ[P] fun ω => ‖ha.mk Θ ω - ha'.mk Θ' ω‖ ^ 2 := by
    filter_upwards [ha.ae_eq_mk, ha'.ae_eq_mk] with ω h1 h2
    rw [h1, h2]
  have hint : Integrable (fun ω => ‖Θ ω - Θ' ω‖ ^ 2) P :=
    (hΘ.sub hΘ').integrable_norm_pow two_ne_zero
  rw [w2P, lawP2_law hΘ, lawP2_law hΘ', Measure.map_congr ha.ae_eq_mk,
    Measure.map_congr ha'.ae_eq_mk, integral_congr_ae hsub]
  exact w2_sq_map_le P ha.measurable_mk ha'.measurable_mk (hint.congr hsub)

/-- **The coupling bound (2.8) as a lower integral.** For square-integrable random elements
`Θ, Θ'` on one probability space, `W₂(Law Θ, Law Θ')² ≤ ∫⁻ ‖Θ − Θ'‖² dP`. -/
theorem ofReal_w2P_lawP2_sq_le (hΘ : MemLp Θ 2 P) (hΘ' : MemLp Θ' 2 P) :
    ENNReal.ofReal (w2P (lawP2 P Θ) (lawP2 P Θ') ^ 2)
      ≤ ∫⁻ ω, ENNReal.ofReal (‖Θ ω - Θ' ω‖ ^ 2) ∂P := by
  have hint : Integrable (fun ω => ‖Θ ω - Θ' ω‖ ^ 2) P :=
    (hΘ.sub hΘ').integrable_norm_pow two_ne_zero
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω => by positivity)]
  exact ENNReal.ofReal_le_ofReal (w2P_lawP2_sq_le hΘ hΘ')

end MVFBSDEJ.Law
