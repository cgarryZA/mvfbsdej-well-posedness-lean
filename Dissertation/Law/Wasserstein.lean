/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The 2-Wasserstein distance on the laws of a normed space

A coupling of two laws `μ, ν` on a normed space `E` is a measure on `E × E` whose first and
second marginals are `μ` and `ν`. Its quadratic transport cost is the `ℝ≥0∞`-valued integral
`∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) ∂γ`, the squared 2-Wasserstein distance `w2sq μ ν` is
the infimum of that cost over the couplings of `μ` and `ν`, and `w2 μ ν` is the square root of
the real part of `w2sq μ ν`.

## Main definitions

* `Dissertation.Law.IsCoupling`: a measure on the product with two prescribed marginals.
* `Dissertation.Law.transportCostSq`: the quadratic transport cost of a measure on the product.
* `Dissertation.Law.w2sq`: the infimum of the quadratic transport cost over the couplings.
* `Dissertation.Law.w2`: the square root of the real part of the squared distance.
* `Dissertation.Law.secondMoment`: the second moment of a law about the origin.

## Main statements

* `Dissertation.Law.isCoupling_prod`: the product measure couples two probability measures.
* `Dissertation.Law.w2sq_le_transportCostSq`: every coupling bounds the squared distance above.
* `Dissertation.Law.w2sq_self`, `Dissertation.Law.w2_self`: the distance of a law from itself is
  zero.
* `Dissertation.Law.w2sq_comm`, `Dissertation.Law.w2_comm`: symmetry in the two laws.
* `Dissertation.Law.w2sq_dirac`: the squared distance to a Dirac mass at `a` equals the second
  moment about `a`.
* `Dissertation.Law.w2sq_ne_top_of_secondMoment_ne_top`: two laws of finite second moment are at
  finite squared distance.

Reflexivity and symmetry are available for `w2` here, and on a separable Banach space so are the
triangle inequality, in `Dissertation/Law/Triangle.lean`, and separation, the vanishing of the
distance forcing the two laws to agree, in `Dissertation/Law/P2Separation.lean`. The real-valued
`w2` sends an infinite squared distance to `0`, so every real-valued statement carries a
hypothesis forcing the squared distance to be finite.
-/

namespace Dissertation.Law

open MeasureTheory
open scoped ENNReal

/-! ### Couplings -/

section Coupling

variable {E : Type*} [MeasurableSpace E]

/-- A coupling of two laws: a measure on the product whose marginals are the two given laws. -/
def IsCoupling (μ ν : Measure E) (γ : Measure (E × E)) : Prop := γ.fst = μ ∧ γ.snd = ν

/-- The product measure couples two probability measures. -/
theorem isCoupling_prod (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsCoupling μ ν (μ.prod ν) :=
  ⟨Measure.fst_prod, Measure.snd_prod⟩

/-- The diagonal coupling of a law with itself. -/
theorem isCoupling_diagonal (μ : Measure E) : IsCoupling μ μ (μ.map fun x => (x, x)) := by
  refine ⟨?_, ?_⟩
  · have h := Measure.fst_map_prodMk (X := (id : E → E)) (Y := (id : E → E)) (μ := μ) measurable_id
    simpa [Measure.map_id] using h
  · have h := Measure.snd_map_prodMk (X := (id : E → E)) (Y := (id : E → E)) (μ := μ) measurable_id
    simpa [Measure.map_id] using h

/-- Swapping the two coordinates turns a coupling into a coupling of the same laws in the
opposite order. -/
theorem isCoupling_swap {μ ν : Measure E} {γ : Measure (E × E)} (hγ : IsCoupling μ ν γ) :
    IsCoupling ν μ (γ.map Prod.swap) := by
  obtain ⟨h1, h2⟩ := hγ
  constructor
  · rw [Measure.fst, Measure.map_map measurable_fst measurable_swap]
    exact h2
  · rw [Measure.snd, Measure.map_map measurable_snd measurable_swap]
    exact h1

/-- The graph of a constant map couples a law with the Dirac mass at the value of that map. -/
theorem isCoupling_dirac (μ : Measure E) [IsProbabilityMeasure μ] (a : E) :
    IsCoupling μ (Measure.dirac a) (μ.map fun x => (x, a)) := by
  refine ⟨?_, ?_⟩
  · have h := Measure.fst_map_prodMk (X := (id : E → E)) (Y := fun _ : E => a) (μ := μ)
      measurable_const
    simpa [Measure.map_id] using h
  · have h := Measure.snd_map_prodMk (X := (id : E → E)) (Y := fun _ : E => a) (μ := μ)
      measurable_id
    simpa [Measure.map_const, measure_univ] using h

end Coupling

/-! ### The squared 2-Wasserstein distance -/

section Defs

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

/-- The quadratic transport cost of a measure on the product. -/
noncomputable def transportCostSq (γ : Measure (E × E)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) ∂γ

/-- The squared 2-Wasserstein distance: the infimum of the quadratic transport cost over the
couplings of the two laws. -/
noncomputable def w2sq (μ ν : Measure E) : ℝ≥0∞ :=
  ⨅ γ, ⨅ _ : IsCoupling μ ν γ, transportCostSq γ

/-- The 2-Wasserstein distance as a real number: the square root of the real part of the squared
distance. -/
noncomputable def w2 (μ ν : Measure E) : ℝ := Real.sqrt (w2sq μ ν).toReal

/-- The second moment of a law about the origin. -/
noncomputable def secondMoment (μ : Measure E) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂μ

/-- Every coupling bounds the squared 2-Wasserstein distance from above. -/
theorem w2sq_le_transportCostSq {μ ν : Measure E} {γ : Measure (E × E)}
    (hγ : IsCoupling μ ν γ) : w2sq μ ν ≤ transportCostSq γ :=
  iInf₂_le γ hγ

/-- The 2-Wasserstein distance is nonnegative. -/
theorem w2_nonneg (μ ν : Measure E) : 0 ≤ w2 μ ν := Real.sqrt_nonneg _

end Defs

/-! ### Reflexivity and symmetry -/

section Cost

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The squared distance between the two coordinates of a product is measurable. -/
theorem measurable_normSq_sub :
    Measurable fun p : E × E => ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) := by
  fun_prop

/-- The diagonal coupling has zero quadratic transport cost. -/
theorem transportCostSq_diagonal (μ : Measure E) :
    transportCostSq (μ.map fun x => (x, x)) = 0 := by
  rw [transportCostSq, lintegral_map measurable_normSq_sub (by fun_prop)]
  simp

/-- The squared 2-Wasserstein distance of a law from itself vanishes. -/
theorem w2sq_self (μ : Measure E) : w2sq μ μ = 0 :=
  le_antisymm (by simpa [transportCostSq_diagonal μ] using
    w2sq_le_transportCostSq (isCoupling_diagonal μ)) bot_le

/-- The 2-Wasserstein distance of a law from itself vanishes. -/
theorem w2_self (μ : Measure E) : w2 μ μ = 0 := by simp [w2, w2sq_self]

/-- Swapping the two coordinates preserves the quadratic transport cost. -/
theorem transportCostSq_swap (γ : Measure (E × E)) :
    transportCostSq (γ.map Prod.swap) = transportCostSq γ := by
  rw [transportCostSq, lintegral_map measurable_normSq_sub measurable_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  exact lintegral_congr fun p => by rw [norm_sub_rev]

/-- The squared 2-Wasserstein distance is symmetric in the two laws. -/
theorem w2sq_comm (μ ν : Measure E) : w2sq μ ν = w2sq ν μ := by
  refine le_antisymm ?_ ?_ <;>
  · refine le_iInf₂ fun γ hγ => ?_
    rw [← transportCostSq_swap γ]
    exact w2sq_le_transportCostSq (isCoupling_swap hγ)

/-- The 2-Wasserstein distance is symmetric in the two laws. -/
theorem w2_comm (μ ν : Measure E) : w2 μ ν = w2 ν μ := by rw [w2, w2, w2sq_comm]

end Cost

/-! ### The distance to a Dirac mass -/

section Dirac

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- Every coupling of a law with a Dirac mass is carried by the graph of the constant map. -/
theorem ae_snd_eq_of_isCoupling_dirac {μ : Measure E} {a : E} {γ : Measure (E × E)}
    (hγ : IsCoupling μ (Measure.dirac a) γ) : ∀ᵐ p ∂γ, p.2 = a := by
  have hset : γ (Prod.snd ⁻¹' {a}ᶜ) = 0 := by
    have : γ.snd {a}ᶜ = 0 := by
      rw [hγ.2]
      simp
    rwa [Measure.snd, Measure.map_apply measurable_snd ((measurableSet_singleton a).compl)] at this
  refine measure_mono_null (fun p hp => ?_) hset
  simpa using hp

variable [SecondCountableTopology E]

/-- The squared 2-Wasserstein distance to a Dirac mass is the second moment about that point. -/
theorem w2sq_dirac (μ : Measure E) [IsProbabilityMeasure μ] (a : E) :
    w2sq μ (Measure.dirac a) = ∫⁻ x, ENNReal.ofReal (‖x - a‖ ^ 2) ∂μ := by
  refine le_antisymm ?_ (le_iInf₂ fun γ hγ => ?_)
  · refine (w2sq_le_transportCostSq (isCoupling_dirac μ a)).trans ?_
    rw [transportCostSq, lintegral_map (g := fun x : E => (x, a)) measurable_normSq_sub
      (by fun_prop)]
  · rw [transportCostSq]
    have hae : (fun p : E × E => ENNReal.ofReal (‖p.1 - p.2‖ ^ 2))
        =ᵐ[γ] fun p => ENNReal.ofReal (‖p.1 - a‖ ^ 2) := by
      filter_upwards [ae_snd_eq_of_isCoupling_dirac hγ] with p hp
      rw [hp]
    rw [lintegral_congr_ae hae]
    have : ∫⁻ p, ENNReal.ofReal (‖p.1 - a‖ ^ 2) ∂γ
        = ∫⁻ x, ENNReal.ofReal (‖x - a‖ ^ 2) ∂γ.fst := by
      rw [Measure.fst, lintegral_map (by fun_prop) measurable_fst]
    rw [this, hγ.1]

end Dirac

/-! ### Finiteness on the laws of finite second moment -/

section Finite

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- Laws of finite second moment are at finite squared 2-Wasserstein distance. -/
theorem w2sq_ne_top_of_secondMoment_ne_top {μ ν : Measure E} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : secondMoment μ ≠ ⊤) (hν : secondMoment ν ≠ ⊤) :
    w2sq μ ν ≠ ⊤ := by
  have hle : transportCostSq (μ.prod ν)
      ≤ 2 * secondMoment μ + 2 * secondMoment ν := by
    rw [transportCostSq]
    calc ∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) ∂(μ.prod ν)
        ≤ ∫⁻ p : E × E, (2 * ENNReal.ofReal (‖p.1‖ ^ 2) + 2 * ENNReal.ofReal (‖p.2‖ ^ 2))
            ∂(μ.prod ν) := by
          refine lintegral_mono fun p => ?_
          have h : ‖p.1 - p.2‖ ^ 2 ≤ 2 * ‖p.1‖ ^ 2 + 2 * ‖p.2‖ ^ 2 := by
            have h1 : ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
            nlinarith [norm_nonneg p.1, norm_nonneg p.2, norm_nonneg (p.1 - p.2),
              sq_nonneg (‖p.1‖ - ‖p.2‖)]
          calc ENNReal.ofReal (‖p.1 - p.2‖ ^ 2)
              ≤ ENNReal.ofReal (2 * ‖p.1‖ ^ 2 + 2 * ‖p.2‖ ^ 2) := ENNReal.ofReal_le_ofReal h
            _ = 2 * ENNReal.ofReal (‖p.1‖ ^ 2) + 2 * ENNReal.ofReal (‖p.2‖ ^ 2) := by
                rw [ENNReal.ofReal_add (by positivity) (by positivity),
                  ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
                norm_num
      _ = 2 * secondMoment μ + 2 * secondMoment ν := by
          have h1 : ∫⁻ p : E × E, ENNReal.ofReal (‖p.1‖ ^ 2) ∂(μ.prod ν) = secondMoment μ := by
            rw [lintegral_prod _ (by fun_prop)]
            simp [secondMoment]
          have h2 : ∫⁻ p : E × E, ENNReal.ofReal (‖p.2‖ ^ 2) ∂(μ.prod ν) = secondMoment ν := by
            rw [lintegral_prod _ (by fun_prop)]
            simp [secondMoment]
          rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
            lintegral_const_mul _ (by fun_prop), h1, h2]
  refine ne_top_of_le_ne_top ?_ ((w2sq_le_transportCostSq (isCoupling_prod μ ν)).trans hle)
  exact (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hμ,
    ENNReal.mul_ne_top (by norm_num) hν⟩)

end Finite

end Dissertation.Law
