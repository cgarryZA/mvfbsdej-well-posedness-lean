/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import MVFBSDEJ.Law.LipschitzFunctional

/-!
# Gluing two couplings along a common marginal

Two couplings `γ₁` of `(μ, ν)` and `γ₂` of `(ν, ρ)` on a standard Borel space are glued by
disintegrating each along the marginal `ν` they share and composing `ν` with the product of the
two conditional kernels. The result is a measure on `E × E × E` with three projections onto pairs
of coordinates: the first two coordinates carry `γ₁`, the first and the last carry `γ₂`, and the
last two carry a coupling of `(μ, ρ)`. A conditional kernel disintegrates a measure along its
first coordinate, so `γ₁` enters the construction with its coordinates exchanged.

## Main definitions

* `MVFBSDEJ.Law.glue`: the composition of a law on `E` with the product of two kernels on `E`.

## Main statements

* `MVFBSDEJ.Law.transportCostSq_map`: the quadratic transport cost of the joint law of a pair
  of measurable maps is the integral of the squared norm of their difference.
* `MVFBSDEJ.Law.glue_map_fst`, `MVFBSDEJ.Law.glue_map_snd`: the two flat projections of a
  glued measure are the compositions of the base law with the two kernels.
* `MVFBSDEJ.Law.isCoupling_glue_snd`: the remaining projection of a measure on `E × E × E`
  with prescribed flat projections couples the two outer laws.
* `MVFBSDEJ.Law.exists_glue`: two couplings along a common marginal are the flat projections
  of a measure on `E × E × E`.

Disintegration requires the space to be standard Borel, which for a normed space follows from
completeness and second countability.
-/

namespace MVFBSDEJ.Law

open MeasureTheory ProbabilityTheory
open scoped ENNReal

section Cost

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The quadratic transport cost of the joint law of a pair of measurable maps. -/
theorem transportCostSq_map {Ω : Type*} [MeasurableSpace Ω] (Γ : Measure Ω) {X Y : Ω → E}
    (hX : Measurable X) (hY : Measurable Y) :
    transportCostSq (Γ.map fun ω => (X ω, Y ω))
      = ∫⁻ ω, ENNReal.ofReal (‖X ω - Y ω‖ ^ 2) ∂Γ := by
  rw [transportCostSq, lintegral_map measurable_normSq_sub (by fun_prop)]

end Cost

section Glue

variable {E : Type*} [MeasurableSpace E]

/-- The composition of a law on `E` with the product of two kernels on `E`. -/
noncomputable def glue (ν : Measure E) (k₁ k₂ : Kernel E E) : Measure (E × E × E) :=
  ν ⊗ₘ (k₁ ×ₖ k₂)

/-- The first flat projection of a glued measure. -/
theorem glue_map_fst (ν : Measure E) [SFinite ν] (k₁ k₂ : Kernel E E)
    [IsMarkovKernel k₁] [IsMarkovKernel k₂] :
    (glue ν k₁ k₂).map (Prod.map id Prod.fst) = ν ⊗ₘ k₁ := by
  rw [glue, ← Measure.compProd_map measurable_fst, ← Kernel.fst_eq, Kernel.fst_prod]

/-- The second flat projection of a glued measure. -/
theorem glue_map_snd (ν : Measure E) [SFinite ν] (k₁ k₂ : Kernel E E)
    [IsMarkovKernel k₁] [IsMarkovKernel k₂] :
    (glue ν k₁ k₂).map (Prod.map id Prod.snd) = ν ⊗ₘ k₂ := by
  rw [glue, ← Measure.compProd_map measurable_snd, ← Kernel.snd_eq, Kernel.snd_prod]

/-- The remaining projection of a measure on `E × E × E` with prescribed flat projections couples
the two outer laws. -/
theorem isCoupling_glue_snd {μ ν ρ : Measure E} {γ₁ γ₂ : Measure (E × E)}
    (h₁ : IsCoupling ν μ γ₁) (h₂ : IsCoupling ν ρ γ₂) {Γ : Measure (E × E × E)}
    (hA : Γ.map (Prod.map id Prod.fst) = γ₁) (hB : Γ.map (Prod.map id Prod.snd) = γ₂) :
    IsCoupling μ ρ (Γ.map fun p => (p.2.1, p.2.2)) := by
  have hm : Measurable fun p : E × E × E => (p.2.1, p.2.2) := by fun_prop
  refine ⟨?_, ?_⟩
  · have e₁ : (Γ.map fun p : E × E × E => (p.2.1, p.2.2)).fst = Γ.map fun p => p.2.1 := by
      rw [Measure.fst, Measure.map_map measurable_fst hm]
      rfl
    have e₂ : γ₁.snd = Γ.map fun p : E × E × E => p.2.1 := by
      rw [← hA, Measure.snd, Measure.map_map measurable_snd (by fun_prop)]
      rfl
    rw [e₁, ← e₂, h₁.2]
  · have e₁ : (Γ.map fun p : E × E × E => (p.2.1, p.2.2)).snd = Γ.map fun p => p.2.2 := by
      rw [Measure.snd, Measure.map_map measurable_snd hm]
      rfl
    have e₂ : γ₂.snd = Γ.map fun p : E × E × E => p.2.2 := by
      rw [← hB, Measure.snd, Measure.map_map measurable_snd (by fun_prop)]
      rfl
    rw [e₁, ← e₂, h₂.2]

variable [StandardBorelSpace E] [Nonempty E]

/-- Two couplings along a common marginal are the flat projections of a measure on `E × E × E`,
the second coupling in the given order and the first with its coordinates exchanged. -/
theorem exists_glue {μ ν ρ : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] {γ₁ γ₂ : Measure (E × E)} (h₁ : IsCoupling μ ν γ₁)
    (h₂ : IsCoupling ν ρ γ₂) :
    ∃ Γ : Measure (E × E × E), Γ.map (Prod.map id Prod.fst) = γ₁.map Prod.swap ∧
      Γ.map (Prod.map id Prod.snd) = γ₂ := by
  have hp₁ : IsProbabilityMeasure (γ₁.map Prod.swap) :=
    isProbabilityMeasure_of_isCoupling (isCoupling_swap h₁)
  have hp₂ : IsProbabilityMeasure γ₂ := isProbabilityMeasure_of_isCoupling h₂
  refine ⟨glue ν (γ₁.map Prod.swap).condKernel γ₂.condKernel, ?_, ?_⟩
  · rw [glue_map_fst]
    conv_rhs => rw [← Measure.disintegrate (γ₁.map Prod.swap) (γ₁.map Prod.swap).condKernel]
    rw [(isCoupling_swap h₁).1]
  · rw [glue_map_snd]
    conv_rhs => rw [← Measure.disintegrate γ₂ γ₂.condKernel]
    rw [h₂.1]

end Glue

end MVFBSDEJ.Law
