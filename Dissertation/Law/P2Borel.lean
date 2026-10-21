/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.P2Measurable
import Dissertation.Law.P2Quantize
import Dissertation.Law.P2Reweight

/-!
# The 2-Wasserstein Borel sets are evaluation measurable

On a separable Banach space `E`, every Borel set of the 2-Wasserstein space `P2W E` lies in the
evaluation σ-algebra of `P2 E`, the coarsest one making every `μ ↦ μ(A)` measurable: the identity
`P2 E → P2W E` is measurable from the evaluation σ-algebra to the Borel σ-algebra of `W₂`.

The identity is the pointwise `W₂`-limit of the quantisations `μ ↦ μ.quantize n`
(`Dissertation.Law.tendsto_quantize`), and a pointwise limit of measurable maps into a
pseudometrizable space is measurable. Each quantisation is measurable: `μ.quantize n` is the
finitely supported law `∑_y μ(quant n ⁻¹' {y}) δ_y` over the finite range of the quantiser, its
weight vector `(μ(quant n ⁻¹' {y}))_y` is an evaluation-measurable point of the standard simplex,
and the reweighting map from the simplex into `P2W E` is continuous
(`Dissertation.Law.continuous_finLaw`). The same two facts make `P2W E` separable: the finitely
supported laws over the ranges of the quantisers are dense, and for each `n` they form the
continuous image of a standard simplex.

## Main definitions

* `Dissertation.Law.quantWeightVec`, `Dissertation.Law.quantWeights`: the weight vector of the
  `n`-th quantised law.

## Main statements

* `Dissertation.Law.P2.quantize_eq_finLaw`: the quantised law is the reweighting of the range of
  the quantiser by `quantWeights`.
* `Dissertation.Law.measurable_quantWeights`: the weight vector is evaluation measurable.
* `Dissertation.Law.measurable_toP2W_quantize`: each quantisation is measurable into `P2W E`.
* `Dissertation.Law.measurable_toP2W`: the identity `P2 E → P2W E` is measurable, so every
  `W₂`-Borel set of laws is in the evaluation σ-algebra.
* `Dissertation.Law.P2W.instSeparableSpace`, `Dissertation.Law.P2W.instSecondCountableTopology`:
  the 2-Wasserstein space is separable and second countable.
* `Measurable.toP2W`: an evaluation-measurable map into `P2 E` is Borel measurable into `P2W E`.
-/

namespace Dissertation.Law

open MeasureTheory Filter Topology
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The masses `μ(quant n ⁻¹' {y})` of the fibres of the `n`-th quantiser over its finite
range. -/
noncomputable def quantWeightVec (n : ℕ) (μ : P2 E) : (quant n : SimpleFunc E E).range → ℝ :=
  fun y => (μ.law (quant n ⁻¹' {y.1})).toReal

/-- The fibre masses of the quantiser form a point of the standard simplex. -/
theorem quantWeightVec_mem (n : ℕ) (μ : P2 E) :
    quantWeightVec n μ ∈ stdSimplex ℝ (quant n : SimpleFunc E E).range := by
  refine ⟨fun _ => ENNReal.toReal_nonneg, ?_⟩
  simp only [quantWeightVec]
  rw [← ENNReal.toReal_sum fun y _ => measure_ne_top _ _,
    Finset.sum_coe_sort (s := (quant n).range) (f := fun y => μ.law (quant n ⁻¹' {y})),
    SimpleFunc.sum_measure_preimage_singleton]
  have h : (quant n : E → E) ⁻¹' ((quant n : SimpleFunc E E).range : Set E) = Set.univ := by
    ext x
    simp
  rw [h, measure_univ, ENNReal.toReal_one]

/-- The weight vector of the `n`-th quantised law, as a point of the standard simplex. -/
noncomputable def quantWeights (n : ℕ) (μ : P2 E) :
    stdSimplex ℝ (quant n : SimpleFunc E E).range :=
  ⟨quantWeightVec n μ, quantWeightVec_mem n μ⟩

/-- **The quantised law is a reweighting of the range of the quantiser**:
`μ.quantize n = ∑_{y ∈ range (quant n)} (quantWeights n μ)_y δ_y`. -/
theorem P2.quantize_eq_finLaw (n : ℕ) (μ : P2 E) :
    μ.quantize n
      = finLaw (fun y : (quant n : SimpleFunc E E).range => (y : E)) (quantWeights n μ) := by
  refine P2.ext_law ?_
  rw [P2.quantize_law, finLaw_law]
  simp only [quantWeights, quantWeightVec, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact (Finset.sum_coe_sort (s := (quant n).range)
    (f := fun y => μ.law (quant n ⁻¹' {y}) • Measure.dirac y)).symm

/-- The fibre masses of the quantiser depend measurably on the law, for the evaluation
σ-algebra. -/
theorem measurable_quantWeightVec (n : ℕ) : Measurable (quantWeightVec n : P2 E → _) :=
  measurable_pi_lambda _ fun y =>
    ((Measure.measurable_coe ((quant n).measurableSet_fiber y.1)).comp
      P2.measurable_law).ennreal_toReal

/-- The weight vector of the `n`-th quantised law depends measurably on the law, for the
evaluation σ-algebra. -/
theorem measurable_quantWeights (n : ℕ) :
    Measurable (quantWeights n : P2 E → stdSimplex ℝ (quant n : SimpleFunc E E).range) :=
  (measurable_quantWeightVec n).subtype_mk

variable [CompleteSpace E]

/-- **Each quantisation is measurable** from the evaluation σ-algebra into the 2-Wasserstein
space. -/
theorem measurable_toP2W_quantize (n : ℕ) :
    Measurable fun μ : P2 E => (μ.quantize n).toP2W := by
  have h := (continuous_finLaw
    (fun y : (quant n : SimpleFunc E E).range => (y : E))).measurable.comp
    (measurable_quantWeights n)
  have heq : (fun μ : P2 E => (μ.quantize n).toP2W)
      = (fun w => (finLaw (fun y : (quant n : SimpleFunc E E).range => (y : E)) w).toP2W)
        ∘ quantWeights n := by
    funext μ
    rw [Function.comp_apply, P2.quantize_eq_finLaw]
  rw [heq]
  exact h

/-- **The identity from the evaluation σ-algebra to the 2-Wasserstein Borel σ-algebra is
measurable.** -/
theorem measurable_toP2W : Measurable (P2.toP2W : P2 E → P2W E) :=
  measurable_of_tendsto_metrizable (f := fun n μ => (μ.quantize n).toP2W)
    measurable_toP2W_quantize (tendsto_pi_nhds.mpr fun μ => tendsto_quantize μ)

/-- **The 2-Wasserstein space of a separable Banach space is separable**: the finitely supported
laws on the ranges of the quantisers are dense, and for each `n` they form the continuous image
of a standard simplex. -/
instance P2W.instSeparableSpace : TopologicalSpace.SeparableSpace (P2W E) := by
  set S : ℕ → Set (P2W E) := fun n =>
    Set.range fun w : stdSimplex ℝ (quant n : SimpleFunc E E).range =>
      (finLaw (fun y : (quant n : SimpleFunc E E).range => (y : E)) w).toP2W with hS
  have hsep : TopologicalSpace.IsSeparable (closure (⋃ n, S n)) :=
    (TopologicalSpace.IsSeparable.iUnion fun n =>
      TopologicalSpace.isSeparable_range (continuous_finLaw _)).closure
  have hdense : closure (⋃ n, S n) = Set.univ := by
    refine Set.eq_univ_of_forall fun μ => ?_
    refine mem_closure_of_tendsto (tendsto_quantize μ.toP2)
      (Eventually.of_forall fun n => Set.mem_iUnion.mpr ⟨n, quantWeights n μ.toP2, ?_⟩)
    rw [P2.quantize_eq_finLaw]
  rw [hdense] at hsep
  exact TopologicalSpace.isSeparable_univ_iff.mp hsep

/-- The 2-Wasserstein space of a separable Banach space is second countable. -/
instance P2W.instSecondCountableTopology : SecondCountableTopology (P2W E) :=
  UniformSpace.secondCountable_of_separable (P2W E)

end Dissertation.Law

open Dissertation.Law in
/-- An evaluation-measurable map into the laws of finite second moment is Borel measurable into
the 2-Wasserstein space. -/
theorem Measurable.toP2W {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {α : Type*} [MeasurableSpace α] {f : α → P2 E}
    (hf : Measurable f) : Measurable fun a => (f a).toP2W :=
  measurable_toP2W.comp hf
