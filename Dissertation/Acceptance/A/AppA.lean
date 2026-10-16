/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.AppA

/-!
# Lemma A.1 of the well-posedness paper: proofs

## Main statements

* `Dissertation.Acceptance.A.lem_lawflow` — the canonical law flows `μ`, `μ⁻` are Borel,
  represent the laws of `Θ_t`, `Θ⁻_t` and agree almost everywhere.
* `Dissertation.Acceptance.A.lem_lawflow_invariant` — the flows are unique up to null sets of
  times, and coefficient evaluations do not depend on the versions of the integrands and of the
  flow.
* `Dissertation.Acceptance.A.lem_lawflow_hypotheses`, `lem_lawflow_invariant_hypotheses` — their
  hypotheses hold.
-/

open MeasureTheory

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.Law

universe u v w

/-- Lemma A.1, the Borel law flows. -/
theorem lem_lawflow : PaperSpec.A.lem_lawflow.{u, v} := by
  intro Ω mΩ ℱ P _ E _ ν _ _ n m d T X Y Z U hΘ
  refine ⟨hΘ.measurable_lawFlow, hΘ.measurable_lawFlow_leftLim, ?_⟩
  filter_upwards [hΘ.ae_memLp_law_eq, hΘ.ae_memLp_law_eq_leftLim, hΘ.ae_lawFlow_leftLim_eq] with
    s h1 h2 h3
  exact ⟨h1.2, h2.2, h3.symm⟩

/-- Lemma A.1, uniqueness and invariance. -/
theorem lem_lawflow_invariant : PaperSpec.A.lem_lawflow_invariant.{u, v, w} := by
  intro Ω _ P _ E _ ν _ _ n m d T X Y Z Z' U U' ρ ρ' W ψ hZ hU hρ hρ'
  refine ⟨?_, ae_eval_eq_of_ae_eq ψ hZ hU hρ hρ'⟩
  filter_upwards [hρ, hρ', ae_ae_tupleAt_eq_of_ae_eq (X := X) (Y := Y) hZ hU] with s h h' hs
  exact P2.ext_law (by rw [h, h', Measure.map_congr hs])

/-- **The hypothesis of the law flows holds** for the zero tuple on a one-point space. -/
theorem lem_lawflow_hypotheses :
    CadlagPredTuple (⊥ : Filtration ℝ (inferInstance : MeasurableSpace Unit)) (Measure.dirac ())
      (Measure.dirac (0 : ℝ)) 1 (n := 1) (m := 1) (d := 1) (fun _ _ _ => 0) (fun _ _ _ => 0)
      (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) where
  X_adapted _ _ := measurable_const
  X_rightCont _ _ _ := tendsto_const_nhds
  X_leftLim _ _ _ := ⟨0, tendsto_const_nhds⟩
  Y_adapted _ _ := measurable_const
  Y_rightCont _ _ _ := tendsto_const_nhds
  Y_leftLim _ _ _ := ⟨0, tendsto_const_nhds⟩
  Z_pred _ _ := stronglyMeasurable_const
  U_pred _ := measurable_const
  X_sq _ := by simp [LevyStochCalc.Brownian.Ito.energy]
  Y_sq _ := by simp [LevyStochCalc.Brownian.Ito.energy]
  Z_sq _ _ := by simp [LevyStochCalc.Brownian.Ito.energy]
  U_sq _ := by simp [LevyStochCalc.Poisson.Compensated.markedEnergy]

/-- **The hypotheses of the invariance hold** on a one-point probability space: for every tuple
of processes, the law flow `s ↦ Law(Θ_s)` represents the laws of `Θ`. -/
theorem lem_lawflow_invariant_hypotheses (X : Fin 1 → ℝ → Unit → ℝ) (Y : Fin 1 → ℝ → Unit → ℝ)
    (Z : Fin 1 → ℝ → Unit → Fin 1 → ℝ) (U : Fin 1 → ℝ → Unit → ℝ → ℝ) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      (lawP2 (Measure.dirac ()) (tupleAt (Measure.dirac (0 : ℝ)) X Y Z U s)).law
        = (Measure.dirac ()).map (tupleAt (Measure.dirac (0 : ℝ)) X Y Z U s) := by
  refine Filter.Eventually.of_forall fun s => lawP2_law ?_
  have hc : tupleAt (Measure.dirac (0 : ℝ)) X Y Z U s
      = fun _ => tupleAt (Measure.dirac (0 : ℝ)) X Y Z U s () := by
    funext ω
    rfl
  rw [hc]
  exact memLp_const _

end Dissertation.Acceptance.A
