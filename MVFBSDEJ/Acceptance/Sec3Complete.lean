/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec3Space
import MVFBSDEJ.WellPosedness.System.Completeness
import MVFBSDEJ.Acceptance.WitnessNonzero

/-!
# Completeness of the solution space of §3 of the well-posedness paper: proofs

## Main statements

* `MVFBSDEJ.Acceptance.sec3_HH_complete` — `(ℍ, ‖·‖_ℍ)` is complete.
* `MVFBSDEJ.Acceptance.sec3_HH_complete_hypotheses` — the constant sequence at the tuple
  `(1, 1, 1_{(0, 1]}, 1_{(0, 1]})` of `ℍ_weak`, with `‖·‖²_ℍ = 4`, is Cauchy.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Enlarged LevyStochCalc

universe u v w

/-- §3, `(ℍ, ‖·‖_ℍ)` is complete. -/
theorem sec3_HH_complete : PaperSpec.sec3_HH_complete.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ T X Y Z U hΘ hfin hcau
  exact PaperWeakTuple.exists_supSize_limit (enlJoint 𝒢₀ D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hΘ hfin hcau

/-- **The hypotheses of the completeness of `ℍ` can be met by a nonzero sequence.** Over a
probability space carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`,
`n = m = 1` and `T = 1`, the constant sequence at `X = Y = 1`, `Z = U = 1_{(0, 1]}` is a sequence
of tuples of `ℍ_weak` with `‖Θ_j‖²_ℍ = 4`, and it is Cauchy for `‖·‖_ℍ`. -/
theorem sec3_HH_complete_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (X : ℕ → Fin 1 → ℝ → Ω → ℝ) (Y : ℕ → Fin 1 → ℝ → Ω → ℝ)
      (Z : ℕ → Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U : ℕ → Fin 1 → ℝ → Ω → ℝ → ℝ),
      (∀ j, PaperWeakTuple (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1
        (X j) (Y j) (Z j) (U j))
      ∧ (∀ j, supSize P (Measure.dirac (0 : ℝ)) 1 (X j) (Y j) (Z j) (U j) = 4)
      ∧ ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
        supSize P (Measure.dirac (0 : ℝ)) 1 (fun i t ω => X j i t ω - X k i t ω)
          (fun l t ω => Y j l t ω - Y k l t ω) (fun l t ω a => Z j l t ω a - Z k l t ω a)
          (fun l t ω e => U j l t ω e - U k l t ω e) < ε := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  set ℱ := enlJoint ⊥ D bot_le
  have hE : Brownian.Ito.energy P 1 (fun (_ : Ω) s => unitWindow s) = 1 := by
    simp [Brownian.Ito.energy, setLIntegral_unitWindow_sq]
  have hEm : Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1
      (fun (_ : Ω) s (_ : ℝ) => unitWindow s) = 1 := by
    simp [Poisson.Compensated.markedEnergy, setLIntegral_unitWindow_sq]
  have hE1 : Brownian.Ito.energy P 1 (fun (_ : Ω) (_ : ℝ) => (1 : ℝ)) = 1 := by
    simp [Brownian.Ito.energy]
  have hS1 : ∫⁻ (_ : Ω), (⨆ t ∈ Set.Icc (0 : ℝ) 1, esq (fun (_ : Fin 1) => (1 : ℝ))) ∂P = 1 := by
    rw [biSup_const ⟨0, Set.left_mem_Icc.mpr zero_le_one⟩]
    simp [esq]
  refine ⟨Ω, inferInstance, P, inferInstance, D, fun _ _ _ _ => 1, fun _ _ _ _ => 1,
    fun _ _ s _ _ => unitWindow s, fun _ _ s _ _ => unitWindow s, fun _ => ?_, fun _ => ?_, ?_⟩
  · exact
    { X_adapted := fun _ _ _ => measurable_const
      X_rightCont := fun _ _ _ _ => tendsto_const_nhds
      X_leftLim := fun _ => Eventually.of_forall fun _ _ _ => ⟨1, tendsto_const_nhds⟩
      X_sq := fun _ => by rw [hE1]; exact ENNReal.one_ne_top
      Y_adapted := fun _ _ _ => measurable_const
      Y_rightCont := fun _ _ _ _ => tendsto_const_nhds
      Y_leftLim := fun _ => Eventually.of_forall fun _ _ _ => ⟨1, tendsto_const_nhds⟩
      Y_sq := fun _ => by rw [hE1]; exact ENNReal.one_ne_top
      Z_pred := fun _ _ => predictable_unitWindow ℱ
      Z_vanish := fun _ _ _ hs => funext fun _ => unitWindow_of_notMem hs
      Z_sq := fun _ _ => by rw [hE]; exact ENNReal.one_ne_top
      U_pred := fun _ => markedPredictable_unitWindow ℱ (Measure.dirac (0 : ℝ))
      U_vanish := fun _ _ _ _ hs => unitWindow_of_notMem hs
      U_sq := fun _ => by rw [hEm]; exact ENNReal.one_ne_top }
  · simp only [supSize, hS1, hE, hEm, Finset.univ_unique, Finset.sum_singleton]
    norm_num
  · intro ε hε
    refine ⟨0, fun j _ k _ => ?_⟩
    simp only [supSize, sub_self]
    simp [esq, Brownian.Ito.energy, Poisson.Compensated.markedEnergy, hε]

end MVFBSDEJ.Acceptance
