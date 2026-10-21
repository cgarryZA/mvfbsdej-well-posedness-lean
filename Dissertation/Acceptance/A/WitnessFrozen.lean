/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Acceptance.A.Witness
import Dissertation.PaperSpec.A.Sec4Frozen

/-!
# An instance of the hypotheses of the frozen step of Lemma 4.2 of paper A

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The instance is
that of `Dissertation.Acceptance.A.thm_cwp_hypotheses`: a Lévy driver with `d = 1` and `ν = δ₀` on
`ℝ`, `𝒢₀ = ⊥`, `n = m = 1`, `T = 1`, and the system of Example 5.1(i) with `β₁ = β₂ = 1`,
`σ_c = h_c = 0` and initial datum `0`.

## Main statements

* `Dissertation.Acceptance.A.hTuple_const` — a tuple with constant `X`, `Y` and zero `Z`, `U` lies
  in `𝕊`.
* `Dissertation.Acceptance.A.frozen_hypotheses` — the hypotheses of (4.7)–(4.9) at `λ = 1`, the
  zero forcing and two distinct trial tuples of `𝕊`: the zero tuple and the constant tuple
  `(1, 1, 0, 0)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.PaperSpec.A
  Dissertation.WellPosedness.Stability LevyStochCalc

universe w

/-- The system of Example 5.1(i) with `n = d = 1`, `ν = δ₀` on `ℝ`, `β₁ = β₂ = β`, `σ_c = 0` and
`h_c = 0`. -/
local notation "sys " β:max =>
  affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) β β 0 0

/-- A tuple with constant `X ≡ a`, `Y ≡ b` and zero `Z`, `U` lies in `𝕊` over every filtration,
for every finite measure and on every horizon. -/
theorem hTuple_const {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) [IsFiniteMeasure P] (T a b : ℝ) :
    HTuple ℱ P ν T (fun (_ : Fin n) _ _ => a) (fun (_ : Fin m) _ _ => b)
      (fun (_ : Fin m) _ _ (_ : Fin d) => (0 : ℝ)) (fun (_ : Fin m) _ _ (_ : E) => (0 : ℝ)) := by
  have hen : ∀ c : ℝ, Brownian.Ito.energy P T (fun _ _ => c) ≠ ⊤ := fun c => by
    simp only [Brownian.Ito.energy, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Real.volume_Icc]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
      (measure_ne_top P _)
  have hsup : ∀ {ι : Type} [Fintype ι] (c : ℝ),
      ∫⁻ _, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun (_ : ι) => c)) ∂P < ⊤ := fun c =>
    (lintegral_mono fun _ => iSup₂_le fun _ _ => le_rfl).trans_lt (by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top (by simp [esq, ENNReal.mul_lt_top]) (measure_lt_top P _))
  refine ⟨{ X_adapted := fun _ _ _ => measurable_const
            X_rightCont := fun _ _ _ _ => tendsto_const_nhds
            X_leftLim := fun _ => ae_of_all _ fun _ _ _ => ⟨a, tendsto_const_nhds⟩
            X_sq := fun _ => hen a
            Y_adapted := fun _ _ _ => measurable_const
            Y_rightCont := fun _ _ _ _ => tendsto_const_nhds
            Y_leftLim := fun _ => ae_of_all _ fun _ _ _ => ⟨b, tendsto_const_nhds⟩
            Y_sq := fun _ => hen b
            Z_pred := fun _ _ => stronglyMeasurable_const
            Z_vanish := fun _ _ _ _ => rfl
            Z_sq := fun _ _ => by simp [Brownian.Ito.energy]
            U_pred := fun _ => measurable_const
            U_vanish := fun _ _ _ _ _ => rfl
            U_sq := fun _ => by simp [Poisson.Compensated.markedEnergy] },
    fun _ _ _ _ => ⟨a, tendsto_const_nhds⟩, fun _ _ _ _ => ⟨b, tendsto_const_nhds⟩,
    hsup a, hsup b⟩

/-- **The hypotheses of the frozen step of Lemma 4.2 hold at Example 5.1(i).** At the instance of
`thm_cwp_hypotheses`, the system with initial datum `0` satisfies (2.3) and Assumptions 2.2–2.3
with `L = 1`; the zero forcing is a forcing of (4.1) in the class of the paper; and the zero tuple
and the constant tuple `(X, Y, Z, U) = (1, 1, 0, 0)` are two distinct trial tuples of `𝕊`. -/
theorem frozen_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver.{0, 0, w} P 1 (Measure.dirac (0 : ℝ)))
      (_ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 (sys 1)
      ∧ Assumption22 (enlJoint ⊥ D bot_le) P 1 (sys 1) (fun _ => 0)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1 (sys 1)
      ∧ PredForcing (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1
          (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (0 : Fin 1 → ℝ → Ω → ℝ → ℝ)
          (0 : Fin 1 → Ω → ℝ → ℝ) (0 : Fin 1 → Ω → ℝ)
      ∧ HTuple (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1
          (fun (_ : Fin 1) _ _ => (0 : ℝ)) (fun (_ : Fin 1) _ _ => (0 : ℝ))
          (fun (_ : Fin 1) _ _ (_ : Fin 1) => (0 : ℝ)) (fun (_ : Fin 1) _ _ (_ : ℝ) => (0 : ℝ))
      ∧ HTuple (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1
          (fun (_ : Fin 1) _ _ => (1 : ℝ)) (fun (_ : Fin 1) _ _ => (1 : ℝ))
          (fun (_ : Fin 1) _ _ (_ : Fin 1) => (0 : ℝ))
          (fun (_ : Fin 1) _ _ (_ : ℝ) => (0 : ℝ)) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  obtain ⟨hJ, h22, h23, -, -⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (0 : EuclideanSpace ℝ (Fin 1))
  have e : max (max (1 : ℝ) 1) 1 = 1 := by norm_num
  rw [e] at h23
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, hJ, h22, h23,
    { toForcing := Forcing.zero, qh_pred := fun _ => measurable_const },
    hTuple_const _ P 1 0 0, hTuple_const _ P 1 1 1⟩

end Dissertation.Acceptance.A
