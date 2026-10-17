/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3Rem34Exist
import Dissertation.WellPosedness.Spec.Bridge22
import Dissertation.WellPosedness.Spec.Bridge25
import Dissertation.WellPosedness.Examples.SingularDrift
import LevyStochCalc.Driver.Existence

/-!
# Remark 3.4 of the well-posedness paper: existence without Assumption 2.2, proofs

## Main statements

* `Dissertation.Acceptance.A.jointBorel_singularDiffusionCoeffs`,
  `assumption23_singularDiffusionCoeffs`, `assumption25_singularDiffusionCoeffs`,
  `not_assumption22_singularDiffusionCoeffs` — (2.3), Assumptions 2.3 and 2.5, and the failure
  of Assumption 2.2 for the singular-diffusion system.
* `Dissertation.Acceptance.A.rem_uniq_exist` — the singular-diffusion system: its assumptions, the
  failure of Assumption 2.2, and the absence of a tuple of `ℍ_weak` satisfying (1.1).
* `Dissertation.Acceptance.A.rem_uniq_exist_hypotheses` — an instance meeting the hypotheses.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec

universe u v w

section Assumptions

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {d : ℕ}

/-- **(2.3) for the singular diffusion.** -/
theorem jointBorel_singularDiffusionCoeffs (T : ℝ) :
    JointBorel T (singularDiffusionCoeffs (ν := ν) (d := d)) :=
  jointBorel_iff.mpr ⟨coeffBorelW2_singularDiffusionCoeffs T, continuous_fst.borel_measurable⟩

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **Assumption 2.3 for the singular diffusion**, with `L = 1`. -/
theorem assumption23_singularDiffusionCoeffs :
    Assumption23 ℱ P T 1 (singularDiffusionCoeffs (ν := ν) (d := d)) :=
  ⟨zero_le_one, LipInterior.of_diagonalLipschitz diagonalLipschitz_singularDiffusionCoeffs,
    terminalLipschitz_singularDiffusionCoeffs⟩

/-- **Assumption 2.5 for the singular diffusion**, with `G = 1`, `α = 1`, `β₁ = 1`, `β₂ = 0`. -/
theorem assumption25_singularDiffusionCoeffs :
    Assumption25 ℱ P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 0
      (singularDiffusionCoeffs (ν := ν) (d := d)) :=
  Assumption25.of_monotone (jointBorel_singularDiffusionCoeffs T)
    assumption23_singularDiffusionCoeffs constants_singularCoeffs
    diagonalMonotone_singularDiffusionCoeffs terminalMonotone_singularDiffusionCoeffs

/-- **Assumption 2.2 fails for the singular diffusion**, for `d ≥ 1`, every horizon `T > 0` and
every initial datum: the origin value `σ(t, 0, δ₀) = t^{-1/2} e₁₁` is not square integrable on
`(0, T)`. -/
theorem not_assumption22_singularDiffusionCoeffs (hd : 0 < d) (hT : 0 < T)
    (ξ₀ : Ω → EuclideanSpace ℝ (Fin 1)) :
    ¬ Assumption22 ℱ P T (singularDiffusionCoeffs (ν := ν) (d := d)) ξ₀ := fun h =>
  not_coeffOrigin_singularDiffusionCoeffs hd hT (originValues_iff_coeffOrigin.mp h.origin)

end Assumptions

/-- Remark 3.4, Assumption 2.2 cannot be dropped from the existence theorem. -/
theorem rem_uniq_exist : PaperSpec.A.rem_uniq_exist.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ d P _ D h𝒢₀ hind₀ hd T hT
  refine ⟨jointBorel_singularDiffusionCoeffs T, assumption23_singularDiffusionCoeffs, by simp,
    assumption25_singularDiffusionCoeffs,
    fun ξ₀ => ⟨not_assumption22_singularDiffusionCoeffs hd hT ξ₀, ?_, ?_⟩⟩
  · rintro ⟨X, Y, Z, U, ⟨γ, h⟩, -, -⟩
    exact not_paperWeakSolutionInt_singularDiffusionCoeffs hd hT h
  · rintro ⟨X, Y, Z, U, ⟨γ, h⟩, -, -⟩
    exact not_paperWeakSolutionInt_singularDiffusionCoeffs hd hT (h.toWeakInt hT.le)

/-- **The hypotheses of the existence clause of Remark 3.4 can be met.** Over a probability space
carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥` independent of it and
`T = 1`, the singular-diffusion system satisfies (2.3), Assumption 2.3 with `L = 1`,
Assumption 2.4 with `G = 1` and Assumption 2.5 with `G = 1`, `α = 1`, `β₁ = 1`, `β₂ = 0`. -/
theorem rem_uniq_exist_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (_ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      0 < (1 : ℕ) ∧ (0 : ℝ) < 1
      ∧ JointBorel 1 (singularDiffusionCoeffs (ν := Measure.dirac (0 : ℝ)) (d := 1))
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 1
          (singularDiffusionCoeffs (ν := Measure.dirac (0 : ℝ)) (d := 1))
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 0
          (singularDiffusionCoeffs (ν := Measure.dirac (0 : ℝ)) (d := 1)) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨hJ, h23, hG, h25, -⟩ :=
    rem_uniq_exist ⊥ (Measure.dirac (0 : ℝ)) 1 P D bot_le hind₀ one_pos 1 one_pos
  exact ⟨Ω, inferInstance, P, inferInstance, D, hind₀, one_pos, one_pos, hJ, h23, hG, h25⟩

end Dissertation.Acceptance.A
