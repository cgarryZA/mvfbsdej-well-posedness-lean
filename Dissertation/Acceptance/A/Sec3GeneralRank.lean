/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3GeneralRank
import Dissertation.Acceptance.A.Sec3
import Dissertation.Acceptance.A.Sec2Remarks
import Dissertation.Acceptance.A.Witness
import Dissertation.WellPosedness.Robustness.GeneralRank
import Dissertation.WellPosedness.Spec.Cor36WellPosed
import Dissertation.WellPosedness.Remarks.Margin

/-!
# Remark 3.7 of the well-posedness paper: proofs

## Main statements

* `Dissertation.Acceptance.A.margin212_weighted`, `margin212_of_weighted`,
  `pairingBound34W_weighted`, `pairingBound34W_of_weighted` — (2.12) and the weighted (3.4) as
  printed are the weighted conditions along the diagonal.
* `Dissertation.Acceptance.A.rem_generalrank` — the assumptions of the perturbed system at
  general rank.
* `Dissertation.Acceptance.A.rem_generalrank_wp` — its well-posedness, with the constant of
  Theorem 3.1.
* `Dissertation.Acceptance.A.rem_generalrank_hypotheses` — the instance of Corollary 3.6 meets
  the hypotheses.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Matrix

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.Law

universe u v w

section Bridges

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T β₁ β₂ c : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d}

/-- (2.12) as printed gives the weighted margin along the diagonal. -/
theorem margin212_weighted (h : PaperSpec.A.Margin212 ℱ P T G β₁ β₂ c C) :
    DiagonalMonotoneWeightedMargin ℱ P T G β₁ β₂ c C := by
  filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  obtain ⟨-, hle⟩ := ht (Θ, lawP2 P Θ) (mk_mem_diagonalInputs hΘ hΘ2) (Θ', lawP2 P Θ')
    (mk_mem_diagonalInputs hΘ' hΘ2')
  rw [integral_dissipation_eq hΘ2 hΘ2', integral_gWeightSq_eq G C t Θ Θ']
  simpa only [pairing27_eq] using hle

/-- For a positive margin and `β₁, β₂ ≥ 0`, the weighted margin along the diagonal gives (2.12)
as printed. -/
theorem margin212_of_weighted (h : DiagonalMonotoneWeightedMargin ℱ P T G β₁ β₂ c C)
    (hc : 0 < c) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) : PaperSpec.A.Margin212 ℱ P T G β₁ β₂ c C := by
  filter_upwards [h, h.integrable hc hβ₁ hβ₂] with t ht hi p hp p' hp'
  obtain ⟨hs, h2, he⟩ := hp
  obtain ⟨hs', h2', he'⟩ := hp'
  rw [he, he']
  refine ⟨by simpa only [pairing27_eq] using hi p.1 p'.1 hs hs' h2 h2', ?_⟩
  rw [← integral_gWeightSq_eq G C t p.1 p'.1, ← integral_dissipation_eq h2 h2']
  simpa only [pairing27_eq] using ht p.1 p'.1 hs hs' h2 h2'

/-- (3.4) in the weighted quantity, as printed, gives the weighted pairing bound along the
diagonal. -/
theorem pairingBound34W_weighted {p : Coeffs ν n m d}
    (h : PaperSpec.A.PairingBound34W ℱ P T G c p) :
    DiagonalWeightedPairingBound ℱ P T G c p := by
  filter_upwards [h] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  rw [integral_gWeightSq_eq G p t Θ Θ']
  simpa only [pairing27_eq] using ht (Θ, lawP2 P Θ) (mk_mem_diagonalInputs hΘ hΘ2)
    (Θ', lawP2 P Θ') (mk_mem_diagonalInputs hΘ' hΘ2')

/-- (3.4) in the weighted quantity along the diagonal gives its printed form. -/
theorem pairingBound34W_of_weighted {p : Coeffs ν n m d}
    (h : DiagonalWeightedPairingBound ℱ P T G c p) : PaperSpec.A.PairingBound34W ℱ P T G c p := by
  filter_upwards [h] with t ht q hq q' hq'
  obtain ⟨hs, h2, he⟩ := hq
  obtain ⟨hs', h2', he'⟩ := hq'
  obtain ⟨hi, hle⟩ := ht q.1 q'.1 hs hs' h2 h2'
  rw [he, he']
  refine ⟨by simpa only [pairing27_eq] using hi, ?_⟩
  rw [← integral_gWeightSq_eq G p t q.1 q'.1]
  simpa only [pairing27_eq] using hle

end Bridges

/-- Remark 3.7, the assumptions of the perturbed system. -/
theorem rem_generalrank : PaperSpec.A.rem_generalrank.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ _ hn hm hd T hT L₀ Lₚ α β₁ β₂ cdiss cpert G C p ξ₀
    hJ h22 h23 hG h25 h212 hcdiss horigp hLp hLp0 h34 _ hJp hc
  obtain ⟨horig', hLH, hLT', hMm, hpos, hM, hMT⟩ := perturb_assumptions_weighted
    (originValues_iff_coeffOrigin.mp h22.origin)
    (lipInterior_iff_diagonalLipschitzH.mp h23.interior)
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal) h25.constants (margin212_weighted h212)
    hcdiss h25.terminalMonotone (originValues_iff_coeffOrigin.mp horigp)
    (lipInterior_iff_diagonalLipschitzH.mp hLp) (pairingBound34W_weighted h34) hc
  have h23' : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T (L₀ + Lₚ) (C.perturb p) :=
    ⟨add_nonneg h23.nonneg hLp0, lipInterior_iff_diagonalLipschitzH.mpr hLH,
      lipTerminal_iff_terminalLipschitz.mpr (hLT'.mono (le_add_of_nonneg_right hLp0))⟩
  exact ⟨⟨h22.initial_meas, h22.initial_memLp, originValues_iff_coeffOrigin.mpr horig'⟩,
    ⟨_, h23'⟩, hG, Assumption25.of_monotone hJp h23' h25.constants hM hMT,
    margin212_of_weighted hMm hpos h25.constants.β₁_nonneg h25.constants.β₂_nonneg⟩

/-- Remark 3.7, well-posedness of the perturbed system, with the constant of Theorem 3.1. -/
theorem rem_generalrank_wp : PaperSpec.A.rem_generalrank_wp.{u, v, w} := by
  obtain ⟨Cstab, hstab⟩ := thm_stab.{u, v, w}
  refine ⟨Cstab, ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L₀ Lₚ α β₁ β₂ cdiss cpert G C p
    ξ₀ hJ h22 h23 hG h25 h212 hcdiss horigp hLp hLp0 h34 hcp hJp hc
  obtain ⟨h22', ⟨L, h23'⟩, -, h25', -⟩ := rem_generalrank 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd
    T hT L₀ Lₚ α β₁ β₂ cdiss cpert G C p ξ₀ hJ h22 h23 hG h25 h212 hcdiss horigp hLp hLp0 h34 hcp
    hJp hc
  refine ⟨(thm_cwp 𝒢₀ ν n m d P D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G _ ξ₀ hJp
      h22' h23' hG h25').1, fun X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ h₁ h₂ => (thm_uniq 𝒢₀ ν n m
      d P D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G _ hJp h23' hG h25' ξ₀ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂
      h₁ h₂).1, L, h23',
    fun L₂ C₂ ξ₂ hJ₂ h22₂ h23₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ h₁ h₂ => hstab 𝒢₀ ν n m d P D h𝒢₀ hind₀
      hn hm hd T hT L L₂ α β₁ β₂ G _ C₂ ξ₀ ξ₂ hJp h22' h23' hG h25' hJ₂ h22₂ h23₂ X₁ X₂ Y₁ Y₂
      Z₁ Z₂ U₁ U₂ h₁ h₂⟩

/-- **The hypotheses of Remark 3.7 hold at the instance of Corollary 3.6.** At the instance of
`Dissertation.cor_robust_hypotheses` (`n = m = 1`, `G = 1`), the baseline satisfies
(2.12) with `β₁ = β₂ = c_diss = 1` and the feedback perturbation with `ε = 1/2` satisfies (3.4)
in the weighted quantity with `c_pert = 1/2`. -/
theorem rem_generalrank_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (_ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      JointBorel 1 (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 2 2 0 0)
      ∧ Assumption22 (enlJoint ⊥ D bot_le) P 1
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 2 2 0 0) (fun _ => 0)
      ∧ Assumption23 (enlJoint ⊥ D bot_le) P 1 2
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 2 2 0 0)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 2 2 0 0)
      ∧ PaperSpec.A.Margin212 (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 1
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 2 2 0 0)
      ∧ (0 : ℝ) < 1
      ∧ OriginValues 1
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) (-(1 / 2)) 0 0 0)
      ∧ LipInterior (enlJoint ⊥ D bot_le) P 1 (1 / 2)
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) (-(1 / 2)) 0 0 0)
      ∧ (0 : ℝ) ≤ 1 / 2
      ∧ PaperSpec.A.PairingBound34W (enlJoint ⊥ D bot_le) P 1 (1 : Matrix (Fin 1) (Fin 1) ℝ)
          (1 / 2)
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) (-(1 / 2)) 0 0 0)
      ∧ (0 : ℝ) ≤ 1 / 2
      ∧ JointBorel 1
          ((affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 2 2 0 0).perturb
            (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) (-(1 / 2)) 0 0 0))
      ∧ (1 / 2 : ℝ) < 1 := by
  obtain ⟨Ω, _, P, _, D, hind₀, hJ, h22, h23, hG, h25, h213, h1, horig, hLp, hLp0, h34, hcp, hJp,
    hc⟩ := cor_robust_hypotheses
  have hW := diagonalMonotoneWeightedMargin_one_iff.mpr
    ((margin213_iff one_pos zero_le_one zero_le_one).mp h213)
  have hP : DiagonalWeightedPairingBound (enlJoint ⊥ D bot_le) P 1
      (1 : Matrix (Fin 1) (Fin 1) ℝ) (1 / 2)
      (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) (-(1 / 2)) 0 0 0) := by
    simp only [DiagonalWeightedPairingBound, gWeightSq_one]
    exact pairingBound34_iff.mp h34
  exact ⟨Ω, inferInstance, P, inferInstance, D, hind₀, hJ, h22, h23, hG, h25,
    margin212_of_weighted hW one_pos zero_le_one zero_le_one, h1, horig, hLp, hLp0,
    pairingBound34W_of_weighted hP, hcp, hJp, hc⟩

end Dissertation.Acceptance.A
