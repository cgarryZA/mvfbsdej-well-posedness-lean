/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec3Uniqueness
import MVFBSDEJ.WellPosedness.System.WeakPairEnergy

/-!
# Two steps of the proof of Theorem 3.3: proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`. Two solutions of
(1.1) in `ℍ²` solve the `λ`-forced system (4.1) at `λ = 1` with zero forcing
(`MVFBSDEJ.WellPosedness.System.paperWeakSolutionForcedInt_one_zero_iff`); extended off
`[0, T]`, their difference is the difference system of the implementation
(`MVFBSDEJ.WellPosedness.System.PaperWeakSolutionForcedInt.exists_pairDiff`), whose integrands
have finite energy, which is (3.2), and whose backward coordinates satisfy the estimate of Lemma 4.1
(`MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.brownianPoisson_estimate`), which is (3.3).
The jump coefficient at the predictable tuples has the marked energy of the solutions'
representatives
(`MVFBSDEJ.WellPosedness.System.PaperWeakSolutionInt.markedEnergy_coeffJump_sub_leftLim_eq`).
The hypotheses are those of Theorem 3.3, an instance of which is
`MVFBSDEJ.Acceptance.thm_uniq_hypotheses`.

## Main statements

* `MVFBSDEJ.Acceptance.eq_uniq_coeff` — (3.2).
* `MVFBSDEJ.Acceptance.eq_uniq_bwd` — (3.3), with `C_BP(T) = 13 e^T + 3T`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.WellPosedness.BrownianPoisson
  MVFBSDEJ.PaperSpec LevyStochCalc

universe u v w

/-- (3.2). -/
theorem eq_uniq_coeff : PaperSpec.eq_uniq_coeff.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25 ξ₀
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, hXl₁, hYl₁⟩ ⟨⟨γ₂, h₂⟩, hXl₂, hYl₂⟩
  obtain ⟨X₁', X₂', Y₁', Y₂', -, -, hD⟩ :=
    (paperWeakSolutionForcedInt_one_zero_iff.mpr h₁).exists_pairDiff
    (paperWeakSolutionForcedInt_one_zero_iff.mpr h₂) hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone
  have hb : ∀ i, Brownian.Ito.energy P T
      (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s) ≠ ⊤ :=
    fun i => by simpa only [one_mul, Pi.zero_apply, sub_self, add_zero] using (hD.fwd i).b_sq
  have hσ : ∀ i j, Brownian.Ito.energy P T (fun ω s => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
      - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) ≠ ⊤ :=
    fun i j => by simpa only [one_mul, Pi.zero_apply, sub_self, add_zero] using (hD.fwd i).σ_sq j
  have hh : ∀ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
      jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i s ω e
        - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e) ≠ ⊤ :=
    fun i => by
      rw [h₁.markedEnergy_coeffJump_sub_leftLim_eq h₂ hT.le
        (jointBorel_iff.mp hJ).1.toCoeffBorel hXl₁ hYl₁ hXl₂ hYl₂ i]
      simpa only [one_mul, Pi.zero_apply, sub_self, add_zero] using (hD.fwd i).γ_sq
  have hf : ∀ k, Brownian.Ito.energy P T
      (fun ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) ≠ ⊤ :=
    fun k => by simpa only [one_mul, Pi.zero_apply, sub_self, add_zero] using (hD.bwd k).φ_sq
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨ENNReal.sum_lt_top.mpr fun i _ => (hb i).lt_top,
      ENNReal.sum_lt_top.mpr fun i _ => ENNReal.sum_lt_top.mpr fun j _ => (hσ i j).lt_top⟩,
    ENNReal.sum_lt_top.mpr fun i _ => (hh i).lt_top⟩,
    ENNReal.sum_lt_top.mpr fun k _ => (hf k).lt_top⟩

/-- (3.3), with `C_BP(T) = 13 e^T + 3T`. -/
theorem eq_uniq_bwd : PaperSpec.eq_uniq_bwd.{u, v, w} := by
  refine ⟨fun T => 13 * Real.exp T + 3 * T, ?_⟩
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L α β₁ β₂ G C hJ h23 hG h25 ξ₀
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩
  obtain ⟨X₁', X₂', Y₁', Y₂', -, hYe, hD⟩ :=
    (paperWeakSolutionForcedInt_one_zero_iff.mpr h₁).exists_pairDiff
    (paperWeakSolutionForcedInt_one_zero_iff.mpr h₂) hT.le
    h23.interior.diagonalLipschitz_two_mul
    (lipTerminal_iff_terminalLipschitz.mp h23.terminal).two_mul h25.diagonalMonotone
    h25.terminalMonotone
  have 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  have hℱ0 := hF0_enlJoint D h𝒢₀
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0
  -- the terminal values and drivers of the backward coordinates
  have hξ : ∀ k, MemLp (fun ω => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) 2 P :=
    fun k => by simpa only [one_mul, Pi.zero_apply, sub_self, add_zero] using (hD.bwd k).ξ_sq
  have hφ : ∀ k, Brownian.Ito.energy P T
      (fun ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) ≠ ⊤ :=
    fun k => by simpa only [one_mul, Pi.zero_apply, sub_self, add_zero] using (hD.bwd k).φ_sq
  have hest : ∀ k, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y₁' k t ω - Y₂' k t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
      ≤ ENNReal.ofReal (13 * Real.exp T + 3 * T)
        * (∫⁻ ω, (‖terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω‖₊ : ℝ≥0∞) ^ 2 ∂P
          + Brownian.Ito.energy P T (fun ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
            - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)) := fun k => by
    have h := (hD.bwd k).brownianPoisson_estimate 𝒲 hℱ0 hnull hT
    simp only [one_mul, Pi.zero_apply, sub_self, add_zero] at h
    exact le_trans (le_self_add.trans le_self_add) h
  -- the running supremum of the original difference is that of the extensions
  have hsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω)) ∂P
      = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁' k t ω - Y₂' k t ω)) ∂P := by
    refine lintegral_congr fun ω => iSup_congr fun t => iSup_congr fun ht => ?_
    simp only [congrFun (hYe _ t ht).1 ω, congrFun (hYe _ t ht).2 ω]
  have hesq : ∫⁻ ω, esq (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) ∂P
      = ∑ k, ∫⁻ ω, (‖terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    unfold esq
    exact lintegral_finsetSum' _ fun k _ =>
      ((hξ k).aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2
  refine ⟨?_, ENNReal.add_lt_top.mpr ⟨lintegral_esq_lt_top hξ,
    ENNReal.sum_lt_top.mpr fun k _ => (hφ k).lt_top⟩⟩
  rw [hsup, hesq, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine (lintegral_biSup_esq_le hT.le
    (fun k t => ((hD.bwd k).Y_adapted t).mono ((enlJoint 𝒢₀ D h𝒢₀).le t) le_rfl)
    fun k => (hD.bwd k).Y_rightCont).trans (Finset.sum_le_sum fun k _ => hest k)

end MVFBSDEJ.Acceptance
