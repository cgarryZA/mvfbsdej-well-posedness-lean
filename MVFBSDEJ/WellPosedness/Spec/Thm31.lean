/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Spec.Bridge22
import MVFBSDEJ.WellPosedness.Spec.Bridge25
import MVFBSDEJ.WellPosedness.Existence.PaperStabilityBorel
import MVFBSDEJ.WellPosedness.Existence.GlobalEnl

/-!
# Theorem 3.1 under the printed assumptions

Theorem 3.1 of the well-posedness paper: let system `1`, with initial datum `ξ¹`, satisfy
Assumptions 2.2–2.5 with constants `L, α, β₁, β₂` and coupling matrix `G`, let system `2`, with
initial datum `ξ²`, satisfy Assumptions 2.2–2.3 with its own Lipschitz constant, and let `Θᵏ`
solve (1.1) for system `k`. Then

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)
  ≤ C_stab (𝔼|δξ₀|² + 𝔼|δ̂g_T|² + 𝔼 ∫_0^T (|δb|² + |δσ|²_F + ‖δh‖² + |δf|²))`,

with the coefficient differences evaluated along `Θ²`. This file states it over the paper's
filtration `enlJoint 𝒢₀ D h𝒢₀`, for the solution notion
`MVFBSDEJ.WellPosedness.System.PaperSolution`, with the hypotheses of the paper and the
measurability (2.3) of both systems.

The proof applies `MVFBSDEJ.WellPosedness.System.PaperSolution.supSize_sub_le_of_coeffBorel`
with the Lipschitz constant `2L` of the maximum-norm form of Assumption 2.3 and `c_G = s_min(G)⁻²`,
so that `C_stab = aprioriConst T (10 (2L)²) (4 (2L)²) ‖G‖ c_G α β₁ β₂ 1`. The bound holds in
`[0, ∞]`, and Assumption 2.2 for either system, Assumption 2.3 for system `2`, the positivity of the
dimensions and the measurability of system `2` beyond its terminal sections are not used; in the
paper they make the right-hand side finite.

## Main statements

* `PaperSolutionEnl.supSize_sub_le_of_assumptions` — Theorem 3.1 under the printed assumptions.
-/

open MeasureTheory Filter ProbabilityTheory Matrix
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.Spec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability LevyStochCalc

universe u v w

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {T L L₂ α β₁ β₂ : ℝ}
  {G : Matrix (Fin m) (Fin n) ℝ} {C₁ C₂ : Coeffs ν n m d}
  {ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)}

/-- **Theorem 3.1 under the printed assumptions.** Over `enlJoint 𝒢₀ D h𝒢₀`, with `n, m, d ≥ 1`
and `T > 0`, let both systems satisfy the measurability (2.3), let system `1` with initial datum
`ξ¹` satisfy Assumption 2.2, Assumption 2.3 with a constant `L`, Assumption 2.4 (`G` of full
rank) and Assumption 2.5 with `G` and constants `α, β₁, β₂`, and let system `2` with initial
datum `ξ²` satisfy Assumption 2.2 and Assumption 2.3 with a constant `L₂`. Then for solutions
`Θ¹, Θ²` of (1.1) in the sense of `PaperSolution`, with jump representatives `γ¹, γ²`,

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)
  ≤ C_stab (𝔼|δξ₀|² + 𝔼|δ̂g_T|² + 𝔼 ∫_0^T (|δb|² + |δσ|²_F + ‖δh‖² + |δf|²))`,

the coefficient differences `ψ¹ − ψ²` evaluated along `Θ²`, the jump coefficients through the
canonical representative `coeffJump` of `h¹` along `Θ²` and `γ²`, and
`C_stab = aprioriConst T (10 (2L)²) (4 (2L)²) ‖G‖ s_min(G)⁻² α β₁ β₂ 1`. -/
theorem PaperSolutionEnl.supSize_sub_le_of_assumptions
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (_hn : 0 < n) (_hm : 0 < m) (_hd : 0 < d)
    (hT : 0 < T) (hJ₁ : JointBorel T C₁) (_h22₁ : Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C₁ ξ₁)
    (h23₁ : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C₁) (hG : G.rank = min m n)
    (h25₁ : Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C₁) (hJ₂ : JointBorel T C₂)
    (_h22₂ : Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C₂ ξ₂)
    (_h23₂ : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L₂ C₂) :
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ)
      (γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ),
      PaperSolutionEnl D h𝒢₀ hind₀ T C₁ (fun i ω => ξ₁ ω i) X₁ Y₁ Z₁ U₁ γ₁ →
      PaperSolutionEnl D h𝒢₀ hind₀ T C₂ (fun i ω => ξ₂ ω i) X₂ Y₂ Z₂ U₂ γ₂ →
      supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
          (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
        ≤ ENNReal.ofReal (aprioriConst T (10 * (2 * L) ^ 2) (4 * (2 * L) ^ 2) ‖GX G‖
            (sMin G ^ 2)⁻¹ α β₁ β₂ 1)
          * dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i)
            (fun i ω s => driftProc P T C₁ X₂ Y₂ Z₂ U₂ i ω s
              - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
            (fun i s ω j => diffusionProc P T C₁ X₂ Y₂ Z₂ U₂ i s ω j
              - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
            (fun i s ω e => jumpProc T (coeffJump P T C₁ X₂ Y₂ Z₂ U₂) i s ω e
              - jumpProc T γ₂ i s ω e)
            (fun k ω s => driverProc P T C₁ X₂ Y₂ Z₂ U₂ k ω s
              - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
            (fun k ω => terminalVal P T C₁ X₂ k ω - terminalVal P T C₂ X₂ k ω) :=
  fun _ _ _ _ _ _ _ _ _ _ h₁ h₂ =>
  PaperSolution.supSize_sub_le_of_coeffBorel
    (h₁ := h₁)
    (h₂ := h₂)
    (hmeas₁ := (jointBorel_iff.mp hJ₁).1.toCoeffBorel)
    (hg₁ := hJ₁.measurable_g_section)
    (hg₂ := hJ₂.measurable_g_section)
    (𝒲 := crossWitnessEnl D h𝒢₀ hind₀)
    (hℱ0 := hF0_enlJoint D h𝒢₀)
    (hnull := fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (hT := hT)
    (hL := h23₁.interior.diagonalLipschitz_two_mul)
    (hLT := (lipTerminal_iff_terminalLipschitz.mp h23₁.terminal).two_mul)
    (hcG := inv_nonneg.mpr (sq_nonneg (sMin G)))
    (hGf := gCoerciveForward_of_rank hG)
    (hGb := gCoerciveBackward_of_rank hG)
    (hconst := h25₁.constants)
    (hM := h25₁.diagonalMonotone)
    (hMT := h25₁.terminalMonotone)

end MVFBSDEJ.WellPosedness.Spec
