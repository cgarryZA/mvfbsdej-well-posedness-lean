/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3

/-!
# The paragraph after Theorem 3.1 of the well-posedness paper

Statement numbers refer to the well-posedness paper at `e939294`, in the standing setting of §2.
The paragraph after Theorem 3.1 draws three consequences of the stability estimate (3.1): the
companion bound with the roles of the two systems exchanged, continuous dependence on the initial
and terminal data for systems sharing the interior coefficients, and the estimate without the
hypotheses on the second system, which serve only to make its right-hand side finite.

## Main definitions

* `Dissertation.PaperSpec.A.thm_stab_companion` — the companion bound.
* `Dissertation.PaperSpec.A.thm_stab_data` — continuous dependence on the data.
* `Dissertation.PaperSpec.A.thm_stab_minimal` — the estimate without Assumptions 2.2–2.3 on the
  second system.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec

universe u v w

/-- The companion bound after Theorem 3.1. There is a function `C_stab` of
`(T, L, ‖G‖, c_G, α, β₁, β₂)` such that: in the standing setting, if system `1` with initial
datum `ξ¹` satisfies (2.3) and Assumptions 2.2–2.3 with a constant `L₁`, system `2` with initial
datum `ξ²` satisfies (2.3) and Assumptions 2.2–2.5 with constants `L, α, β₁, β₂` and coupling
matrix `G`, and `Θᵏ` solves (1.1) for system `k`, then (3.1) holds with the coefficient
differences `ψ¹ − ψ²` evaluated along `Θ¹` and the constant built from system `2`. -/
def thm_stab_companion : Prop :=
  ∃ Cstab : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L₁ L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C₁ C₂ : Coeffs ν n m d)
      (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C₁ → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C₁ ξ₁ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L₁ C₁ →
    JointBorel T C₂ → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C₂ ξ₂ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C₂ → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C₂ →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    Solution D h𝒢₀ hind₀ T C₁ ξ₁ X₁ Y₁ Z₁ U₁ → Solution D h𝒢₀ hind₀ T C₂ ξ₂ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      ≤ ENNReal.ofReal (Cstab T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
        * dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i)
          (fun i ω s => driftProc P T C₁ X₁ Y₁ Z₁ U₁ i ω s
            - driftProc P T C₂ X₁ Y₁ Z₁ U₁ i ω s)
          (fun i s ω j => diffusionProc P T C₁ X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C₂ X₁ Y₁ Z₁ U₁ i s ω j)
          (fun i s ω e =>
            jumpProc T (coeffJump P T C₁ (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i s ω e
              - jumpProc T (coeffJump P T C₂ (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i s ω e)
          (fun k ω s => driverProc P T C₁ X₁ Y₁ Z₁ U₁ k ω s
            - driverProc P T C₂ X₁ Y₁ Z₁ U₁ k ω s)
          (fun k ω => terminalVal P T C₁ X₁ k ω - terminalVal P T C₂ X₁ k ω)

/-- Continuous dependence on the data after Theorem 3.1. There is a function `C_stab` of
`(T, L, ‖G‖, c_G, α, β₁, β₂)` such that: under the hypotheses of Theorem 3.1, if the two systems
share the interior coefficients `b, σ, h, f`, then
`𝔼 sup |δX|² + 𝔼 sup |δY|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²) ≤ C_stab (𝔼|δξ₀|² + 𝔼|δ̂g_T|²)`. -/
def thm_stab_data : Prop :=
  ∃ Cstab : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L L₂ α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C₁ C₂ : Coeffs ν n m d)
      (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C₁ → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C₁ ξ₁ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C₁ → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C₁ →
    JointBorel T C₂ → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C₂ ξ₂ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L₂ C₂ →
    C₂.b = C₁.b → C₂.σ = C₁.σ → C₂.h = C₁.h → C₂.f = C₁.f →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    Solution D h𝒢₀ hind₀ T C₁ ξ₁ X₁ Y₁ Z₁ U₁ → Solution D h𝒢₀ hind₀ T C₂ ξ₂ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      ≤ ENNReal.ofReal (Cstab T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
        * (∫⁻ ω, esq (fun i => ξ₁ ω i - ξ₂ ω i) ∂P
          + ∫⁻ ω, esq (fun k => terminalVal P T C₁ X₂ k ω - terminalVal P T C₂ X₂ k ω) ∂P)

/-- The estimate (3.1) without the hypotheses on the second system after Theorem 3.1. There is
a function `C_stab` of `(T, L, ‖G‖, c_G, α, β₁, β₂)` such that (3.1) holds, read in `[0, ∞]`,
when system `1` satisfies (2.3) and Assumptions 2.2–2.5, system `2` satisfies only the standing
measurability (2.3), and `Θᵏ` solves (1.1) for system `k`. -/
def thm_stab_minimal : Prop :=
  ∃ Cstab : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C₁ C₂ : Coeffs ν n m d)
      (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C₁ → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C₁ ξ₁ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C₁ → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C₁ →
    JointBorel T C₂ →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    Solution D h𝒢₀ hind₀ T C₁ ξ₁ X₁ Y₁ Z₁ U₁ → Solution D h𝒢₀ hind₀ T C₂ ξ₂ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      ≤ ENNReal.ofReal (Cstab T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
        * dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i)
          (fun i ω s => driftProc P T C₁ X₂ Y₂ Z₂ U₂ i ω s
            - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
          (fun i s ω j => diffusionProc P T C₁ X₂ Y₂ Z₂ U₂ i s ω j
            - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
          (fun i s ω e =>
            jumpProc T (coeffJump P T C₁ (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e
              - jumpProc T (coeffJump P T C₂ (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e)
          (fun k ω s => driverProc P T C₁ X₂ Y₂ Z₂ U₂ k ω s
            - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
          (fun k ω => terminalVal P T C₁ X₂ k ω - terminalVal P T C₂ X₂ k ω)

end Dissertation.PaperSpec.A
