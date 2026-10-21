/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3

/-!
# Two steps of the proof of Theorem 3.3 of the well-posedness paper

Statement and equation numbers refer to the well-posedness paper at `1f67672`. Along two solutions
`Θ¹, Θ² ∈ ℍ²` of (1.1) with the same initial condition, with `μ^k_t = Law(Θ^k_t)`,
`δψ_t = ψ(t, Θ¹_t, μ¹_t) − ψ(t, Θ²_t, μ²_t)` for `ψ ∈ {b, σ, f}`,
`δh_t = h(t, Θ^{1,−}_t, ·, μ^{1,−}_t) − h(t, Θ^{2,−}_t, ·, μ^{2,−}_t)` at the predictable tuples and
`δg_T = g(X¹_T, Law X¹_T) − g(X²_T, Law X²_T)`, the proof of Theorem 3.3 shows

`𝔼 ∫_0^T (|δb_t|² + |δσ_t|²_F + ‖δh_t‖²_{L²(ν)} + |δf_t|²) dt < ∞`, (3.2)

`𝔼 sup_{t ≤ T} |δY_t|² ≤ C_BP (𝔼|δg_T|² + 𝔼 ∫_0^T |δf_s|² ds) < ∞`, (3.3)

with `C_BP` the constant of Lemma 4.1.

## Main definitions

* `Dissertation.PaperSpec.A.eq_uniq_coeff` — (3.2).
* `Dissertation.PaperSpec.A.eq_uniq_bwd` — (3.3).
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec

universe u v w

/-- **(3.2).** In the standing setting, for every horizon `T > 0`, if the coefficients satisfy
(2.3) and Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix `G`, and
`Θ¹, Θ² ∈ ℍ²` satisfy (1.1) with the same initial datum `ξ₀`, then
`𝔼 ∫_0^T (|δb_t|² + |δσ_t|²_F + ‖δh_t‖²_{L²(ν)} + |δf_t|²) dt < ∞`, with
`δψ_t = ψ(t, Θ¹_t, μ¹_t) − ψ(t, Θ²_t, μ²_t)` for `ψ ∈ {b, σ, f}`, `μ^k_t = Law(Θ^k_t)`, and
`δh_t = h(t, Θ^{1,−}_t, ·, μ^{1,−}_t) − h(t, Θ^{2,−}_t, ·, μ^{2,−}_t)` at the predictable tuples,
through the canonical representative `coeffJump`; the expectation is read in `[0, ∞]`. -/
def eq_uniq_coeff : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)) (X₁ X₂ : Fin n → ℝ → Ω → ℝ)
      (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ)
      (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakSolution D h𝒢₀ hind₀ T C ξ₀ X₁ Y₁ Z₁ U₁ → WeakSolution D h𝒢₀ hind₀ T C ξ₀ X₂ Y₂ Z₂ U₂ →
    ∑ i, LevyStochCalc.Brownian.Ito.energy P T
        (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
      + ∑ i, ∑ j, LevyStochCalc.Brownian.Ito.energy P T
        (fun ω s => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
          - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
      + ∑ i, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
        jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i s ω e
          - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e)
      + ∑ k, LevyStochCalc.Brownian.Ito.energy P T
        (fun ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
      < ⊤

/-- **(3.3).** There is a function `C_BP` of `T` such that: in the standing setting, for every
horizon `T > 0`, if the coefficients satisfy (2.3) and Assumptions 2.3–2.5 with constants
`L, α, β₁, β₂` and coupling matrix `G`, and `Θ¹, Θ² ∈ ℍ²` satisfy (1.1) with the same initial
datum `ξ₀`, then
`𝔼 sup_{t ≤ T} |δY_t|² ≤ C_BP(T) (𝔼|δg_T|² + 𝔼 ∫_0^T |δf_s|² ds) < ∞`, with
`δg_T = g(X¹_T, Law X¹_T) − g(X²_T, Law X²_T)`, `δf_s = f(s, Θ¹_s, μ¹_s) − f(s, Θ²_s, μ²_s)` and
`μ^k_s = Law(Θ^k_s)`; the expectations are read in `[0, ∞]`. -/
def eq_uniq_bwd : Prop :=
  ∃ CBP : ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)) (X₁ X₂ : Fin n → ℝ → Ω → ℝ)
      (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ)
      (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakSolution D h𝒢₀ hind₀ T C ξ₀ X₁ Y₁ Z₁ U₁ → WeakSolution D h𝒢₀ hind₀ T C ξ₀ X₂ Y₂ Z₂ U₂ →
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω)) ∂P
        ≤ ENNReal.ofReal (CBP T)
          * (∫⁻ ω, esq (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) ∂P
          + ∑ k, LevyStochCalc.Brownian.Ito.energy P T
            (fun ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s))
      ∧ ∫⁻ ω, esq (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) ∂P
          + ∑ k, LevyStochCalc.Brownian.Ito.energy P T
            (fun ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) < ⊤

end Dissertation.PaperSpec.A
