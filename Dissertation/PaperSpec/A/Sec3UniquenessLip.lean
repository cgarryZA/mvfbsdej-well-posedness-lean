/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3

/-!
# The proof of Theorem 3.3 under the Lipschitz condition alone

Statement and equation numbers refer to the well-posedness paper at `1f67672`. Remark 3.4 says that
the uniqueness argument needs only the Lipschitz control of the coefficient differences to place
the difference of two solutions in `ℍ`. Along two solutions `Θ¹, Θ² ∈ ℍ_weak` of (1.1) with the
same initial condition, whose coefficients satisfy (2.3) and Assumption 2.3 (no monotonicity, no
Assumption 2.2), with `μ^k_t = Law(Θ^k_t)`, `δψ_t = ψ(t, Θ¹_t, μ¹_t) − ψ(t, Θ²_t, μ²_t)` for
`ψ ∈ {b, σ, f}`, `δh_t` at the predictable tuples and
`δg_T = g(X¹_T, Law X¹_T) − g(X²_T, Law X²_T)`, the proof of Theorem 3.3 shows

`𝔼[|δb_t|² + |δσ_t|²_F + ‖δh_t‖² + |δf_t|²] ≤ C 𝔼|δΘ_t|²_H` for a.e. `t`, `C` independent of `t`,

`𝔼 ∫_0^T (|δb_t|² + |δσ_t|²_F + ‖δh_t‖² + |δf_t|²) dt < ∞`, (3.2)

`δX_t = ∫_0^t δb_s ds + ∫_0^t δσ_s dW_s + ∫_0^t ∫_E δh_s(e) Ñ(ds, de)`,
`𝔼 sup_{t ≤ T} |δX_t|² ≤ C_T 𝔼 ∫_0^T (|δb_s|² + |δσ_s|²_F + ‖δh_s‖²) ds < ∞`,

`δY_t = δg_T + ∫_t^T δf_s ds − ∫_t^T δZ_s dW_s − ∫_t^T ∫_E δU_s(e) Ñ(ds, de)`,

`X^k_T ∈ L²` and `𝔼|δg_T|² ≤ C 𝔼|δX_T|² < ∞`,

`𝔼 sup_{t ≤ T} |δY_t|² ≤ C_BP (𝔼|δg_T|² + 𝔼 ∫_0^T |δf_s|² ds) < ∞`, (3.3)

and `δΘ ∈ ℍ`.

## Main definitions

* `Dissertation.PaperSpec.A.eq_uniq_coeff_ae` — the bound at almost every time before (3.2).
* `Dissertation.PaperSpec.A.eq_uniq_coeff_lip` — (3.2).
* `Dissertation.PaperSpec.A.eq_uniq_fwd` — the forward difference and its supremum bound.
* `Dissertation.PaperSpec.A.eq_uniq_bwd_eq` — the backward difference.
* `Dissertation.PaperSpec.A.eq_uniq_bwd_terminal` — the terminal bound before (3.3).
* `Dissertation.PaperSpec.A.eq_uniq_bwd_lip` — (3.3).
* `Dissertation.PaperSpec.A.rem_uniq_lip_mem` — `Θ¹ − Θ² ∈ ℍ`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec LevyStochCalc

universe u v w

/-- **The bound before (3.2), at almost every time.** There is a function `K` of the Lipschitz
constant such that: in the standing setting, for every horizon `T > 0`, if the coefficients
satisfy (2.3) and Assumption 2.3 with constant `L`, and `Θ¹, Θ² ∈ ℍ_weak` satisfy (1.1) with the
same initial datum `ξ₀`, then for almost every `t ∈ [0, T]`
`𝔼[|δb_t|² + |δσ_t|²_F + ‖δh_t‖²_{L²(ν)} + |δf_t|²]
  ≤ K(L) 𝔼[|δX_t|² + |δY_t|² + |δZ_t|²_F + ‖δU_t‖²_{L²(ν)}]`,
with `δψ_t = ψ(t, Θ¹_t, μ¹_t) − ψ(t, Θ²_t, μ²_t)` for `ψ ∈ {b, σ, f}`, `μ^k_t = Law(Θ^k_t)`, and
`δh_t = h(t, Θ^{1,−}_t, ·, μ^{1,−}_t) − h(t, Θ^{2,−}_t, ·, μ^{2,−}_t)` at the predictable tuples,
through the canonical representative `coeffJump`; the expectations are read in `[0, ∞]`. -/
def eq_uniq_coeff_ae : Prop :=
  ∃ K : ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
    ∀ (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)) (X₁ X₂ : Fin n → ℝ → Ω → ℝ)
      (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ)
      (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakSolution D h𝒢₀ hind₀ T C ξ₀ X₁ Y₁ Z₁ U₁ → WeakSolution D h𝒢₀ hind₀ T C ξ₀ X₂ Y₂ Z₂ U₂ →
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∫⁻ ω, (esq (fun i => driftProc P T C X₁ Y₁ Z₁ U₁ i ω t
            - driftProc P T C X₂ Y₂ Z₂ U₂ i ω t)
          + ∑ i, esq (fun j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i t ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i t ω j)
          + ∑ i, ∫⁻ e,
            (‖jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i t ω e
              - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i t ω e‖₊
                : ℝ≥0∞) ^ 2 ∂ν
          + esq (fun k => driverProc P T C X₁ Y₁ Z₁ U₁ k ω t
            - driverProc P T C X₂ Y₂ Z₂ U₂ k ω t)) ∂P
        ≤ ENNReal.ofReal (K L) * ∫⁻ ω, (esq (fun i => X₁ i t ω - X₂ i t ω)
          + esq (fun k => Y₁ k t ω - Y₂ k t ω) + ∑ k, esq (fun j => Z₁ k t ω j - Z₂ k t ω j)
          + ∑ k, ∫⁻ e, (‖U₁ k t ω e - U₂ k t ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P

/-- **(3.2) under the Lipschitz condition.** In the standing setting, for every horizon `T > 0`,
if the coefficients satisfy (2.3) and Assumption 2.3 with constant `L`, and `Θ¹, Θ² ∈ ℍ_weak`
satisfy (1.1) with the same initial datum `ξ₀`, then
`𝔼 ∫_0^T (|δb_t|² + |δσ_t|²_F + ‖δh_t‖²_{L²(ν)} + |δf_t|²) dt < ∞`, the coefficient differences
as in `eq_uniq_coeff_ae`, the expectation read in `[0, ∞]`. -/
def eq_uniq_coeff_lip : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
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

/-- **The forward difference in the proof of Theorem 3.3, and its supremum bound.** There is a
function `K` of the horizon such that: in the standing setting, for every horizon `T > 0`, if the
coefficients satisfy (2.3) and Assumption 2.3 with constant `L`, and `Θ¹, Θ² ∈ ℍ_weak` satisfy
(1.1) with the same initial datum `ξ₀`, then each coordinate `i` of `δX = X¹ − X²` satisfies,
almost surely at every `t ∈ [0, T]`,
`δX_t = ∫_0^t δb_s ds + ∫_0^t δσ_s dW_s + ∫_0^t ∫_E δh_s(e) Ñ(ds, de)`:
the drift has almost surely integrable paths on `[0, T]`, the diffusion meets the conditions of the
Brownian integral, the jump integrand — `δh` at the predictable tuples, through the canonical
representative `coeffJump` — agrees almost everywhere on `Ω × [0, T] × E` with an integrand meeting
the conditions of the compensated integral, and the identity holds with every such integrand; and
`𝔼 sup_{t ≤ T} |δX_t|² ≤ K(T) 𝔼 ∫_0^T (|δb_s|² + |δσ_s|²_F + ‖δh_s‖²_{L²(ν)}) ds < ∞`, the
expectations read in `[0, ∞]`. -/
def eq_uniq_fwd : Prop :=
  ∃ K : ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
    ∀ (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)) (X₁ X₂ : Fin n → ℝ → Ω → ℝ)
      (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ)
      (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakSolution D h𝒢₀ hind₀ T C ξ₀ X₁ Y₁ Z₁ U₁ → WeakSolution D h𝒢₀ hind₀ T C ξ₀ X₂ Y₂ Z₂ U₂ →
    (∀ i : Fin n,
      (∀ᵐ ω ∂P, IntegrableOn (fun s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
          - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s) (Set.Icc (0 : ℝ) T))
      ∧ ∃ (hσm : ∀ j, Measurable (Function.uncurry fun ω s =>
            diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j))
          (hσp : ∀ j, Probability.ProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀) fun ω s =>
            diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
          (hσq : ∀ j, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
            (‖diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
              - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
        (∃ H : Ω → ℝ → E → ℝ, (Measurable fun p : Ω × ℝ × E => H p.1 p.2.1 p.2.2)
          ∧ Probability.MarkedProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀) H
          ∧ (∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
              (‖H ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
          ∧ ∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P ν T), H p.1 p.2.1 p.2.2
            = jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
                p.2.1 p.1 p.2.2
              - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
                p.2.1 p.1 p.2.2)
        ∧ ∀ (H : Ω → ℝ → E → ℝ) (hHm : Measurable fun p : Ω × ℝ × E => H p.1 p.2.1 p.2.2)
            (hHp : Probability.MarkedProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀) H)
            (hHq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
              (‖H ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
            (∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P ν T), H p.1 p.2.1 p.2.2
              = jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
                  p.2.1 p.1 p.2.2
                - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
                  p.2.1 p.1 p.2.2) →
            ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
              X₁ i t ω - X₂ i t ω
                = (∫ s in Set.Icc (0 : ℝ) t, driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
                    - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
                  + Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
                      (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
                      (fun s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
                        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) hσm hσp hσq t ω
                  + Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
                      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) H hHm hHp hHq t ω)
    ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁ i t ω - X₂ i t ω)) ∂P
        ≤ ENNReal.ofReal (K T)
          * (∑ i, Brownian.Ito.energy P T
              (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
            + ∑ i, ∑ j, Brownian.Ito.energy P T
              (fun ω s => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
                - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
            + ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
              jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i s ω e
                - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e))
    ∧ ∑ i, Brownian.Ito.energy P T
          (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
        + ∑ i, ∑ j, Brownian.Ito.energy P T
          (fun ω s => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
        + ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
          jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i s ω e
            - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e) < ⊤

/-- **The backward difference in the proof of Theorem 3.3.** In the standing setting, for every
horizon `T > 0`, if the coefficients satisfy (2.3) and Assumption 2.3 with constant `L`, and
`Θ¹, Θ² ∈ ℍ_weak` satisfy (1.1) with the same initial datum `ξ₀`, then each coordinate `k` of
`(δY, δZ, δU)` satisfies, almost surely at every `t ∈ [0, T]`,
`δY_t = δg_T + ∫_t^T δf_s ds − ∫_t^T δZ_s dW_s − ∫_t^T ∫_E δU_s(e) Ñ(ds, de)`,
`δg_T = g(X¹_T, Law(X¹_T)) − g(X²_T, Law(X²_T))`: the driver has almost surely integrable paths on
`[0, T]` and `δZ`, `δU` meet the conditions of the stochastic integrals. -/
def eq_uniq_bwd_eq : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
    ∀ (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)) (X₁ X₂ : Fin n → ℝ → Ω → ℝ)
      (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ)
      (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakSolution D h𝒢₀ hind₀ T C ξ₀ X₁ Y₁ Z₁ U₁ → WeakSolution D h𝒢₀ hind₀ T C ξ₀ X₂ Y₂ Z₂ U₂ →
    ∀ k : Fin m,
      (∀ᵐ ω ∂P, IntegrableOn (fun s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
          - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) (Set.Icc (0 : ℝ) T))
      ∧ ∃ (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z₁ k s ω j - Z₂ k s ω j))
          (hZp : ∀ j, Probability.ProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀)
            fun ω s => Z₁ k s ω j - Z₂ k s ω j)
          (hZq : ∀ j, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
            (‖Z₁ k s ω j - Z₂ k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
          (hUm : Measurable fun p : Ω × ℝ × E => U₁ k p.2.1 p.1 p.2.2 - U₂ k p.2.1 p.1 p.2.2)
          (hUp : Probability.MarkedProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀)
            fun ω s e => U₁ k s ω e - U₂ k s ω e)
          (hUq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
            (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
          Y₁ k t ω - Y₂ k t ω
            = (terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
              + (∫ s in Set.Icc t T, driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
                  - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
              - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
                    (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
                    (fun s ω j => Z₁ k s ω j - Z₂ k s ω j) hZm hZp hZq T ω
                  - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
                    (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
                    (fun s ω j => Z₁ k s ω j - Z₂ k s ω j) hZm hZp hZq t ω)
              - (Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
                    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀)
                    (fun ω s e => U₁ k s ω e - U₂ k s ω e) hUm hUp hUq T ω
                  - Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
                    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀)
                    (fun ω s e => U₁ k s ω e - U₂ k s ω e) hUm hUp hUq t ω)

/-- **The terminal bound before (3.3).** There is a function `K` of the Lipschitz constant such
that: in the standing setting, for every horizon `T > 0`, if the coefficients satisfy (2.3) and
Assumption 2.3 with constant `L`, and `Θ¹, Θ² ∈ ℍ_weak` satisfy (1.1) with the same initial datum
`ξ₀`, then `X¹_T, X²_T ∈ L²` and `𝔼|δg_T|² ≤ K(L) 𝔼|δX_T|² < ∞`, with
`δg_T = g(X¹_T, Law X¹_T) − g(X²_T, Law X²_T)` and `δX_T = X¹_T − X²_T`; the expectations are
read in `[0, ∞]`. -/
def eq_uniq_bwd_terminal : Prop :=
  ∃ K : ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
    ∀ (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)) (X₁ X₂ : Fin n → ℝ → Ω → ℝ)
      (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ)
      (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakSolution D h𝒢₀ hind₀ T C ξ₀ X₁ Y₁ Z₁ U₁ → WeakSolution D h𝒢₀ hind₀ T C ξ₀ X₂ Y₂ Z₂ U₂ →
    (∀ i : Fin n, MemLp (X₁ i T) 2 P ∧ MemLp (X₂ i T) 2 P)
    ∧ ∫⁻ ω, esq (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) ∂P
        ≤ ENNReal.ofReal (K L) * ∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P
    ∧ ∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P < ⊤

/-- **(3.3) under the Lipschitz condition.** There is a function `C_BP` of `T` such that: in the
standing setting, for every horizon `T > 0`, if the coefficients satisfy (2.3) and Assumption 2.3
with constant `L`, and `Θ¹, Θ² ∈ ℍ_weak` satisfy (1.1) with the same initial datum `ξ₀`, then
`𝔼 sup_{t ≤ T} |δY_t|² ≤ C_BP(T) (𝔼|δg_T|² + 𝔼 ∫_0^T |δf_s|² ds) < ∞`, with
`δg_T = g(X¹_T, Law X¹_T) − g(X²_T, Law X²_T)`, `δf_s = f(s, Θ¹_s, μ¹_s) − f(s, Θ²_s, μ²_s)` and
`μ^k_s = Law(Θ^k_s)`; the expectations are read in `[0, ∞]`. -/
def eq_uniq_bwd_lip : Prop :=
  ∃ CBP : ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
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

/-- **`Θ¹ − Θ² ∈ ℍ` under the Lipschitz condition** (Remark 3.4). In the standing setting, for
every horizon `T > 0`, if the coefficients satisfy (2.3) and Assumption 2.3 with constant `L`, and
`Θ¹, Θ² ∈ ℍ_weak` satisfy (1.1) with the same initial datum `ξ₀`, then `‖Θ¹ − Θ²‖²_ℍ < ∞`:
`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ_t|²_F + ‖δU_t‖²_{L²(ν)}) dt < ∞`. -/
def rem_uniq_lip_mem : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
    ∀ (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)) (X₁ X₂ : Fin n → ℝ → Ω → ℝ)
      (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ)
      (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakSolution D h𝒢₀ hind₀ T C ξ₀ X₁ Y₁ Z₁ U₁ → WeakSolution D h𝒢₀ hind₀ T C ξ₀ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
      (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤

end Dissertation.PaperSpec.A
