/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4
import Dissertation.PaperSpec.A.Sec3

/-!
# Steps 1 and 2 of the proof of Lemma 4.3 of the well-posedness paper

Statement and equation numbers refer to the well-posedness paper at `1f67672`. In the proof of
Lemma 4.3 the forcings enter only through their difference `δq`, written `q`, and
`δψ_t = ψ(t, Θ¹_t, μ¹_t) − ψ(t, Θ²_t, μ²_t)` for `ψ ∈ {b, σ, h, f}`, likewise `δg_T`, with `δh`
evaluated at the predictable tuples `(Θ^{k,−}_t, μ^{k,−}_t)`. The difference equations are

`d δX_t = (λ δb_t + q^b_t) dt + (λ δσ_t + q^σ_t) dW_t + ∫_E (λ δh_t(e) + q^h_t(e)) Ñ(dt, de)`,
(4.15)

`d δY_t = −(λ δf_t + q^f_t) dt + δZ_t dW_t + ∫_E δU_t(e) Ñ(dt, de)`,
`δY_T = λ δg_T + q^g_T`. (4.16)

Step 1 gives the `G`-energy identity in expectation

`𝔼⟨G δX_T, δY_T⟩ − 𝔼⟨G δξ₀, δY_0⟩ = 𝔼 ∫_0^T [⟨λ δb + q^b, Gᵀ δY⟩ + ⟨λ δσ + q^σ, Gᵀ δZ⟩_F
  + ∫_E ⟨λ δh(e) + q^h(e), Gᵀ δU(e)⟩ ν(de) + ⟨−λ δf − q^f, G δX⟩] dt`, (4.19)

and Step 2 inserts Assumption 2.5: at almost every `t`,

`λ 𝔼[⟨δb_t, Gᵀ δY_t⟩ + ⟨δσ_t, Gᵀ δZ_t⟩_F + ∫_E ⟨δh_t(e), Gᵀ δU_t(e)⟩ ν(de)
  + ⟨−δf_t, G δX_t⟩] ≤ −λ β₁ 𝔼[|Gᵀ δY_t|² + |Gᵀ δZ_t|²_F + ‖Gᵀ δU_t‖²] − λ β₂ 𝔼|G δX_t|²`,
(4.20)

`𝔼⟨G δX_T, δY_T⟩ = λ 𝔼⟨G δX_T, δg_T⟩ + 𝔼⟨G δX_T, q^g_T⟩
  ≥ λ α 𝔼|G δX_T|² − |𝔼⟨G δX_T, q^g_T⟩|`, (4.21)

and, with `N' = 𝔼|δX_T|² + 𝔼|δY_0|² + 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²) dt`, the data
size `P` of (4.14) and `𝒦 = η N' + ‖G‖²/(4η) P` for `η > 0`,

`λ α 𝔼|G δX_T|² + λ β₂ 𝔼 ∫_0^T |G δX|² + λ β₁ 𝔼 ∫_0^T [|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²]
  ≤ |𝔼⟨G δξ₀, δY_0⟩| + |𝔼⟨G δX_T, q^g_T⟩| + 𝔼 ∫_0^T (|⟨q^b, Gᵀ δY⟩| + |⟨q^σ, Gᵀ δZ⟩_F|)
    + 𝔼 ∫_0^T (|∫_E ⟨q^h(e), Gᵀ δU(e)⟩ ν(de)| + |⟨q^f, G δX⟩|) ≤ 𝒦`. (4.22)

## Main definitions

* `Dissertation.PaperSpec.A.eq_dX` — (4.15).
* `Dissertation.PaperSpec.A.eq_dY` — (4.16).
* `Dissertation.PaperSpec.A.eq_Gid` — (4.19).
* `Dissertation.PaperSpec.A.eq_intmono` — (4.20).
* `Dissertation.PaperSpec.A.eq_termmono` — (4.21).
* `Dissertation.PaperSpec.A.eq_coerc` — (4.22).
* `Dissertation.PaperSpec.A.eq_coerc_blocks` — each coercive block of (4.22) is at most `𝒦`.
-/

open MeasureTheory Filter ProbabilityTheory Matrix
open scoped Topology ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.Law LevyStochCalc

universe u v w

/-- **(4.15).** In the standing setting, under the hypotheses of Lemma 4.3 — `T > 0`,
coefficients with (2.3) and Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix
`G`, `λ̲ ∈ (0, 1]`, `λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak` with
`X^k_T ∈ L²`, `ℱ₀`-measurable initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` — each
coordinate `i` of `δX = X¹ − X²` satisfies, almost surely at every `t ∈ [0, T]`,
`δX_t = δξ₀ + ∫_0^t (λ δb_s + q^b_s) ds + ∫_0^t (λ δσ_s + q^σ_s) dW_s
  + ∫_0^t ∫_E (λ δh_s(e) + q^h_s(e)) Ñ(ds, de)`,
`q = δq`: the drift has almost surely integrable paths on `[0, T]`, the diffusion meets the
conditions of the Brownian integral, the jump integrand — `δh` at the predictable tuples, through
the canonical representative `coeffJump` — agrees almost everywhere on `Ω × [0, T] × E` with an
integrand meeting the conditions of the compensated integral, and the identity holds with every
such integrand. -/
def eq_dX : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ lamLow lam : ℝ, 0 < lamLow → lamLow ≤ 1 → lamLow ≤ lam → lam ≤ 1 →
    ∀ (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₁ → Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₂ →
    ∀ (qb₁ qb₂ : Fin n → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ)
      (qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ) (qf₁ qf₂ : Fin m → Ω → ℝ → ℝ)
      (qg₁ qg₂ : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₁ qσ₁ qh₁ qf₁ qg₁ →
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₂ qσ₂ qh₂ qf₂ qg₂ →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ →
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤ →
    ∀ i : Fin n,
      (∀ᵐ ω ∂P, IntegrableOn (fun s => lam * (driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
          - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s) + (qb₁ i ω s - qb₂ i ω s)) (Set.Icc (0 : ℝ) T))
      ∧ ∃ (hσm : ∀ j, Measurable (Function.uncurry fun ω s =>
            lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
              - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j)))
          (hσp : ∀ j, Probability.ProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀) fun ω s =>
            lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
              - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j))
          (hσq : ∀ j, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
            (‖lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
              - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j)‖₊
                : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
        (∃ H : Ω → ℝ → E → ℝ, (Measurable fun p : Ω × ℝ × E => H p.1 p.2.1 p.2.2)
          ∧ Probability.MarkedProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀) H
          ∧ (∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
              (‖H ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
          ∧ ∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P ν T), H p.1 p.2.1 p.2.2
            = lam * (jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
                p.2.1 p.1 p.2.2
              - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
                p.2.1 p.1 p.2.2) + (qh₁ i p.2.1 p.1 p.2.2 - qh₂ i p.2.1 p.1 p.2.2))
        ∧ ∀ (H : Ω → ℝ → E → ℝ) (hHm : Measurable fun p : Ω × ℝ × E => H p.1 p.2.1 p.2.2)
            (hHp : Probability.MarkedProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀) H)
            (hHq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
              (‖H ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
            (∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P ν T), H p.1 p.2.1 p.2.2
              = lam * (jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
                  p.2.1 p.1 p.2.2
                - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
                  p.2.1 p.1 p.2.2) + (qh₁ i p.2.1 p.1 p.2.2 - qh₂ i p.2.1 p.1 p.2.2)) →
            ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
              X₁ i t ω - X₂ i t ω = (ξ₁ ω i - ξ₂ ω i)
                + (∫ s in Set.Icc (0 : ℝ) t, lam * (driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
                  - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s) + (qb₁ i ω s - qb₂ i ω s))
                + Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
                    (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
                    (fun s ω j => lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
                      - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j))
                    hσm hσp hσq t ω
                + Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
                    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) H hHm hHp hHq t ω

/-- **(4.16).** In the standing setting, under the hypotheses of Lemma 4.3 — `T > 0`,
coefficients with (2.3) and Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix
`G`, `λ̲ ∈ (0, 1]`, `λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak` with
`X^k_T ∈ L²`, `ℱ₀`-measurable initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` — each
coordinate `k` of `(δY, δZ, δU)` satisfies `δY_T = λ δg_T + q^g_T` almost surely and, almost
surely at every `t ∈ [0, T]`,
`δY_t = λ δg_T + q^g_T + ∫_t^T (λ δf_s + q^f_s) ds − ∫_t^T δZ_s dW_s
  − ∫_t^T ∫_E δU_s(e) Ñ(ds, de)`,
`q = δq`: the driver has almost surely integrable paths on `[0, T]` and `δZ`, `δU` meet the
conditions of the stochastic integrals. -/
def eq_dY : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ lamLow lam : ℝ, 0 < lamLow → lamLow ≤ 1 → lamLow ≤ lam → lam ≤ 1 →
    ∀ (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₁ → Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₂ →
    ∀ (qb₁ qb₂ : Fin n → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ)
      (qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ) (qf₁ qf₂ : Fin m → Ω → ℝ → ℝ)
      (qg₁ qg₂ : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₁ qσ₁ qh₁ qf₁ qg₁ →
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₂ qσ₂ qh₂ qf₂ qg₂ →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ →
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤ →
    ∀ k : Fin m,
      (∀ᵐ ω ∂P, IntegrableOn (fun s => lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
          - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) + (qf₁ k ω s - qf₂ k ω s)) (Set.Icc (0 : ℝ) T))
      ∧ (∀ᵐ ω ∂P, Y₁ k T ω - Y₂ k T ω
          = lam * (terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) + (qg₁ k ω - qg₂ k ω))
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
            = lam * (terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) + (qg₁ k ω - qg₂ k ω)
              + (∫ s in Set.Icc t T, lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
                  - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) + (qf₁ k ω s - qf₂ k ω s))
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

/-- **(4.19).** In the standing setting, under the hypotheses of Lemma 4.3 — `T > 0`,
coefficients with (2.3) and Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix
`G`, `λ̲ ∈ (0, 1]`, `λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak` with
`X^k_T ∈ L²`, `ℱ₀`-measurable initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` — the
pairings `⟨G δX_T, δY_T⟩` and `⟨G δξ₀, δY_0⟩` are integrable, the integrand
`⟨λ δb + q^b, Gᵀ δY⟩ + ⟨λ δσ + q^σ, Gᵀ δZ⟩_F + ∫_E ⟨λ δh(e) + q^h(e), Gᵀ δU(e)⟩ ν(de)
  + ⟨−λ δf − q^f, G δX⟩`
is integrable on `Ω × [0, T]`, and
`𝔼⟨G δX_T, δY_T⟩ − 𝔼⟨G δξ₀, δY_0⟩` is its integral `𝔼 ∫_0^T … dt`, with `q = δq` and `δh` at
the predictable tuples, through the canonical representative `coeffJump`. -/
def eq_Gid : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ lamLow lam : ℝ, 0 < lamLow → lamLow ≤ 1 → lamLow ≤ lam → lam ≤ 1 →
    ∀ (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₁ → Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₂ →
    ∀ (qb₁ qb₂ : Fin n → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ)
      (qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ) (qf₁ qf₂ : Fin m → Ω → ℝ → ℝ)
      (qg₁ qg₂ : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₁ qσ₁ qh₁ qf₁ qg₁ →
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₂ qσ₂ qh₂ qf₂ qg₂ →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ →
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤ →
    Integrable (fun ω => (G *ᵥ fun i => X₁ i T ω - X₂ i T ω)
        ⬝ᵥ (fun k => Y₁ k T ω - Y₂ k T ω)) P
    ∧ Integrable (fun ω => (G *ᵥ fun i => ξ₁ ω i - ξ₂ ω i)
        ⬝ᵥ (fun k => Y₁ k 0 ω - Y₂ k 0 ω)) P
    ∧ Integrable (fun p : Ω × ℝ =>
        (fun i => lam * (driftProc P T C X₁ Y₁ Z₁ U₁ i p.1 p.2
            - driftProc P T C X₂ Y₂ Z₂ U₂ i p.1 p.2) + (qb₁ i p.1 p.2 - qb₂ i p.1 p.2))
          ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k p.2 p.1 - Y₂ k p.2 p.1)
        + ∑ j, (fun i => lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i p.2 p.1 j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i p.2 p.1 j) + (qσ₁ i p.2 p.1 j - qσ₂ i p.2 p.1 j))
          ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k p.2 p.1 j - Z₂ k p.2 p.1 j)
        + ∫ e, (fun i =>
            lam * (jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
                p.2 p.1 e
              - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
                p.2 p.1 e) + (qh₁ i p.2 p.1 e - qh₂ i p.2 p.1 e))
          ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k p.2 p.1 e - U₂ k p.2 p.1 e) ∂ν
        + (fun k => -(lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k p.1 p.2
            - driverProc P T C X₂ Y₂ Z₂ U₂ k p.1 p.2)) - (qf₁ k p.1 p.2 - qf₂ k p.1 p.2))
          ⬝ᵥ (G *ᵥ fun i => X₁ i p.2 p.1 - X₂ i p.2 p.1))
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
    ∧ (∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (fun k => Y₁ k T ω - Y₂ k T ω) ∂P)
        - ∫ ω, (G *ᵥ fun i => ξ₁ ω i - ξ₂ ω i) ⬝ᵥ (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T,
        ((fun i => lam * (driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
            - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s) + (qb₁ i ω s - qb₂ i ω s))
          ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
        + ∑ j, (fun i => lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j))
          ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
        + ∫ e, (fun i =>
            lam * (jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i s ω e
              - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e)
            + (qh₁ i s ω e - qh₂ i s ω e))
          ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν
        + (fun k => -(lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
            - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)) - (qf₁ k ω s - qf₂ k ω s))
          ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)) ∂volume ∂P

/-- **(4.20).** In the standing setting, under the hypotheses of Lemma 4.3 — `T > 0`,
coefficients with (2.3) and Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix
`G`, `λ̲ ∈ (0, 1]`, `λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak` with
`X^k_T ∈ L²`, `ℱ₀`-measurable initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` — at almost
every `t ∈ [0, T]` the pairing
`⟨δb_t, Gᵀ δY_t⟩ + ⟨δσ_t, Gᵀ δZ_t⟩_F + ∫_E ⟨δh_t(e), Gᵀ δU_t(e)⟩ ν(de) + ⟨−δf_t, G δX_t⟩`,
with `δψ_t = ψ(t, Θ¹_t, μ¹_t) − ψ(t, Θ²_t, μ²_t)` for `ψ = b, σ, f` and `δh_t` at the
predictable tuples `(Θ^{k,−}_t, μ^{k,−}_t)`, `μ = Law`, is integrable, and `λ` times its
expectation is at most
`−λ β₁ 𝔼[|Gᵀ δY_t|² + |Gᵀ δZ_t|²_F + ‖Gᵀ δU_t‖²_{L²(ν)}] − λ β₂ 𝔼|G δX_t|²`. -/
def eq_intmono : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ lamLow lam : ℝ, 0 < lamLow → lamLow ≤ 1 → lamLow ≤ lam → lam ≤ 1 →
    ∀ (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₁ → Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₂ →
    ∀ (qb₁ qb₂ : Fin n → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ)
      (qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ) (qf₁ qf₂ : Fin m → Ω → ℝ → ℝ)
      (qg₁ qg₂ : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₁ qσ₁ qh₁ qf₁ qg₁ →
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₂ qσ₂ qh₂ qf₂ qg₂ →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ →
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤ →
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Integrable (fun ω =>
        inner ℝ (C.b t (tupleAt ν X₁ Y₁ Z₁ U₁ t ω) (lawP2 P (tupleAt ν X₁ Y₁ Z₁ U₁ t))
            - C.b t (tupleAt ν X₂ Y₂ Z₂ U₂ t ω) (lawP2 P (tupleAt ν X₂ Y₂ Z₂ U₂ t)))
          (GX Gᵀ ((tupleAt ν X₁ Y₁ Z₁ U₁ t ω).2.1 - (tupleAt ν X₂ Y₂ Z₂ U₂ t ω).2.1))
        + inner ℝ (C.σ t (tupleAt ν X₁ Y₁ Z₁ U₁ t ω) (lawP2 P (tupleAt ν X₁ Y₁ Z₁ U₁ t))
            - C.σ t (tupleAt ν X₂ Y₂ Z₂ U₂ t ω) (lawP2 P (tupleAt ν X₂ Y₂ Z₂ U₂ t)))
          (GZ Gᵀ ((tupleAt ν X₁ Y₁ Z₁ U₁ t ω).2.2.1 - (tupleAt ν X₂ Y₂ Z₂ U₂ t ω).2.2.1))
        + ∫ e, inner ℝ
            (C.h t (tupleAt ν (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁ t ω)
                (lawP2 P (tupleAt ν (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁ t)) e
              - C.h t (tupleAt ν (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂ t ω)
                (lawP2 P (tupleAt ν (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂ t)) e)
            (GX Gᵀ ((tupleAt ν X₁ Y₁ Z₁ U₁ t ω).2.2.2 e - (tupleAt ν X₂ Y₂ Z₂ U₂ t ω).2.2.2 e)) ∂ν
        + inner ℝ (-(C.f t (tupleAt ν X₁ Y₁ Z₁ U₁ t ω) (lawP2 P (tupleAt ν X₁ Y₁ Z₁ U₁ t))
            - C.f t (tupleAt ν X₂ Y₂ Z₂ U₂ t ω) (lawP2 P (tupleAt ν X₂ Y₂ Z₂ U₂ t))))
          (GX G ((tupleAt ν X₁ Y₁ Z₁ U₁ t ω).1 - (tupleAt ν X₂ Y₂ Z₂ U₂ t ω).1))) P
      ∧ lam * ∫ ω,
        (inner ℝ (C.b t (tupleAt ν X₁ Y₁ Z₁ U₁ t ω) (lawP2 P (tupleAt ν X₁ Y₁ Z₁ U₁ t))
            - C.b t (tupleAt ν X₂ Y₂ Z₂ U₂ t ω) (lawP2 P (tupleAt ν X₂ Y₂ Z₂ U₂ t)))
          (GX Gᵀ ((tupleAt ν X₁ Y₁ Z₁ U₁ t ω).2.1 - (tupleAt ν X₂ Y₂ Z₂ U₂ t ω).2.1))
        + inner ℝ (C.σ t (tupleAt ν X₁ Y₁ Z₁ U₁ t ω) (lawP2 P (tupleAt ν X₁ Y₁ Z₁ U₁ t))
            - C.σ t (tupleAt ν X₂ Y₂ Z₂ U₂ t ω) (lawP2 P (tupleAt ν X₂ Y₂ Z₂ U₂ t)))
          (GZ Gᵀ ((tupleAt ν X₁ Y₁ Z₁ U₁ t ω).2.2.1 - (tupleAt ν X₂ Y₂ Z₂ U₂ t ω).2.2.1))
        + ∫ e, inner ℝ
            (C.h t (tupleAt ν (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁ t ω)
                (lawP2 P (tupleAt ν (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁ t)) e
              - C.h t (tupleAt ν (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂ t ω)
                (lawP2 P (tupleAt ν (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂ t)) e)
            (GX Gᵀ ((tupleAt ν X₁ Y₁ Z₁ U₁ t ω).2.2.2 e - (tupleAt ν X₂ Y₂ Z₂ U₂ t ω).2.2.2 e)) ∂ν
        + inner ℝ (-(C.f t (tupleAt ν X₁ Y₁ Z₁ U₁ t ω) (lawP2 P (tupleAt ν X₁ Y₁ Z₁ U₁ t))
            - C.f t (tupleAt ν X₂ Y₂ Z₂ U₂ t ω) (lawP2 P (tupleAt ν X₂ Y₂ Z₂ U₂ t))))
          (GX G ((tupleAt ν X₁ Y₁ Z₁ U₁ t ω).1 - (tupleAt ν X₂ Y₂ Z₂ U₂ t ω).1))) ∂P
        ≤ -lam * β₁ * ∫ ω,
            (‖GX Gᵀ ((tupleAt ν X₁ Y₁ Z₁ U₁ t ω).2.1 - (tupleAt ν X₂ Y₂ Z₂ U₂ t ω).2.1)‖ ^ 2
            + ‖GZ Gᵀ ((tupleAt ν X₁ Y₁ Z₁ U₁ t ω).2.2.1 - (tupleAt ν X₂ Y₂ Z₂ U₂ t ω).2.2.1)‖ ^ 2
            + ‖GU Gᵀ ν ((tupleAt ν X₁ Y₁ Z₁ U₁ t ω).2.2.2
              - (tupleAt ν X₂ Y₂ Z₂ U₂ t ω).2.2.2)‖ ^ 2) ∂P
          - lam * β₂ * ∫ ω,
            ‖GX G ((tupleAt ν X₁ Y₁ Z₁ U₁ t ω).1 - (tupleAt ν X₂ Y₂ Z₂ U₂ t ω).1)‖ ^ 2 ∂P

/-- **(4.21).** In the standing setting, under the hypotheses of Lemma 4.3 — `T > 0`,
coefficients with (2.3) and Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix
`G`, `λ̲ ∈ (0, 1]`, `λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak` with
`X^k_T ∈ L²`, `ℱ₀`-measurable initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` — the
pairings `⟨G δX_T, δY_T⟩`, `⟨G δX_T, δg_T⟩` and `⟨G δX_T, q^g_T⟩` are integrable,
`𝔼⟨G δX_T, δY_T⟩ = λ 𝔼⟨G δX_T, δg_T⟩ + 𝔼⟨G δX_T, q^g_T⟩`, and
`λ 𝔼⟨G δX_T, δg_T⟩ + 𝔼⟨G δX_T, q^g_T⟩ ≥ λ α 𝔼|G δX_T|² − |𝔼⟨G δX_T, q^g_T⟩|`, with
`δg_T = g(X¹_T, Law X¹_T) − g(X²_T, Law X²_T)` and `q^g = δq^g`. -/
def eq_termmono : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ lamLow lam : ℝ, 0 < lamLow → lamLow ≤ 1 → lamLow ≤ lam → lam ≤ 1 →
    ∀ (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₁ → Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₂ →
    ∀ (qb₁ qb₂ : Fin n → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ)
      (qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ) (qf₁ qf₂ : Fin m → Ω → ℝ → ℝ)
      (qg₁ qg₂ : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₁ qσ₁ qh₁ qf₁ qg₁ →
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₂ qσ₂ qh₂ qf₂ qg₂ →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ →
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤ →
    Integrable (fun ω => (G *ᵥ fun i => X₁ i T ω - X₂ i T ω)
        ⬝ᵥ (fun k => Y₁ k T ω - Y₂ k T ω)) P
    ∧ Integrable (fun ω => (G *ᵥ fun i => X₁ i T ω - X₂ i T ω)
        ⬝ᵥ (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)) P
    ∧ Integrable (fun ω => (G *ᵥ fun i => X₁ i T ω - X₂ i T ω)
        ⬝ᵥ (fun k => qg₁ k ω - qg₂ k ω)) P
    ∧ ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (fun k => Y₁ k T ω - Y₂ k T ω) ∂P
      = lam * ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω)
          ⬝ᵥ (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) ∂P
        + ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (fun k => qg₁ k ω - qg₂ k ω) ∂P
    ∧ lam * α * ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω)
          ⬝ᵥ (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ∂P
        - |∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (fun k => qg₁ k ω - qg₂ k ω) ∂P|
      ≤ lam * ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω)
          ⬝ᵥ (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) ∂P
        + ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (fun k => qg₁ k ω - qg₂ k ω) ∂P

/-- **(4.22).** In the standing setting, under the hypotheses of Lemma 4.3 — `T > 0`,
coefficients with (2.3) and Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix
`G`, `λ̲ ∈ (0, 1]`, `λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak` with
`X^k_T ∈ L²`, `ℱ₀`-measurable initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` — the
quantity `N' = 𝔼|δX_T|² + 𝔼|δY_0|² + 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²) dt` and the data
size `P` of (4.14) are finite, and
`λ α 𝔼|G δX_T|² + λ β₂ 𝔼 ∫_0^T |G δX|² + λ β₁ 𝔼 ∫_0^T [|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²]`
is at most
`|𝔼⟨G δξ₀, δY_0⟩| + |𝔼⟨G δX_T, q^g_T⟩| + 𝔼 ∫_0^T (|⟨q^b, Gᵀ δY⟩| + |⟨q^σ, Gᵀ δZ⟩_F|)
  + 𝔼 ∫_0^T (|∫_E ⟨q^h(e), Gᵀ δU(e)⟩ ν(de)| + |⟨q^f, G δX⟩|)`,
which for every `η > 0` is at most `η N' + ‖G‖²/(4η) P`, with `q = δq` and `‖G‖` the operator
norm. -/
def eq_coerc : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ lamLow lam : ℝ, 0 < lamLow → lamLow ≤ 1 → lamLow ≤ lam → lam ≤ 1 →
    ∀ (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₁ → Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₂ →
    ∀ (qb₁ qb₂ : Fin n → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ)
      (qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ) (qf₁ qf₂ : Fin m → Ω → ℝ → ℝ)
      (qg₁ qg₂ : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₁ qσ₁ qh₁ qf₁ qg₁ →
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₂ qσ₂ qh₂ qf₂ qg₂ →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ →
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤ →
    ∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P + ∫⁻ ω, esq (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P
        + (∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)
          + ∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω)
          + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ k s ω e - U₂ k s ω e))
      ≠ ⊤
    ∧ dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
        (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
        (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω) ≠ ⊤
    ∧ lam * α * ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω)
          ⬝ᵥ (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ∂P
        + lam * β₂ * ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)
          ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω) ∂volume ∂P
        + lam * β₁ * ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ((Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
          + ∑ j, (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
          + ∫ e, (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e)
            ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν) ∂volume ∂P
      ≤ |∫ ω, (G *ᵥ fun i => ξ₁ ω i - ξ₂ ω i) ⬝ᵥ (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P|
        + |∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (fun k => qg₁ k ω - qg₂ k ω) ∂P|
        + ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (|(fun i => qb₁ i ω s - qb₂ i ω s)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)|
          + |∑ j, (fun i => qσ₁ i s ω j - qσ₂ i s ω j)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)|) ∂volume ∂P
        + ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (|∫ e, (fun i => qh₁ i s ω e - qh₂ i s ω e)
            ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν|
          + |(fun k => qf₁ k ω s - qf₂ k ω s) ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)|)
            ∂volume ∂P
    ∧ ∀ η : ℝ, 0 < η →
      |∫ ω, (G *ᵥ fun i => ξ₁ ω i - ξ₂ ω i) ⬝ᵥ (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P|
          + |∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ⬝ᵥ (fun k => qg₁ k ω - qg₂ k ω) ∂P|
          + ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (|(fun i => qb₁ i ω s - qb₂ i ω s)
              ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)|
            + |∑ j, (fun i => qσ₁ i s ω j - qσ₂ i s ω j)
              ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)|) ∂volume ∂P
          + ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (|∫ e, (fun i => qh₁ i s ω e - qh₂ i s ω e)
              ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν|
            + |(fun k => qf₁ k ω s - qf₂ k ω s) ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)|)
              ∂volume ∂P
        ≤ η * (∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P
            + ∫⁻ ω, esq (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P
            + (∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)
              + ∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω)
              + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
              + ∑ k, Poisson.Compensated.markedEnergy P ν T
                (fun ω s e => U₁ k s ω e - U₂ k s ω e))).toReal
          + ‖GX G‖ ^ 2 / (4 * η) * (dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i)
            (fun i ω s => qb₁ i ω s - qb₂ i ω s) (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
            (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
            (fun k ω => qg₁ k ω - qg₂ k ω)).toReal

/-- **The sentence after (4.22).** Under the hypotheses of Lemma 4.3, as in `eq_coerc`, for every
`η > 0` each coercive block on the left of (4.22) is at most `𝒦 = η N' + ‖G‖²/(4η) P`:
`λ α 𝔼|G δX_T|² ≤ 𝒦`, `λ β₂ 𝔼 ∫_0^T |G δX|² ≤ 𝒦` and
`λ β₁ 𝔼 ∫_0^T [|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²] ≤ 𝒦`, with
`N' = 𝔼|δX_T|² + 𝔼|δY_0|² + 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²) dt`, the data size `P` of
(4.14), `q = δq` and `‖G‖` the operator norm. -/
def eq_coerc_blocks : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ lamLow lam : ℝ, 0 < lamLow → lamLow ≤ 1 → lamLow ≤ lam → lam ≤ 1 →
    ∀ (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₁ → Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₂ →
    ∀ (qb₁ qb₂ : Fin n → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ)
      (qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ) (qf₁ qf₂ : Fin m → Ω → ℝ → ℝ)
      (qg₁ qg₂ : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₁ qσ₁ qh₁ qf₁ qg₁ →
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₂ qσ₂ qh₂ qf₂ qg₂ →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ →
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤ →
    ∀ η : ℝ, 0 < η →
      lam * α * ∫ ω, (G *ᵥ fun i => X₁ i T ω - X₂ i T ω)
          ⬝ᵥ (G *ᵥ fun i => X₁ i T ω - X₂ i T ω) ∂P
        ≤ η * (∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P
            + ∫⁻ ω, esq (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P
            + (∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)
              + ∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω)
              + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
              + ∑ k, Poisson.Compensated.markedEnergy P ν T
                (fun ω s e => U₁ k s ω e - U₂ k s ω e))).toReal
          + ‖GX G‖ ^ 2 / (4 * η) * (dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i)
            (fun i ω s => qb₁ i ω s - qb₂ i ω s) (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
            (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
            (fun k ω => qg₁ k ω - qg₂ k ω)).toReal
      ∧ lam * β₂ * ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (G *ᵥ fun i => X₁ i s ω - X₂ i s ω)
          ⬝ᵥ (G *ᵥ fun i => X₁ i s ω - X₂ i s ω) ∂volume ∂P
        ≤ η * (∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P
            + ∫⁻ ω, esq (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P
            + (∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)
              + ∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω)
              + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
              + ∑ k, Poisson.Compensated.markedEnergy P ν T
                (fun ω s e => U₁ k s ω e - U₂ k s ω e))).toReal
          + ‖GX G‖ ^ 2 / (4 * η) * (dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i)
            (fun i ω s => qb₁ i ω s - qb₂ i ω s) (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
            (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
            (fun k ω => qg₁ k ω - qg₂ k ω)).toReal
      ∧ lam * β₁ * ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ((Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Y₁ k s ω - Y₂ k s ω)
          + ∑ j, (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
            ⬝ᵥ (Gᵀ *ᵥ fun k => Z₁ k s ω j - Z₂ k s ω j)
          + ∫ e, (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e)
            ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e) ∂ν) ∂volume ∂P
        ≤ η * (∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P
            + ∫⁻ ω, esq (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P
            + (∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)
              + ∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω)
              + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
              + ∑ k, Poisson.Compensated.markedEnergy P ν T
                (fun ω s e => U₁ k s ω e - U₂ k s ω e))).toReal
          + ‖GX G‖ ^ 2 / (4 * η) * (dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i)
            (fun i ω s => qb₁ i ω s - qb₂ i ω s) (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
            (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
            (fun k ω => qg₁ k ω - qg₂ k ω)).toReal

end Dissertation.PaperSpec.A
