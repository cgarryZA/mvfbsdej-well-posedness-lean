/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4Difference
import Dissertation.WellPosedness.Martingale.LocalIntegral

/-!
# The four stochastic integrals of the `G`-energy identity of Lemma 4.3 and (4.18)

Statement and equation numbers refer to the well-posedness paper at `1f67672`. Of the five
stochastic terms of the pathwise `G`-energy identity (4.17), the first four are the local
martingales

`∫_0^t ⟨G δX_{s−}, δZ_s dW_s⟩`, `∫_0^t ⟨G (λ δσ_s + q^σ_s) dW_s, δY_{s−}⟩`,
`∫_0^t ∫_E ⟨G δX_{s−}, δU_s(e)⟩ Ñ(ds, de)`, `∫_0^t ∫_E ⟨G (λ δh_s + q^h_s)(e), δY_{s−}⟩ Ñ(ds, de)`,

local stochastic integrals (`IsLocalBrownianIntegral`, `IsLocalCompensatedIntegral`) of
integrands carrying a left limit of `δX` or `δY`, which has no moment beyond the second. The
Burkholder–Davis–Gundy inequality and the Cauchy–Schwarz inequality bound them (4.18):

`𝔼 sup_{t ≤ T} |∫_0^t ⟨G δX_{s−}, δZ_s dW_s⟩|
  ≤ c_BDG ‖G‖ (𝔼 sup_{t ≤ T} |δX_t|²)^{1/2} (𝔼 ∫_0^T |δZ_t|²_F dt)^{1/2}`,

and likewise for the other three with `(δY, λ δσ + q^σ)`, `(δX, δU)` and `(δY, λ δh + q^h)`. The
bounds are finite, so the supremum criterion gives the four local martingales zero-mean
increments. The fifth integrand `⟨λ δh + q^h, Gᵀ δU⟩` is integrable against `dP ⊗ ds ⊗ ν` by the
Cauchy–Schwarz inequality.

`c_BDG` is the constant of the Burkholder–Davis–Gundy inequality fixed in §4; each bound holds for
every value of it at least some `c₀ > 0`. `‖G‖` is the operator norm, `q = δq`, and `δh` is
evaluated at the predictable tuples, through the canonical representative `coeffJump`;
`λ δh + q^h` enters the integrals through any jointly measurable, marked progressively measurable
integrand of finite energy that agrees with it almost everywhere on `Ω × [0, T] × E`, as in
(4.15). In the integrands the left limits `δX_{s−}`, `δY_{s−}` are those at the times of `(0, T]`,
and `0` at other times.

## Main definitions

* `Dissertation.PaperSpec.A.eq_bdg4_XZ` — the first bound of (4.18).
* `Dissertation.PaperSpec.A.eq_bdg4_sigmaY` — the second bound of (4.18).
* `Dissertation.PaperSpec.A.eq_bdg4_XU` — the third bound of (4.18).
* `Dissertation.PaperSpec.A.eq_bdg4_hY` — the fourth bound of (4.18).
* `Dissertation.PaperSpec.A.eq_bdg4_fifth` — the integrability of the forced diffusion and jump
  integrands and of the fifth integrand.
-/

open MeasureTheory Filter ProbabilityTheory Matrix
open scoped Topology ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.WellPosedness.Martingale Dissertation.Law
  LevyStochCalc

universe u v w

/-- **The first bound of (4.18).** There is `c₀ > 0` such that, for every value `c ≥ c₀` of the
constant `c_BDG`, under the hypotheses of Lemma 4.3 — `T > 0`, coefficients with (2.3) and
Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix `G`, `λ̲ ∈ (0, 1]`,
`λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak` with `X^k_T ∈ L²`, `ℱ₀`-measurable
initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` — the integrand `⟨G δX_{s−}, δZ_s ·⟩` has a
local Itô integral `M_t = ∫_0^t ⟨G δX_{s−}, δZ_s dW_s⟩` on `[0, T]`, and every such `M` satisfies `𝔼
sup_{t ≤ T} |M_t| ≤ c ‖G‖ (𝔼 sup_{t ≤ T} |δX_t|²)^{1/2} (𝔼 ∫_0^T |δZ_t|²_F dt)^{1/2} < ∞` and, for
every `t ∈ [0, T]`, `𝔼[M_T − M_t] = 0` with `M_T − M_t` integrable; the expectations of nonnegative
quantities are read in `[0, ∞]`. -/
def eq_bdg4_XZ : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
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
    (∃ M : ℝ → Ω → ℝ, IsLocalBrownianIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
        (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) T
        (fun s ω j => ∑ k, (G *ᵥ fun i => if s ∈ Set.Ioc (0 : ℝ) T then
          leftLimProc (fun a t ω => X₁ a t ω - X₂ a t ω) i s ω else 0) k
        * (Z₁ k s ω j - Z₂ k s ω j)) M)
    ∧ ∀ M : ℝ → Ω → ℝ, IsLocalBrownianIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
        (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) T
        (fun s ω j => ∑ k, (G *ᵥ fun i => if s ∈ Set.Ioc (0 : ℝ) T then
          leftLimProc (fun a t ω => X₁ a t ω - X₂ a t ω) i s ω else 0) k
        * (Z₁ k s ω j - Z₂ k s ω j)) M →
      ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
          ≤ ENNReal.ofReal (c * ‖GX G‖)
            * (∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁ i t ω - X₂ i t ω) ∂P) ^ (1 / 2 : ℝ)
            * (∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j))
                ^ (1 / 2 : ℝ)
        ∧ ENNReal.ofReal (c * ‖GX G‖)
            * (∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁ i t ω - X₂ i t ω) ∂P) ^ (1 / 2 : ℝ)
            * (∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j))
                ^ (1 / 2 : ℝ) < ⊤
        ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun ω => M T ω - M t ω) P
          ∧ ∫ ω, (M T ω - M t ω) ∂P = 0

/-- **The second bound of (4.18).** There is `c₀ > 0` such that, for every value `c ≥ c₀` of the
constant `c_BDG`, under the hypotheses of Lemma 4.3 — `T > 0`, coefficients with (2.3) and
Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix `G`, `λ̲ ∈ (0, 1]`,
`λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak` with `X^k_T ∈ L²`, `ℱ₀`-measurable
initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` — the integrand
`⟨G (λ δσ_s + q^σ_s) ·, δY_{s−}⟩` has a local Itô integral
`M_t = ∫_0^t ⟨G (λ δσ_s + q^σ_s) dW_s, δY_{s−}⟩` on `[0, T]`, and every such `M` satisfies `𝔼 sup_{t
≤ T} |M_t| ≤ c ‖G‖ (𝔼 sup_{t ≤ T} |δY_t|²)^{1/2} (𝔼 ∫_0^T |λ δσ_t + q^σ_t|²_F dt)^{1/2} < ∞` and,
for every `t ∈ [0, T]`, `𝔼[M_T − M_t] = 0` with `M_T − M_t` integrable, with `q = δq`; the
expectations of nonnegative quantities are read in `[0, ∞]`. -/
def eq_bdg4_sigmaY : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
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
    (∃ M : ℝ → Ω → ℝ, IsLocalBrownianIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
        (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) T
        (fun s ω j => ∑ k, (G *ᵥ fun i => lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j)) k
        * (if s ∈ Set.Ioc (0 : ℝ) T then
            leftLimProc (fun a t ω => Y₁ a t ω - Y₂ a t ω) k s ω else 0)) M)
    ∧ ∀ M : ℝ → Ω → ℝ, IsLocalBrownianIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
        (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) T
        (fun s ω j => ∑ k, (G *ᵥ fun i => lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j)) k
        * (if s ∈ Set.Ioc (0 : ℝ) T then
            leftLimProc (fun a t ω => Y₁ a t ω - Y₂ a t ω) k s ω else 0)) M →
      ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
          ≤ ENNReal.ofReal (c * ‖GX G‖)
            * (∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω) ∂P) ^ (1 / 2 : ℝ)
            * (∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s =>
                  lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
                    - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j)))
                ^ (1 / 2 : ℝ)
        ∧ ENNReal.ofReal (c * ‖GX G‖)
            * (∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω) ∂P) ^ (1 / 2 : ℝ)
            * (∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s =>
                  lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
                    - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j)))
                ^ (1 / 2 : ℝ) < ⊤
        ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun ω => M T ω - M t ω) P
          ∧ ∫ ω, (M T ω - M t ω) ∂P = 0

/-- **The third bound of (4.18).** There is `c₀ > 0` such that, for every value `c ≥ c₀` of the
constant `c_BDG`, under the hypotheses of Lemma 4.3 — `T > 0`, coefficients with (2.3) and
Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix `G`, `λ̲ ∈ (0, 1]`,
`λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak` with `X^k_T ∈ L²`, `ℱ₀`-measurable
initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` — the marked integrand `⟨G δX_{s−}, δU_s(e)⟩`
has a local compensated Poisson integral `M_t = ∫_0^t ∫_E ⟨G δX_{s−}, δU_s(e)⟩ Ñ(ds, de)` on
`[0, T]`, and every such `M` satisfies `𝔼 sup_{t ≤ T} |M_t| ≤ c ‖G‖ (𝔼 sup_{t ≤ T} |δX_t|²)^{1/2} (𝔼
∫_0^T ‖δU_t‖²_{L²(ν)} dt)^{1/2} < ∞` and, for every `t ∈ [0, T]`, `𝔼[M_T − M_t] = 0` with
`M_T − M_t` integrable; the expectations of nonnegative quantities are read in `[0, ∞]`. -/
def eq_bdg4_XU : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
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
    (∃ M : ℝ → Ω → ℝ, IsLocalCompensatedIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
        (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T
        (fun ω s e => ∑ k, (G *ᵥ fun i => if s ∈ Set.Ioc (0 : ℝ) T then
          leftLimProc (fun a t ω => X₁ a t ω - X₂ a t ω) i s ω else 0) k
        * (U₁ k s ω e - U₂ k s ω e)) M)
    ∧ ∀ M : ℝ → Ω → ℝ, IsLocalCompensatedIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
        (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T
        (fun ω s e => ∑ k, (G *ᵥ fun i => if s ∈ Set.Ioc (0 : ℝ) T then
          leftLimProc (fun a t ω => X₁ a t ω - X₂ a t ω) i s ω else 0) k
        * (U₁ k s ω e - U₂ k s ω e)) M →
      ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
          ≤ ENNReal.ofReal (c * ‖GX G‖)
            * (∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁ i t ω - X₂ i t ω) ∂P) ^ (1 / 2 : ℝ)
            * (∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ k s ω e - U₂ k s ω e))
                ^ (1 / 2 : ℝ)
        ∧ ENNReal.ofReal (c * ‖GX G‖)
            * (∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁ i t ω - X₂ i t ω) ∂P) ^ (1 / 2 : ℝ)
            * (∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ k s ω e - U₂ k s ω e))
                ^ (1 / 2 : ℝ) < ⊤
        ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun ω => M T ω - M t ω) P
          ∧ ∫ ω, (M T ω - M t ω) ∂P = 0

/-- **The fourth bound of (4.18).** There is `c₀ > 0` such that, for every value `c ≥ c₀` of the
constant `c_BDG`, under the hypotheses of Lemma 4.3 — `T > 0`, coefficients with (2.3) and
Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix `G`, `λ̲ ∈ (0, 1]`,
`λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak` with `X^k_T ∈ L²`, `ℱ₀`-measurable
initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` — the forced jump integrand `λ δh + q^h` (with
`q = δq` and `δh` at the predictable tuples) agrees almost everywhere on `Ω × [0, T] × E` with an
integrand `H` meeting the conditions of the compensated integral, and for every such `H` the marked
integrand `⟨G H_s(e), δY_{s−}⟩` has a local compensated Poisson integral
`M_t = ∫_0^t ∫_E ⟨G (λ δh_s + q^h_s)(e), δY_{s−}⟩ Ñ(ds, de)` on `[0, T]`, and every such `M`
satisfies `𝔼 sup_{t ≤ T} |M_t| ≤ c ‖G‖ (𝔼 sup_{t ≤ T} |δY_t|²)^{1/2} (𝔼 ∫_0^T ‖λ δh_t +
q^h_t‖²_{L²(ν)} dt)^{1/2} < ∞` and, for every `t ∈ [0, T]`, `𝔼[M_T − M_t] = 0` with `M_T − M_t`
integrable; the expectations of nonnegative quantities are read in `[0, ∞]`. -/
def eq_bdg4_hY : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
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
    (∃ H : Fin n → Ω → ℝ → E → ℝ,
      (∀ i, Measurable fun p : Ω × ℝ × E => H i p.1 p.2.1 p.2.2)
      ∧ (∀ i, Probability.MarkedProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀) (H i))
      ∧ (∀ i, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖H i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
      ∧ ∀ i, ∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P ν T), H i p.1 p.2.1 p.2.2
          = lam * (jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
              p.2.1 p.1 p.2.2
            - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
              p.2.1 p.1 p.2.2) + (qh₁ i p.2.1 p.1 p.2.2 - qh₂ i p.2.1 p.1 p.2.2))
    ∧ ∀ H : Fin n → Ω → ℝ → E → ℝ,
      (∀ i, Measurable fun p : Ω × ℝ × E => H i p.1 p.2.1 p.2.2) →
      (∀ i, Probability.MarkedProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀) (H i)) →
      (∀ i, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖H i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) →
      (∀ i, ∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P ν T), H i p.1 p.2.1 p.2.2
        = lam * (jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
            p.2.1 p.1 p.2.2
          - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
            p.2.1 p.1 p.2.2) + (qh₁ i p.2.1 p.1 p.2.2 - qh₂ i p.2.1 p.1 p.2.2)) →
      (∃ M : ℝ → Ω → ℝ, IsLocalCompensatedIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
          (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T
          (fun ω s e => ∑ k, (G *ᵥ fun i => H i ω s e) k
          * (if s ∈ Set.Ioc (0 : ℝ) T then
              leftLimProc (fun a t ω => Y₁ a t ω - Y₂ a t ω) k s ω else 0)) M)
      ∧ ∀ M : ℝ → Ω → ℝ, IsLocalCompensatedIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
          (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T
          (fun ω s e => ∑ k, (G *ᵥ fun i => H i ω s e) k
          * (if s ∈ Set.Ioc (0 : ℝ) T then
              leftLimProc (fun a t ω => Y₁ a t ω - Y₂ a t ω) k s ω else 0)) M →
        ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
            ≤ ENNReal.ofReal (c * ‖GX G‖)
              * (∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω) ∂P) ^ (1 / 2 : ℝ)
              * (∑ i, Poisson.Compensated.markedEnergy P ν T (H i)) ^ (1 / 2 : ℝ)
          ∧ ENNReal.ofReal (c * ‖GX G‖)
              * (∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω) ∂P) ^ (1 / 2 : ℝ)
              * (∑ i, Poisson.Compensated.markedEnergy P ν T (H i)) ^ (1 / 2 : ℝ) < ⊤
          ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun ω => M T ω - M t ω) P
            ∧ ∫ ω, (M T ω - M t ω) ∂P = 0

/-- **The integrability of the forced integrands and of the fifth integrand of (4.17).** Under the
hypotheses of Lemma 4.3 — `T > 0`, coefficients with (2.3) and Assumptions 2.3–2.5 with constants
`L, α, β₁, β₂` and coupling matrix `G`, `λ̲ ∈ (0, 1]`, `λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at
`λ` in `ℍ_weak` with `X^k_T ∈ L²`, `ℱ₀`-measurable initial data `ξ₀^k`, forcings `q^k` and
`Θ¹ − Θ² ∈ ℍ` — `𝔼 ∫_0^T |λ δσ_t + q^σ_t|²_F dt < ∞`; the forced jump integrand `λ δh + q^h` (with
`q = δq` and `δh` at the predictable tuples) agrees almost everywhere on `Ω × [0, T] × E` with an
integrand `H` meeting the conditions of the compensated integral; and for every such `H`,
`𝔼 ∫_0^T ‖λ δh_t + q^h_t‖²_{L²(ν)} dt < ∞` and `𝔼 ∫_0^T ∫_E |⟨λ δh_t(e) + q^h_t(e), Gᵀ δU_t(e)⟩|
ν(de) dt ≤ ‖G‖ (𝔼 ∫_0^T ‖λ δh_t + q^h_t‖²_{L²(ν)} dt)^{1/2} (𝔼 ∫_0^T ‖δU_t‖²_{L²(ν)} dt)^{1/2} < ∞`;
the expectations of nonnegative quantities are read in `[0, ∞]`. -/
def eq_bdg4_fifth : Prop :=
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
  ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s =>
      lam * (diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
        - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) + (qσ₁ i s ω j - qσ₂ i s ω j)) < ⊤
  ∧ (∃ H : Fin n → Ω → ℝ → E → ℝ,
      (∀ i, Measurable fun p : Ω × ℝ × E => H i p.1 p.2.1 p.2.2)
      ∧ (∀ i, Probability.MarkedProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀) (H i))
      ∧ (∀ i, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖H i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
      ∧ ∀ i, ∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P ν T), H i p.1 p.2.1 p.2.2
          = lam * (jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
              p.2.1 p.1 p.2.2
            - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
              p.2.1 p.1 p.2.2) + (qh₁ i p.2.1 p.1 p.2.2 - qh₂ i p.2.1 p.1 p.2.2))
  ∧ ∀ H : Fin n → Ω → ℝ → E → ℝ,
      (∀ i, Measurable fun p : Ω × ℝ × E => H i p.1 p.2.1 p.2.2) →
      (∀ i, Probability.MarkedProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀) (H i)) →
      (∀ i, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖H i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) →
      (∀ i, ∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P ν T), H i p.1 p.2.1 p.2.2
        = lam * (jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i
            p.2.1 p.1 p.2.2
          - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i
            p.2.1 p.1 p.2.2) + (qh₁ i p.2.1 p.1 p.2.2 - qh₂ i p.2.1 p.1 p.2.2)) →
      ∑ i, Poisson.Compensated.markedEnergy P ν T (H i) < ⊤
      ∧ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal
            |(fun i => H i ω s e) ⬝ᵥ (Gᵀ *ᵥ fun k => U₁ k s ω e - U₂ k s ω e)| ∂ν ∂volume ∂P
          ≤ ENNReal.ofReal ‖GX G‖
            * (∑ i, Poisson.Compensated.markedEnergy P ν T (H i)) ^ (1 / 2 : ℝ)
            * (∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ k s ω e - U₂ k s ω e))
                ^ (1 / 2 : ℝ)
      ∧ ENNReal.ofReal ‖GX G‖
            * (∑ i, Poisson.Compensated.markedEnergy P ν T (H i)) ^ (1 / 2 : ℝ)
            * (∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ k s ω e - U₂ k s ω e))
                ^ (1 / 2 : ℝ) < ⊤

end Dissertation.PaperSpec.A
