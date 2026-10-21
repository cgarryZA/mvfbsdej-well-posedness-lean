/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4

/-!
# Steps 3 and 4 of the proof of Lemma 4.3 of the well-posedness paper

Statement and equation numbers refer to the well-posedness paper at `1f67672`. In the proof of
Lemma 4.3 the forcings enter only through their difference `δq`, written `q`; `P` is the data size
of (4.14), and `C` is a constant depending only on `T, L, ‖G‖, c_G, α, β₁, β₂` (§4). Step 3 bounds
the forward difference,

`𝔼 sup_{t ≤ T} |δX_t|² ≤ C (𝔼 ∫_0^T (|δY_t|² + |δZ_t|²_F + ‖δU_t‖²) dt + P)`, (4.23)

and Step 4 the backward one: Itô's formula for `e^{κt} |δY_t|²` gives, for `κ > 0` and every `t`,

`𝔼 e^{κt} |δY_t|² + 𝔼 ∫_t^T e^{κs} (κ |δY_s|² + |δZ_s|²_F + ‖δU_s‖²) ds
  ≤ 𝔼 e^{κT} |λ δg_T + q^g_T|² + 2 𝔼 ∫_t^T e^{κs} ⟨δY_s, λ δf_s + q^f_s⟩ ds`, (4.24)

and the Young bound (4.25), the choice of `ε` and `κ`, and BDG then give

`sup_{t ≤ T} 𝔼|δY_t|² + 𝔼 ∫_0^T (|δZ_t|²_F + ‖δU_t‖²) dt ≤ C (𝔼|δX_T|² + 𝔼 ∫_0^T |δX_t|² dt + P)`,
(4.26)

`𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ_t|²_F + ‖δU_t‖²) dt ≤ C (𝔼|δX_T|² + 𝔼 ∫_0^T |δX_t|² dt + P)`.
(4.27)

## Main definitions

* `Dissertation.PaperSpec.A.eq_fwd` — (4.23).
* `Dissertation.PaperSpec.A.eq_bwdito` — (4.24).
* `Dissertation.PaperSpec.A.eq_wgt` — (4.26).
* `Dissertation.PaperSpec.A.eq_bwd` — (4.27).
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec LevyStochCalc

universe u v w

/-- **(4.23).** There is a function `K` of `(T, L, ‖G‖, c_G, α, β₁, β₂)` such that: in the
standing setting, under the hypotheses of Lemma 4.3 — `T > 0`, coefficients with (2.3) and
Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix `G`, `λ̲ ∈ (0, 1]`,
`λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ²` with `X^k_T ∈ L²`, `ℱ₀`-measurable
initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ 𝕊` —
`𝔼 sup_{t ≤ T} |δX_t|² ≤ C (𝔼 ∫_0^T (|δY_t|² + |δZ_t|²_F + ‖δU_t‖²_{L²(ν)}) dt + P)`
with `C = K(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂)`, `P` the data size of (4.14) of the differences
of the data, and the expectations read in `[0, ∞]`. -/
def eq_fwd : Prop :=
  ∃ K : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
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
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁ i t ω - X₂ i t ω)) ∂P
      ≤ ENNReal.ofReal (K T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
        * (∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω)
          + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ k s ω e - U₂ k s ω e)
          + dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
          (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
          (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω))

/-- **(4.24).** In the standing setting, under the hypotheses of Lemma 4.3 — `T > 0`, coefficients
with (2.3) and Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix `G`,
`λ̲ ∈ (0, 1]`, `λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ²` with `X^k_T ∈ L²`,
`ℱ₀`-measurable initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ 𝕊` —
for every `κ > 0` and every `t ∈ [0, T]`, the functions `|δY_t|²`, `|λ δg_T + q^g_T|²` (on `Ω`),
`e^{κs} (κ |δY_s|² + |δZ_s|²_F + ‖δU_s‖²_{L²(ν)})` and `e^{κs} ⟨δY_s, λ δf_s + q^f_s⟩` (on
`Ω × [t, T]`) are integrable, and
`𝔼 e^{κt} |δY_t|² + 𝔼 ∫_t^T e^{κs} (κ |δY_s|² + |δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds
  ≤ 𝔼 e^{κT} |λ δg_T + q^g_T|² + 2 𝔼 ∫_t^T e^{κs} ⟨δY_s, λ δf_s + q^f_s⟩ ds`,
with `q = δq`, `δg_T = g(X¹_T, Law X¹_T) − g(X²_T, Law X²_T)` and
`δf_s = f(s, Θ¹_s, μ¹_s) − f(s, Θ²_s, μ²_s)`. -/
def eq_bwdito : Prop :=
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
    ∀ κ : ℝ, 0 < κ → ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun ω => ∑ k, (Y₁ k t ω - Y₂ k t ω) ^ 2) P
      ∧ Integrable (fun ω => ∑ k, (lam * (terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
          + (qg₁ k ω - qg₂ k ω)) ^ 2) P
      ∧ Integrable (fun p : Ω × ℝ => Real.exp (κ * p.2)
          * (κ * ∑ k, (Y₁ k p.2 p.1 - Y₂ k p.2 p.1) ^ 2
            + ∑ k, ∑ j, (Z₁ k p.2 p.1 j - Z₂ k p.2 p.1 j) ^ 2
            + ∑ k, ∫ e, (U₁ k p.2 p.1 e - U₂ k p.2 p.1 e) ^ 2 ∂ν))
        (P.prod (volume.restrict (Set.Icc t T)))
      ∧ Integrable (fun p : Ω × ℝ => Real.exp (κ * p.2)
          * ∑ k, (Y₁ k p.2 p.1 - Y₂ k p.2 p.1)
            * (lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k p.1 p.2
              - driverProc P T C X₂ Y₂ Z₂ U₂ k p.1 p.2) + (qf₁ k p.1 p.2 - qf₂ k p.1 p.2)))
        (P.prod (volume.restrict (Set.Icc t T)))
      ∧ Real.exp (κ * t) * ∫ ω, ∑ k, (Y₁ k t ω - Y₂ k t ω) ^ 2 ∂P
          + ∫ ω, ∫ s in Set.Icc t T, Real.exp (κ * s)
            * (κ * ∑ k, (Y₁ k s ω - Y₂ k s ω) ^ 2 + ∑ k, ∑ j, (Z₁ k s ω j - Z₂ k s ω j) ^ 2
              + ∑ k, ∫ e, (U₁ k s ω e - U₂ k s ω e) ^ 2 ∂ν) ∂volume ∂P
        ≤ Real.exp (κ * T) * ∫ ω, ∑ k, (lam * (terminalVal P T C X₁ k ω
            - terminalVal P T C X₂ k ω) + (qg₁ k ω - qg₂ k ω)) ^ 2 ∂P
          + 2 * ∫ ω, ∫ s in Set.Icc t T, Real.exp (κ * s) * ∑ k, (Y₁ k s ω - Y₂ k s ω)
            * (lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
              + (qf₁ k ω s - qf₂ k ω s)) ∂volume ∂P

/-- **(4.26).** There is a function `K` of `(T, L, ‖G‖, c_G, α, β₁, β₂)` such that: in the
standing setting, under the hypotheses of Lemma 4.3 — `T > 0`, coefficients with (2.3) and
Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix `G`, `λ̲ ∈ (0, 1]`,
`λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ²` with `X^k_T ∈ L²`, `ℱ₀`-measurable
initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ 𝕊` —
`sup_{t ≤ T} 𝔼|δY_t|² + 𝔼 ∫_0^T (|δZ_t|²_F + ‖δU_t‖²_{L²(ν)}) dt
  ≤ C (𝔼|δX_T|² + 𝔼 ∫_0^T |δX_t|² dt + P)`
with `C = K(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂)`, `P` the data size of (4.14) of the differences
of the data, and the expectations read in `[0, ∞]`. -/
def eq_wgt : Prop :=
  ∃ K : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
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
    (⨆ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, esq (fun k => Y₁ k t ω - Y₂ k t ω) ∂P)
      + ((∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j))
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ k s ω e - U₂ k s ω e))
      ≤ ENNReal.ofReal (K T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
        * (∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P
          + ∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)
          + dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
          (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
          (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω))

/-- **(4.27).** There is a function `K` of `(T, L, ‖G‖, c_G, α, β₁, β₂)` such that: in the
standing setting, under the hypotheses of Lemma 4.3 — `T > 0`, coefficients with (2.3) and
Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix `G`, `λ̲ ∈ (0, 1]`,
`λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ²` with `X^k_T ∈ L²`, `ℱ₀`-measurable
initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ 𝕊` —
`𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ_t|²_F + ‖δU_t‖²_{L²(ν)}) dt
  ≤ C (𝔼|δX_T|² + 𝔼 ∫_0^T |δX_t|² dt + P)`
with `C = K(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂)`, `P` the data size of (4.14) of the differences
of the data, and the expectations read in `[0, ∞]`. -/
def eq_bwd : Prop :=
  ∃ K : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
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
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω)) ∂P
      + ((∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j))
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ k s ω e - U₂ k s ω e))
      ≤ ENNReal.ofReal (K T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
        * (∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P
          + ∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)
          + dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
          (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
          (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω))

end Dissertation.PaperSpec.A
