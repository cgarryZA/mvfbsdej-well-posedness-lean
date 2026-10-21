/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4Frozen

/-!
# The contraction chain in the proof of Lemma 4.2

Statement and equation numbers refer to the well-posedness paper at `1f67672`. For two trials
`Θ¹, Θ² ∈ 𝕊` and their frozen steps `Θ̄ᵏ = Φ_λ(Θᵏ)` (4.7)–(4.8), with
`δψ_s = ψ(s, Θ¹_s, μ^{Θ¹}_s) − ψ(s, Θ²_s, μ^{Θ²}_s)` for `ψ ∈ {b, σ, h, f}`, `S_s` as in (4.9),
`L⋆² = 10 L² max{T, 1}`, `C_X = 3 max{T, c_BDG} L⋆²`, `C_g = 4 L²`,
`C_BP = C₀ (5 + 4 c_BDG) + 4T` with `C₀ = 2 e^T`, `C_Y = C_BP (C_g C_X + L⋆²)` and
`C_Φ = max{1, C_X + C_Y}`: the forward difference solves

`δX̄_t = λ ∫_0^t δb_s ds + λ ∫_0^t δσ_s dW_s + λ ∫_0^t ∫_E δh_s(e) Ñ(ds, de)`,

and

`𝔼 sup_{t ≤ T} |δX̄_t|² ≤ 3λ² [𝔼 (∫_0^T |δb_s| ds)² + 𝔼 sup_{t ≤ T} |∫_0^t δσ_s dW_s|²
    + 𝔼 sup_{t ≤ T} |∫_0^t ∫_E δh_s(e) Ñ(ds, de)|²]
  ≤ 3λ² [T 𝔼 ∫_0^T |δb_s|² ds + c_BDG 𝔼 ∫_0^T |δσ_s|²_F ds + c_BDG 𝔼 ∫_0^T ‖δh_s‖² ds]
  ≤ 3λ² max{T, c_BDG} 𝔼 ∫_0^T (|δb_s|² + |δσ_s|²_F + ‖δh_s‖²) ds
  ≤ 3λ² max{T, c_BDG} 𝔼 ∫_0^T S_s² ds ≤ C_X λ² ‖Θ¹ − Θ²‖²_𝕊`, (4.10)

`𝔼 sup_{t ≤ T} |δȲ_t|² + 𝔼 ∫_0^T (|δZ̄_s|²_F + ‖δŪ_s‖²) ds
  ≤ C_BP (𝔼|δξ̄|² + λ² 𝔼 ∫_0^T |δf_s|² ds)
  ≤ C_BP (C_g λ² 𝔼|δX̄_T|² + L⋆² λ² ‖Θ¹ − Θ²‖²_𝕊)
  ≤ C_BP (C_g λ² 𝔼 sup_{t ≤ T} |δX̄_t|² + L⋆² λ² ‖Θ¹ − Θ²‖²_𝕊)
  ≤ C_BP (C_g C_X λ⁴ + L⋆² λ²) ‖Θ¹ − Θ²‖²_𝕊 ≤ C_Y λ² ‖Θ¹ − Θ²‖²_𝕊`, (4.12)

with `δξ̄ = λ [g(X̄¹_T, Law(X̄¹_T)) − g(X̄²_T, Law(X̄²_T))]`, and

`‖Φ_λ(Θ¹) − Φ_λ(Θ²)‖²_𝕊 = 𝔼 sup_{t ≤ T} |δX̄_t|² + 𝔼 sup_{t ≤ T} |δȲ_t|²
    + 𝔼 ∫_0^T (|δZ̄_s|²_F + ‖δŪ_s‖²) ds
  ≤ (C_X + C_Y) λ² ‖Θ¹ − Θ²‖²_𝕊 ≤ C_Φ λ² ‖Θ¹ − Θ²‖²_𝕊`. (4.13)

`c_BDG` is the constant of the Burkholder–Davis–Gundy inequality fixed in §4; each proposition
asserts its chain for every value of it at least some `c₀ > 0`.

## Main definitions

* `Dissertation.PaperSpec.A.eq_fwddiff_identity` — the forward difference before (4.10).
* `Dissertation.PaperSpec.A.eq_fwddiff` — (4.10).
* `Dissertation.PaperSpec.A.eq_bwddiff` — (4.12).
* `Dissertation.PaperSpec.A.eq_contract` — (4.13).
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.WellPosedness.BrownianPoisson Dissertation.Law
  LevyStochCalc

universe u v w

/-- **The forward difference before (4.10).** In the standing setting, under the hypotheses of
Lemma 4.2 — `T > 0`, coefficients with (2.3) and Assumptions 2.2–2.3 with constant `L` and initial
datum `ξ₀` — for `λ ∈ [0, 1]`, a forcing `q` of the class of (4.1), two trial tuples `Θ¹, Θ²` of
`𝕊` and their frozen steps `Θ̄ᵏ = Φ_λ(Θᵏ)` (`FrozenStep`, with the same `λ`, `ξ₀` and `q`), with
`δb, δσ, δh` the coefficient differences at `(Θᵏ_s, Law(Θᵏ_s))` (the jump coefficient through its
representative `coeffJump`): `δσ` and `δh` meet the conditions of the Itô and compensated
integrals, almost every path of `δb` is integrable on `[0, T]`, and for every `t ∈ [0, T]`,
almost surely,
`δX̄_t = λ ∫_0^t δb_s ds + λ ∫_0^t δσ_s dW_s + λ ∫_0^t ∫_E δh_s(e) Ñ(ds, de)`;
with any version of `∫_0^t δσ_s dW_s` almost every path of which is right-continuous on `[0, T)`,
the identity holds almost surely at every `t ∈ [0, T]` at once. -/
def eq_fwddiff_identity : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d) (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
    ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    ∀ (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
      (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb qσ qh qf qg →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₁ Y₁ Z₁ U₁ → HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₂ Y₂ Z₂ U₂ →
    ∀ (X₁' X₂' : Fin n → ℝ → Ω → ℝ) (Y₁' Y₂' : Fin m → ℝ → Ω → ℝ)
      (Z₁' Z₂' : Fin m → ℝ → Ω → Fin d → ℝ) (U₁' U₂' : Fin m → ℝ → Ω → E → ℝ),
    FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₁ Y₁ Z₁ U₁ X₁' Y₁' Z₁' U₁' →
    FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₂ Y₂ Z₂ U₂ X₂' Y₂' Z₂' U₂' →
    ∃ (hσm : ∀ i j, Measurable (Function.uncurry fun ω s =>
          diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j))
      (hσp : ∀ i j, Probability.ProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀) fun ω s =>
          diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
      (hσq : ∀ i j, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
      (hhm : ∀ i, Measurable fun p : Ω × ℝ × E =>
          coeffJump P T C X₁ Y₁ Z₁ U₁ i p.2.1 p.1 p.2.2
            - coeffJump P T C X₂ Y₂ Z₂ U₂ i p.2.1 p.1 p.2.2)
      (hhp : ∀ i, Probability.MarkedProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀) fun ω s e =>
          coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e)
      (hhq : ∀ i, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
            - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
      (∀ i, ∀ᵐ ω ∂P, IntegrableOn (fun s =>
          driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
          (Set.Icc (0 : ℝ) T))
      ∧ (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
          X₁' i t ω - X₂' i t ω
            = lam * (∫ s in Set.Icc (0 : ℝ) t,
                driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
              + lam * Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
                  (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
                  (fun s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
                    - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) (hσm i) (hσp i) (hσq i) t ω
              + lam * Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
                  (isPoissonFiltration_enlJoint D h𝒢₀ hind₀)
                  (fun ω s e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
                    - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e) (hhm i) (hhp i) (hhq i) t ω)
      ∧ ∀ Mσ : Fin n → ℝ → Ω → ℝ,
        (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Mσ i t =ᵐ[P]
          Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
            (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
            (fun s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
              - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) (hσm i) (hσp i) (hσq i) t) →
        (∀ i, ∀ᵐ ω ∂P,
          ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => Mσ i s ω) (𝓝[>] t) (𝓝 (Mσ i t ω))) →
        ∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
          X₁' i t ω - X₂' i t ω
            = lam * (∫ s in Set.Icc (0 : ℝ) t,
                driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
              + lam * Mσ i t ω
              + lam * Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
                  (isPoissonFiltration_enlJoint D h𝒢₀ hind₀)
                  (fun ω s e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
                    - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e) (hhm i) (hhp i) (hhq i) t ω

/-- **(4.10).** There is `c₀ > 0` such that, for every value `c ≥ c₀` of the constant `c_BDG`: in
the standing setting, under the hypotheses of Lemma 4.2 — `T > 0`, coefficients with (2.3) and
Assumptions 2.2–2.3 with constant `L` and initial datum `ξ₀` — for `λ ∈ [0, 1]`, a forcing `q` of
the class of (4.1), two trial tuples `Θ¹, Θ²` of `𝕊` and their frozen steps `Θ̄ᵏ = Φ_λ(Θᵏ)`
(`FrozenStep`, with the same `λ`, `ξ₀` and `q`), with `δb, δσ, δh` the coefficient differences at
`(Θᵏ_s, Law(Θᵏ_s))` (the jump coefficient through its representative `coeffJump`): `δσ` and `δh`
meet the conditions of the Itô and compensated integrals; `∫_0^t δσ_s dW_s` has a càdlàg version
on `[0, T]`; and, with any such version,
`𝔼 sup_{t ≤ T} |δX̄_t|² ≤ 3λ² [𝔼 (∫_0^T |δb_s| ds)² + 𝔼 sup_{t ≤ T} |∫_0^t δσ_s dW_s|²
    + 𝔼 sup_{t ≤ T} |∫_0^t ∫_E δh_s(e) Ñ(ds, de)|²]
  ≤ 3λ² [T 𝔼 ∫_0^T |δb_s|² ds + c 𝔼 ∫_0^T |δσ_s|²_F ds + c 𝔼 ∫_0^T ‖δh_s‖²_{L²(ν)} ds]
  ≤ 3λ² max{T, c} 𝔼 ∫_0^T (|δb_s|² + |δσ_s|²_F + ‖δh_s‖²_{L²(ν)}) ds
  ≤ 3λ² max{T, c} 𝔼 ∫_0^T S_s² ds ≤ C_X λ² ‖Θ¹ − Θ²‖²_𝕊`,
`C_X = 3 max{T, c} · 10 L² max{T, 1}`, the expectations read in `[0, ∞]`. -/
def eq_fwddiff : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d) (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
    ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    ∀ (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
      (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb qσ qh qf qg →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₁ Y₁ Z₁ U₁ → HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₂ Y₂ Z₂ U₂ →
    ∀ (X₁' X₂' : Fin n → ℝ → Ω → ℝ) (Y₁' Y₂' : Fin m → ℝ → Ω → ℝ)
      (Z₁' Z₂' : Fin m → ℝ → Ω → Fin d → ℝ) (U₁' U₂' : Fin m → ℝ → Ω → E → ℝ),
    FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₁ Y₁ Z₁ U₁ X₁' Y₁' Z₁' U₁' →
    FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₂ Y₂ Z₂ U₂ X₂' Y₂' Z₂' U₂' →
    ∃ (hσm : ∀ i j, Measurable (Function.uncurry fun ω s =>
          diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j))
      (hσp : ∀ i j, Probability.ProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀) fun ω s =>
          diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
      (hσq : ∀ i j, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
            - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
      (hhm : ∀ i, Measurable fun p : Ω × ℝ × E =>
          coeffJump P T C X₁ Y₁ Z₁ U₁ i p.2.1 p.1 p.2.2
            - coeffJump P T C X₂ Y₂ Z₂ U₂ i p.2.1 p.1 p.2.2)
      (hhp : ∀ i, Probability.MarkedProgressivelyMeasurable (enlJoint 𝒢₀ D h𝒢₀) fun ω s e =>
          coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e)
      (hhq : ∀ i, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
            - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
      (∃ Mσ : Fin n → ℝ → Ω → ℝ,
        (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Mσ i t =ᵐ[P]
          Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
            (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
            (fun s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
              - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) (hσm i) (hσp i) (hσq i) t)
        ∧ ∀ i, ∀ᵐ ω ∂P,
          (∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => Mσ i s ω) (𝓝[>] t) (𝓝 (Mσ i t ω)))
          ∧ ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Mσ i s ω) (𝓝[<] t) (𝓝 l))
      ∧ (∀ Mσ : Fin n → ℝ → Ω → ℝ,
        (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Mσ i t =ᵐ[P]
          Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
            (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
            (fun s ω j => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
              - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j) (hσm i) (hσp i) (hσq i) t) →
        (∀ i, ∀ᵐ ω ∂P,
          (∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => Mσ i s ω) (𝓝[>] t) (𝓝 (Mσ i t ω)))
          ∧ ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Mσ i s ω) (𝓝[<] t) (𝓝 l)) →
        ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁' i t ω - X₂' i t ω)) ∂P
          ≤ ENNReal.ofReal (3 * lam ^ 2)
            * (∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
                ‖(WithLp.toLp 2 fun i => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
                  - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s : EuclideanSpace ℝ (Fin n))‖ₑ) ^ 2 ∂P
              + ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => Mσ i t ω)) ∂P
              + ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i =>
                  Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
                    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀)
                    (fun ω s e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
                      - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e) (hhm i) (hhp i) (hhq i) t ω)) ∂P)
        ∧ ENNReal.ofReal (3 * lam ^ 2)
            * (∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
                ‖(WithLp.toLp 2 fun i => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
                  - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s : EuclideanSpace ℝ (Fin n))‖ₑ) ^ 2 ∂P
              + ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => Mσ i t ω)) ∂P
              + ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i =>
                  Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
                    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀)
                    (fun ω s e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
                      - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e) (hhm i) (hhp i) (hhq i) t ω)) ∂P)
          ≤ ENNReal.ofReal (3 * lam ^ 2)
            * (ENNReal.ofReal T * ∑ i, Brownian.Ito.energy P T
                (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
              + ENNReal.ofReal c * ∑ i, ∑ j, Brownian.Ito.energy P T
                (fun ω s => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
                  - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
              + ENNReal.ofReal c * ∑ i, Poisson.Compensated.markedEnergy P ν T
                (fun ω s e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
                  - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e)))
      ∧ ENNReal.ofReal (3 * lam ^ 2)
            * (ENNReal.ofReal T * ∑ i, Brownian.Ito.energy P T
                (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
              + ENNReal.ofReal c * ∑ i, ∑ j, Brownian.Ito.energy P T
                (fun ω s => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
                  - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
              + ENNReal.ofReal c * ∑ i, Poisson.Compensated.markedEnergy P ν T
                (fun ω s e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
                  - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e))
          ≤ ENNReal.ofReal (3 * lam ^ 2 * max T c)
            * (∑ i, Brownian.Ito.energy P T
                (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
              + ∑ i, ∑ j, Brownian.Ito.energy P T
                (fun ω s => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
                  - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
              + ∑ i, Poisson.Compensated.markedEnergy P ν T
                (fun ω s e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
                  - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e))
      ∧ ENNReal.ofReal (3 * lam ^ 2 * max T c)
            * (∑ i, Brownian.Ito.energy P T
                (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
              + ∑ i, ∑ j, Brownian.Ito.energy P T
                (fun ω s => diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
                  - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
              + ∑ i, Poisson.Compensated.markedEnergy P ν T
                (fun ω s e => coeffJump P T C X₁ Y₁ Z₁ U₁ i s ω e
                  - coeffJump P T C X₂ Y₂ Z₂ U₂ i s ω e))
          ≤ ENNReal.ofReal (3 * lam ^ 2 * max T c) * ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω,
              coeffDiffNorm P C (tupleAt ν X₁ Y₁ Z₁ U₁) (tupleAt ν X₂ Y₂ Z₂ U₂) s ω ^ 2 ∂P
      ∧ ENNReal.ofReal (3 * lam ^ 2 * max T c) * ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω,
              coeffDiffNorm P C (tupleAt ν X₁ Y₁ Z₁ U₁) (tupleAt ν X₂ Y₂ Z₂ U₂) s ω ^ 2 ∂P
          ≤ ENNReal.ofReal (3 * max T c * (10 * L ^ 2 * max T 1) * lam ^ 2)
            * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
              (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)

/-- **(4.12).** There is `c₀ > 0` such that, for every value `c ≥ c₀` of the constant `c_BDG`: in
the standing setting, under the hypotheses of Lemma 4.2 — `T > 0`, coefficients with (2.3) and
Assumptions 2.2–2.3 with constant `L` and initial datum `ξ₀` — for `λ ∈ [0, 1]`, a forcing `q` of
the class of (4.1), two trial tuples `Θ¹, Θ²` of `𝕊` and their frozen steps `Θ̄ᵏ = Φ_λ(Θᵏ)`
(`FrozenStep`, with the same `λ`, `ξ₀` and `q`), with
`δξ̄ = λ [g(X̄¹_T, Law(X̄¹_T)) − g(X̄²_T, Law(X̄²_T))]` and `δf` the driver difference at
`(Θᵏ_s, Law(Θᵏ_s))`,
`𝔼 sup_{t ≤ T} |δȲ_t|² + 𝔼 ∫_0^T (|δZ̄_s|²_F + ‖δŪ_s‖²_{L²(ν)}) ds
  ≤ C_BP (𝔼|δξ̄|² + λ² 𝔼 ∫_0^T |δf_s|² ds)
  ≤ C_BP (C_g λ² 𝔼|δX̄_T|² + L⋆² λ² ‖Θ¹ − Θ²‖²_𝕊)
  ≤ C_BP (C_g λ² 𝔼 sup_{t ≤ T} |δX̄_t|² + L⋆² λ² ‖Θ¹ − Θ²‖²_𝕊)
  ≤ C_BP (C_g C_X λ⁴ + L⋆² λ²) ‖Θ¹ − Θ²‖²_𝕊 ≤ C_Y λ² ‖Θ¹ − Θ²‖²_𝕊`,
with `C_BP = 2 e^T (5 + 4c) + 4T`, `C_g = 4 L²`, `L⋆² = 10 L² max{T, 1}`,
`C_X = 3 max{T, c} L⋆²` and `C_Y = C_BP (C_g C_X + L⋆²)`, the expectations read in `[0, ∞]`. -/
def eq_bwddiff : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d) (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
    ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    ∀ (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
      (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb qσ qh qf qg →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₁ Y₁ Z₁ U₁ → HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₂ Y₂ Z₂ U₂ →
    ∀ (X₁' X₂' : Fin n → ℝ → Ω → ℝ) (Y₁' Y₂' : Fin m → ℝ → Ω → ℝ)
      (Z₁' Z₂' : Fin m → ℝ → Ω → Fin d → ℝ) (U₁' U₂' : Fin m → ℝ → Ω → E → ℝ),
    FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₁ Y₁ Z₁ U₁ X₁' Y₁' Z₁' U₁' →
    FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₂ Y₂ Z₂ U₂ X₂' Y₂' Z₂' U₂' →
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁' k t ω - Y₂' k t ω)) ∂P
        + ((∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁' k s ω j - Z₂' k s ω j))
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁' k s ω e - U₂' k s ω e))
      ≤ ENNReal.ofReal (2 * Real.exp T * (5 + 4 * c) + 4 * T)
        * (∫⁻ ω, esq (fun k => lam * (terminalVal P T C X₁' k ω - terminalVal P T C X₂' k ω)) ∂P
          + ENNReal.ofReal (lam ^ 2) * ∑ k, Brownian.Ito.energy P T
            (fun ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s))
    ∧ ENNReal.ofReal (2 * Real.exp T * (5 + 4 * c) + 4 * T)
        * (∫⁻ ω, esq (fun k => lam * (terminalVal P T C X₁' k ω - terminalVal P T C X₂' k ω)) ∂P
          + ENNReal.ofReal (lam ^ 2) * ∑ k, Brownian.Ito.energy P T
            (fun ω s => driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s))
      ≤ ENNReal.ofReal (2 * Real.exp T * (5 + 4 * c) + 4 * T)
        * (ENNReal.ofReal (4 * L ^ 2 * lam ^ 2)
            * ∫⁻ ω, esq (fun i => X₁' i T ω - X₂' i T ω) ∂P
          + ENNReal.ofReal (10 * L ^ 2 * max T 1 * lam ^ 2)
            * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
              (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e))
    ∧ ENNReal.ofReal (2 * Real.exp T * (5 + 4 * c) + 4 * T)
        * (ENNReal.ofReal (4 * L ^ 2 * lam ^ 2)
            * ∫⁻ ω, esq (fun i => X₁' i T ω - X₂' i T ω) ∂P
          + ENNReal.ofReal (10 * L ^ 2 * max T 1 * lam ^ 2)
            * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
              (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e))
      ≤ ENNReal.ofReal (2 * Real.exp T * (5 + 4 * c) + 4 * T)
        * (ENNReal.ofReal (4 * L ^ 2 * lam ^ 2)
            * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁' i t ω - X₂' i t ω)) ∂P
          + ENNReal.ofReal (10 * L ^ 2 * max T 1 * lam ^ 2)
            * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
              (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e))
    ∧ ENNReal.ofReal (2 * Real.exp T * (5 + 4 * c) + 4 * T)
        * (ENNReal.ofReal (4 * L ^ 2 * lam ^ 2)
            * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁' i t ω - X₂' i t ω)) ∂P
          + ENNReal.ofReal (10 * L ^ 2 * max T 1 * lam ^ 2)
            * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
              (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e))
      ≤ ENNReal.ofReal (2 * Real.exp T * (5 + 4 * c) + 4 * T)
        * (ENNReal.ofReal (4 * L ^ 2 * (3 * max T c * (10 * L ^ 2 * max T 1)) * lam ^ 4
            + 10 * L ^ 2 * max T 1 * lam ^ 2)
          * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
            (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e))
    ∧ ENNReal.ofReal (2 * Real.exp T * (5 + 4 * c) + 4 * T)
        * (ENNReal.ofReal (4 * L ^ 2 * (3 * max T c * (10 * L ^ 2 * max T 1)) * lam ^ 4
            + 10 * L ^ 2 * max T 1 * lam ^ 2)
          * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
            (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e))
      ≤ ENNReal.ofReal ((2 * Real.exp T * (5 + 4 * c) + 4 * T)
          * (4 * L ^ 2 * (3 * max T c * (10 * L ^ 2 * max T 1)) + 10 * L ^ 2 * max T 1) * lam ^ 2)
        * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
          (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)

/-- **(4.13).** There is `c₀ > 0` such that, for every value `c ≥ c₀` of the constant `c_BDG`: in
the standing setting, under the hypotheses of Lemma 4.2 — `T > 0`, coefficients with (2.3) and
Assumptions 2.2–2.3 with constant `L` and initial datum `ξ₀` — for `λ ∈ [0, 1]`, a forcing `q` of
the class of (4.1), two trial tuples `Θ¹, Θ²` of `𝕊` and their frozen steps `Θ̄ᵏ = Φ_λ(Θᵏ)`
(`FrozenStep`, with the same `λ`, `ξ₀` and `q`),
`‖Φ_λ(Θ¹) − Φ_λ(Θ²)‖²_𝕊 = 𝔼 sup_{t ≤ T} |δX̄_t|² + 𝔼 sup_{t ≤ T} |δȲ_t|²
    + 𝔼 ∫_0^T (|δZ̄_s|²_F + ‖δŪ_s‖²_{L²(ν)}) ds
  ≤ (C_X + C_Y) λ² ‖Θ¹ − Θ²‖²_𝕊 ≤ C_Φ λ² ‖Θ¹ − Θ²‖²_𝕊`,
with `L⋆² = 10 L² max{T, 1}`, `C_X = 3 max{T, c} L⋆²`, `C_BP = 2 e^T (5 + 4c) + 4T`,
`C_Y = C_BP (4 L² C_X + L⋆²)` and `C_Φ = max{1, C_X + C_Y}`, the expectations read in `[0, ∞]`. -/
def eq_contract : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d) (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
    ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    ∀ (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
      (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb qσ qh qf qg →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₁ Y₁ Z₁ U₁ → HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₂ Y₂ Z₂ U₂ →
    ∀ (X₁' X₂' : Fin n → ℝ → Ω → ℝ) (Y₁' Y₂' : Fin m → ℝ → Ω → ℝ)
      (Z₁' Z₂' : Fin m → ℝ → Ω → Fin d → ℝ) (U₁' U₂' : Fin m → ℝ → Ω → E → ℝ),
    FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₁ Y₁ Z₁ U₁ X₁' Y₁' Z₁' U₁' →
    FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₂ Y₂ Z₂ U₂ X₂' Y₂' Z₂' U₂' →
    supSize P ν T (fun i t ω => X₁' i t ω - X₂' i t ω) (fun k t ω => Y₁' k t ω - Y₂' k t ω)
        (fun k t ω j => Z₁' k t ω j - Z₂' k t ω j) (fun k t ω e => U₁' k t ω e - U₂' k t ω e)
      = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁' i t ω - X₂' i t ω)) ∂P
        + ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁' k t ω - Y₂' k t ω)) ∂P
        + ((∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁' k s ω j - Z₂' k s ω j))
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁' k s ω e - U₂' k s ω e))
    ∧ supSize P ν T (fun i t ω => X₁' i t ω - X₂' i t ω) (fun k t ω => Y₁' k t ω - Y₂' k t ω)
        (fun k t ω j => Z₁' k t ω j - Z₂' k t ω j) (fun k t ω e => U₁' k t ω e - U₂' k t ω e)
      ≤ ENNReal.ofReal ((3 * max T c * (10 * L ^ 2 * max T 1)
          + (2 * Real.exp T * (5 + 4 * c) + 4 * T)
            * (4 * L ^ 2 * (3 * max T c * (10 * L ^ 2 * max T 1)) + 10 * L ^ 2 * max T 1))
          * lam ^ 2)
        * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
          (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
    ∧ ENNReal.ofReal ((3 * max T c * (10 * L ^ 2 * max T 1)
          + (2 * Real.exp T * (5 + 4 * c) + 4 * T)
            * (4 * L ^ 2 * (3 * max T c * (10 * L ^ 2 * max T 1)) + 10 * L ^ 2 * max T 1))
          * lam ^ 2)
        * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
          (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      ≤ ENNReal.ofReal (max 1 (3 * max T c * (10 * L ^ 2 * max T 1)
          + (2 * Real.exp T * (5 + 4 * c) + 4 * T)
            * (4 * L ^ 2 * (3 * max T c * (10 * L ^ 2 * max T 1)) + 10 * L ^ 2 * max T 1))
          * lam ^ 2)
        * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
          (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)

end Dissertation.PaperSpec.A
