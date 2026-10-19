/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4

/-!
# The Young bound (4.25) of the proof of Lemma 4.3 of the well-posedness paper

Statement and equation numbers refer to the well-posedness paper at `f598204`. Step 4 of the
proof of Lemma 4.3 bounds the driver pairing of the backward difference equation (4.16): by
Assumption 2.3, the coupling bound (2.8) and Young's inequality, for every `ε > 0`,

`2 𝔼⟨δY_s, λ δf_s + q^f_s⟩ ≤ (C/ε) 𝔼|δY_s|² + ε 𝔼(|δZ_s|²_F + ‖δU_s‖²)
  + (C/ε) 𝔼(|δX_s|² + |q^f_s|²)`,   (4.25)

with `C` independent of `ε`, where `q^f` is the difference `δq^f` of the driver forcings. The
proof only uses `ε < 1`.

## Main definitions

* `Dissertation.PaperSpec.A.eq_bwdyoung` — (4.25) for every `ε > 0`, as printed.
* `Dissertation.PaperSpec.A.eq_bwdyoung_corr` — (4.25) for every `ε ∈ (0, 1]`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec LevyStochCalc

universe u v w

/-- **(4.25), as printed.** There is a function `K` of `(T, L, ‖G‖, c_G, α, β₁, β₂, λ̲)` such
that: in the standing setting, under the hypotheses of Lemma 4.3 — `T > 0`, coefficients with
(2.3) and Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix `G`,
`λ̲ ∈ (0, 1]`, `λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak` with `X^k_T ∈ L²`,
`ℱ₀`-measurable initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` — for every `ε > 0`, at
almost every `s ∈ [0, T]`,
`2 𝔼⟨δY_s, λ δf_s + δq^f_s⟩ ≤ (C/ε) 𝔼|δY_s|² + ε 𝔼(|δZ_s|²_F + ‖δU_s‖²_{L²(ν)})
  + (C/ε) 𝔼(|δX_s|² + |δq^f_s|²)`,
with `C = K(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂, λ̲)`, `δf_s = f(s, Θ¹_s, μ¹_s) − f(s, Θ²_s, μ²_s)`
and `μ^k_s = Law(Θ^k_s)`. The expectations on the right are read in `[0, ∞]`, and the left side,
a Bochner integral, through its positive part. -/
def eq_bwdyoung : Prop :=
  ∃ K : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
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
    ∀ ε : ℝ, 0 < ε →
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ENNReal.ofReal (2 * ∫ ω, ∑ k, (Y₁ k s ω - Y₂ k s ω)
          * (lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
            + (qf₁ k ω s - qf₂ k ω s)) ∂P)
        ≤ ENNReal.ofReal (K T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ lamLow / ε)
            * ∫⁻ ω, esq (fun k => Y₁ k s ω - Y₂ k s ω) ∂P
          + ENNReal.ofReal ε * ∫⁻ ω, (∑ k, esq (fun j => Z₁ k s ω j - Z₂ k s ω j)
              + ∑ k, ∫⁻ e, (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P
          + ENNReal.ofReal (K T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ lamLow / ε)
            * ∫⁻ ω, (esq (fun i => X₁ i s ω - X₂ i s ω)
              + esq (fun k => qf₁ k ω s - qf₂ k ω s)) ∂P

/-- **(4.25) for `ε ∈ (0, 1]`.** The statement `eq_bwdyoung` with `ε > 0` replaced by
`0 < ε ≤ 1`: there is a function `K` of `(T, L, ‖G‖, c_G, α, β₁, β₂, λ̲)` such that, under the
hypotheses of Lemma 4.3, for every `ε ∈ (0, 1]`, at almost every `s ∈ [0, T]`,
`2 𝔼⟨δY_s, λ δf_s + δq^f_s⟩ ≤ (C/ε) 𝔼|δY_s|² + ε 𝔼(|δZ_s|²_F + ‖δU_s‖²_{L²(ν)})
  + (C/ε) 𝔼(|δX_s|² + |δq^f_s|²)`,
with `C = K(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂, λ̲)`. -/
def eq_bwdyoung_corr : Prop :=
  ∃ K : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
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
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ENNReal.ofReal (2 * ∫ ω, ∑ k, (Y₁ k s ω - Y₂ k s ω)
          * (lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s)
            + (qf₁ k ω s - qf₂ k ω s)) ∂P)
        ≤ ENNReal.ofReal (K T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ lamLow / ε)
            * ∫⁻ ω, esq (fun k => Y₁ k s ω - Y₂ k s ω) ∂P
          + ENNReal.ofReal ε * ∫⁻ ω, (∑ k, esq (fun j => Z₁ k s ω j - Z₂ k s ω j)
              + ∑ k, ∫⁻ e, (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P
          + ENNReal.ofReal (K T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ lamLow / ε)
            * ∫⁻ ω, (esq (fun i => X₁ i s ω - X₂ i s ω)
              + esq (fun k => qf₁ k ω s - qf₂ k ω s)) ∂P

end Dissertation.PaperSpec.A
