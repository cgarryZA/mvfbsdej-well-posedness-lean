/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Setting

/-!
# Section 4 of the well-posedness paper: the lemmas of the proof

Statement and equation numbers refer to the well-posedness paper at `1f67672`.

## Main definitions

* `Dissertation.PaperSpec.A.lem_bpbsde` — Lemma 4.1.
* `Dissertation.PaperSpec.A.lem_small` — Lemma 4.2.
* `Dissertation.PaperSpec.A.lem_pert` — Lemma 4.3.
* `Dissertation.PaperSpec.A.lem_cont` — Lemma 4.4.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec LevyStochCalc

universe u v w

/-- Lemma 4.1 (Brownian–Poisson `L²` estimate). There is a function `C_BP` of `T` such that: in
the standing setting, for `m ≥ 1` and `T > 0`, let `δY` be an `ℝᵐ`-valued adapted process on
`[0, T]` with càdlàg paths, `δZ ∈ H²_W`, `δU ∈ H²_N`, `δξ ∈ L²(Ω, ℱ_T; ℝᵐ)` and
`φ ∈ L²(Ω × [0, T]; ℝᵐ)`, and let

`δY_t = δξ + ∫_t^T φ_s ds − ∫_t^T δZ_s dW_s − ∫_t^T ∫_E δU_s(e) Ñ(ds, de)`

hold almost surely for every `t ∈ [0, T]`. Then `δY ∈ S²(ℝᵐ)`, and
`𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds
  ≤ C_BP(T) (𝔼|δξ|² + 𝔼 ∫_0^T |φ_s|² ds)`. -/
def lem_bpbsde : Prop :=
  ∃ CBP : ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (δξ : Ω → EuclideanSpace ℝ (Fin m)) (φ : Fin m → Ω → ℝ → ℝ) (δY : Fin m → ℝ → Ω → ℝ)
      (δZ : Fin m → ℝ → Ω → Fin d → ℝ) (δU : Fin m → ℝ → Ω → E → ℝ)
      (hZ : ∀ k j, Probability.Predictable (enlJoint 𝒢₀ D h𝒢₀) fun ω s => δZ k s ω j)
      (hZv : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) T → δZ k s ω = 0)
      (hZs : ∀ k j, Brownian.Ito.energy P T (fun ω s => δZ k s ω j) ≠ ⊤)
      (hU : ∀ k, Probability.MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) ν
        fun ω s e => δU k s ω e)
      (hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → δU k s ω e = 0)
      (hUs : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e) ≠ ⊤),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ T] δξ → MemLp δξ 2 P →
    (∀ k, Measurable (Function.uncurry (φ k))) → (∀ k, Brownian.Ito.energy P T (φ k) ≠ ⊤) →
    (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[enlJoint 𝒢₀ D h𝒢₀ t] (δY k t)) →
    (∀ k ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => δY k s ω) (𝓝[>] t) (𝓝 (δY k t ω))) →
    (∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => δY k s ω) (𝓝[<] t) (𝓝 l)) →
    (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      δY k t ω = δξ ω k + (∫ s in Set.Icc t T, φ k ω s)
        - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
              (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (δZ k)
              (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
              (progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k))
              (BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k)) T ω
            - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
              (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (δZ k)
              (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
              (progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k))
              (BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k)) t ω)
        - (Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
              (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => δU k s ω' e)
              ((hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
              (hU k).markedProgressivelyMeasurable
              (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) T ω
            - Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
              (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => δU k s ω' e)
              ((hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
              (hU k).markedProgressivelyMeasurable
              (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) t ω)) →
    (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq fun k => δY k t ω) ∂P < ⊤)
    ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq fun k => δY k t ω) ∂P
        + (∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => δZ k s ω j))
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e)
      ≤ ENNReal.ofReal (CBP T)
        * (∫⁻ ω, (esq fun k => δξ ω k) ∂P + ∑ k, Brownian.Ito.energy P T (φ k))

/-- Lemma 4.2 (small-coupling base case). There is a function `λ*` of `(T, L)` such that: in the
standing setting, for `T > 0`, if the coefficients with initial datum `ξ₀` satisfy (2.3) and
Assumptions 2.2–2.3 with constant `L`, then `λ* = λ*(T, L) ∈ (0, 1]` and `WP(λ)` holds for every
`λ ∈ [0, λ*]`. -/
def lem_small : Prop :=
  ∃ lamStar : ℝ → ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d) (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
    0 < lamStar T L ∧ lamStar T L ≤ 1
      ∧ ∀ lam : ℝ, 0 ≤ lam → lam ≤ lamStar T L → WP D h𝒢₀ hind₀ T lam C ξ₀

/-- Lemma 4.3 (continuous perturbation stability along the homotopy). There is a function `C_B`
of `(T, L, ‖G‖, c_G, α, β₁, β₂, λ̲)` such that: in the standing setting, for `T > 0`, if the
coefficients satisfy (2.3) and Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling
matrix `G`, `λ̲ ∈ (0, 1]` and `λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solve (4.1) at `λ` in `ℍ²`, with
`X^k_T ∈ L²`, `ℱ₀`-measurable initial data `ξ₀^k` and forcings `q^k`, and `Θ¹ − Θ² ∈ 𝕊`, then
`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ_t|²_F + ‖δU_t‖²) dt
  ≤ C_B (𝔼|δξ₀|² + 𝔼|δq^g_T|² + 𝔼 ∫_0^T (|δq^b|² + |δq^σ|²_F + ‖δq^h‖² + |δq^f|²) dt)`
with `C_B = C_B(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂, λ̲)`. -/
def lem_pert : Prop :=
  ∃ CB : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
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
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      ≤ ENNReal.ofReal (CB T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ lamLow)
        * dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
          (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
          (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω)

/-- Lemma 4.4 (continuation). There is a function `ζ₀` of
`(T, L, ‖G‖, c_G, α, β₁, β₂, λ*)` such that: in the standing setting, for `T > 0`, if the
coefficients with initial datum `ξ₀` satisfy (2.3) and Assumptions 2.2–2.5 with constants
`L, α, β₁, β₂` and coupling matrix `G`, and `λ* ∈ (0, 1]`, then
`ζ₀ = ζ₀(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂, λ*) > 0`, and for every `λ₀ ∈ [λ*, 1]` with
`WP(λ₀)`, `WP(λ₀ + ζ)` holds for every `ζ ∈ [0, ζ₀]` with `λ₀ + ζ ≤ 1`. -/
def lem_cont : Prop :=
  ∃ zeta0 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d)
      (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ lamStar : ℝ, 0 < lamStar → lamStar ≤ 1 →
    0 < zeta0 T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ lamStar
      ∧ ∀ lam0 : ℝ, lamStar ≤ lam0 → lam0 ≤ 1 → WP D h𝒢₀ hind₀ T lam0 C ξ₀ →
        ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ zeta0 T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ lamStar →
          lam0 + ζ ≤ 1 → WP D h𝒢₀ hind₀ T (lam0 + ζ) C ξ₀

end Dissertation.PaperSpec.A
