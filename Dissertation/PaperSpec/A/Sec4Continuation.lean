/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4

/-!
# Sections 4.4 and 4.5 of the well-posedness paper: the continuation

Statement and equation numbers refer to the well-posedness paper at `1f67672`. Before Lemma 4.4,
Lemma 4.3 with identical sources and initial datum gives uniqueness at each `λ ∈ [λ*, 1]` and
Lemma 4.2 gives it on `[0, λ*]`. The proof of Theorem 3.5 steps along
`λ_k = min{λ* + k ζ₀, 1}` with Lemma 4.4 from `WP(λ*)` to `WP(1)`.

## Main definitions

* `Dissertation.PaperSpec.A.sec4_uniq_homotopy` — uniqueness along the homotopy.
* `Dissertation.PaperSpec.A.sec45_proof_thm35` — with `ζ₀` of Lemma 4.4, `WP(λ_k)` for every `k`,
  and `WP(1)`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec LevyStochCalc

universe u v w

/-- §4.4, before Lemma 4.4: uniqueness along the homotopy. There is a function `λ*` of `(T, L)`
such that: in the standing setting, for `T > 0`, if the coefficients with initial datum `ξ₀`
satisfy (2.3) and Assumptions 2.2–2.5 with constants `L, α, β₁, β₂` and coupling matrix `G`, then
`λ*(T, L) ∈ (0, 1]`, and for every `λ ∈ [λ*, 1]` and every `λ ∈ [0, λ*]`, every forcing `q` and
any two solutions of (4.1) at `λ` in `𝕊` with the datum `ξ₀` and the forcing `q`, `X` and `Y` are
indistinguishable on `[0, T]` and the differences of `Z` and of `U` have zero energy. -/
def sec4_uniq_homotopy : Prop :=
  ∃ lamStar : ℝ → ℝ → ℝ,
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
    0 < lamStar T L ∧ lamStar T L ≤ 1
    ∧ ∀ lam : ℝ, (lamStar T L ≤ lam ∧ lam ≤ 1 ∨ 0 ≤ lam ∧ lam ≤ lamStar T L) →
      ∀ (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ)
        (qh : Fin n → ℝ → Ω → E → ℝ) (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ),
      PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb qσ qh qf qg →
      ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
        (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
      ForcedSolution D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₁ Y₁ Z₁ U₁ →
      ForcedSolution D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₂ Y₂ Z₂ U₂ →
      (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
        ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
        ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
        ∧ ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0

/-- §4.5, the proof of Theorem 3.5. There are a function `λ*` of `(T, L)` and a function `ζ₀` of
`(T, L, ‖G‖, c_G, α, β₁, β₂, λ*)` such that: in the standing setting, for `T > 0`, if the
coefficients with initial datum `ξ₀` satisfy (2.3) and Assumptions 2.2–2.5 with constants
`L, α, β₁, β₂` and coupling matrix `G`, then, with `λ* = λ*(T, L)`,
`ζ₀ = ζ₀(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂, λ*)` and `λ_k = min{λ* + k ζ₀, 1}`: `λ* ∈ (0, 1]`,
`ζ₀ > 0`, and `ζ₀` has the property of Lemma 4.4: for every `λ₀ ∈ [λ*, 1]` with `WP(λ₀)`,
`WP(λ₀ + ζ)` holds for every `ζ ∈ [0, ζ₀]` with `λ₀ + ζ ≤ 1`; `WP(λ)` for every
`λ ∈ [0, λ*]`; `λ_0 = λ*`, `λ_{k+1} − λ_k ≤ ζ₀` and `λ_k = 1` for `k ≥ ⌈(1 − λ*)/ζ₀⌉`;
`WP(λ_k)` for every `k`; and `WP(1)`. -/
def sec45_proof_thm35 : Prop :=
  ∃ (lamStar : ℝ → ℝ → ℝ) (zeta0 : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ),
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
    0 < lamStar T L ∧ lamStar T L ≤ 1
    ∧ 0 < zeta0 T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ (lamStar T L)
    ∧ (∀ lam0 : ℝ, lamStar T L ≤ lam0 → lam0 ≤ 1 → WP D h𝒢₀ hind₀ T lam0 C ξ₀ →
        ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ zeta0 T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ (lamStar T L) →
          lam0 + ζ ≤ 1 → WP D h𝒢₀ hind₀ T (lam0 + ζ) C ξ₀)
    ∧ (∀ lam : ℝ, 0 ≤ lam → lam ≤ lamStar T L → WP D h𝒢₀ hind₀ T lam C ξ₀)
    ∧ min (lamStar T L + ((0 : ℕ) : ℝ) * zeta0 T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ (lamStar T L))
        1 = lamStar T L
    ∧ (∀ k : ℕ,
        min (lamStar T L + ((k + 1 : ℕ) : ℝ)
            * zeta0 T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ (lamStar T L)) 1
          - min (lamStar T L + (k : ℝ)
            * zeta0 T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ (lamStar T L)) 1
        ≤ zeta0 T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ (lamStar T L))
    ∧ (∀ k : ℕ,
        ⌈(1 - lamStar T L) / zeta0 T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ (lamStar T L)⌉₊ ≤ k →
        min (lamStar T L + (k : ℝ)
          * zeta0 T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ (lamStar T L)) 1 = 1)
    ∧ (∀ k : ℕ, WP D h𝒢₀ hind₀ T
        (min (lamStar T L + (k : ℝ)
          * zeta0 T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ (lamStar T L)) 1) C ξ₀)
    ∧ WP D h𝒢₀ hind₀ T 1 C ξ₀

end Dissertation.PaperSpec.A
