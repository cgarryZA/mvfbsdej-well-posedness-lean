/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.LawFlow

/-!
# Lemma A.1 of the well-posedness paper

Statement numbers refer to arXiv 2608.23203v1. Lemma A.1: for `X, Y` càdlàg
adapted and `Z, U` predictable, of finite energy on `[0, T]`, the maps `t ↦ Law(Θ_t)` and
`t ↦ Law(Θ⁻_t)` have Borel representatives into `(P₂(H), W₂)`, unique up to Lebesgue-null sets of
times and equal for almost every `t`; and coefficient evaluations along them do not depend, up to
`dt ⊗ dP`-null sets, on the predictable versions of `(Z, U)` or on the Borel representatives.

## Main definitions

* `Dissertation.PaperSpec.A.lem_lawflow` — the Borel law flows.
* `Dissertation.PaperSpec.A.lem_lawflow_invariant` — uniqueness of the flows and invariance of
  coefficient evaluations.
-/

open MeasureTheory

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.Law

universe u v w

/-- Lemma A.1, the Borel law flows. For `X, Y` càdlàg adapted and `Z, U` predictable, all of
finite energy on `[0, T]`, the flows `s ↦ Law(Θ_s)` and `s ↦ Law(Θ⁻_s)`, `Θ⁻_s = (X_{s−}, Y_{s−},
Z_s, U_s)`, are Borel into `(P₂(H), W₂)`, and for almost every `s ∈ [0, T]` they are the laws
`P ∘ Θ_s⁻¹` and `P ∘ (Θ⁻_s)⁻¹` and coincide. -/
def lem_lawflow : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ)
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Type v} [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (T : ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ),
    CadlagPredTuple ℱ P ν T X Y Z U →
    Measurable (fun s => (lawP2 P (tupleAt ν X Y Z U s)).toP2WH) ∧
    Measurable (fun s => (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).toP2WH) ∧
    (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (lawP2 P (tupleAt ν X Y Z U s)).law = P.map (tupleAt ν X Y Z U s) ∧
      (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).law =
        P.map (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s) ∧
      lawP2 P (tupleAt ν X Y Z U s) =
        lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s))

/-- Lemma A.1, uniqueness and invariance. For processes `X, Y`, two versions `Z, Z'` equal
`dt ⊗ dP`-a.e. and `U, U'` equal `dt ⊗ dP ⊗ ν`-a.e., and flows `ρ, ρ'` representing the laws of
`Θ_s = (X_s, Y_s, Z_s, U_s)` and `Θ'_s = (X_s, Y_s, Z'_s, U'_s)` for almost every `s ∈ [0, T]`:
`ρ = ρ'` for almost every `s ∈ [0, T]`, and every coefficient `ψ(s, θ, μ)` evaluated along
`(Θ, ρ)` and along `(Θ', ρ')` agrees `dt ⊗ dP`-a.e. on `[0, T] × Ω`. -/
def lem_lawflow_invariant : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d : ℕ) (T : ℝ)
    (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z Z' : Fin m → ℝ → Ω → Fin d → ℝ) (U U' : Fin m → ℝ → Ω → E → ℝ)
    (ρ ρ' : ℝ → P2 (TupleH ν n m d)) {W : Type w}
    (ψ : ℝ → TupleH ν n m d → P2 (TupleH ν n m d) → W),
    (∀ k j, ∀ᵐ p ∂(LevyStochCalc.Brownian.Ito.energyMeasure P T),
      Z k p.2 p.1 j = Z' k p.2 p.1 j) →
    (∀ k, ∀ᵐ q ∂(LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T),
      U k q.2.1 q.1 q.2.2 = U' k q.2.1 q.1 q.2.2) →
    (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (ρ s).law = P.map (tupleAt ν X Y Z U s)) →
    (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (ρ' s).law = P.map (tupleAt ν X Y Z' U' s)) →
    (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ρ s = ρ' s) ∧
    ∀ᵐ p ∂(LevyStochCalc.Brownian.Ito.energyMeasure P T),
      ψ p.2 (tupleAt ν X Y Z U p.2 p.1) (ρ p.2) =
        ψ p.2 (tupleAt ν X Y Z' U' p.2 p.1) (ρ' p.2)

end Dissertation.PaperSpec.A
