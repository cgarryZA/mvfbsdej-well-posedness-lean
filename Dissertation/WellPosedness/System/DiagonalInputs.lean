/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.DiagonalLipschitzH

/-!
# The diagonal inputs of Definition 2.1

Definition 2.1 of the well-posedness paper fixes `t ∈ [0, T]` and calls a pair `(Θ, μ)` a
*diagonal input at time `t`* when `Θ ∈ L²(Ω, ℱ_t; H)` and `μ = Law(Θ) ∈ P₂(H)`; such pairs form
the diagonal

`𝒟_t = {(Θ, Law(Θ)) : Θ ∈ L²(Ω, ℱ_t; H)} ⊂ L²(Ω, ℱ_t; H) × P₂(H)`.

Here `Θ` ranges over the strongly `ℱ_t`-measurable square-integrable maps `Ω → H`, the
representatives of the elements of `L²(Ω, ℱ_t; H)`, and `Law(Θ)` is `lawP2 P Θ`. Assumptions 2.3
and 2.5 are imposed at pairs of diagonal inputs; the predicates `DiagonalLipschitzH` and
`DiagonalMonotone` quantify over the maps `Θ` and use their laws, and they are the same
conditions quantified over `𝒟_t`.

## Main definitions

* `diagonalInputs` — the diagonal `𝒟_t`.

## Main statements

* `mk_mem_diagonalInputs` — a tuple together with its law lies in `𝒟_t`.
* `diagonalMonotone_iff_diagonalInputs`, `diagonalLipschitzH_iff_diagonalInputs` — Assumptions
  2.5 and 2.3 along the diagonal, as conditions at pairs of elements of `𝒟_t`.
-/

open MeasureTheory Filter Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] (ν : Measure E) (n m d : ℕ)
  {Ω : Type*} [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- **The diagonal `𝒟_t` of Definition 2.1**: the pairs `(Θ, μ)` of a strongly `ℱ_t`-measurable
square-integrable `Θ : Ω → H` and its law `μ = Law(Θ)`. -/
def diagonalInputs (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (t : ℝ) : Set ((Ω → TupleH ν n m d) × P2 (TupleH ν n m d)) :=
  {p | StronglyMeasurable[ℱ t] p.1 ∧ MemLp p.1 2 P ∧ p.2 = lawP2 P p.1}

variable {ν n m d} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {t : ℝ}

/-- A strongly `ℱ_t`-measurable square-integrable tuple together with its law lies in `𝒟_t`. -/
theorem mk_mem_diagonalInputs {Θ : Ω → TupleH ν n m d} (hΘ : StronglyMeasurable[ℱ t] Θ)
    (hΘ2 : MemLp Θ 2 P) : (Θ, lawP2 P Θ) ∈ diagonalInputs ν n m d ℱ P t :=
  ⟨hΘ, hΘ2, rfl⟩

variable {T β₁ β₂ L : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d}

/-- **Assumption 2.5, interior, over `𝒟_t`**: (2.7) along the diagonal holds if and only if, for
almost every `t ∈ [0, T]`, it holds at every pair `(Θ, μ), (Θ', μ')` of elements of `𝒟_t`. -/
theorem diagonalMonotone_iff_diagonalInputs :
    DiagonalMonotone ℱ P T G β₁ β₂ C ↔ ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ p ∈ diagonalInputs ν n m d ℱ P t, ∀ p' ∈ diagonalInputs ν n m d ℱ P t,
        ∫ ω, interiorPairing (GX G) (GZ G) (GU G ν) (diagDiff C t (p.1 ω) (p'.1 ω) p.2 p'.2) ∂P
          ≤ ∫ ω, dissipation (GX G) (GZ G) (GU G ν) β₁ β₂
            (diagDiff C t (p.1 ω) (p'.1 ω) p.2 p'.2) ∂P := by
  refine eventually_congr (Eventually.of_forall fun t => ⟨fun h p hp p' hp' => ?_,
    fun h Θ Θ' hΘ hΘ' hΘ2 hΘ2' =>
      h (Θ, lawP2 P Θ) (mk_mem_diagonalInputs hΘ hΘ2) (Θ', lawP2 P Θ')
        (mk_mem_diagonalInputs hΘ' hΘ2')⟩)
  obtain ⟨hs, hL, he⟩ := hp
  obtain ⟨hs', hL', he'⟩ := hp'
  rw [he, he']
  exact h _ _ hs hs' hL hL'

/-- **Assumption 2.3, interior, with the Hilbert-norm `W₂`, over `𝒟_t`**: the diagonal Lipschitz
bound holds if and only if, for almost every `t ∈ [0, T]`, it holds almost surely at every pair
of elements of `𝒟_t`. -/
theorem diagonalLipschitzH_iff_diagonalInputs :
    DiagonalLipschitzH ℱ P T L C ↔ ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ p ∈ diagonalInputs ν n m d ℱ P t, ∀ p' ∈ diagonalInputs ν n m d ℱ P t,
        ∀ᵐ ω ∂P, ‖C.b t (p.1 ω) p.2 - C.b t (p'.1 ω) p'.2‖
            + ‖C.σ t (p.1 ω) p.2 - C.σ t (p'.1 ω) p'.2‖
            + ‖C.h t (p.1 ω) p.2 - C.h t (p'.1 ω) p'.2‖
            + ‖C.f t (p.1 ω) p.2 - C.f t (p'.1 ω) p'.2‖
          ≤ L * (tupleNorm (p.1 ω - p'.1 ω) + w2H p.2 p'.2) := by
  refine eventually_congr (Eventually.of_forall fun t => ⟨fun h p hp p' hp' => ?_,
    fun h Θ Θ' hΘ hΘ' hΘ2 hΘ2' =>
      h (Θ, lawP2 P Θ) (mk_mem_diagonalInputs hΘ hΘ2) (Θ', lawP2 P Θ')
        (mk_mem_diagonalInputs hΘ' hΘ2')⟩)
  obtain ⟨hs, hL, he⟩ := hp
  obtain ⟨hs', hL', he'⟩ := hp'
  rw [he, he']
  exact h _ _ hs hs' hL hL'

end Dissertation.WellPosedness.System
