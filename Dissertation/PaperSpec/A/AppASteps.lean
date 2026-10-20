/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.HilbertW2Space
import Dissertation.WellPosedness.System.LawFlow

/-!
# Steps of the proof of Lemma A.1 of the well-posedness paper

Statement numbers refer to the well-posedness paper at `1f67672`. Step 1 of the proof of
Lemma A.1 places the left-limit tuple `Θ⁻ = (X₋, Y₋, Z, U)` in `L²([0, T] × Ω; H)`, identifies
that space with `L²(0, T; L²(Ω; H))` by the Fubini isometry, and obtains a Borel version of
`t ↦ Θ⁻_t ∈ L²(Ω; H)` through the Pettis measurability theorem; Step 2 uses that
`(P₂(H), W₂)` is Polish. In Step 1 the tuple space `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)` carries
its Hilbert norm: it is `TupleL2 …`, into which `toL2` maps a tuple.

## Main definitions

* `Dissertation.PaperSpec.A.lemA1_L2` — `Θ⁻ ∈ L²([0, T] × Ω; H)`.
* `Dissertation.PaperSpec.A.lemA1_fubini` — the Fubini isometry
  `L²([0, T] × Ω; H) ≅ L²(0, T; L²(Ω; H))`.
* `Dissertation.PaperSpec.A.lemA1_pettis` — a Borel version of `t ↦ Θ⁻_t ∈ L²(Ω; H)`.
* `Dissertation.PaperSpec.A.lemA1_polish` — `(P₂(H), W₂)` is Polish.
-/

open MeasureTheory

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.Law

universe u v

/-- Lemma A.1, Step 1: for `X, Y` càdlàg adapted and `Z, U` predictable, all of finite energy on
`[0, T]`, the left-limit tuple `(t, ω) ↦ Θ⁻_t(ω) = (X_{t−}, Y_{t−}, Z_t, U_t)(ω)`, with the
Hilbert norm of `H`, is jointly strongly measurable and lies in `L²([0, T] × Ω; H)`:
`𝔼 ∫_0^T ‖Θ⁻_t‖²_H dt < ∞`. -/
def lemA1_L2 : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ)
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Type v} [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (T : ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ),
    CadlagPredTuple ℱ P ν T X Y Z U →
    StronglyMeasurable (fun p : ℝ × Ω =>
        toL2 (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U p.1 p.2))
    ∧ MemLp (fun p : ℝ × Ω => toL2 (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U p.1 p.2)) 2
        ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P)

/-- Lemma A.1, Step 1, the Fubini isometry: for a probability space `(Ω, P)` and `T ∈ ℝ`, a linear
isometric equivalence `Φ : L²([0, T] × Ω; H) ≃ L²(0, T; L²(Ω; H))`, `H` with its Hilbert norm,
with `Φ(f)(t) = f(t, ·)` in `L²(Ω; H)` for almost every `t ∈ [0, T]`. -/
def lemA1_fubini : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (T : ℝ),
    ∃ Φ : Lp (TupleL2 (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)) 2
          ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P)
        ≃ₗᵢ[ℝ] Lp (Lp (TupleL2 (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)) 2 P) 2
          (volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ f, ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        (Φ f t : Ω → TupleL2 (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν))
          =ᵐ[P] fun ω => f (t, ω)

/-- Lemma A.1, Step 1, the Pettis step: for `X, Y` càdlàg adapted and `Z, U` predictable, all of
finite energy on `[0, T]`, there is `F : ℝ → L²(Ω; H)`, `H` with its Hilbert norm, which is
strongly measurable, takes values in a closed separable subspace, is Borel measurable, and equals
the class of `Θ⁻_t` for almost every `t ∈ [0, T]`. -/
def lemA1_pettis : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ)
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Type v} [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (T : ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ),
    CadlagPredTuple ℱ P ν T X Y Z U →
    ∃ F : ℝ → Lp (TupleL2 (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))
        (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)) 2 P,
      StronglyMeasurable F
      ∧ (∃ V : Submodule ℝ (Lp (TupleL2 (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))
            (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)) 2 P),
          IsClosed (SetLike.coe V) ∧ TopologicalSpace.IsSeparable (SetLike.coe V)
            ∧ ∀ t, F t ∈ V)
      ∧ @Measurable ℝ (Lp (TupleL2 (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))
          (EuclideanSpace ℝ (Fin m × Fin d)) (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)) 2 P) _
          (borel _) F
      ∧ ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
          ∃ h : MemLp (fun ω => toL2 (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U t ω)) 2 P,
            F t = h.toLp _

/-- Lemma A.1, Step 2: the tuple space `H` is Polish, and the laws of finite second moment on
`H` with the 2-Wasserstein distance of its Hilbert norm form a Polish metric space: `W₂`
separates laws, and `(P₂(H), W₂)` is complete and separable. -/
def lemA1_polish : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d : ℕ),
    PolishSpace (TupleH ν n m d)
    ∧ (∀ μ μ' : TupleP2WH ν n m d, dist μ μ' = 0 → μ = μ')
    ∧ CompleteSpace (TupleP2WH ν n m d)
    ∧ TopologicalSpace.SeparableSpace (TupleP2WH ν n m d)
    ∧ PolishSpace (TupleP2WH ν n m d)

end Dissertation.PaperSpec.A
