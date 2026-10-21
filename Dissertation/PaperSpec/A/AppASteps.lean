/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.LawFlow

/-!
# Steps of the proof of Lemma A.1 of the well-posedness paper

Statement numbers refer to the well-posedness paper at `1f67672`. Step 1 of the proof of
Lemma A.1 shows that the left limits `X₋, Y₋` are predictable and agree with `X, Y`
`dt ⊗ dP`-almost everywhere, that `H` is separable, and that `U` has a predictable
`L²(ν)`-valued representative; it then places the left-limit tuple `Θ⁻ = (X₋, Y₋, Z, U)`, a
predictable field, in `L²([0, T] × Ω; H)`, identifies that space with `L²(0, T; L²(Ω; H))` by the
Fubini isometry, and obtains a Borel version of `t ↦ Θ⁻_t ∈ L²(Ω; H)` through the Pettis
measurability theorem; Step 2 uses that `(P₂(H), W₂)` is Polish. In Step 1 the tuple space
`H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)` carries its Hilbert norm: it is `TupleL2 …`, into which
`Dissertation.WellPosedness.System.toL2` maps a tuple.

## Main definitions

* `Dissertation.PaperSpec.A.lemA1_leftlim` — `X₋, Y₋` are predictable and agree with `X, Y`
  `dt ⊗ dP`-almost everywhere.
* `Dissertation.PaperSpec.A.lemA1_separable` — `L²(ν; ℝᵐ)` and `H` are separable.
* `Dissertation.PaperSpec.A.lemA1_U` — `U ∈ L²([0, T] × Ω × E)` has a predictable
  `L²(ν)`-valued representative.
* `Dissertation.PaperSpec.A.lemA1_pred` — `Θ⁻` is predictable.
* `Dissertation.PaperSpec.A.lemA1_L2` — `Θ⁻ ∈ L²([0, T] × Ω; H)`.
* `Dissertation.PaperSpec.A.lemA1_fubini` — the Fubini isometry
  `L²([0, T] × Ω; H) ≅ L²(0, T; L²(Ω; H))`.
* `Dissertation.PaperSpec.A.lemA1_pettis` — a Borel version of `t ↦ Θ⁻_t ∈ L²(Ω; H)`.
* `Dissertation.PaperSpec.A.lemA1_polish` — `(P₂(H), W₂)` is Polish.
-/

open MeasureTheory
open scoped ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.Law

universe u v

/-- Lemma A.1, Step 1, the left limits: for `X, Y` càdlàg adapted and `Z, U` predictable, all of
finite energy on `[0, T]`, the left limits `X₋, Y₋` are predictable; on every path the times `t`
with `X_{t−} ≠ X_t` form a countable set and `∫_0^T 1{X_{t−} ≠ X_t} dt = 0`, and likewise for
`Y`; `X₋ = X` and `Y₋ = Y` `dt ⊗ dP`-almost everywhere on `[0, T] × Ω`; and `X₋, Y₋` have finite
energy on `[0, T]`. -/
def lemA1_leftlim : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ)
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Type v} [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (T : ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ),
    CadlagPredTuple ℱ P ν T X Y Z U →
    (∀ i, LevyStochCalc.Probability.Predictable ℱ fun ω t => leftLimProc X i t ω)
    ∧ (∀ k, LevyStochCalc.Probability.Predictable ℱ fun ω t => leftLimProc Y k t ω)
    ∧ (∀ i ω, {t : ℝ | leftLimProc X i t ω ≠ X i t ω}.Countable
        ∧ ∫⁻ t in Set.Icc (0 : ℝ) T,
            {t : ℝ | leftLimProc X i t ω ≠ X i t ω}.indicator (1 : ℝ → ℝ≥0∞) t = 0)
    ∧ (∀ k ω, {t : ℝ | leftLimProc Y k t ω ≠ Y k t ω}.Countable
        ∧ ∫⁻ t in Set.Icc (0 : ℝ) T,
            {t : ℝ | leftLimProc Y k t ω ≠ Y k t ω}.indicator (1 : ℝ → ℝ≥0∞) t = 0)
    ∧ (∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P),
        (∀ i, leftLimProc X i p.1 p.2 = X i p.1 p.2) ∧ ∀ k, leftLimProc Y k p.1 p.2 = Y k p.1 p.2)
    ∧ (∀ i, LevyStochCalc.Brownian.Ito.energy P T (fun ω t => leftLimProc X i t ω) ≠ ⊤)
    ∧ ∀ k, LevyStochCalc.Brownian.Ito.energy P T (fun ω t => leftLimProc Y k t ω) ≠ ⊤

/-- Lemma A.1, Step 1: for `ν` σ-finite on a countably generated `E`, `L²(ν; ℝᵐ)` is separable,
and so is the tuple space `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)` with its Hilbert norm. -/
def lemA1_separable : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d : ℕ),
    TopologicalSpace.SeparableSpace (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)
    ∧ TopologicalSpace.SeparableSpace (TupleL2 (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m × Fin d))
        (Lp (EuclideanSpace ℝ (Fin m)) 2 ν))

/-- Lemma A.1, Step 1, the jump channel: for `X, Y` càdlàg adapted and `Z, U` predictable, all of
finite energy on `[0, T]`, `U ∈ L²([0, T] × Ω × E; ℝᵐ)`, and the induced map
`(t, ω) ↦ U_t(ω, ·)` has a predictable, strongly measurable `L²(ν; ℝᵐ)`-valued representative:
a map `V`, strongly measurable for the predictable σ-algebra and square integrable on
`[0, T] × Ω`, with `V_t(ω) = U_t(ω, ·)` `ν`-almost everywhere for `dt ⊗ dP`-almost every
`(t, ω) ∈ [0, T] × Ω`. -/
def lemA1_U : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ)
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Type v} [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (T : ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ),
    CadlagPredTuple ℱ P ν T X Y Z U →
    MemLp (fun q : (ℝ × Ω) × E =>
        (WithLp.toLp 2 fun k => U k q.1.1 q.1.2 q.2 : EuclideanSpace ℝ (Fin m))) 2
      (((volume.restrict (Set.Icc (0 : ℝ) T)).prod P).prod ν)
    ∧ ∃ V : Ω → ℝ → Lp (EuclideanSpace ℝ (Fin m)) 2 ν,
        LevyStochCalc.Probability.Predictable ℱ V
        ∧ MemLp (fun p : ℝ × Ω => V p.2 p.1) 2 ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P)
        ∧ ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P),
            (V p.2 p.1 : E → EuclideanSpace ℝ (Fin m))
              =ᵐ[ν] fun e => (WithLp.toLp 2 fun k => U k p.1 p.2 e : EuclideanSpace ℝ (Fin m))

/-- Lemma A.1, Step 1: for `X, Y` càdlàg adapted and `Z, U` predictable, all of finite energy on
`[0, T]`, the left-limit tuple `(t, ω) ↦ Θ⁻_t(ω) = (X_{t−}, Y_{t−}, Z_t, U_t)(ω)`, with the
Hilbert norm of `H`, is predictable: strongly measurable for the predictable σ-algebra. -/
def lemA1_pred : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ)
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Type v} [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (T : ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ),
    CadlagPredTuple ℱ P ν T X Y Z U →
    LevyStochCalc.Probability.Predictable ℱ fun ω t =>
      toL2 (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U t ω)

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
