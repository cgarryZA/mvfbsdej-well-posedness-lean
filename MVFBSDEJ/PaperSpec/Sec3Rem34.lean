/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec3
import MVFBSDEJ.WellPosedness.Examples.SingularDrift

/-!
# Remark 3.4 of the well-posedness paper: uniqueness without origin integrability

Statement numbers refer to the well-posedness paper at `1f67672`, in the standing setting of §2.
Remark 3.4: uniqueness (Theorem 3.3, `thm_uniq`) needs only Assumptions 2.3–2.5; the initial-data
condition `ξ₀ ∈ L²` is necessary for a solution in `ℍ`; the origin-value conditions of
Assumption 2.2 are sufficient but not necessary, as adding the drift `t^{-1/2}` shows: the shift
`X ↦ X − 2√t`, translating the law argument accordingly, returns a system satisfying
Assumptions 2.2–2.5.

## Main definitions

* `MVFBSDEJ.PaperSpec.rem_uniq_initial` — a solution in `ℍ` has `ξ₀ ∈ L²`.
* `MVFBSDEJ.PaperSpec.rem_uniq_singular` — a system violating Assumption 2.2 and satisfying
  Assumptions 2.3–2.5 with a solution in `ℍ`.
* `MVFBSDEJ.PaperSpec.translateTuple`, `MVFBSDEJ.PaperSpec.translatedCoeffs` — the
  translation of the forward coordinate and the coefficients translated in state and law.
* `MVFBSDEJ.PaperSpec.rem_uniq_translation` — for every system satisfying (2.3) and
  Assumptions 2.2–2.5, the drift `t^{-1/2} e` added, a solution in `ℍ` exists.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MVFBSDEJ.PaperSpec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.Law

universe u v w

/-- Remark 3.4, the initial datum. In the standing setting, for `T ≥ 0`, a tuple of `ℍ_weak`
satisfying (1.1) with initial datum `ξ₀` whose forward component has `𝔼 sup_{t ≤ T} |X_t|² < ∞`
has `ξ₀ ∈ L²`. -/
def rem_uniq_initial : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 ≤ T →
    ∀ (C : Coeffs ν n m d) (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)) (X : Fin n → ℝ → Ω → ℝ)
      (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ),
    WeakSolution D h𝒢₀ hind₀ T C ξ₀ X Y Z U →
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P < ⊤ →
    ∀ i, MemLp (fun ω => ξ₀ ω i) 2 P

/-- Remark 3.4, the singular drift. In the standing setting with `𝒢₀ = ⊥`, `n = m = 1` and any
`d`, on every horizon `T > 0`: the affine coefficients of Example 5.1(i) taken at `β₁ = 1`,
`β₂ = 0`, `σ_c = 0`, `h_c = 0`, with the deterministic drift `t^{-1/2}` added to `b`, satisfy
(2.3), Assumption 2.3 with `L = 1`, Assumption 2.4 with `G = 1` and Assumption 2.5 with `G = 1`,
`α = 1`, `β₁ = 1`, `β₂ = 0`, violate Assumption 2.2 for every initial datum, and have a solution
of (1.1) in `ℍ` from the initial datum `0`. -/
def rem_uniq_singular : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] (ν : Measure E)
    [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] (d : ℕ) (P : Measure Ω)
    [IsProbabilityMeasure P] (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    JointBorel T (singularCoeffs (ν := ν) (d := d))
    ∧ Assumption23 (enlJoint ⊥ D bot_le) P T 1 (singularCoeffs (ν := ν) (d := d))
    ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
    ∧ Assumption25 (enlJoint ⊥ D bot_le) P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 1 0
        (singularCoeffs (ν := ν) (d := d))
    ∧ (∀ ξ₀ : Ω → EuclideanSpace ℝ (Fin 1),
        ¬ Assumption22 (enlJoint ⊥ D bot_le) P T (singularCoeffs (ν := ν) (d := d)) ξ₀)
    ∧ ∃ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin d → ℝ)
        (U : Fin 1 → ℝ → Ω → E → ℝ),
        Solution D bot_le hind₀ T (singularCoeffs (ν := ν) (d := d)) (fun _ => 0) X Y Z U

/-- The translation `(x, y, z, u) ↦ (x + r, y, z, u)` of the forward coordinate of a tuple. -/
def translateTuple {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
    (r : EuclideanSpace ℝ (Fin n)) (θ : TupleH ν n m d) : TupleH ν n m d :=
  (θ.1 + r, θ.2)

/-- The coefficients `C` translated by a deterministic path `r : ℝ → ℝⁿ` in the forward state and
its law: `ψ̃(t, θ, μ) = ψ(t, θ + r_t, μ ∘ (· + r_t)⁻¹)` for `ψ ∈ {b, σ, h, f}`, translating only
the forward coordinate, and `g̃(x, ρ) = g(x + r_T, ρ ∘ (· + r_T)⁻¹)`. -/
noncomputable def translatedCoeffs {E : Type v} [MeasurableSpace E] {ν : Measure E}
    [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ} (C : Coeffs ν n m d)
    (r : ℝ → EuclideanSpace ℝ (Fin n)) (T : ℝ) : Coeffs ν n m d where
  b t θ μ := C.b t (translateTuple (r t) θ) (lawP2 μ.law (translateTuple (r t)))
  σ t θ μ := C.σ t (translateTuple (r t) θ) (lawP2 μ.law (translateTuple (r t)))
  h t θ μ := C.h t (translateTuple (r t) θ) (lawP2 μ.law (translateTuple (r t)))
  f t θ μ := C.f t (translateTuple (r t) θ) (lawP2 μ.law (translateTuple (r t)))
  g x ρ := C.g (x + r T) (lawP2 ρ.law fun y => y + r T)

/-- Remark 3.4, the singular drift for a general system. In the standing setting with
`n, m, d ≥ 1`, for `T > 0`, let `C` with initial datum `ξ₀` satisfy (2.3) and Assumptions 2.2–2.5
with constants `L, α, β₁, β₂` and coupling matrix `G`, and let `e ∈ ℝⁿ` be nonzero. Adding the
deterministic drift `t^{-1/2} e` to `b` gives a system `C⁺` that satisfies (2.3) and
Assumptions 2.3 and 2.5 with the same constants and violates Assumption 2.2 for every initial
datum. The system `C̃` obtained from `C` by the shift `X ↦ X − 2√t e`, translating the law
argument accordingly, satisfies (2.3) and Assumptions 2.2–2.5 with the same constants, and has a
solution `Θ = (X, Y, Z, U)` in `ℍ` from `ξ₀` such that `(X + 2√t e, Y, Z, U)` is a solution of
(1.1) for `C⁺` in `ℍ` from `ξ₀`. -/
def rem_uniq_translation : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d)
      (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)) (e : EuclideanSpace ℝ (Fin n)), e ≠ 0 →
    JointBorel T C → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    JointBorel T (C.addDrift fun t => (Real.sqrt t)⁻¹ • e)
    ∧ Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L (C.addDrift fun t => (Real.sqrt t)⁻¹ • e)
    ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂
        (C.addDrift fun t => (Real.sqrt t)⁻¹ • e)
    ∧ (∀ ξ : Ω → EuclideanSpace ℝ (Fin n), ¬ Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T
        (C.addDrift fun t => (Real.sqrt t)⁻¹ • e) ξ)
    ∧ JointBorel T (translatedCoeffs C (fun t => (2 * Real.sqrt t) • e) T)
    ∧ Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T
        (translatedCoeffs C (fun t => (2 * Real.sqrt t) • e) T) ξ₀
    ∧ Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L
        (translatedCoeffs C (fun t => (2 * Real.sqrt t) • e) T)
    ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂
        (translatedCoeffs C (fun t => (2 * Real.sqrt t) • e) T)
    ∧ ∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
        (U : Fin m → ℝ → Ω → E → ℝ),
        Solution D h𝒢₀ hind₀ T (translatedCoeffs C (fun t => (2 * Real.sqrt t) • e) T) ξ₀
          X Y Z U
        ∧ Solution D h𝒢₀ hind₀ T (C.addDrift fun t => (Real.sqrt t)⁻¹ • e) ξ₀
          (fun i t ω => X i t ω + 2 * Real.sqrt t * e i) Y Z U

end MVFBSDEJ.PaperSpec
