/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3Margin
import Dissertation.PaperSpec.A.Sec3Rem34
import Dissertation.PaperSpec.A.Sec5FreeLaw
import Dissertation.PaperSpec.A.Sec5

/-!
# Claims of the well-posedness paper read as printed

Statement and equation numbers refer to arXiv 2608.23203v1, in the standing setting of §2. Each
proposition here is a claim of the paper read with the hypotheses it prints. Where a printed claim
fails in a case it does not exclude (`ν = 0`, a finite-dimensional `L²(ν)`, features that make the
cylindrical term constant), the statement beside its claim with the missing hypothesis is its
correction.

## Main definitions

* `Dissertation.PaperSpec.A.rem_beta1_dich_printed` — Remark 2.10 over every σ-finite `ν`.
* `Dissertation.PaperSpec.A.rem_uniq_exist_printed` — Remark 3.4, existence requires
  Assumption 2.2.
* `Dissertation.PaperSpec.A.cor_margin_additive_printed`, `cor_margin_finite_printed` — the
  paragraph after Corollary 3.6 over every σ-finite `ν`.
* `Dissertation.PaperSpec.A.ex_fulllaw_beyond_Q_printed` — Example 5.4, the cylindrical term of a
  non-affine `Q` and arbitrary bounded Lipschitz features is no expectation functional.
* `Dissertation.PaperSpec.A.rem_freelaw_printed` — Remark 5.6 over every σ-finite `ν`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Matrix

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.Law

universe u v w

/-- Remark 2.10, the `β₁` dichotomy, as printed (every σ-finite `ν`). In the standing setting with
`n, m ≥ 1`, for `T > 0` and `G ∈ ℝ^{m×n}` of full rank, let the coefficients satisfy
Assumption 2.5 with `G` and the constants `α, β₁, β₂`. Then: for almost every `t ∈ [0, T]` and
all `(Θ, μ), (Θ', μ') ∈ 𝒟_t` with `δX = δY = δZ = 0`,
`𝔼 ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de) ≤ −β₁ 𝔼 ‖Gᵀ δU‖²_{L²(ν)}`; if `h(t, θ, μ)` depends on `t` and the
forward state `x` only, then `β₁ = 0`, `m ≥ n` and `α, β₂ > 0`; and if `m < n`, then `β₁ > 0`
and `h` does not depend on `t` and `x` only. -/
def rem_beta1_dich_printed : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → 0 < n → 0 < m → ∀ T : ℝ, 0 < T →
    ∀ (G : Matrix (Fin m) (Fin n) ℝ), G.rank = min m n →
    ∀ (α β₁ β₂ : ℝ) (C : Coeffs ν n m d),
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ p ∈ diagonalInputs ν n m d (enlJoint 𝒢₀ D h𝒢₀) P t,
      ∀ p' ∈ diagonalInputs ν n m d (enlJoint 𝒢₀ D h𝒢₀) P t,
      (∀ ω, (p.1 ω).1 = (p'.1 ω).1 ∧ (p.1 ω).2.1 = (p'.1 ω).2.1
        ∧ (p.1 ω).2.2.1 = (p'.1 ω).2.2.1) →
      ∫ ω, (∫ e, inner ℝ (C.h t (p.1 ω) p.2 e - C.h t (p'.1 ω) p'.2 e)
          (GX Gᵀ ((p.1 ω).2.2.2 e - (p'.1 ω).2.2.2 e)) ∂ν) ∂P
        ≤ -β₁ * ∫ ω, ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2 ∂P)
    ∧ ((∀ (t : ℝ) (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)), θ.1 = θ'.1 →
        C.h t θ μ = C.h t θ' μ') → β₁ = 0 ∧ n ≤ m ∧ 0 < α ∧ 0 < β₂)
    ∧ (m < n → 0 < β₁ ∧ ¬ ∀ (t : ℝ) (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)),
        θ.1 = θ'.1 → C.h t θ μ = C.h t θ' μ')

/-- Remark 3.4, existence requires Assumption 2.2, as printed. In the standing setting, for
`T > 0` and coefficients satisfying (2.3) and Assumptions 2.3–2.5 with constants `L, α, β₁, β₂`
and a full-rank `G`: if (1.1) has, from an initial datum `ξ₀`, a tuple of `ℍ_weak` satisfying it
with `𝔼 sup_{t ≤ T} |X_t|² < ∞` and `𝔼 sup_{t ≤ T} |Y_t|² < ∞` (a solution in `ℍ`), then
Assumption 2.2 holds with `ξ₀`. -/
def rem_uniq_exist_printed : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ ξ₀ : Ω → EuclideanSpace ℝ (Fin n),
    (∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
        (U : Fin m → ℝ → Ω → E → ℝ),
      WeakSolution D h𝒢₀ hind₀ T C ξ₀ X Y Z U
        ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P < ⊤
        ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y k t ω)) ∂P < ⊤) →
    Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀

/-- The paragraph after Corollary 3.6, the additive jump coefficient, as printed (every σ-finite
`ν`). In the standing setting with `m ≥ 1`, for `T > 0`: if `h(t, θ, μ)` depends on `t` and the
forward state `x` only, then (2.13) fails for all constants `β₁ ≥ 0`, `β₂` and every margin
`c > 0`. -/
def cor_margin_additive_printed : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → 0 < m → ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ c : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d), 0 ≤ β₁ → 0 < c →
    (∀ (t : ℝ) (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)), θ.1 = θ'.1 →
      C.h t θ μ = C.h t θ' μ') →
    ¬ Margin213 (enlJoint 𝒢₀ D h𝒢₀) P T G β₁ β₂ c C

/-- The paragraph after Corollary 3.6, finitely many functionals, as printed (every σ-finite `ν`).
In the standing setting, for `T > 0`: if the jump coefficient depends on `u` only through `k`
linear functionals `ℓ : L²(ν; ℝᵐ) → ℝᵏ` along deterministic inputs,
`h(t, (x, y, z, u), δ_{(x,y,z,u)}) = h(t, (x, y, z, u'), δ_{(x,y,z,u')})` whenever `ℓ u = ℓ u'`,
then (2.13) fails for all constants `β₁ ≥ 0`, `β₂` and every margin `c > 0`. -/
def cor_margin_finite_printed : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ c : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d) (k : ℕ)
      (ℓ : Lp (EuclideanSpace ℝ (Fin m)) 2 ν →ₗ[ℝ] (Fin k → ℝ)), 0 ≤ β₁ → 0 < c →
    (∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m))
      (z : EuclideanSpace ℝ (Fin m × Fin d)) (u u' : Lp (EuclideanSpace ℝ (Fin m)) 2 ν),
      ℓ u = ℓ u' → C.h t (x, y, z, u) (P2.dirac ((x, y, z, u) : TupleH ν n m d))
        = C.h t (x, y, z, u') (P2.dirac ((x, y, z, u') : TupleH ν n m d))) →
    ¬ Margin213 (enlJoint 𝒢₀ D h𝒢₀) P T G β₁ β₂ c C

/-- Example 5.4, the cylindrical term is no expectation functional, as printed. For `ν` σ-finite
on a countably generated space, bounded Lipschitz features `φ_j : L²(ν; ℝᵐ) → ℝ` and a bounded
Lipschitz `Q : ℝᴶ → ℝ` that is not affine, no `φ' : H → ℝ` integrable against every law of finite
second moment has `Q((∫ φ_j dμ^U)_j) = ∫_H φ' dμ` for every `μ ∈ P₂(H)`. -/
def ex_fulllaw_beyond_Q_printed : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d J : ℕ)
    (Q : EuclideanSpace ℝ (Fin J) → ℝ) (φ : Fin J → Lp (EuclideanSpace ℝ (Fin m)) 2 ν → ℝ)
    (LQ BQ B : ℝ) (K : Fin J → ℝ), (∀ v v', |Q v - Q v'| ≤ LQ * ‖v - v'‖) → (∀ v, |Q v| ≤ BQ) →
    (∀ j u u', |φ j u - φ j u'| ≤ K j * ‖u - u'‖) → (∀ j u, |φ j u| ≤ B) →
    (¬ ∃ (a : ℝ) (c : Fin J → ℝ), ∀ s : EuclideanSpace ℝ (Fin J), Q s = a + ∑ j, c j * s j) →
    ∀ φ' : TupleH ν n m d → ℝ, (∀ μ : P2 (TupleH ν n m d), Integrable φ' μ.law) →
      ∃ μ : P2 (TupleH ν n m d),
        Q (WithLp.toLp 2 fun j => ∫ u, φ j u ∂μ.margU.law) ≠ ∫ θ, φ' θ ∂μ.law

/-- Remark 5.6, the measure argument, as printed (every σ-finite `ν`). In the standing setting
with `n, m, d ≥ 1`, `T > 0` and `G ∈ ℝ^{m×n}` of full rank, let the coefficients satisfy
Assumption 2.5 with `G` and `β₁ > 0`. Then for almost every `t ∈ [0, T]` there are
`(Θ, μ), (Θ', μ') ∈ 𝒟_t` with one and the same law and the same `(X, Y, Z)` at which the jump
coefficient differs with positive probability. -/
def rem_freelaw_printed : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → 0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (G : Matrix (Fin m) (Fin n) ℝ), G.rank = min m n →
    ∀ (α β₁ β₂ : ℝ) (C : Coeffs ν n m d),
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C → 0 < β₁ →
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∃ p ∈ diagonalInputs ν n m d (enlJoint 𝒢₀ D h𝒢₀) P t,
      ∃ p' ∈ diagonalInputs ν n m d (enlJoint 𝒢₀ D h𝒢₀) P t,
        p.2 = p'.2
        ∧ (∀ ω, (p.1 ω).1 = (p'.1 ω).1 ∧ (p.1 ω).2.1 = (p'.1 ω).2.1
          ∧ (p.1 ω).2.2.1 = (p'.1 ω).2.2.1)
        ∧ ¬ ∀ᵐ ω ∂P, C.h t (p.1 ω) p.2 = C.h t (p'.1 ω) p'.2

end Dissertation.PaperSpec.A
