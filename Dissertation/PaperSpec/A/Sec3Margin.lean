/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3

/-!
# The paragraph after Corollary 3.6 of the well-posedness paper

Statement and equation numbers refer to arXiv 2608.23203v1, in the standing setting of §2. The
paragraph after Corollary 3.6 reads the unweighted margin (2.13) along two diagonal inputs that
differ in one channel: a margin forces every channel to be strictly dissipative, so an additive
jump coefficient `h₀ = h₀(t, x, e)` supplies no margin, nor does jump feedback through finitely
many functionals of `u`. The propositions below state these for `ν ≠ 0` and for `L²(ν)` infinite
dimensional, and the case of a finite-dimensional `L²(ν)`.

## Main definitions

* `Dissertation.PaperSpec.A.cor_margin_channels` — a margin makes every channel strictly
  dissipative.
* `Dissertation.PaperSpec.A.cor_margin_additive` — an additive jump coefficient supplies no
  margin.
* `Dissertation.PaperSpec.A.cor_margin_finite` — finitely many functionals of `u` supply no
  margin on an infinite-dimensional `L²(ν)`.
* `Dissertation.PaperSpec.A.cor_margin_findim` — on a finite-dimensional `L²(ν)`, jump feedback
  through finitely many functionals of `u` carries a margin.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Matrix

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.Law

universe u v w

/-- The paragraph after Corollary 3.6, every channel. In the standing setting, if (2.13) holds
with the constants `β₁, β₂` and the margin `c`, then for almost every `t ∈ [0, T]` and all
`(Θ, μ), (Θ', μ') ∈ 𝒟_t`: if `δY = δZ = δU = 0`, then
`𝔼 ⟨−δf, G δX⟩ ≤ −β₂ 𝔼|G δX|² − c 𝔼|δX|²`; if `δX = δZ = δU = 0`, then
`𝔼 ⟨δb, Gᵀ δY⟩ ≤ −β₁ 𝔼|Gᵀ δY|² − c 𝔼|δY|²`; if `δX = δY = δU = 0`, then
`𝔼 ⟨δσ, Gᵀ δZ⟩_F ≤ −β₁ 𝔼|Gᵀ δZ|²_F − c 𝔼|δZ|²_F`; and if `δX = δY = δZ = 0`, then
`𝔼 ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de) ≤ −β₁ 𝔼‖Gᵀ δU‖²_{L²(ν)} − c 𝔼‖δU‖²_{L²(ν)}`. -/
def cor_margin_channels : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P →
    ∀ (T β₁ β₂ c : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    Margin213 (enlJoint 𝒢₀ D h𝒢₀) P T G β₁ β₂ c C →
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ p ∈ diagonalInputs ν n m d (enlJoint 𝒢₀ D h𝒢₀) P t,
      ∀ p' ∈ diagonalInputs ν n m d (enlJoint 𝒢₀ D h𝒢₀) P t,
      ((∀ ω, (p.1 ω).2.1 = (p'.1 ω).2.1 ∧ (p.1 ω).2.2.1 = (p'.1 ω).2.2.1
          ∧ (p.1 ω).2.2.2 = (p'.1 ω).2.2.2) →
        ∫ ω, inner ℝ (-(C.f t (p.1 ω) p.2 - C.f t (p'.1 ω) p'.2))
            (GX G ((p.1 ω).1 - (p'.1 ω).1)) ∂P
          ≤ -β₂ * ∫ ω, ‖GX G ((p.1 ω).1 - (p'.1 ω).1)‖ ^ 2 ∂P
            - c * ∫ ω, ‖(p.1 ω).1 - (p'.1 ω).1‖ ^ 2 ∂P)
      ∧ ((∀ ω, (p.1 ω).1 = (p'.1 ω).1 ∧ (p.1 ω).2.2.1 = (p'.1 ω).2.2.1
          ∧ (p.1 ω).2.2.2 = (p'.1 ω).2.2.2) →
        ∫ ω, inner ℝ (C.b t (p.1 ω) p.2 - C.b t (p'.1 ω) p'.2)
            (GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)) ∂P
          ≤ -β₁ * ∫ ω, ‖GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)‖ ^ 2 ∂P
            - c * ∫ ω, ‖(p.1 ω).2.1 - (p'.1 ω).2.1‖ ^ 2 ∂P)
      ∧ ((∀ ω, (p.1 ω).1 = (p'.1 ω).1 ∧ (p.1 ω).2.1 = (p'.1 ω).2.1
          ∧ (p.1 ω).2.2.2 = (p'.1 ω).2.2.2) →
        ∫ ω, inner ℝ (C.σ t (p.1 ω) p.2 - C.σ t (p'.1 ω) p'.2)
            (GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)) ∂P
          ≤ -β₁ * ∫ ω, ‖GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)‖ ^ 2 ∂P
            - c * ∫ ω, ‖(p.1 ω).2.2.1 - (p'.1 ω).2.2.1‖ ^ 2 ∂P)
      ∧ ((∀ ω, (p.1 ω).1 = (p'.1 ω).1 ∧ (p.1 ω).2.1 = (p'.1 ω).2.1
          ∧ (p.1 ω).2.2.1 = (p'.1 ω).2.2.1) →
        ∫ ω, (∫ e, inner ℝ (C.h t (p.1 ω) p.2 e - C.h t (p'.1 ω) p'.2 e)
            (GX Gᵀ ((p.1 ω).2.2.2 e - (p'.1 ω).2.2.2 e)) ∂ν) ∂P
          ≤ -β₁ * ∫ ω, ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2 ∂P
            - c * ∫ ω, ‖(p.1 ω).2.2.2 - (p'.1 ω).2.2.2‖ ^ 2 ∂P)

/-- The paragraph after Corollary 3.6, the additive jump coefficient. In the standing setting
with `m ≥ 1`, for `T > 0` and `ν ≠ 0`: if `h(t, θ, μ)` depends on `t` and the forward state `x`
only, then (2.13) fails for all constants `β₁ ≥ 0`, `β₂` and every margin `c > 0`. -/
def cor_margin_additive : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → 0 < m → ∀ T : ℝ, 0 < T → ν ≠ 0 →
    ∀ (β₁ β₂ c : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d), 0 ≤ β₁ → 0 < c →
    (∀ (t : ℝ) (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)), θ.1 = θ'.1 →
      C.h t θ μ = C.h t θ' μ') →
    ¬ Margin213 (enlJoint 𝒢₀ D h𝒢₀) P T G β₁ β₂ c C

/-- The paragraph after Corollary 3.6, finitely many functionals. In the standing setting, for
`T > 0` with `L²(ν; ℝᵐ)` infinite dimensional: if the jump coefficient depends on `u` only
through `k` linear functionals `ℓ : L²(ν; ℝᵐ) → ℝᵏ` along deterministic inputs,
`h(t, (x, y, z, u), δ_{(x,y,z,u)}) = h(t, (x, y, z, u'), δ_{(x,y,z,u')})` whenever
`ℓ u = ℓ u'`, then (2.13) fails for all constants `β₁ ≥ 0`, `β₂` and every margin `c > 0`. -/
def cor_margin_finite : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ T : ℝ, 0 < T →
    ¬ FiniteDimensional ℝ (Lp (EuclideanSpace ℝ (Fin m)) 2 ν) →
    ∀ (β₁ β₂ c : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d) (k : ℕ)
      (ℓ : Lp (EuclideanSpace ℝ (Fin m)) 2 ν →ₗ[ℝ] (Fin k → ℝ)), 0 ≤ β₁ → 0 < c →
    (∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m))
      (z : EuclideanSpace ℝ (Fin m × Fin d)) (u u' : Lp (EuclideanSpace ℝ (Fin m)) 2 ν),
      ℓ u = ℓ u' → C.h t (x, y, z, u) (P2.dirac ((x, y, z, u) : TupleH ν n m d))
        = C.h t (x, y, z, u') (P2.dirac ((x, y, z, u') : TupleH ν n m d))) →
    ¬ Margin213 (enlJoint 𝒢₀ D h𝒢₀) P T G β₁ β₂ c C

/-- The paragraph after Corollary 3.6, the finite-dimensional case. In the standing setting with
`m = n ≥ 1` and `L²(ν; ℝⁿ)` finite dimensional, for `T > 0`, constants `β₁, β₂ ≥ 0`, a margin
`c > 0`, `σ_c ∈ ℝ^{n×d}` and `h_c ∈ L²(ν; ℝⁿ)`: there are finitely many linear functionals
`ℓ : L²(ν; ℝⁿ) → ℝᵏ` that determine `u` (`ℓ` is injective), and the system of Example 5.1(i)
with the constants `β₁ + c, β₂ + c`, whose jump coefficient `h_c − (β₁ + c) u` depends on `u`
only through `ℓ u`, satisfies (2.13) at `G = I` with the constants `β₁, β₂` and the margin
`c`. -/
def cor_margin_findim : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → 0 < n → ∀ T : ℝ, 0 < T →
    FiniteDimensional ℝ (Lp (EuclideanSpace ℝ (Fin n)) 2 ν) →
    ∀ (β₁ β₂ c : ℝ), 0 ≤ β₁ → 0 ≤ β₂ → 0 < c →
    ∀ (σc : EuclideanSpace ℝ (Fin n × Fin d)) (hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν),
    ∃ (k : ℕ) (ℓ : Lp (EuclideanSpace ℝ (Fin n)) 2 ν →ₗ[ℝ] (Fin k → ℝ)),
      Function.Injective ℓ
      ∧ (∀ (t : ℝ) (θ θ' : TupleH ν n n d) (μ μ' : P2 (TupleH ν n n d)),
        ℓ θ.2.2.2 = ℓ θ'.2.2.2 →
          (affineCoeffs (β₁ + c) (β₂ + c) σc hc).h t θ μ
            = (affineCoeffs (β₁ + c) (β₂ + c) σc hc).h t θ' μ')
      ∧ Margin213 (enlJoint 𝒢₀ D h𝒢₀) P T (1 : Matrix (Fin n) (Fin n) ℝ) β₁ β₂ c
          (affineCoeffs (β₁ + c) (β₂ + c) σc hc)

end Dissertation.PaperSpec.A
