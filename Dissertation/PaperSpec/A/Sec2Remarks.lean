/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Setting
import Dissertation.WellPosedness.Spec.CorollaryHyps
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Section 2 of the well-posedness paper: the remarks on the assumptions

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The standing
setting is that of §2 (see `Dissertation.PaperSpec.A.thm_cwp`).

## Main definitions

* `Dissertation.PaperSpec.A.rem_diag_mono`, `rem_diag_mono_converse` — Remark 2.8: the pointwise
  condition gives Assumption 2.5, and the converse fails.
* `Dissertation.PaperSpec.A.rem_intrinsic_uniform`, `rem_intrinsic_coupling`,
  `rem_intrinsic_basis` — Remark 2.9: a uniform variable at positive times, couplings as joint
  laws of inputs, and the diagonal assumptions independent of the basis.
* `Dissertation.PaperSpec.A.rem_beta1_fibre`, `rem_beta1_dich`, `rem_beta1_zero` — Remark 2.10:
  the fibre `L²(ν)`, the `β₁` dichotomy, and zero intensity.
* `Dissertation.PaperSpec.A.Margin212` — (2.12), the weighted margin.
* `Dissertation.PaperSpec.A.rem_margin_reduce`, `rem_margin_unweighted`, `rem_margin_smaller` —
  Remark 2.11: the reduced constants, the unweighted margin `c / c_G`, and its comparison with
  `c`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Matrix

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.Law

universe u v w

/-- Remark 2.8, the pointwise condition gives Assumption 2.5. In the standing setting, for a
horizon `T`, a coupling matrix `G`, constants `β₁, β₂` and coefficients with (2.3): if for almost
every `t ∈ [0, T]` the inequality of (2.7) holds without expectations at all points `θ, θ' ∈ H`
and laws `μ, μ' ∈ P₂(H)`, then for almost every `t ∈ [0, T]` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`
the positive part of the pairing of (2.7) has finite expectation, so that its expectation exists in
`[−∞, ∞)`, and when the pairing is integrable its expectation satisfies (2.7); and if the
coefficients also satisfy Assumption 2.3 with some `L`, then (2.7) holds for almost every
`t ∈ [0, T]`, the expectation of the pairing existing. -/
def rem_diag_mono : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P →
    ∀ (T β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C →
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ (θ θ' : TupleH ν n m d)
      (μ μ' : P2 (TupleH ν n m d)),
      pairing27 G C t θ θ' μ μ'
        ≤ -β₁ * (‖GX Gᵀ (θ.2.1 - θ'.2.1)‖ ^ 2 + ‖GZ Gᵀ (θ.2.2.1 - θ'.2.2.1)‖ ^ 2
            + ‖GU Gᵀ ν (θ.2.2.2 - θ'.2.2.2)‖ ^ 2)
          - β₂ * ‖GX G (θ.1 - θ'.1)‖ ^ 2) →
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ p ∈ diagonalInputs ν n m d (enlJoint 𝒢₀ D h𝒢₀) P t,
      ∀ p' ∈ diagonalInputs ν n m d (enlJoint 𝒢₀ D h𝒢₀) P t,
        ∫⁻ ω, ENNReal.ofReal (pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2) ∂P < ⊤
        ∧ (Integrable (fun ω => pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2) P →
          ∫ ω, pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2 ∂P
            ≤ -β₁ * ∫ ω, (‖GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)‖ ^ 2
                + ‖GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)‖ ^ 2
                + ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2) ∂P
              - β₂ * ∫ ω, ‖GX G ((p.1 ω).1 - (p'.1 ω).1)‖ ^ 2 ∂P))
    ∧ ∀ L : ℝ, Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Mono27At (enlJoint 𝒢₀ D h𝒢₀) P t G β₁ β₂ C

/-- Remark 2.8, the converse fails. In the standing setting with `n = m = d = 1`, for every
horizon `T > 0` some coefficients satisfy (2.3), Assumption 2.3 with some `L` and Assumption 2.5
with `G = 1` and some constants `α, β₁, β₂`, while for no constants `β ≥ 0`, `β'` does the
inequality of (2.7) with `G = 1` hold without expectations at all points and laws for almost
every `t ∈ [0, T]`. -/
def rem_diag_mono_converse : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ T : ℝ, 0 < T →
    ∃ (C : Coeffs ν 1 1 1) (L α β₁ β₂ : ℝ), JointBorel T C
      ∧ Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C
      ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T (1 : Matrix (Fin 1) (Fin 1) ℝ) α β₁ β₂ C
      ∧ ∀ β β' : ℝ, 0 ≤ β →
        ¬ ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ (θ θ' : TupleH ν 1 1 1)
          (μ μ' : P2 (TupleH ν 1 1 1)),
          pairing27 (1 : Matrix (Fin 1) (Fin 1) ℝ) C t θ θ' μ μ'
            ≤ -β * (‖GX (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ (θ.2.1 - θ'.2.1)‖ ^ 2
                + ‖GZ (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ (θ.2.2.1 - θ'.2.2.1)‖ ^ 2
                + ‖GU (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ ν (θ.2.2.2 - θ'.2.2.2)‖ ^ 2)
              - β' * ‖GX (1 : Matrix (Fin 1) (Fin 1) ℝ) (θ.1 - θ'.1)‖ ^ 2

/-- Remark 2.9, a uniform variable. For a Lévy driver with `d ≥ 1` Brownian coordinates and a
σ-algebra `𝒢₀`, at every `t > 0` some variable with the uniform law on `[0, 1]` is a measurable
function of the first Brownian coordinate `W¹_t` and is measurable for `ℱ_t`. -/
def rem_intrinsic_uniform : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] (d : ℕ) (hd : 0 < d) (P : Measure Ω)
    [IsProbabilityMeasure P] (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (h𝒢₀ : 𝒢₀ ≤ mΩ), ∀ t : ℝ, 0 < t →
    ∃ φ : ℝ → unitInterval, Measurable φ
      ∧ Measurable[enlJoint 𝒢₀ D h𝒢₀ t] (fun ω => φ ((D.W.W ⟨0, hd⟩).W t ω))
      ∧ P.map (fun ω => φ ((D.W.W ⟨0, hd⟩).W t ω)) = volume

/-- Remark 2.9, couplings are joint laws of inputs. In the standing setting with `d ≥ 1`, for
every `t > 0`, all laws `μ, μ' ∈ P₂(H)` and every coupling `γ` of them, some square-integrable
tuples `Θ, Θ'`, strongly measurable for `ℱ_t`, have laws `μ, μ'` and joint law `γ`. -/
def rem_intrinsic_coupling : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ), 0 < d → ∀ (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ), ∀ t : ℝ, 0 < t →
    ∀ (μ μ' : P2 (TupleH ν n m d)) (γ : Measure (TupleH ν n m d × TupleH ν n m d)),
    IsCoupling μ.law μ'.law γ →
    ∃ Θ Θ' : Ω → TupleH ν n m d, StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ t] Θ
      ∧ StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ t] Θ' ∧ MemLp Θ 2 P ∧ MemLp Θ' 2 P
      ∧ P.map (fun ω => (Θ ω, Θ' ω)) = γ ∧ lawP2 P Θ = μ ∧ lawP2 P Θ' = μ'

/-- Remark 2.9, the diagonal assumptions are intrinsic. For two standing bases (Lévy drivers
with the same `d ≥ 1` Brownian coordinates and mark measure `ν`, and σ-algebras `𝒢₀, 𝒢₀'`), a
horizon `T > 0` and coefficients with (2.3), Assumption 2.3 with a constant `L` and
Assumption 2.5 with given `G, α, β₁, β₂` each hold over one basis exactly when they hold over the
other. -/
def rem_intrinsic_basis : Prop :=
  ∀ {Ω Ω' : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (𝒢₀' : MeasurableSpace Ω') [mΩ' : MeasurableSpace Ω'] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ), 0 < d → ∀ (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (D' : LevyStochCalc.Driver.LevyDriver.{u, v, w} P' d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ) (h𝒢₀' : 𝒢₀' ≤ mΩ'),
    ∀ T : ℝ, 0 < T → ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C →
    (Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C ↔ Assumption23 (enlJoint 𝒢₀' D' h𝒢₀') P' T L C)
    ∧ (Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C
      ↔ Assumption25 (enlJoint 𝒢₀' D' h𝒢₀') P' T G α β₁ β₂ C)

/-- Remark 2.10, the fibre. For a σ-finite measure `ν` on a measurable space and `m ≥ 1`:
`L²(ν; ℝᵐ) ≠ {0}` when `ν ≠ 0`, and `L²(ν; ℝᵐ) = {0}` when `ν = 0`. -/
def rem_beta1_fibre : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] (m : ℕ), 0 < m →
    (ν ≠ 0 → ∃ u : Lp (EuclideanSpace ℝ (Fin m)) 2 ν, u ≠ 0)
      ∧ (ν = 0 → ∀ u : Lp (EuclideanSpace ℝ (Fin m)) 2 ν, u = 0)

/-- Remark 2.10, the `β₁` dichotomy. In the standing setting with `n, m ≥ 1`, for `T > 0`,
`ν ≠ 0` and `G ∈ ℝ^{m×n}` of full rank, let the coefficients satisfy Assumption 2.5 with `G` and
the constants `α, β₁, β₂`. Then: for almost every `t ∈ [0, T]` and all
`(Θ, μ), (Θ', μ') ∈ 𝒟_t` with `δX = δY = δZ = 0`,
`𝔼 ∫_E ⟨δh(e), Gᵀ δU(e)⟩ ν(de) ≤ −β₁ 𝔼 ‖Gᵀ δU‖²_{L²(ν)}`; if `h(t, θ, μ)` depends on `t` and the
forward state `x` only, then `β₁ = 0`, `m ≥ n` and `α, β₂ > 0`; and if `m < n`, then `β₁ > 0`
and `h` does not depend on `t` and `x` only. -/
def rem_beta1_dich : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → 0 < n → 0 < m → ∀ T : ℝ, 0 < T → ν ≠ 0 →
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

/-- Remark 2.10, zero intensity. In the standing setting with `n = m ≥ 1` and `ν = 0`, for
`T > 0`, `β₁, β₂ > 0`, `σ_c ∈ ℝ^{n×d}` and `h_c ∈ L²(ν; ℝⁿ)`, the coefficients of
Example 5.1(i) have a jump coefficient depending on `t` and `x` only and satisfy Assumption 2.5
with `G = I`, `α = 1` and the constants `β₁ > 0`, `β₂`. -/
def rem_beta1_zero : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] (n d : ℕ) (P : Measure Ω)
    [IsProbabilityMeasure P] (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d (0 : Measure E))
    (h𝒢₀ : 𝒢₀ ≤ mΩ), Indep 𝒢₀ (⨆ t, D.filtration t) P → 0 < n → ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ →
    ∀ (σc : EuclideanSpace ℝ (Fin n × Fin d))
      (hc : Lp (EuclideanSpace ℝ (Fin n)) 2 (0 : Measure E)),
    (∀ (t : ℝ) (θ θ' : TupleH (0 : Measure E) n n d) (μ μ' : P2 (TupleH (0 : Measure E) n n d)),
        θ.1 = θ'.1 → (affineCoeffs β₁ β₂ σc hc).h t θ μ = (affineCoeffs β₁ β₂ σc hc).h t θ' μ')
      ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T (1 : Matrix (Fin n) (Fin n) ℝ) 1 β₁ β₂
          (affineCoeffs β₁ β₂ σc hc)

/-- **(2.12)**, the interior inequality with the margin `c` in the weighted form: for almost
every `t ∈ [0, T]` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, the expectation of the pairing exists and is
at most `−β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}] − β₂ 𝔼|G δX|²
− c 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)} + |G δX|²]`. -/
def Margin212 {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
    [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (β₁ β₂ c : ℝ) (C : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
    ∀ p ∈ diagonalInputs ν n m d ℱ P t, ∀ p' ∈ diagonalInputs ν n m d ℱ P t,
      Integrable (fun ω => pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2) P
        ∧ ∫ ω, pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2 ∂P
          ≤ -β₁ * ∫ ω, (‖GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)‖ ^ 2
              + ‖GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)‖ ^ 2
              + ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2) ∂P
            - β₂ * ∫ ω, ‖GX G ((p.1 ω).1 - (p'.1 ω).1)‖ ^ 2 ∂P
            - c * ∫ ω, (‖GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)‖ ^ 2
              + ‖GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)‖ ^ 2
              + ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2
              + ‖GX G ((p.1 ω).1 - (p'.1 ω).1)‖ ^ 2) ∂P

/-- Remark 2.11, the reduced constants. In the standing setting, if (2.7) holds with the
constants `β̄₁, β̄₂` for almost every `t ∈ [0, T]`, then for every `0 < c < min{β̄₁, β̄₂}`,
(2.12) holds with the constants `β̄₁ − c, β̄₂ − c` and margin `c`. -/
def rem_margin_reduce : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P →
    ∀ (T β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Mono27At (enlJoint 𝒢₀ D h𝒢₀) P t G β₁ β₂ C) →
    ∀ c : ℝ, 0 < c → c < min β₁ β₂ →
    Margin212 (enlJoint 𝒢₀ D h𝒢₀) P T G (β₁ - c) (β₂ - c) c C

/-- Remark 2.11, the unweighted margin. In the standing setting with `m = n ≥ 1`, for
`G ∈ ℝ^{n×n}` of full rank, `c_G = s_min(G)⁻²` and `c > 0`: (2.12) with the constants `β₁, β₂`
and margin `c` gives (2.13) with the same constants and margin `c / c_G`. -/
def rem_margin_unweighted : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → 0 < n →
    ∀ (T β₁ β₂ c : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (C : Coeffs ν n n d),
    G.rank = min n n → 0 < c →
    Margin212 (enlJoint 𝒢₀ D h𝒢₀) P T G β₁ β₂ c C →
    Margin213 (enlJoint 𝒢₀ D h𝒢₀) P T G β₁ β₂ (c / (sMin G ^ 2)⁻¹) C

/-- Remark 2.11, the comparison of the margins. For `n ≥ 1` and `G ∈ ℝ^{n×n}` of full rank with
`c_G = s_min(G)⁻² > 1`, and `c > 0`, the unweighted margin `c / c_G` is smaller than `c`. -/
def rem_margin_smaller : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℝ) (c : ℝ), 0 < n → G.rank = min n n → 0 < c →
    1 < (sMin G ^ 2)⁻¹ → c / (sMin G ^ 2)⁻¹ < c

end Dissertation.PaperSpec.A
