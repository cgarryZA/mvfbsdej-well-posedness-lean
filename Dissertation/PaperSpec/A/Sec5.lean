/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Setting
import Dissertation.WellPosedness.Spec.Assumptions
import Dissertation.WellPosedness.Spec.CorollaryHyps
import Dissertation.WellPosedness.Existence.ClampAffine
import Dissertation.WellPosedness.Examples.MeanField
import Dissertation.WellPosedness.Examples.Brownian
import Dissertation.WellPosedness.Robustness.Perturb
import Dissertation.WellPosedness.Spec.Cor36Law
import Dissertation.Law.TupleMarginal
import Dissertation.WellPosedness.Examples.Dealer.ExposureCoeffs
import Dissertation.WellPosedness.Examples.Dealer.ExposureSDE

/-!
# Section 5 of the well-posedness paper: the examples

Statement and equation numbers refer to arXiv 2608.23203v1. The standing
setting is that of §2 (see `Dissertation.PaperSpec.A.thm_cwp`), here with `n = m = d = 1` and
`G = 1`.

## Main definitions

* `Dissertation.PaperSpec.A.ex_concrete_i_ham` — Example 5.1(i), the Hamiltonian and its
  minimiser.
* `Dissertation.PaperSpec.A.ex_concrete_i` — Example 5.1(i), the assumptions.
* `Dissertation.PaperSpec.A.ex_concrete_i_pairing` — Example 5.1(i), the exact pairings, the
  margin and the jump identity.
* `Dissertation.PaperSpec.A.ex_concrete_i_wp` — Example 5.1(i), well-posedness.
* `Dissertation.PaperSpec.A.ex_concrete_i_clamp`, `ex_concrete_i_clamp_wp` — Example 5.1(i) with
  the drift (3.6): the assumptions of Theorem 3.5, and well-posedness.
* `Dissertation.PaperSpec.A.ex_concrete_ii_mean` — Example 5.1(ii), the mean and the barycentre.
* `Dissertation.PaperSpec.A.ex_concrete_ii` — Example 5.1(ii), the assumptions.
* `Dissertation.PaperSpec.A.ex_concrete_ii_pairing` — Example 5.1(ii), the pairings along the
  diagonal.
* `Dissertation.PaperSpec.A.ex_brownian` — Example 5.2, the Brownian case `ν = 0`.
* `Dissertation.PaperSpec.A.ex_expfunc`, `ex_expfunc_limin`, `ex_expfunc_jump` — Example 5.3:
  expectation functionals, the kernels of independent-copy interactions, and the jump
  coefficient through the Nemytskii map.
* `Dissertation.PaperSpec.A.ex54Pert` — the perturbation of Example 5.4.
* `Dissertation.PaperSpec.A.ex_fulllaw_lip`, `ex_fulllaw_pert`, `ex_fulllaw_wp`,
  `ex_fulllaw_affineQ` — Example 5.4: the Lipschitz constants of the law statistics, the
  perturbation, well-posedness, and the affine cylindrical term.
* `Dissertation.PaperSpec.A.ex_fulllaw_beyond_radial`, `ex_fulllaw_beyond_U`,
  `ex_fulllaw_beyond_Q` — Example 5.4: the law statistics are no expectation functionals;
  `ex_fulllaw_beyond_U_corr` — the `U`-marginal statement with `L²(ν) ≠ 0`.
* `Dissertation.PaperSpec.A.ex55Crowd`, `ex55Coeffs` — the crowding correction and the
  coefficients of Example 5.5.
* `Dissertation.PaperSpec.A.ex_dealer_potential`, `ex_dealer_crowd`, `ex_dealer_coeffs`,
  `ex_dealer`, `ex_dealer_mono`, `ex_dealer_wp` — Example 5.5: the potential, the crowding
  correction, the coefficients, the assumptions, the monotonicity at every `ε ≥ 0`, and
  well-posedness.
* `Dissertation.PaperSpec.A.ex_dealer_twopoint`, `ex_dealer_not_mean`, `ex_dealer_not_mean_corr`,
  `ex_dealer_affine` — Example 5.5 beyond the mean: the two-point values, the crowding correction
  is no function of the mean and is nonlinear in the valuation curve (as printed, and with
  `L²(ν) ≠ 0`), and it is affine in the law and an expectation kernel.
* `Dissertation.PaperSpec.A.ex_dealer_marks` — Example 5.5, the mark measure.
* `Dissertation.PaperSpec.A.ex_dealer_inert` — Example 5.5, the interaction is inert without the
  exposure term.
* `Dissertation.PaperSpec.A.ex_dealer_active_data`, `ex_dealer_active_sde`,
  `ex_dealer_active_sol`, `ex_dealer_active_moments`, `ex_dealer_sym`, `ex_dealer_active_pos`,
  `ex_dealer_active_dep` — Example 5.5, the interaction is active: the data, the exposure
  equation, the solution at `ε = 0`, its moments, the crowding pairing of a law, the positive
  crowding energy at `ε > 0`, and the dependence of the solution on `ε`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.Law
  Dissertation.WellPosedness.Stability

universe u v w

/-- Example 5.1(i), the Hamiltonian. For `β₁ > 0`, `β₂ ∈ ℝ`, `σ_c ∈ ℝ`, `h_c ∈ L²(ν)` and a point
`(x, y, z, u)` of `H`, the Hamiltonian
`H(a) = a^b y + (σ_c + a^σ) z + ∫_E (h_c(e) + a^h(e)) u(e) ν(de) + (β₂/2) |x|²
  + (1/(2β₁)) (|a^b|² + |a^σ|² + ‖a^h‖²_{L²(ν)})`
is strictly convex in the controls `a = (a^b, a^σ, a^h) ∈ ℝ × ℝ × L²(ν)`, with minimiser
`a^{b*} = −β₁ y`, `a^{σ*} = −β₁ z`, `a^{h*} = −β₁ u`. -/
def ex_concrete_i_ham : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) (β₁ β₂ : ℝ), 0 < β₁ →
  ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
    (x y : EuclideanSpace ℝ (Fin 1)) (z : EuclideanSpace ℝ (Fin 1 × Fin 1))
    (u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
    let H : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1 × Fin 1)
        × Lp (EuclideanSpace ℝ (Fin 1)) 2 ν → ℝ := fun a =>
      inner ℝ a.1 y + inner ℝ (σc + a.2.1) z + ∫ e, inner ℝ (hc e + a.2.2 e) (u e) ∂ν
        + β₂ / 2 * ‖x‖ ^ 2 + 1 / (2 * β₁) * (‖a.1‖ ^ 2 + ‖a.2.1‖ ^ 2 + ‖a.2.2‖ ^ 2)
    StrictConvexOn ℝ Set.univ H ∧ ∀ a, H (-(β₁ • y), -(β₁ • z), -(β₁ • u)) ≤ H a

/-- Example 5.1(i), the assumptions. In the standing setting with `n = m = d = 1`, for `T > 0`,
`β₁, β₂ > 0`, `σ_c ∈ ℝ`, `h_c ∈ L²(ν)` and `ξ₀ ∈ L²(Ω, ℱ₀)`, the affine coefficients
`b = −β₁ y`, `σ = σ_c − β₁ z`, `h = h_c − β₁ u`, `f = β₂ x`, `g(x, ρ) = x` satisfy (2.3),
Assumption 2.2, Assumption 2.3 with `L = max{β₁, β₂, 1}`, Assumption 2.4 for `G = 1` with
`c_G = 1`, and Assumption 2.5 with `G = 1`, `α = 1` and the constants `β₁, β₂`. -/
def ex_concrete_i : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ →
    ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
      (ξ₀ : Ω → EuclideanSpace ℝ (Fin 1)),
    StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₀ → MemLp ξ₀ 2 P →
    JointBorel T (affineCoeffs β₁ β₂ σc hc)
      ∧ Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T (affineCoeffs β₁ β₂ σc hc) ξ₀
      ∧ Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T (max (max β₁ β₂) 1) (affineCoeffs β₁ β₂ σc hc)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ (sMin (1 : Matrix (Fin 1) (Fin 1) ℝ) ^ 2)⁻¹ = 1
      ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 β₁ β₂
          (affineCoeffs β₁ β₂ σc hc)

/-- Example 5.1(i), the pairings. In the setting of `ex_concrete_i`, with `G = 1`: for every
`t` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, the interior pairing of (2.7) evaluates exactly to
`𝔼[⟨δb, δY⟩ + ⟨δσ, δZ⟩_F + ⟨−δf, δX⟩ + ∫_E ⟨δh(e), δU(e)⟩ ν(de)]
  = −β₁ 𝔼[|δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}] − β₂ 𝔼|δX|²`;
for all `X_T, X'_T ∈ L²(Ω, ℱ_T)` the terminal pairing is `𝔼⟨δg_T, δX_T⟩ = 𝔼|δX_T|²`; for every
`0 < c < min{β₁, β₂}`, (2.13) holds with the constants `(β₁ − c, β₂ − c)` and the margin `c`;
and at all points `θ, θ'` of `H`, laws `μ, μ'` and times `t`,
`∫_E ⟨δh(e), δU(e)⟩ ν(de) = −β₁ ‖δU‖²_{L²(ν)}`. -/
def ex_concrete_i_pairing : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ →
    ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
    (∀ t, ∀ p ∈ diagonalInputs ν 1 1 1 (enlJoint 𝒢₀ D h𝒢₀) P t,
      ∀ p' ∈ diagonalInputs ν 1 1 1 (enlJoint 𝒢₀ D h𝒢₀) P t,
      ∫ ω, pairing27 (1 : Matrix (Fin 1) (Fin 1) ℝ) (affineCoeffs β₁ β₂ σc hc) t (p.1 ω)
          (p'.1 ω) p.2 p'.2 ∂P
        = -β₁ * ∫ ω, (‖(p.1 ω).2.1 - (p'.1 ω).2.1‖ ^ 2 + ‖(p.1 ω).2.2.1 - (p'.1 ω).2.2.1‖ ^ 2
            + ‖(p.1 ω).2.2.2 - (p'.1 ω).2.2.2‖ ^ 2) ∂P
          - β₂ * ∫ ω, ‖(p.1 ω).1 - (p'.1 ω).1‖ ^ 2 ∂P)
    ∧ (∀ XT XT' : Ω → EuclideanSpace ℝ (Fin 1), StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ T] XT →
      StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ T] XT' → MemLp XT 2 P → MemLp XT' 2 P →
      ∫ ω, inner ℝ ((affineCoeffs β₁ β₂ σc hc).g (XT ω) (lawP2 P XT)
          - (affineCoeffs β₁ β₂ σc hc).g (XT' ω) (lawP2 P XT')) (XT ω - XT' ω) ∂P
        = ∫ ω, ‖XT ω - XT' ω‖ ^ 2 ∂P)
    ∧ (∀ c : ℝ, 0 < c → c < min β₁ β₂ →
      Margin213 (enlJoint 𝒢₀ D h𝒢₀) P T (1 : Matrix (Fin 1) (Fin 1) ℝ) (β₁ - c) (β₂ - c) c
        (affineCoeffs β₁ β₂ σc hc))
    ∧ ∀ (t : ℝ) (θ θ' : TupleH ν 1 1 1) (μ μ' : P2 (TupleH ν 1 1 1)),
      ∫ e, inner ℝ ((affineCoeffs β₁ β₂ σc hc).h t θ μ e
          - (affineCoeffs β₁ β₂ σc hc).h t θ' μ' e) (θ.2.2.2 e - θ'.2.2.2 e) ∂ν
        = -β₁ * ‖θ.2.2.2 - θ'.2.2.2‖ ^ 2

/-- Example 5.1(i), well-posedness. In the setting of `ex_concrete_i`, (1.1) with the affine
coefficients and the initial datum `ξ₀` has a solution in `ℍ`, and any two solutions are equal
in `ℍ`: their `X` and their `Y` are indistinguishable on `[0, T]`, and
`𝔼 ∫_0^T |Z¹_t − Z²_t|² dt = 0` and `𝔼 ∫_0^T ‖U¹_t − U²_t‖²_{L²(ν)} dt = 0`. -/
def ex_concrete_i_wp : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ →
    ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
      (ξ₀ : Ω → EuclideanSpace ℝ (Fin 1)),
    StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₀ → MemLp ξ₀ 2 P →
    (∃ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U : Fin 1 → ℝ → Ω → E → ℝ),
      Solution D h𝒢₀ hind₀ T (affineCoeffs β₁ β₂ σc hc) ξ₀ X Y Z U)
    ∧ ∀ (X₁ X₂ : Fin 1 → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U₁ U₂ : Fin 1 → ℝ → Ω → E → ℝ),
      Solution D h𝒢₀ hind₀ T (affineCoeffs β₁ β₂ σc hc) ξ₀ X₁ Y₁ Z₁ U₁ →
      Solution D h𝒢₀ hind₀ T (affineCoeffs β₁ β₂ σc hc) ξ₀ X₂ Y₂ Z₂ U₂ →
      (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
        ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
        ∧ (∀ k j, LevyStochCalc.Brownian.Ito.energy P T
            (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
        ∧ ∀ k, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0

/-- Example 5.1(i) with the drift (3.6), the assumptions. In the setting of `ex_concrete_i`, for
every `0 < ε < β₁`, replacing the drift `−β₁ y` by (3.6),
`b = −β₁ y + ε g₀(y − m_Y(μ))`, gives coefficients satisfying (2.3), Assumption 2.2,
Assumption 2.3 with some constant `L`, Assumption 2.4 for `G = 1`, and Assumption 2.5 with
`G = 1`, `α = 1` and the constants `(β₁ − ε, β₂)`: the hypotheses of Theorem 3.5. -/
def ex_concrete_i_clamp : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ ε : ℝ), 0 < β₁ → 0 < β₂ → 0 < ε → ε < β₁ →
    ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
      (ξ₀ : Ω → EuclideanSpace ℝ (Fin 1)),
    StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₀ → MemLp ξ₀ 2 P →
    JointBorel T (clampAffineCoeffs β₁ β₂ ε σc hc)
      ∧ Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T (clampAffineCoeffs β₁ β₂ ε σc hc) ξ₀
      ∧ (∃ L : ℝ, Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L (clampAffineCoeffs β₁ β₂ ε σc hc))
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (β₁ - ε) β₂
          (clampAffineCoeffs β₁ β₂ ε σc hc)

/-- Example 5.1(i) with the drift (3.6), well-posedness: in the setting of
`ex_concrete_i_clamp`, (1.1) has a solution in `ℍ`, and any two solutions are equal in `ℍ`, as
in `ex_concrete_i_wp`. -/
def ex_concrete_i_clamp_wp : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ ε : ℝ), 0 < β₁ → 0 < β₂ → 0 < ε → ε < β₁ →
    ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
      (ξ₀ : Ω → EuclideanSpace ℝ (Fin 1)),
    StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₀ → MemLp ξ₀ 2 P →
    (∃ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U : Fin 1 → ℝ → Ω → E → ℝ),
      Solution D h𝒢₀ hind₀ T (clampAffineCoeffs β₁ β₂ ε σc hc) ξ₀ X Y Z U)
    ∧ ∀ (X₁ X₂ : Fin 1 → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U₁ U₂ : Fin 1 → ℝ → Ω → E → ℝ),
      Solution D h𝒢₀ hind₀ T (clampAffineCoeffs β₁ β₂ ε σc hc) ξ₀ X₁ Y₁ Z₁ U₁ →
      Solution D h𝒢₀ hind₀ T (clampAffineCoeffs β₁ β₂ ε σc hc) ξ₀ X₂ Y₂ Z₂ U₂ →
      (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
        ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
        ∧ (∀ k j, LevyStochCalc.Brownian.Ito.energy P T
            (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
        ∧ ∀ k, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0

/-- Example 5.1(ii), the mean and the barycentre. For `ν` σ-finite and laws `μ, μ' ∈ P₂(H)`
(`n = m = d = 1`) and `ρ, ρ' ∈ P₂(ℝ)`: the mean `∫_H θ μ(dθ)` has the marginal means
`m_Ψ(μ) = ∫_H π_Ψ(θ) μ(dθ)` as its channels; `δm = ∫_H θ dμ − ∫_H θ dμ'` satisfies
`|δm|_H ≤ W₂(μ, μ')` and `|δm_X| + |δm_Y| + |δm_Z|_F + ‖δm_U‖_{L²(ν)} ≤ 2 |δm|_H`, with `|·|_H`
the Hilbert norm of `H` and `W₂` its 2-Wasserstein distance; and the barycentre satisfies
`|𝔟(ρ) − 𝔟(ρ')| ≤ W₂(ρ, ρ')`. -/
def ex_concrete_ii_mean : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E],
    (∀ μ μ' : P2 (TupleH ν 1 1 1),
      tupleMean μ = (∫ θ, θ.1 ∂μ.law, ∫ θ, θ.2.1 ∂μ.law, ∫ θ, θ.2.2.1 ∂μ.law,
          ∫ θ, θ.2.2.2 ∂μ.law)
        ∧ ‖toL2 (tupleMean μ - tupleMean μ')‖ ≤ w2H μ μ'
        ∧ ‖(tupleMean μ - tupleMean μ').1‖ + ‖(tupleMean μ - tupleMean μ').2.1‖
            + ‖(tupleMean μ - tupleMean μ').2.2.1‖ + ‖(tupleMean μ - tupleMean μ').2.2.2‖
          ≤ 2 * ‖toL2 (tupleMean μ - tupleMean μ')‖)
    ∧ ∀ ρ ρ' : P2 (EuclideanSpace ℝ (Fin 1)), ‖barycentre ρ - barycentre ρ'‖ ≤ w2P ρ ρ'

/-- Example 5.1(ii), the assumptions. In the standing setting with `n = m = d = 1`, for `T > 0`
and `ξ₀ ∈ L²(Ω, ℱ₀)`, the mean-field coefficients
`b = −2y − m_Y(μ)`, `σ = −2z − m_Z(μ)`, `h = −2u − m_U(μ)`, `f = 2x + m_X(μ)`,
`g(x, ρ) = 2x + 𝔟(ρ)` satisfy (2.3); `b, σ, h, f` vanish at `(t, 0, δ₀)`; and they satisfy
Assumption 2.2, Assumption 2.3 with `L = 2`, Assumption 2.4 for `G = 1`, and Assumption 2.5 with
`G = 1` and `α = β₁ = β₂ = 2`. -/
def ex_concrete_ii : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ T : ℝ, 0 < T →
    ∀ ξ₀ : Ω → EuclideanSpace ℝ (Fin 1),
    StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₀ → MemLp ξ₀ 2 P →
    JointBorel T (meanFieldCoeffs ν 1 1)
      ∧ (∀ t, (meanFieldCoeffs ν 1 1).b t 0 (P2.dirac 0) = 0
        ∧ (meanFieldCoeffs ν 1 1).σ t 0 (P2.dirac 0) = 0
        ∧ (meanFieldCoeffs ν 1 1).h t 0 (P2.dirac 0) = 0
        ∧ (meanFieldCoeffs ν 1 1).f t 0 (P2.dirac 0) = 0)
      ∧ Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T (meanFieldCoeffs ν 1 1) ξ₀
      ∧ Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T 2 (meanFieldCoeffs ν 1 1)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 2 2 2
          (meanFieldCoeffs ν 1 1)

/-- Example 5.1(ii), the pairings along the diagonal. In the setting of `ex_concrete_ii`, with
`G = 1`: for every `t` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, the mean of `μ` is `𝔼 Θ`; each channel
contributes its own mean square,
`𝔼⟨−δf, δX⟩ = −2 𝔼|δX|² − |𝔼 δX|²`, `𝔼⟨δb, δY⟩ = −2 𝔼|δY|² − |𝔼 δY|²`,
`𝔼⟨δσ, δZ⟩_F = −2 𝔼|δZ|²_F − |𝔼 δZ|²_F`,
`𝔼 ∫_E ⟨δh(e), δU(e)⟩ ν(de) = −2 𝔼‖δU‖²_{L²(ν)} − ‖𝔼 δU‖²_{L²(ν)}`;
and the interior pairing is
`𝔼[⟨δb, δY⟩ + ⟨δσ, δZ⟩_F + ⟨−δf, δX⟩ + ∫_E ⟨δh(e), δU(e)⟩ ν(de)]
  = −2 𝔼[|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)}]
    − (|𝔼 δX|² + |𝔼 δY|² + |𝔼 δZ|²_F + ‖𝔼 δU‖²_{L²(ν)})`;
and for all `X_T, X'_T ∈ L²(Ω, ℱ_T)`, `𝔼⟨δg_T, δX_T⟩ = 2 𝔼|δX_T|² + |𝔼 δX_T|²`. -/
def ex_concrete_ii_pairing : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ T : ℝ, 0 < T →
    (∀ t, ∀ p ∈ diagonalInputs ν 1 1 1 (enlJoint 𝒢₀ D h𝒢₀) P t,
      ∀ p' ∈ diagonalInputs ν 1 1 1 (enlJoint 𝒢₀ D h𝒢₀) P t,
      tupleMean p.2 = ∫ ω, p.1 ω ∂P
        ∧ ∫ ω, inner ℝ (-((meanFieldCoeffs ν 1 1).f t (p.1 ω) p.2
            - (meanFieldCoeffs ν 1 1).f t (p'.1 ω) p'.2)) ((p.1 ω).1 - (p'.1 ω).1) ∂P
          = -2 * ∫ ω, ‖(p.1 ω).1 - (p'.1 ω).1‖ ^ 2 ∂P
            - ‖∫ ω, ((p.1 ω).1 - (p'.1 ω).1) ∂P‖ ^ 2
        ∧ ∫ ω, inner ℝ ((meanFieldCoeffs ν 1 1).b t (p.1 ω) p.2
            - (meanFieldCoeffs ν 1 1).b t (p'.1 ω) p'.2) ((p.1 ω).2.1 - (p'.1 ω).2.1) ∂P
          = -2 * ∫ ω, ‖(p.1 ω).2.1 - (p'.1 ω).2.1‖ ^ 2 ∂P
            - ‖∫ ω, ((p.1 ω).2.1 - (p'.1 ω).2.1) ∂P‖ ^ 2
        ∧ ∫ ω, inner ℝ ((meanFieldCoeffs ν 1 1).σ t (p.1 ω) p.2
            - (meanFieldCoeffs ν 1 1).σ t (p'.1 ω) p'.2) ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1) ∂P
          = -2 * ∫ ω, ‖(p.1 ω).2.2.1 - (p'.1 ω).2.2.1‖ ^ 2 ∂P
            - ‖∫ ω, ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1) ∂P‖ ^ 2
        ∧ ∫ ω, ∫ e, inner ℝ ((meanFieldCoeffs ν 1 1).h t (p.1 ω) p.2 e
            - (meanFieldCoeffs ν 1 1).h t (p'.1 ω) p'.2 e)
            ((p.1 ω).2.2.2 e - (p'.1 ω).2.2.2 e) ∂ν ∂P
          = -2 * ∫ ω, ‖(p.1 ω).2.2.2 - (p'.1 ω).2.2.2‖ ^ 2 ∂P
            - ‖∫ ω, ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2) ∂P‖ ^ 2
        ∧ ∫ ω, pairing27 (1 : Matrix (Fin 1) (Fin 1) ℝ) (meanFieldCoeffs ν 1 1) t (p.1 ω)
            (p'.1 ω) p.2 p'.2 ∂P
          = -2 * ∫ ω, (‖(p.1 ω).1 - (p'.1 ω).1‖ ^ 2 + ‖(p.1 ω).2.1 - (p'.1 ω).2.1‖ ^ 2
              + ‖(p.1 ω).2.2.1 - (p'.1 ω).2.2.1‖ ^ 2 + ‖(p.1 ω).2.2.2 - (p'.1 ω).2.2.2‖ ^ 2) ∂P
            - (‖∫ ω, ((p.1 ω).1 - (p'.1 ω).1) ∂P‖ ^ 2
              + ‖∫ ω, ((p.1 ω).2.1 - (p'.1 ω).2.1) ∂P‖ ^ 2
              + ‖∫ ω, ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1) ∂P‖ ^ 2
              + ‖∫ ω, ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2) ∂P‖ ^ 2))
    ∧ ∀ XT XT' : Ω → EuclideanSpace ℝ (Fin 1), StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ T] XT →
      StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ T] XT' → MemLp XT 2 P → MemLp XT' 2 P →
      ∫ ω, inner ℝ ((meanFieldCoeffs ν 1 1).g (XT ω) (lawP2 P XT)
          - (meanFieldCoeffs ν 1 1).g (XT' ω) (lawP2 P XT')) (XT ω - XT' ω) ∂P
        = 2 * ∫ ω, ‖XT ω - XT' ω‖ ^ 2 ∂P + ‖∫ ω, (XT ω - XT' ω) ∂P‖ ^ 2

/-- Example 5.2 (Brownian reduction). In the standing setting with the intensity `ν = 0`: the
filtration is the usual augmentation of the filtration generated by `W` and `ℱ₀`; the fibre
`L²(ν; ℝᵐ)` is trivial, so the `U`-coordinate is deleted; `W₂` on `P₂(H)` is `W₂` on the laws of
`(X, Y, Z)` in `ℝⁿ × ℝᵐ × ℝ^{m×d}` with its Euclidean norm; and the `m < n` rank branch of
Assumption 2.5 is available with a jump coefficient of the additive form `h = h(t, x)`: for
`1 ≤ m < n`, `T > 0` and `ξ₀ ∈ L²(Ω, ℱ₀)` there are a coupling matrix `G` of full rank and
coefficients with such a jump coefficient satisfying (2.3) and Assumptions 2.2–2.5 with
`β₁ > 0`. -/
def ex_brownian : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] (d : ℕ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d (0 : Measure E)) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P →
    enlJoint 𝒢₀ D h𝒢₀ = LevyStochCalc.Brownian.augFiltration
        (D.W.naturalFiltration ⊔ MeasureTheory.Filtration.const ℝ 𝒢₀ h𝒢₀).rightCont P
    ∧ (∀ (m : ℕ) (u : Lp (EuclideanSpace ℝ (Fin m)) 2 (0 : Measure E)), u = 0)
    ∧ (∀ (n m : ℕ) (μ μ' : P2 (TupleH (0 : Measure E) n m d)),
      w2P (projP2 μ) (projP2 μ') = w2H μ μ')
    ∧ ∀ n m : ℕ, 0 < m → m < n → 0 < d → ∀ T : ℝ, 0 < T →
      ∀ ξ₀ : Ω → EuclideanSpace ℝ (Fin n),
      StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₀ → MemLp ξ₀ 2 P →
      ∃ (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs (0 : Measure E) n m d) (L α β₁ β₂ : ℝ),
        (∀ (t : ℝ) (θ θ' : TupleH (0 : Measure E) n m d)
          (μ μ' : P2 (TupleH (0 : Measure E) n m d)), θ.1 = θ'.1 → C.h t θ μ = C.h t θ' μ')
        ∧ JointBorel T C ∧ Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀
        ∧ Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C ∧ G.rank = min m n
        ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C ∧ 0 < β₁

/-- Example 5.3 (expectation-functional interactions), the class. For `ν` σ-finite on a countably
generated space, dimensions `n, m, d, k`, and `φ̄ : [0, T] × H × H → ℝᵏ` measurable and Lipschitz
in `(θ, θ')` uniformly in `t` with constant `L ≥ 0`,
`|φ̄(t, θ₁, θ₁') − φ̄(t, θ₂, θ₂')| ≤ L (|θ₁ − θ₂|_H + |θ₁' − θ₂'|_H)`: at each `t` and `θ` the
kernel `φ̄(t, θ, ·)` is `L`-Lipschitz, and `φ(t, θ, μ) = ∫_H φ̄(t, θ, θ') μ(dθ')` satisfies
`|φ(t, θ, μ) − φ(t, θ, μ')| ≤ L W₂(μ, μ')`: the law-dependence component of Assumption 2.3. -/
def ex_expfunc : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d k : ℕ)
    (φbar : ℝ → TupleH ν n m d → TupleH ν n m d → EuclideanSpace ℝ (Fin k)) (L : ℝ), 0 ≤ L →
    Measurable (fun p : ℝ × TupleH ν n m d × TupleH ν n m d => φbar p.1 p.2.1 p.2.2) →
    (∀ (t : ℝ) (θ₁ θ₁' θ₂ θ₂' : TupleH ν n m d), ‖φbar t θ₁ θ₁' - φbar t θ₂ θ₂'‖
      ≤ L * (‖toL2 θ₁ - toL2 θ₂‖ + ‖toL2 θ₁' - toL2 θ₂'‖)) →
    ∀ (t : ℝ) (θ : TupleH ν n m d),
      (∀ θ₁' θ₂' : TupleH ν n m d, ‖φbar t θ θ₁' - φbar t θ θ₂'‖ ≤ L * ‖toL2 θ₁' - toL2 θ₂'‖)
      ∧ ∀ μ μ' : P2 (TupleH ν n m d),
        ‖(∫ θ', φbar t θ θ' ∂μ.law) - ∫ θ', φbar t θ θ' ∂μ'.law‖ ≤ L * w2H μ μ'

/-- Example 5.3, the kernels of independent-copy interactions. For a finite measure `ν`, a
kernel `ψ̄ : [0, T] × B × B → ℝᵏ` on the blocks `B = ℝⁿ × ℝᵐ × ℝ^{m×d} × ℝᵐ`, Lipschitz with
constant `Lip ≥ 0` for the Euclidean norm on each argument block `(x, y, z, u(e))`,
`(x', y', z', u'(e))`, uniformly in `t`: at every `t` and `θ, θ' ∈ H`, the integrand of
`φ̄(t, θ, θ') = ∫_E ψ̄(t, x, y, z, u(e), x', y', z', u'(e)) ν(de)` is `ν`-integrable;
`|φ̄(t, θ₁, θ₁') − φ̄(t, θ₂, θ₂')| ≤ Lip max{ν(E), ν(E)^{1/2}} (|θ₁ − θ₂|_H + |θ₁' − θ₂'|_H)`; and
changing `u, u'` on a `ν`-null set does not change `φ̄`. -/
def ex_expfunc_limin : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [IsFiniteMeasure ν] (n m d k : ℕ)
    (ψbar : ℝ → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)
        × EuclideanSpace ℝ (Fin m × Fin d) × EuclideanSpace ℝ (Fin m))
      → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)
        × EuclideanSpace ℝ (Fin m × Fin d) × EuclideanSpace ℝ (Fin m))
      → EuclideanSpace ℝ (Fin k)) (Lip : ℝ), 0 ≤ Lip →
    (∀ t a a' b b', ‖ψbar t a a' - ψbar t b b'‖ ≤ Lip * (Real.sqrt (‖a.1 - b.1‖ ^ 2
      + ‖a.2.1 - b.2.1‖ ^ 2 + ‖a.2.2.1 - b.2.2.1‖ ^ 2 + ‖a.2.2.2 - b.2.2.2‖ ^ 2)
      + Real.sqrt (‖a'.1 - b'.1‖ ^ 2 + ‖a'.2.1 - b'.2.1‖ ^ 2 + ‖a'.2.2.1 - b'.2.2.1‖ ^ 2
        + ‖a'.2.2.2 - b'.2.2.2‖ ^ 2))) →
    ∀ t : ℝ,
      (∀ θ θ' : TupleH ν n m d, Integrable (fun e => ψbar t (θ.1, θ.2.1, θ.2.2.1, θ.2.2.2 e)
        (θ'.1, θ'.2.1, θ'.2.2.1, θ'.2.2.2 e)) ν)
      ∧ (∀ θ₁ θ₁' θ₂ θ₂' : TupleH ν n m d,
        ‖(∫ e, ψbar t (θ₁.1, θ₁.2.1, θ₁.2.2.1, θ₁.2.2.2 e)
            (θ₁'.1, θ₁'.2.1, θ₁'.2.2.1, θ₁'.2.2.2 e) ∂ν)
          - ∫ e, ψbar t (θ₂.1, θ₂.2.1, θ₂.2.2.1, θ₂.2.2.2 e)
            (θ₂'.1, θ₂'.2.1, θ₂'.2.2.1, θ₂'.2.2.2 e) ∂ν‖
        ≤ Lip * max (ν.real Set.univ) (Real.sqrt (ν.real Set.univ))
          * (‖toL2 θ₁ - toL2 θ₂‖ + ‖toL2 θ₁' - toL2 θ₂'‖))
      ∧ ∀ (θ θ' : TupleH ν n m d) (v v' : E → EuclideanSpace ℝ (Fin m)),
        v =ᵐ[ν] θ.2.2.2 → v' =ᵐ[ν] θ'.2.2.2 →
        ∫ e, ψbar t (θ.1, θ.2.1, θ.2.2.1, v e) (θ'.1, θ'.2.1, θ'.2.2.1, v' e) ∂ν
          = ∫ e, ψbar t (θ.1, θ.2.1, θ.2.2.1, θ.2.2.2 e)
            (θ'.1, θ'.2.1, θ'.2.2.1, θ'.2.2.2 e) ∂ν

/-- Example 5.3, the jump coefficient. For `ν` σ-finite on a countably generated space and a
kernel `h̄ : [0, T] × B × B × E → ℝⁿ` on the blocks `B = ℝⁿ × ℝᵐ × ℝ^{m×d} × ℝᵐ`: the Nemytskii
map `[𝐇_t(θ, θ')](e) = h̄(t, x, y, z, u(e), x', y', z', u'(e), e)` is well defined on equivalence
classes, changing `u, u'` on a `ν`-null set changing it on a `ν`-null set; and if
`𝐇_t : H × H → L²(ν; ℝⁿ)` represents it and is Lipschitz with constant `C ≥ 0`,
`‖𝐇_t(θ₁, θ₁') − 𝐇_t(θ₂, θ₂')‖_{L²(ν)} ≤ C (|θ₁ − θ₂|_H + |θ₁' − θ₂'|_H)`, then
`h(t, θ, μ) = ∫_H 𝐇_t(θ, θ') μ(dθ')` satisfies `‖h(t, θ, μ) − h(t, θ, μ')‖_{L²(ν)} ≤ C W₂(μ, μ')`:
(2.10) with `K = L²(ν; ℝⁿ)`. -/
def ex_expfunc_jump : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d : ℕ)
    (hbar : ℝ → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)
        × EuclideanSpace ℝ (Fin m × Fin d) × EuclideanSpace ℝ (Fin m))
      → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)
        × EuclideanSpace ℝ (Fin m × Fin d) × EuclideanSpace ℝ (Fin m))
      → E → EuclideanSpace ℝ (Fin n)),
    (∀ (t : ℝ) (θ θ' : TupleH ν n m d) (v v' : E → EuclideanSpace ℝ (Fin m)),
      v =ᵐ[ν] θ.2.2.2 → v' =ᵐ[ν] θ'.2.2.2 →
      (fun e => hbar t (θ.1, θ.2.1, θ.2.2.1, v e) (θ'.1, θ'.2.1, θ'.2.2.1, v' e) e)
        =ᵐ[ν] fun e => hbar t (θ.1, θ.2.1, θ.2.2.1, θ.2.2.2 e)
          (θ'.1, θ'.2.1, θ'.2.2.1, θ'.2.2.2 e) e)
    ∧ ∀ (H : ℝ → TupleH ν n m d → TupleH ν n m d → Lp (EuclideanSpace ℝ (Fin n)) 2 ν)
      (C : ℝ), 0 ≤ C →
      (∀ (t : ℝ) (θ θ' : TupleH ν n m d), (H t θ θ' : E → EuclideanSpace ℝ (Fin n))
        =ᵐ[ν] fun e => hbar t (θ.1, θ.2.1, θ.2.2.1, θ.2.2.2 e)
          (θ'.1, θ'.2.1, θ'.2.2.1, θ'.2.2.2 e) e) →
      (∀ (t : ℝ) (θ₁ θ₁' θ₂ θ₂' : TupleH ν n m d),
        ‖H t θ₁ θ₁' - H t θ₂ θ₂'‖ ≤ C * (‖toL2 θ₁ - toL2 θ₂‖ + ‖toL2 θ₁' - toL2 θ₂'‖)) →
      ∀ (t : ℝ) (θ : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)),
        ‖(∫ θ', H t θ θ' ∂μ.law) - ∫ θ', H t θ θ' ∂μ'.law‖ ≤ C * w2H μ μ'

/-- The perturbation of Example 5.4 (with `m = n`): for a size `ε`, radial profiles `𝔮, 𝔮̃, 𝔮̂`,
an outer function `Q : ℝᴶ → ℝ`, features `φ_1, …, φ_J : L²(ν; ℝⁿ) → ℝ`, reference laws
`μ₀ ∈ P₂(H)`, `Λ₀ ∈ P₂(L²(ν; ℝⁿ))` and directions `w₀, w₁, v₀ ∈ ℝⁿ`, `ĥ ∈ L²(ν; ℝⁿ)`:
`p_f = ε 𝔮(W₂(μ, μ₀)) w₀ + ε Q(∫ φ_1 dμ^U, …, ∫ φ_J dμ^U) w₁`, `p_b = ε 𝔮̃(W₂(μ^U, Λ₀)) v₀`,
`p_h = ε 𝔮̂(W₂(μ^U, Λ₀)) ĥ`, `p_σ = 0`, independent of the time and the tuple, with `W₂` the
2-Wasserstein distance of the Hilbert norm on `P₂(H)` and of the norm on `P₂(L²(ν; ℝⁿ))`. The
perturbed system is `C.perturb (ex54Pert …)`: `f = f₀ + p_f`, `b = b₀ + p_b`, `h = h₀ + p_h`. -/
noncomputable def ex54Pert {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n d J : ℕ) (ε : ℝ) (q qb qh : ℝ → ℝ)
    (Q : EuclideanSpace ℝ (Fin J) → ℝ) (φ : Fin J → Lp (EuclideanSpace ℝ (Fin n)) 2 ν → ℝ)
    (μ₀ : P2 (TupleH ν n n d)) (Λ₀ : P2 (Lp (EuclideanSpace ℝ (Fin n)) 2 ν))
    (w₀ w₁ v₀ : EuclideanSpace ℝ (Fin n)) (hhat : Lp (EuclideanSpace ℝ (Fin n)) 2 ν) :
    Coeffs ν n n d :=
  Coeffs.ofLaw (fun _ μ => (ε * qb (w2P μ.margU Λ₀)) • v₀) (fun _ _ => 0)
    (fun _ μ => (ε * qh (w2P μ.margU Λ₀)) • hhat)
    (fun _ μ => (ε * q (w2H μ μ₀)) • w₀
      + (ε * Q (WithLp.toLp 2 fun j => ∫ u, φ j u ∂μ.margU.law)) • w₁)

/-- Example 5.4, the law statistics are `W₂`-Lipschitz. For `ν` σ-finite on a countably generated
space, profiles `𝔮, 𝔮̃, 𝔮̂` Lipschitz with constants `Lip(𝔮), Lip(𝔮̃), Lip(𝔮̂)`, `Q` Lipschitz
with constant `Lip(Q)` for the Euclidean norm, features `φ_j` Lipschitz with constants
`Lip(φ_j)`, and reference laws `μ₀, Λ₀`: for all `μ, μ' ∈ P₂(H)`,
`|𝔮(W₂(μ, μ₀)) − 𝔮(W₂(μ', μ₀))| ≤ Lip(𝔮) W₂(μ, μ')`, the same for `𝔮̃(W₂(·^U, Λ₀))` and
`𝔮̂(W₂(·^U, Λ₀))` with `Lip(𝔮̃)`, `Lip(𝔮̂)`, and
`|Q((∫ φ_j dμ^U)_j) − Q((∫ φ_j dμ'^U)_j)| ≤ L_Q W₂(μ, μ')`,
`L_Q = Lip(Q) (∑_j Lip(φ_j)²)^{1/2}`. -/
def ex_fulllaw_lip : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d J : ℕ) (q qb qh : ℝ → ℝ)
    (Q : EuclideanSpace ℝ (Fin J) → ℝ) (φ : Fin J → Lp (EuclideanSpace ℝ (Fin m)) 2 ν → ℝ)
    (Lq Lqb Lqh LQ : ℝ) (K : Fin J → ℝ), 0 ≤ Lq → 0 ≤ Lqb → 0 ≤ Lqh → 0 ≤ LQ →
    (∀ r r', |q r - q r'| ≤ Lq * |r - r'|) → (∀ r r', |qb r - qb r'| ≤ Lqb * |r - r'|) →
    (∀ r r', |qh r - qh r'| ≤ Lqh * |r - r'|) → (∀ v v', |Q v - Q v'| ≤ LQ * ‖v - v'‖) →
    (∀ j u u', |φ j u - φ j u'| ≤ K j * ‖u - u'‖) →
    ∀ (μ₀ : P2 (TupleH ν n m d)) (Λ₀ : P2 (Lp (EuclideanSpace ℝ (Fin m)) 2 ν))
      (μ μ' : P2 (TupleH ν n m d)),
      |q (w2H μ μ₀) - q (w2H μ' μ₀)| ≤ Lq * w2H μ μ'
      ∧ |qb (w2P μ.margU Λ₀) - qb (w2P μ'.margU Λ₀)| ≤ Lqb * w2H μ μ'
      ∧ |qh (w2P μ.margU Λ₀) - qh (w2P μ'.margU Λ₀)| ≤ Lqh * w2H μ μ'
      ∧ |Q (WithLp.toLp 2 fun j => ∫ u, φ j u ∂μ.margU.law)
          - Q (WithLp.toLp 2 fun j => ∫ u, φ j u ∂μ'.margU.law)|
        ≤ LQ * Real.sqrt (∑ j, K j ^ 2) * w2H μ μ'

/-- Example 5.4, the perturbation. In the standing setting with `m = n`, for `T > 0`, a coupling
matrix `G`, `ε > 0` and the data of `ex_fulllaw_lip`: the perturbation `ex54Pert` is independent
of the tuple, satisfies the origin integrability of Assumption 2.2, (3.5) and the interior bound
of Assumption 2.3 with
`L_p = ε (|w₀| Lip(𝔮) + |v₀| Lip(𝔮̃) + |w₁| L_Q + ‖ĥ‖ Lip(𝔮̂))`, and (3.4) with
`c_pert = ‖G‖ L_p`. -/
def ex_fulllaw_pert : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n d J : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → 0 < n → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (G : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (q qb qh : ℝ → ℝ)
      (Q : EuclideanSpace ℝ (Fin J) → ℝ) (φ : Fin J → Lp (EuclideanSpace ℝ (Fin n)) 2 ν → ℝ)
      (μ₀ : P2 (TupleH ν n n d)) (Λ₀ : P2 (Lp (EuclideanSpace ℝ (Fin n)) 2 ν))
      (w₀ w₁ v₀ : EuclideanSpace ℝ (Fin n)) (hhat : Lp (EuclideanSpace ℝ (Fin n)) 2 ν)
      (Lq Lqb Lqh LQ : ℝ) (K : Fin J → ℝ), 0 < ε →
    0 ≤ Lq → 0 ≤ Lqb → 0 ≤ Lqh → 0 ≤ LQ →
    (∀ r r', |q r - q r'| ≤ Lq * |r - r'|) → (∀ r r', |qb r - qb r'| ≤ Lqb * |r - r'|) →
    (∀ r r', |qh r - qh r'| ≤ Lqh * |r - r'|) → (∀ v v', |Q v - Q v'| ≤ LQ * ‖v - v'‖) →
    (∀ j u u', |φ j u - φ j u'| ≤ K j * ‖u - u'‖) →
    (ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat).TupleIndep
      ∧ OriginValues T (ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat)
      ∧ LawLip35 (enlJoint 𝒢₀ D h𝒢₀) P T
          (ε * (‖w₀‖ * Lq + ‖v₀‖ * Lqb + ‖w₁‖ * (LQ * Real.sqrt (∑ j, K j ^ 2)) + ‖hhat‖ * Lqh))
          (ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat)
      ∧ LipInterior (enlJoint 𝒢₀ D h𝒢₀) P T
          (ε * (‖w₀‖ * Lq + ‖v₀‖ * Lqb + ‖w₁‖ * (LQ * Real.sqrt (∑ j, K j ^ 2)) + ‖hhat‖ * Lqh))
          (ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat)
      ∧ PairingBound34 (enlJoint 𝒢₀ D h𝒢₀) P T G (‖GX G‖
          * (ε * (‖w₀‖ * Lq + ‖v₀‖ * Lqb + ‖w₁‖ * (LQ * Real.sqrt (∑ j, K j ^ 2))
            + ‖hhat‖ * Lqh)))
          (ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat)

/-- Example 5.4, well-posedness. In the standing setting with `m = n`, for `T > 0`, let the
baseline `C` with initial datum `ξ₀` satisfy the hypotheses of Corollary 3.6 on the baseline:
(2.3), Assumptions 2.2–2.5 with `L₀, G, α, β₁, β₂` and the margin `c_diss > 0` in (2.13). With
the data of `ex_fulllaw_pert`, if (5.1),
`ε ‖G‖ (|w₀| Lip(𝔮) + |v₀| Lip(𝔮̃) + |w₁| L_Q + ‖ĥ‖ Lip(𝔮̂)) < c_diss`, holds, then the perturbed
system satisfies (2.3), Assumptions 2.2–2.5 with the baseline's `G, α, β₁, β₂` and (2.13) with
margin `c_diss − ‖G‖ L_p`, and it is well-posed: (1.1) has a solution, and any two solutions
are equal in `ℍ`. -/
def ex_fulllaw_wp : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n d J : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), 0 < n → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L₀ α β₁ β₂ cdiss : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (C : Coeffs ν n n d)
      (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L₀ C → G.rank = min n n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    Margin213 (enlJoint 𝒢₀ D h𝒢₀) P T G β₁ β₂ cdiss C → 0 < cdiss →
    ∀ (ε : ℝ) (q qb qh : ℝ → ℝ)
      (Q : EuclideanSpace ℝ (Fin J) → ℝ) (φ : Fin J → Lp (EuclideanSpace ℝ (Fin n)) 2 ν → ℝ)
      (μ₀ : P2 (TupleH ν n n d)) (Λ₀ : P2 (Lp (EuclideanSpace ℝ (Fin n)) 2 ν))
      (w₀ w₁ v₀ : EuclideanSpace ℝ (Fin n)) (hhat : Lp (EuclideanSpace ℝ (Fin n)) 2 ν)
      (Lq Lqb Lqh LQ : ℝ) (K : Fin J → ℝ), 0 < ε →
    0 ≤ Lq → 0 ≤ Lqb → 0 ≤ Lqh → 0 ≤ LQ →
    (∀ r r', |q r - q r'| ≤ Lq * |r - r'|) → (∀ r r', |qb r - qb r'| ≤ Lqb * |r - r'|) →
    (∀ r r', |qh r - qh r'| ≤ Lqh * |r - r'|) → (∀ v v', |Q v - Q v'| ≤ LQ * ‖v - v'‖) →
    (∀ j u u', |φ j u - φ j u'| ≤ K j * ‖u - u'‖) →
    ε * ‖GX G‖ * (‖w₀‖ * Lq + ‖v₀‖ * Lqb + ‖w₁‖ * (LQ * Real.sqrt (∑ j, K j ^ 2))
      + ‖hhat‖ * Lqh) < cdiss →
    JointBorel T (C.perturb (ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat))
      ∧ Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T
          (C.perturb (ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat)) ξ₀
      ∧ (∃ L : ℝ, Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L
          (C.perturb (ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat)))
      ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂
          (C.perturb (ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat))
      ∧ Margin213 (enlJoint 𝒢₀ D h𝒢₀) P T G β₁ β₂
          (cdiss - ‖GX G‖ * (ε * (‖w₀‖ * Lq + ‖v₀‖ * Lqb
            + ‖w₁‖ * (LQ * Real.sqrt (∑ j, K j ^ 2)) + ‖hhat‖ * Lqh)))
          (C.perturb (ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat))
      ∧ (∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin n → ℝ → Ω → ℝ) (Z : Fin n → ℝ → Ω → Fin d → ℝ)
          (U : Fin n → ℝ → Ω → E → ℝ), Solution D h𝒢₀ hind₀ T
            (C.perturb (ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat)) ξ₀ X Y Z U)
      ∧ ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin n → ℝ → Ω → ℝ)
        (Z₁ Z₂ : Fin n → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin n → ℝ → Ω → E → ℝ),
        Solution D h𝒢₀ hind₀ T
          (C.perturb (ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat)) ξ₀ X₁ Y₁ Z₁ U₁ →
        Solution D h𝒢₀ hind₀ T
          (C.perturb (ex54Pert ν n d J ε q qb qh Q φ μ₀ Λ₀ w₀ w₁ v₀ hhat)) ξ₀ X₂ Y₂ Z₂ U₂ →
        (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
          ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
          ∧ (∀ k j, LevyStochCalc.Brownian.Ito.energy P T
              (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
          ∧ ∀ k, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
              (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0

/-- Example 5.4, the affine cylindrical term. For `ν` σ-finite on a countably generated space,
features `φ_j : L²(ν; ℝᵐ) → ℝ` Lipschitz, and `Q` affine on the attained range of the feature
vector, `Q(s) = a + ∑_j c_j s_j` at every `s = (∫ φ_j dμ^U)_j`, `μ ∈ P₂(H)`: the `Q`-term is the
expectation functional `Q((∫ φ_j dμ^U)_j) = ∫_H (a + ∑_j c_j φ_j(u')) μ(dθ')` of Example 5.3. -/
def ex_fulllaw_affineQ : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d J : ℕ)
    (Q : EuclideanSpace ℝ (Fin J) → ℝ) (φ : Fin J → Lp (EuclideanSpace ℝ (Fin m)) 2 ν → ℝ)
    (K : Fin J → ℝ) (a : ℝ) (c : Fin J → ℝ),
    (∀ j u u', |φ j u - φ j u'| ≤ K j * ‖u - u'‖) →
    (∀ μ : P2 (TupleH ν n m d), Q (WithLp.toLp 2 fun j => ∫ u, φ j u ∂μ.margU.law)
      = a + ∑ j, c j * ∫ u, φ j u ∂μ.margU.law) →
    ∀ μ : P2 (TupleH ν n m d), Q (WithLp.toLp 2 fun j => ∫ u, φ j u ∂μ.margU.law)
      = ∫ θ', (a + ∑ j, c j * φ j θ'.2.2.2) ∂μ.law

/-- Example 5.4, the radial statistic of the full law is no expectation functional. For `ν`
σ-finite on a countably generated space, `n ≥ 1`, a bounded Lipschitz profile `𝔮` not constant on
`[0, ∞)` and a reference law `μ₀ ∈ P₂(H)`: no `φ : H → ℝ` integrable against every law of
finite second moment has `𝔮(W₂(μ, μ₀)) = ∫_H φ dμ` for every `μ ∈ P₂(H)`. -/
def ex_fulllaw_beyond_radial : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d : ℕ), 0 < n →
    ∀ (q : ℝ → ℝ) (Lq B : ℝ), (∀ r r', |q r - q r'| ≤ Lq * |r - r'|) → (∀ r, |q r| ≤ B) →
    (∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ q a ≠ q b) →
    ∀ (μ₀ : P2 (TupleH ν n m d)) (φ : TupleH ν n m d → ℝ),
      (∀ μ : P2 (TupleH ν n m d), Integrable φ μ.law) →
      ∃ μ : P2 (TupleH ν n m d), q (w2H μ μ₀) ≠ ∫ θ, φ θ ∂μ.law

/-- Example 5.4, the radial statistic of the `U`-marginal is no expectation functional, as
printed (every σ-finite `ν`). For `ν` σ-finite on a countably generated space, `m ≥ 1`, a bounded
Lipschitz profile `𝔮̃` not constant on `[0, ∞)` and a reference law `Λ₀ ∈ P₂(L²(ν; ℝᵐ))`: no
`φ : H → ℝ` integrable against every law of finite second moment has
`𝔮̃(W₂(μ^U, Λ₀)) = ∫_H φ dμ` for every `μ ∈ P₂(H)`. -/
def ex_fulllaw_beyond_U : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d : ℕ), 0 < m →
    ∀ (q : ℝ → ℝ) (Lq B : ℝ), (∀ r r', |q r - q r'| ≤ Lq * |r - r'|) → (∀ r, |q r| ≤ B) →
    (∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ q a ≠ q b) →
    ∀ (Λ₀ : P2 (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)) (φ : TupleH ν n m d → ℝ),
      (∀ μ : P2 (TupleH ν n m d), Integrable φ μ.law) →
      ∃ μ : P2 (TupleH ν n m d), q (w2P μ.margU Λ₀) ≠ ∫ θ, φ θ ∂μ.law

/-- Example 5.4, the radial statistic of the `U`-marginal is no expectation functional, corrected:
as `ex_fulllaw_beyond_U` with the fibre `L²(ν; ℝᵐ)` not reduced to `0` (for `m ≥ 1`, `ν ≠ 0`). -/
def ex_fulllaw_beyond_U_corr : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d : ℕ),
    (∃ u : Lp (EuclideanSpace ℝ (Fin m)) 2 ν, u ≠ 0) →
    ∀ (q : ℝ → ℝ) (Lq B : ℝ), (∀ r r', |q r - q r'| ≤ Lq * |r - r'|) → (∀ r, |q r| ≤ B) →
    (∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ q a ≠ q b) →
    ∀ (Λ₀ : P2 (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)) (φ : TupleH ν n m d → ℝ),
      (∀ μ : P2 (TupleH ν n m d), Integrable φ μ.law) →
      ∃ μ : P2 (TupleH ν n m d), q (w2P μ.margU Λ₀) ≠ ∫ θ, φ θ ∂μ.law

/-- Example 5.4, the cylindrical term is no expectation functional when `Q` is not affine on the
attained range of the feature vector. For `ν` σ-finite on a countably generated space, bounded
Lipschitz features `φ_j` and `Q : ℝᴶ → ℝ` Lipschitz, if no `a, c` have
`Q(s) = a + ∑_j c_j s_j` at every `s = (∫ φ_j dμ^U)_j`, `μ ∈ P₂(H)`, then no `φ' : H → ℝ`
integrable against every law of finite second moment has `Q((∫ φ_j dμ^U)_j) = ∫_H φ' dμ` for
every `μ ∈ P₂(H)`. -/
def ex_fulllaw_beyond_Q : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d J : ℕ)
    (Q : EuclideanSpace ℝ (Fin J) → ℝ) (φ : Fin J → Lp (EuclideanSpace ℝ (Fin m)) 2 ν → ℝ)
    (LQ B : ℝ) (K : Fin J → ℝ), (∀ v v', |Q v - Q v'| ≤ LQ * ‖v - v'‖) →
    (∀ j u u', |φ j u - φ j u'| ≤ K j * ‖u - u'‖) → (∀ j u, |φ j u| ≤ B) →
    (¬ ∃ (a : ℝ) (c : Fin J → ℝ), ∀ μ : P2 (TupleH ν n m d),
      Q (WithLp.toLp 2 fun j => ∫ u, φ j u ∂μ.margU.law)
        = a + ∑ j, c j * ∫ u, φ j u ∂μ.margU.law) →
    ∀ φ' : TupleH ν n m d → ℝ, (∀ μ : P2 (TupleH ν n m d), Integrable φ' μ.law) →
      ∃ μ : P2 (TupleH ν n m d),
        Q (WithLp.toLp 2 fun j => ∫ u, φ j u ∂μ.margU.law) ≠ ∫ θ, φ' θ ∂μ.law

/-- The crowding correction of Example 5.5: for a measure `Λ` on a real Hilbert space `F` and
`u ∈ F`, `A_Λ(u) = ∫_F ∇V(u − v) Λ(dv)` with `∇V(w) = w / √(1 + ‖w‖²)`. -/
noncomputable def ex55Crowd {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] (Λ : Measure F) (u : F) : F :=
  ∫ v, (Real.sqrt (1 + ‖u - v‖ ^ 2))⁻¹ • (u - v) ∂Λ

/-- The coefficients of Example 5.5 (with `n = m = d = 1`): for `β₁, β₂ ∈ ℝ`, `σ_c ∈ ℝ`,
`h_c ∈ L²(ν)`, an exposure profile `h_x ∈ L²(ν)` and `ε ∈ ℝ`, at `θ = (x, y, z, u)` and a law
`μ` with `U`-marginal `μ^U`: `b = −β₁ y`, `σ = σ_c − β₁ z`,
`h = h_c + h_x x − β₁ u − ε A_{μ^U}(u)`, `f = β₂ x + ⟨h_x, u⟩_{L²(ν)}` and `g(x, ρ) = x`, with
`(h_x x)(e) = h_x(e) x` and `⟨h_x, u⟩_{L²(ν)} = ∫_E h_x(e) u(e) ν(de)`. -/
noncomputable def ex55Coeffs {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (β₁ β₂ : ℝ) (σc : EuclideanSpace ℝ (Fin 1 × Fin 1))
    (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) (hx : Lp ℝ 2 ν) (ε : ℝ) : Coeffs ν 1 1 1 where
  b _ θ _ := -(β₁ • θ.2.1)
  σ _ θ _ := σc - β₁ • θ.2.2.1
  h _ θ μ := hc + exposureOp hx θ.1 - β₁ • θ.2.2.2 - ε • ex55Crowd μ.margU.law θ.2.2.2
  f _ θ _ := β₂ • θ.1 + ∫ e, hx e • θ.2.2.2 e ∂ν
  g x _ := x

/-- Example 5.5, the potential. On `L²(ν)`, `V(w) = √(1 + ‖w‖²) − 1` is even and convex, with
gradient `∇V(w) = w / √(1 + ‖w‖²)`, `‖∇V(w)‖ ≤ 1` and `‖∇V(w) − ∇V(w')‖ ≤ ‖w − w'‖`. -/
def ex_dealer_potential : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E),
    let V : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν → ℝ := fun w => Real.sqrt (1 + ‖w‖ ^ 2) - 1
    let gradV : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν → Lp (EuclideanSpace ℝ (Fin 1)) 2 ν :=
      fun w => (Real.sqrt (1 + ‖w‖ ^ 2))⁻¹ • w
    (∀ w, V (-w) = V w) ∧ ConvexOn ℝ Set.univ V ∧ (∀ w, HasGradientAt V (gradV w) w)
      ∧ (∀ w, ‖gradV w‖ ≤ 1) ∧ ∀ w w', ‖gradV w - gradV w'‖ ≤ ‖w - w'‖

/-- Example 5.5, the crowding correction is jointly Lipschitz. For `ν` σ-finite on a countably
generated space, `u, u' ∈ L²(ν)` and `λ, λ' ∈ P₂(L²(ν))`,
`‖A_λ(u) − A_λ'(u')‖_{L²(ν)} ≤ ‖u − u'‖_{L²(ν)} + W₂(λ, λ')`. -/
def ex_dealer_crowd : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (Λ Λ' : P2 (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν))
    (u u' : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
    ‖ex55Crowd Λ.law u - ex55Crowd Λ'.law u'‖ ≤ ‖u - u'‖ + w2P Λ Λ'

/-- Example 5.5, the coefficients. For `ν` σ-finite on a countably generated space: at `ε = 0`
and `h_x = 0` the coefficients are those of Example 5.1(i); and for `h_x, u ∈ L²(ν)` the
Hamiltonian term `x ↦ ⟨h_x x, u⟩_{L²(ν)}` has gradient `⟨h_x, u⟩_{L²(ν)}` at every `x ∈ ℝ`. -/
def ex_dealer_coeffs : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E],
    (∀ (β₁ β₂ : ℝ) (σc : EuclideanSpace ℝ (Fin 1 × Fin 1))
      (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
      ex55Coeffs ν β₁ β₂ σc hc 0 0 = affineCoeffs β₁ β₂ σc hc)
    ∧ ∀ (hx : Lp ℝ 2 ν) (u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) (x : EuclideanSpace ℝ (Fin 1)),
      HasGradientAt (fun x' => inner ℝ (exposureOp hx x') u) (∫ e, hx e • u e ∂ν) x

/-- Example 5.5, the assumptions. In the standing setting with `n = m = d = 1`, for `T > 0`,
`β₁, β₂ > 0`, `σ_c ∈ ℝ`, `h_c, h_x ∈ L²(ν)`, `ε ≥ 0` and `ξ₀ ∈ L²(Ω, ℱ₀)`, the coefficients of
Example 5.5 have origin value `h(t, 0, δ₀) = h_c` and satisfy (2.3), Assumption 2.2,
Assumption 2.3 with `L = max{β₁ + ε + ‖h_x‖, β₂ + ‖h_x‖, 1}`, and Assumption 2.4 for `G = 1`
with `c_G = 1`. -/
def ex_dealer : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ →
    ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
      (hx : Lp ℝ 2 ν) (ε : ℝ), 0 ≤ ε →
    ∀ ξ₀ : Ω → EuclideanSpace ℝ (Fin 1),
    StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₀ → MemLp ξ₀ 2 P →
    (∀ t, (ex55Coeffs ν β₁ β₂ σc hc hx ε).h t 0 (P2.dirac 0) = hc)
      ∧ JointBorel T (ex55Coeffs ν β₁ β₂ σc hc hx ε)
      ∧ Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T (ex55Coeffs ν β₁ β₂ σc hc hx ε) ξ₀
      ∧ Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T (max (max (β₁ + ε + ‖hx‖) (β₂ + ‖hx‖)) 1)
          (ex55Coeffs ν β₁ β₂ σc hc hx ε)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ (sMin (1 : Matrix (Fin 1) (Fin 1) ℝ) ^ 2)⁻¹ = 1

/-- Example 5.5, monotonicity at every `ε ≥ 0`. In the setting of `ex_dealer`, for every `t` and
all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`: `𝔼⟨A_{μ^U}(U) − A_{μ'^U}(U'), U − U'⟩_{L²(ν)} ≥ 0`; the exposure
terms cancel, `⟨h_x x, u⟩_{L²(ν)} − ⟨⟨h_x, u⟩_{L²(ν)}, x⟩ = 0` for all `x ∈ ℝ`, `u ∈ L²(ν)`;
`𝔼[∫_E ⟨δh(e), δU(e)⟩ ν(de) + ⟨−δf, δX⟩] ≤ −β₁ 𝔼‖δU‖²_{L²(ν)} − β₂ 𝔼|δX|²`; and Assumption 2.5
holds with `G = 1`, `α = 1` and the constants `β₁, β₂`. -/
def ex_dealer_mono : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ →
    ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
      (hx : Lp ℝ 2 ν) (ε : ℝ), 0 ≤ ε →
    (∀ t, ∀ p ∈ diagonalInputs ν 1 1 1 (enlJoint 𝒢₀ D h𝒢₀) P t,
      ∀ p' ∈ diagonalInputs ν 1 1 1 (enlJoint 𝒢₀ D h𝒢₀) P t,
      0 ≤ ∫ ω, inner ℝ (ex55Crowd p.2.margU.law (p.1 ω).2.2.2
          - ex55Crowd p'.2.margU.law (p'.1 ω).2.2.2) ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2) ∂P)
    ∧ (∀ (x : EuclideanSpace ℝ (Fin 1)) (u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
      inner ℝ (exposureOp hx x) u - inner ℝ (∫ e, hx e • u e ∂ν) x = 0)
    ∧ (∀ t, ∀ p ∈ diagonalInputs ν 1 1 1 (enlJoint 𝒢₀ D h𝒢₀) P t,
      ∀ p' ∈ diagonalInputs ν 1 1 1 (enlJoint 𝒢₀ D h𝒢₀) P t,
      ∫ ω, ((∫ e, inner ℝ ((ex55Coeffs ν β₁ β₂ σc hc hx ε).h t (p.1 ω) p.2 e
            - (ex55Coeffs ν β₁ β₂ σc hc hx ε).h t (p'.1 ω) p'.2 e)
            ((p.1 ω).2.2.2 e - (p'.1 ω).2.2.2 e) ∂ν)
          + inner ℝ (-((ex55Coeffs ν β₁ β₂ σc hc hx ε).f t (p.1 ω) p.2
            - (ex55Coeffs ν β₁ β₂ σc hc hx ε).f t (p'.1 ω) p'.2)) ((p.1 ω).1 - (p'.1 ω).1)) ∂P
        ≤ -β₁ * ∫ ω, ‖(p.1 ω).2.2.2 - (p'.1 ω).2.2.2‖ ^ 2 ∂P
          - β₂ * ∫ ω, ‖(p.1 ω).1 - (p'.1 ω).1‖ ^ 2 ∂P)
    ∧ Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 β₁ β₂
        (ex55Coeffs ν β₁ β₂ σc hc hx ε)

/-- Example 5.5, well-posedness at every `ε ≥ 0`. In the setting of `ex_dealer`, (1.1) with the
coefficients of Example 5.5 and the initial datum `ξ₀` has a solution in `ℍ`, and any two
solutions are equal in `ℍ`: their `X` and their `Y` are indistinguishable on `[0, T]`, and
`𝔼 ∫_0^T |Z¹_t − Z²_t|² dt = 0` and `𝔼 ∫_0^T ‖U¹_t − U²_t‖²_{L²(ν)} dt = 0`. -/
def ex_dealer_wp : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ →
    ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
      (hx : Lp ℝ 2 ν) (ε : ℝ), 0 ≤ ε →
    ∀ ξ₀ : Ω → EuclideanSpace ℝ (Fin 1),
    StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₀ → MemLp ξ₀ 2 P →
    (∃ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U : Fin 1 → ℝ → Ω → E → ℝ),
      Solution D h𝒢₀ hind₀ T (ex55Coeffs ν β₁ β₂ σc hc hx ε) ξ₀ X Y Z U)
    ∧ ∀ (X₁ X₂ : Fin 1 → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin 1 → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U₁ U₂ : Fin 1 → ℝ → Ω → E → ℝ),
      Solution D h𝒢₀ hind₀ T (ex55Coeffs ν β₁ β₂ σc hc hx ε) ξ₀ X₁ Y₁ Z₁ U₁ →
      Solution D h𝒢₀ hind₀ T (ex55Coeffs ν β₁ β₂ σc hc hx ε) ξ₀ X₂ Y₂ Z₂ U₂ →
      (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
        ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
        ∧ (∀ k j, LevyStochCalc.Brownian.Ito.energy P T
            (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
        ∧ ∀ k, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0

/-- Example 5.5, the two-point laws. For `ν` σ-finite on a countably generated space and a unit
`w ∈ L²(ν)`, the laws `λ₁ = ½(δ_{−w} + δ_w)` and `λ₂ = ½(δ_{−2w} + δ_{2w})` have the same mean, and
`A_{λ₁}(w) = (1/√5) w` and `A_{λ₂}(w) = ½ (3/√10 − 1/√2) w`. -/
def ex_dealer_twopoint : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (w : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν), ‖w‖ = 1 →
    let Λ₁ : Measure (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) :=
      (1 / 2 : ℝ≥0∞) • (Measure.dirac (-w) + Measure.dirac w)
    let Λ₂ : Measure (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) :=
      (1 / 2 : ℝ≥0∞) • (Measure.dirac (-((2 : ℝ) • w)) + Measure.dirac ((2 : ℝ) • w))
    (∫ v, v ∂Λ₁ = ∫ v, v ∂Λ₂) ∧ ex55Crowd Λ₁ w = (1 / Real.sqrt 5) • w
      ∧ ex55Crowd Λ₂ w = ((1 / 2 : ℝ) * (3 / Real.sqrt 10 - 1 / Real.sqrt 2)) • w

/-- Example 5.5, the crowding correction is no function of the mean and is nonlinear in the
valuation curve, as printed (every σ-finite `ν`). For `ν` σ-finite on a countably generated space,
there is no `Φ` with `A_λ(u) = Φ(∫ v λ(dv), u)` for every `λ ∈ P₂(L²(ν))` and `u ∈ L²(ν)`; and for
some `λ ∈ P₂(L²(ν))` the map `u ↦ A_λ(u)` is not linear. -/
def ex_dealer_not_mean : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E],
    (¬ ∃ Φ : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν → Lp (EuclideanSpace ℝ (Fin 1)) 2 ν
        → Lp (EuclideanSpace ℝ (Fin 1)) 2 ν,
      ∀ (Λ : P2 (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)) (u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
        ex55Crowd Λ.law u = Φ (∫ v, v ∂Λ.law) u)
    ∧ ∃ Λ : P2 (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν), ¬ IsLinearMap ℝ (ex55Crowd Λ.law)

/-- Example 5.5, the crowding correction is no function of the mean and is nonlinear in the
valuation curve, corrected: as `ex_dealer_not_mean` with `L²(ν)` not reduced to `0` (for
`ν ≠ 0`). -/
def ex_dealer_not_mean_corr : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E],
    (∃ u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν, u ≠ 0) →
    (¬ ∃ Φ : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν → Lp (EuclideanSpace ℝ (Fin 1)) 2 ν
        → Lp (EuclideanSpace ℝ (Fin 1)) 2 ν,
      ∀ (Λ : P2 (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)) (u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
        ex55Crowd Λ.law u = Φ (∫ v, v ∂Λ.law) u)
    ∧ ∃ Λ : P2 (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν), ¬ IsLinearMap ℝ (ex55Crowd Λ.law)

/-- Example 5.5, the crowding correction is affine in the law and an expectation kernel. For `ν`
σ-finite on a countably generated space: for `λ₁, λ₂ ∈ P₂(L²(ν))`, `s ∈ [0, 1]` and `u ∈ L²(ν)`,
`A_{s λ₁ + (1 − s) λ₂}(u) = s A_{λ₁}(u) + (1 − s) A_{λ₂}(u)`; for `μ ∈ P₂(H)` and `u ∈ L²(ν)`,
`A_{μ^U}(u) = ∫_H 𝐇(u, u') μ(dθ')` with `θ' = (x', y', z', u')` and `𝐇(u, u') = ∇V(u − u')`;
and `‖∇V(u₁ − u₁') − ∇V(u₂ − u₂')‖ ≤ |θ₁ − θ₂|_H + |θ₁' − θ₂'|_H` at all points of `H`: the
kernel of Example 5.3 with `K = L²(ν)`. -/
def ex_dealer_affine : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E],
    (∀ (Λ₁ Λ₂ : P2 (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν,
      ex55Crowd (ENNReal.ofReal s • Λ₁.law + ENNReal.ofReal (1 - s) • Λ₂.law) u
        = s • ex55Crowd Λ₁.law u + (1 - s) • ex55Crowd Λ₂.law u)
    ∧ (∀ (μ : P2 (TupleH ν 1 1 1)) (u : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν),
      ex55Crowd μ.margU.law u
        = ∫ θ', (Real.sqrt (1 + ‖u - θ'.2.2.2‖ ^ 2))⁻¹ • (u - θ'.2.2.2) ∂μ.law)
    ∧ ∀ θ₁ θ₁' θ₂ θ₂' : TupleH ν 1 1 1,
      ‖(Real.sqrt (1 + ‖θ₁.2.2.2 - θ₁'.2.2.2‖ ^ 2))⁻¹ • (θ₁.2.2.2 - θ₁'.2.2.2)
          - (Real.sqrt (1 + ‖θ₂.2.2.2 - θ₂'.2.2.2‖ ^ 2))⁻¹ • (θ₂.2.2.2 - θ₂'.2.2.2)‖
        ≤ ‖toL2 θ₁ - toL2 θ₂‖ + ‖toL2 θ₁' - toL2 θ₂'‖

/-- Example 5.5, the mark measure. On `E = {−1, +1} × (0, 1]`, for `c_{±1} > 0` and `0 < ϱ < 2`,
the measure `ν(dς, dq) = c_ς q^{−1−ϱ} dq` (counting measure on the sides) has `ν(E) = ∞` and
`∫_E q² ν(dς, dq) < ∞`, and `h_c(ς, q) = ς q` lies in `L²(ν)`. -/
def ex_dealer_marks : Prop :=
  ∀ (c : Bool → ℝ), (∀ b, 0 < c b) → ∀ ϱ : ℝ, 0 < ϱ → ϱ < 2 →
    let ν : Measure (Bool × Set.Ioc (0 : ℝ) 1) :=
      (Measure.count.prod (Measure.comap Subtype.val volume)).withDensity fun e =>
        ENNReal.ofReal (c e.1 * (e.2 : ℝ) ^ (-1 - ϱ))
    ν Set.univ = ∞ ∧ ∫⁻ e, ENNReal.ofReal ((e.2 : ℝ) ^ 2) ∂ν < ∞
      ∧ MemLp (fun e : Bool × Set.Ioc (0 : ℝ) 1 => (if e.1 then 1 else -1) * (e.2 : ℝ)) 2 ν

/-- Example 5.5, the interaction is inert without the exposure term. In the standing setting with
`n = m = d = 1`, for `T > 0`, `β₁, β₂ > 0`, `σ_c ∈ ℝ`, `h_c ∈ L²(ν)` and `ξ₀ ∈ L²(Ω, ℱ₀)`: some
`p` is positive on `[0, T]`, with `p' = β₁ p² − β₂` there (derivatives within `[0, T]`) and
`p(T) = 1`, and agrees on `[0, T]` with every such function; and, with
`Z_t = p(t) σ_c / (1 + β₁ p(t))` on `[0, T]` and `U_t = p(t) h_c / (1 + β₁ p(t))` on `(0, T]`
(both `0` elsewhere), there are `X`, `Y` with `Y_t = p(t) X_t` on `[0, T]` almost surely such
that, for every `ε ≥ 0`, `(X, Y, Z, U)` solves (1.1) in `ℍ` with the coefficients of Example 5.5
at `h_x = 0` and initial datum `ξ₀`; and for almost every `t ∈ [0, T]` the `U`-marginal of the
law of `Θ⁻_t = (X_{t−}, Y_{t−}, Z_t, U_t)` is the Dirac mass at `p(t) h_c / (1 + β₁ p(t))`, and
`A_{(Law Θ⁻_t)^U}(U_t) = 0` at every sample point. -/
def ex_dealer_inert : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ →
    ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
      (ξ₀ : Ω → EuclideanSpace ℝ (Fin 1)),
    StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₀ → MemLp ξ₀ 2 P →
    ∃ p : ℝ → ℝ,
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        0 < p t ∧ HasDerivWithinAt p (β₁ * p t ^ 2 - β₂) (Set.Icc 0 T) t) ∧ p T = 1
      ∧ (∀ q : ℝ → ℝ, (∀ t ∈ Set.Icc (0 : ℝ) T,
          0 < q t ∧ HasDerivWithinAt q (β₁ * q t ^ 2 - β₂) (Set.Icc 0 T) t) → q T = 1 →
        Set.EqOn q p (Set.Icc 0 T))
      ∧ let Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ := fun k t _ j =>
          (Set.Icc (0 : ℝ) T).indicator (fun s => p s / (1 + β₁ * p s)) t * σc.ofLp (k, j)
        let U : Fin 1 → ℝ → Ω → E → ℝ := fun k t _ e =>
          (Set.Ioc (0 : ℝ) T).indicator (fun s => p s / (1 + β₁ * p s)) t * (hc e).ofLp k
        ∃ X Y : Fin 1 → ℝ → Ω → ℝ,
          (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y k t ω = p t * X k t ω)
          ∧ (∀ ε : ℝ, 0 ≤ ε →
            Solution D h𝒢₀ hind₀ T (ex55Coeffs ν β₁ β₂ σc hc 0 ε) ξ₀ X Y Z U)
          ∧ ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
            (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U t)).margU.law
                = Measure.dirac
                  ((Set.Ioc (0 : ℝ) T).indicator (fun s => p s / (1 + β₁ * p s)) t • hc)
            ∧ ∀ ω, ex55Crowd (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U t)).margU.law
                (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U t ω).2.2.2 = 0

/-- Example 5.5, the data of the active case. On the mark space of the example with
`c_{±1} = (2 − ϱ)/2`, `0 < ϱ < 2`, the profiles `h_c(ς, q) = ς q` (in `L²(ν; ℝ¹)`) and
`h_x(ς, q) = q` (in `L²(ν)`) have `‖h_c‖ = ‖h_x‖ = 1` and `⟨h_x, h_c⟩_{L²(ν)} = 0`. -/
def ex_dealer_active_data : Prop :=
  ∀ ϱ : ℝ, 0 < ϱ → ϱ < 2 →
    ∀ (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ))
      (hx : Lp ℝ 2 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ)),
    (hc : DealerMark → EuclideanSpace ℝ (Fin 1)) =ᵐ[dealerMarks (fun _ => (2 - ϱ) / 2) ϱ]
      (fun e => WithLp.toLp 2 fun _ : Fin 1 => (if e.1 then 1 else -1) * (e.2 : ℝ)) →
    (hx : DealerMark → ℝ) =ᵐ[dealerMarks (fun _ => (2 - ϱ) / 2) ϱ] (fun e => (e.2 : ℝ)) →
    ‖hc‖ = 1 ∧ ‖hx‖ = 1 ∧ ∫ e, hx e • hc e ∂(dealerMarks (fun _ => (2 - ϱ) / 2) ϱ) = 0

/-- Example 5.5, the exposure equation. On the mark space of the example with
`c_{±1} = (2 − ϱ)/2`, `0 < ϱ < 2`, a Lévy driver `D` with one Brownian coordinate, over the
filtration of the standing setting and for `T > 0`, the linear equation
`X_t = ∫_0^t (−X_s ds + ½ dW_s) + ½ ∫_0^t ∫_E (ς q + q X_s) Ñ(ds, dς, dq)` has a solution with
`𝔼 sup_{t ≤ T} |X_t|² < ∞`, and any two solutions are indistinguishable on `[0, T]`. -/
def ex_dealer_active_sde : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ϱ : ℝ), 0 < ϱ → ϱ < 2 →
    ∀ (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ))
      (h𝒢₀ : 𝒢₀ ≤ mΩ) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    let Sol : (ℝ → Ω → ℝ) → Prop := fun X =>
      LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
        (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (fun _ => 0)
        (fun ω s => (Set.Icc (0 : ℝ) T).indicator (fun s => -X s ω) s) X
        (fun s _ _ => (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) s)
        (fun s ω e => (Set.Icc (0 : ℝ) T).indicator
          (fun s => ((if e.1 then 1 else -1) * (e.2 : ℝ) + (e.2 : ℝ) * X s ω) / 2) s)
    (∃ X, Sol X ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖X t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
      ∧ ∀ X X', Sol X → Sol X' → ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X t ω = X' t ω

/-- Example 5.5, the solution at `ε = 0` in the active case. In the setting of
`ex_dealer_active_sde`, with `β₁ = 1`, `β₂ = ½`, `σ_c = 1`, `h_c(ς, q) = ς q`, `h_x(ς, q) = q` and
`ξ₀ = 0`: (1.1) with the coefficients of Example 5.5 at `ε = 0` has a solution
`(X, Y, Z, U)` in `ℍ` with `Y = X` on `[0, T]` almost surely, `Z = ½` and
`U_t(ς, q) = ½ (ς q + q X_{t−})` in energy on `[0, T]`, and `X` indistinguishable on `[0, T]` from
every solution of the exposure equation. -/
def ex_dealer_active_sol : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ϱ : ℝ), 0 < ϱ → ϱ < 2 →
    ∀ (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ))
      (h𝒢₀ : 𝒢₀ ≤ mΩ) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ))
      (hx : Lp ℝ 2 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ)),
    (hc : DealerMark → EuclideanSpace ℝ (Fin 1)) =ᵐ[dealerMarks (fun _ => (2 - ϱ) / 2) ϱ]
      (fun e => WithLp.toLp 2 fun _ : Fin 1 => (if e.1 then 1 else -1) * (e.2 : ℝ)) →
    (hx : DealerMark → ℝ) =ᵐ[dealerMarks (fun _ => (2 - ϱ) / 2) ϱ] (fun e => (e.2 : ℝ)) →
    ∃ (X Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U : Fin 1 → ℝ → Ω → DealerMark → ℝ),
      Solution D h𝒢₀ hind₀ T (ex55Coeffs (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ) 1 (1 / 2)
          (WithLp.toLp 2 fun _ => 1) hc hx 0) (fun _ => 0) X Y Z U
      ∧ (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y 0 t ω = X 0 t ω)
      ∧ LevyStochCalc.Brownian.Ito.energy P T
          (fun ω s => Z 0 s ω 0 - (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) s) = 0
      ∧ LevyStochCalc.Poisson.Compensated.markedEnergy P (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ) T
          (fun ω s e => U 0 s ω e - (Set.Icc (0 : ℝ) T).indicator
            (fun s => ((if e.1 then 1 else -1) * (e.2 : ℝ) + (e.2 : ℝ) * leftLimProc X 0 s ω) / 2)
            s) = 0
      ∧ ∀ X₀ : ℝ → Ω → ℝ,
        LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
          (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (fun _ => 0)
          (fun ω s => (Set.Icc (0 : ℝ) T).indicator (fun s => -X₀ s ω) s) X₀
          (fun s _ _ => (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) s)
          (fun s ω e => (Set.Icc (0 : ℝ) T).indicator
            (fun s => ((if e.1 then 1 else -1) * (e.2 : ℝ) + (e.2 : ℝ) * X₀ s ω) / 2) s) →
        ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X 0 t ω = X₀ t ω

/-- Example 5.5, the moments of the active case. In the setting of `ex_dealer_active_sol`, for a
solution `X` of the exposure equation and `U_t = ½ (h_c + h_x X_t) ∈ L²(ν; ℝ¹)`: for
`t ∈ [0, T]`, `𝔼 X_t = 0`; `v(t) = 𝔼|X_t|²` has `v'(t) = −(7/4) v(t) + ½` (derivative within
`[0, T]`); `𝔼‖U_t − 𝔼 U_t‖² = ¼ v(t) = (1/14)(1 − e^{−7t/4})`; and for `t ∈ (0, T]`, `Law(U_t)` is
no Dirac mass and `A_{Law(U_t)}(U_t) = 0` fails with positive probability. -/
def ex_dealer_active_moments : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ϱ : ℝ), 0 < ϱ → ϱ < 2 →
    ∀ (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ))
      (h𝒢₀ : 𝒢₀ ≤ mΩ) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ))
      (hx : Lp ℝ 2 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ)),
    (hc : DealerMark → EuclideanSpace ℝ (Fin 1)) =ᵐ[dealerMarks (fun _ => (2 - ϱ) / 2) ϱ]
      (fun e => WithLp.toLp 2 fun _ : Fin 1 => (if e.1 then 1 else -1) * (e.2 : ℝ)) →
    (hx : DealerMark → ℝ) =ᵐ[dealerMarks (fun _ => (2 - ϱ) / 2) ϱ] (fun e => (e.2 : ℝ)) →
    ∀ X : ℝ → Ω → ℝ,
    LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (fun _ => 0)
      (fun ω s => (Set.Icc (0 : ℝ) T).indicator (fun s => -X s ω) s) X
      (fun s _ _ => (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) s)
      (fun s ω e => (Set.Icc (0 : ℝ) T).indicator
        (fun s => ((if e.1 then 1 else -1) * (e.2 : ℝ) + (e.2 : ℝ) * X s ω) / 2) s) →
    let U : ℝ → Ω → Lp (EuclideanSpace ℝ (Fin 1)) 2 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ) :=
      fun t ω => (1 / 2 : ℝ) • (hc + exposureOp hx (WithLp.toLp 2 fun _ : Fin 1 => X t ω))
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ ω, X t ω ∂P = 0
      ∧ HasDerivWithinAt (fun s => ∫ ω, X s ω ^ 2 ∂P) (-(7 / 4) * ∫ ω, X t ω ^ 2 ∂P + 1 / 2)
          (Set.Icc 0 T) t
      ∧ ∫ ω, ‖U t ω - ∫ ω', U t ω' ∂P‖ ^ 2 ∂P = 1 / 4 * ∫ ω, X t ω ^ 2 ∂P
      ∧ 1 / 4 * ∫ ω, X t ω ^ 2 ∂P = 1 / 14 * (1 - Real.exp (-(7 / 4) * t)))
    ∧ ∀ t ∈ Set.Ioc (0 : ℝ) T,
      (∀ a, P.map (U t) ≠ Measure.dirac a)
      ∧ ¬ ∀ᵐ ω ∂P, ex55Crowd (P.map (U t)) (U t ω) = 0

/-- Example 5.5, the crowding pairing of a law. For `ν` σ-finite on a countably generated space
and `λ ∈ P₂(L²(ν))`,
`∫ ⟨A_λ(u), u⟩ λ(du) = ½ ∬ ‖u − v‖² / √(1 + ‖u − v‖²) λ(du) λ(dv)`, positive unless `λ` is a
Dirac mass. -/
def ex_dealer_sym : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (Λ : P2 (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)),
    (∫ u, inner ℝ (ex55Crowd Λ.law u) u ∂Λ.law
      = 1 / 2 * ∫ z : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν × Lp (EuclideanSpace ℝ (Fin 1)) 2 ν,
          ‖z.1 - z.2‖ ^ 2 / Real.sqrt (1 + ‖z.1 - z.2‖ ^ 2) ∂(Λ.law.prod Λ.law))
    ∧ ((∀ a, Λ.law ≠ Measure.dirac a) → 0 < ∫ u, inner ℝ (ex55Crowd Λ.law u) u ∂Λ.law)

/-- Example 5.5, the interaction is active. In the setting of `ex_dealer_active_sol`, for every
`ε > 0` and every solution `(X, Y, Z, U)` in `ℍ` of (1.1) at `ε` with `ξ₀ = 0`,
`𝔼 ∫_0^T ‖ε A_{μ⁻_t^U}(U_t)‖²_{L²(ν)} dt > 0`, with `μ⁻_t` the law of
`Θ⁻_t = (X_{t−}, Y_{t−}, Z_t, U_t)` (whose `U`-marginal is the law of `U_t`). -/
def ex_dealer_active_pos : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ϱ : ℝ), 0 < ϱ → ϱ < 2 →
    ∀ (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ))
      (h𝒢₀ : 𝒢₀ ≤ mΩ) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ))
      (hx : Lp ℝ 2 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ)),
    (hc : DealerMark → EuclideanSpace ℝ (Fin 1)) =ᵐ[dealerMarks (fun _ => (2 - ϱ) / 2) ϱ]
      (fun e => WithLp.toLp 2 fun _ : Fin 1 => (if e.1 then 1 else -1) * (e.2 : ℝ)) →
    (hx : DealerMark → ℝ) =ᵐ[dealerMarks (fun _ => (2 - ϱ) / 2) ϱ] (fun e => (e.2 : ℝ)) →
    ∀ ε : ℝ, 0 < ε →
    ∀ (X Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U : Fin 1 → ℝ → Ω → DealerMark → ℝ),
      Solution D h𝒢₀ hind₀ T (ex55Coeffs (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ) 1 (1 / 2)
          (WithLp.toLp 2 fun _ => 1) hc hx ε) (fun _ => 0) X Y Z U →
      0 < ∫ ω, (∫ s in Set.Icc (0 : ℝ) T,
        ‖ε • ex55Crowd
          (lawP2 P (tupleAt (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ) (leftLimProc X)
            (leftLimProc Y) Z U s)).margU.law
          (tupleAt (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ) (leftLimProc X) (leftLimProc Y) Z U s
            ω).2.2.2‖ ^ 2) ∂P

/-- Example 5.5, the solution depends on the interaction strength. In the setting of
`ex_dealer_active_sol`, for `0 ≤ ε ≠ ε' ≥ 0` no `(X, Y, Z, U)` solves (1.1) in `ℍ` with `ξ₀ = 0`
both at `ε` and at `ε'`. -/
def ex_dealer_active_dep : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ϱ : ℝ), 0 < ϱ → ϱ < 2 →
    ∀ (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ))
      (h𝒢₀ : 𝒢₀ ≤ mΩ) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ))
      (hx : Lp ℝ 2 (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ)),
    (hc : DealerMark → EuclideanSpace ℝ (Fin 1)) =ᵐ[dealerMarks (fun _ => (2 - ϱ) / 2) ϱ]
      (fun e => WithLp.toLp 2 fun _ : Fin 1 => (if e.1 then 1 else -1) * (e.2 : ℝ)) →
    (hx : DealerMark → ℝ) =ᵐ[dealerMarks (fun _ => (2 - ϱ) / 2) ϱ] (fun e => (e.2 : ℝ)) →
    ∀ ε ε' : ℝ, 0 ≤ ε → 0 ≤ ε' → ε ≠ ε' →
    ∀ (X Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U : Fin 1 → ℝ → Ω → DealerMark → ℝ),
      Solution D h𝒢₀ hind₀ T (ex55Coeffs (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ) 1 (1 / 2)
          (WithLp.toLp 2 fun _ => 1) hc hx ε) (fun _ => 0) X Y Z U →
      ¬ Solution D h𝒢₀ hind₀ T (ex55Coeffs (dealerMarks (fun _ => (2 - ϱ) / 2) ϱ) 1 (1 / 2)
          (WithLp.toLp 2 fun _ => 1) hc hx ε') (fun _ => 0) X Y Z U

end Dissertation.PaperSpec.A
