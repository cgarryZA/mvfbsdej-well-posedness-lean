/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Setting
import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Section 2 of the well-posedness paper: the setting

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The setting of §2
is a Lévy driver `D` (a `d`-dimensional Brownian motion and an independent Poisson random measure
with intensity `dt ⊗ ν(de)`, `ν` σ-finite) on `(Ω, P)`, and the usual augmentation `(ℱ_t)` of the
filtration of the driver enlarged at time `0` by a σ-algebra `ℱ₀` independent of it.

## Main definitions

* `MVFBSDEJ.PaperSpec.sec2_separable` — `L²(ν; ℝʲ)` is separable.
* `MVFBSDEJ.PaperSpec.sec2_infinite_activity` — infinitely many atoms on every interval when
  `ν(E) = ∞`.
* `MVFBSDEJ.PaperSpec.eq_compid`, `eq_zeromean`, `eq_fubiniiso` — (2.1), (2.2) and (2.4).
* `MVFBSDEJ.PaperSpec.RepresentsMart` — a predictable pair represents a martingale.
* `MVFBSDEJ.PaperSpec.sec2_prp` — the predictable representation property.
* `MVFBSDEJ.PaperSpec.sec2_hborel` — joint pointwise measurability of `h` gives (2.3).
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace MVFBSDEJ.PaperSpec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Enlarged
  MVFBSDEJ.WellPosedness.Spec

universe u v w

/-- §2, first paragraph: for `ν` σ-finite on a countably generated measurable space `(E, ℰ)`,
`L²(ν; ℝʲ)` is separable for every `j ≥ 1`. -/
def sec2_separable : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (j : ℕ), 1 ≤ j →
    TopologicalSpace.SeparableSpace (Lp (EuclideanSpace ℝ (Fin j)) 2 ν)

/-- §2, first paragraph, the infinite-activity regime: if `ν(E) = ∞`, then almost surely
`N((s, t] × E) = ∞` for all `0 ≤ s < t`, so `N` has infinitely many atoms on every nondegenerate
time interval. -/
def sec2_infinite_activity : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] (d : ℕ)
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν), ν Set.univ = ⊤ →
    ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 ≤ s → s < t → D.N.N ω (Set.Ioc s t ×ˢ Set.univ) = ⊤

/-- (2.1), the compensation formula: in the setting of §2, for `ψ ≥ 0` measurable for the marked
predictable σ-algebra of `(ℱ_t)` and `T ∈ ℝ`,
`𝔼 ∫_0^T ∫_E ψ_s(e) N(ds, de) = 𝔼 ∫_0^T ∫_E ψ_s(e) ν(de) ds ∈ [0, ∞]`, the integral against `N`
taken over `(0, T] × E`. -/
def eq_compid : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] (d : ℕ) (P : Measure Ω)
    [IsProbabilityMeasure P] (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (h𝒢₀ : 𝒢₀ ≤ mΩ), Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ (T : ℝ) (ψ : Ω × ℝ × E → ℝ≥0∞),
    Measurable[LevyStochCalc.Probability.markedPredictableSigma (enlJoint 𝒢₀ D h𝒢₀) ν] ψ →
    ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ, ψ (ω, p) ∂(D.N.N ω) ∂P
      = ∫⁻ ω, (∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ψ (ω, s, e) ∂ν) ∂P

/-- (2.2), the zero mean of the compensated integral: in the setting of §2, for `ψ` measurable for
the marked predictable σ-algebra of `(ℱ_t)` with `𝔼 ∫_0^T ∫_E |ψ_s(e)| ν(de) ds < ∞`,
`𝔼 ∫_0^T ∫_E ψ_s(e) Ñ(ds, de) = 0`, the compensated integral read pathwise as
`∫_{(0, T] × E} ψ dN − ∫_0^T ∫_E ψ_s(e) ν(de) ds`. -/
def eq_zeromean : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] (d : ℕ) (P : Measure Ω)
    [IsProbabilityMeasure P] (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (h𝒢₀ : 𝒢₀ ≤ mΩ), Indep 𝒢₀ (⨆ t, D.filtration t) P → ∀ (T : ℝ) (ψ : Ω × ℝ × E → ℝ),
    Measurable[LevyStochCalc.Probability.markedPredictableSigma (enlJoint 𝒢₀ D h𝒢₀) ν] ψ →
    ∫⁻ ω, (∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ‖ψ (ω, s, e)‖ₑ ∂ν) ∂P < ⊤ →
    ∫ ω, ((∫ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ, ψ (ω, p) ∂(D.N.N ω))
      - ∫ s in Set.Ioc (0 : ℝ) T, ∫ e, ψ (ω, s, e) ∂ν) ∂P = 0

section Rep

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ} {P : Measure Ω}
  [IsProbabilityMeasure P]

open LevyStochCalc in
/-- `(Z, U)` represents `M` on `[0, T]` over the filtration `(ℱ_t)` of §2: `Z` and `U` are
predictable with finite energy and vanish off `[0, T]`, and for every `t ∈ [0, T]`, almost surely
`M_t = M_0 + ∫_0^t Z_s dW_s + ∫_0^t ∫_E U_s(e) Ñ(ds, de)`. -/
def RepresentsMart (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T : ℝ) (M : ℝ → Ω → ℝ)
    (Z : ℝ → Ω → Fin d → ℝ) (U : ℝ → Ω → E → ℝ) : Prop :=
  ∃ (hZ : ∀ j, Probability.Predictable (enlJoint 𝒢₀ D h𝒢₀) fun ω s => Z s ω j)
    (hZv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
    (hZe : ∀ j, Brownian.Ito.energy P T (fun ω s => Z s ω j) ≠ ⊤)
    (hU : Probability.MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) ν fun ω s e => U s ω e)
    (hUv : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0)
    (hUe : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤),
    ∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P] fun ω => M 0 ω
      + Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
          (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) Z
          (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ j))
          (progressivelyMeasurable_of_predictable_of_vanish hZ hZv)
          (BSDEJ.Solves.sq_int_global_of_vanishing hZv hZe) t ω
      + Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
          (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω s e => U s ω e)
          (hU.mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
          hU.markedProgressivelyMeasurable
          (BSDEJ.Solves.marked_sq_int_global_of_vanishing hUv hUe) t ω

end Rep

/-- §2, the Brownian–Poisson predictable representation property, passed to the independent
initial enlargement: for `d ≥ 1` and `T > 0`, every square-integrable `(ℱ_t)`-martingale `M` is
represented on `[0, T]` by a predictable square-integrable pair `(Z, U)`, and any two representing
pairs agree up to null sets (the energies of their differences vanish). -/
def sec2_prp : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] (ν : Measure E) [SigmaFinite ν]
    (d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), 0 < d → ∀ T : ℝ, 0 < T →
    ∀ M : ℝ → Ω → ℝ, Martingale M (enlJoint 𝒢₀ D h𝒢₀) P → (∀ t, MemLp (M t) 2 P) →
      (∃ (Z : ℝ → Ω → Fin d → ℝ) (U : ℝ → Ω → E → ℝ), RepresentsMart D h𝒢₀ hind₀ T M Z U)
      ∧ ∀ (Z Z' : ℝ → Ω → Fin d → ℝ) (U U' : ℝ → Ω → E → ℝ),
        RepresentsMart D h𝒢₀ hind₀ T M Z U → RepresentsMart D h𝒢₀ hind₀ T M Z' U' →
        (∀ j, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω j - Z' s ω j) = 0)
          ∧ LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
              (fun ω s e => U s ω e - U' s ω e) = 0

/-- The paragraph after (2.3): joint pointwise measurability of `(t, θ, e, μ) ↦ h(t, θ, e, μ)` gives
(2.3) for `h`. For a function `H` on `([0, T] × H × P₂(H)) × E`, measurable for the Borel σ-algebra
of `[0, T] × H × P₂(H)` (with `W₂` of the Hilbert norm on `P₂(H)`) times `ℰ`, whose sections in `e`
represent the jump coefficient, `(t, θ, μ) ↦ h(t, θ, ·, μ)` is Borel measurable into
`L²(ν; ℝⁿ)`. -/
def sec2_hborel : Prop :=
  ∀ {E : Type v} [mE : MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d : ℕ) (T : ℝ) (C : Coeffs ν n m d)
    (H : (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d) × E →
      EuclideanSpace ℝ (Fin n)),
    Measurable[(borel (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d)).prod mE] H →
    (∀ p, (C.h p.1 p.2.1 p.2.2.toP2 : E → EuclideanSpace ℝ (Fin n)) =ᵐ[ν] fun e => H (p, e)) →
    Measurable[borel (Set.Icc (0 : ℝ) T × TupleH ν n m d × TupleP2WH ν n m d),
      borel (Lp (EuclideanSpace ℝ (Fin n)) 2 ν)] fun p => C.h p.1 p.2.1 p.2.2.toP2

/-- (2.4), the Fubini isometry: for `μ` σ-finite on a measurable space `X` (in the paper, the
predictable σ-field on `Ω × [0, T]` with `dt ⊗ dP`) and `ν` σ-finite on a countably generated `E`,
there is a linear isometric equivalence `L²(μ ⊗ ν; ℝʲ) ≃ L²(μ; L²(ν; ℝʲ))` under which the sections
of a function represent its image; every element of `L²(μ; L²(ν; ℝʲ))` has a jointly measurable
representative; and two jointly measurable representatives of the same sections agree
`μ ⊗ ν`-almost everywhere. -/
def eq_fubiniiso : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (j : ℕ),
    (∃ Φ : Lp (EuclideanSpace ℝ (Fin j)) 2 (μ.prod ν) ≃ₗᵢ[ℝ]
        Lp (Lp (EuclideanSpace ℝ (Fin j)) 2 ν) 2 μ,
      ∀ g, ∀ᵐ x ∂μ, (Φ g x : E → EuclideanSpace ℝ (Fin j)) =ᵐ[ν] fun e => g (x, e))
    ∧ (∀ u : Lp (Lp (EuclideanSpace ℝ (Fin j)) 2 ν) 2 μ,
        ∃ g : X × E → EuclideanSpace ℝ (Fin j), Measurable g
          ∧ ∀ᵐ x ∂μ, (u x : E → EuclideanSpace ℝ (Fin j)) =ᵐ[ν] fun e => g (x, e))
    ∧ ∀ (u : Lp (Lp (EuclideanSpace ℝ (Fin j)) 2 ν) 2 μ)
      (g g' : X × E → EuclideanSpace ℝ (Fin j)), Measurable g → Measurable g' →
      (∀ᵐ x ∂μ, (u x : E → EuclideanSpace ℝ (Fin j)) =ᵐ[ν] fun e => g (x, e)) →
      (∀ᵐ x ∂μ, (u x : E → EuclideanSpace ℝ (Fin j)) =ᵐ[ν] fun e => g' (x, e)) →
      g =ᵐ[μ.prod ν] g'

end MVFBSDEJ.PaperSpec
