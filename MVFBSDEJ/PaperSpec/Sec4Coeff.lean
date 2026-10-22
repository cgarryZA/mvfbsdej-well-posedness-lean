/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec3

/-!
# The coefficient bounds (4.2) and (4.3) of the well-posedness paper

Statement and equation numbers refer to the well-posedness paper at `1f67672`. By the Lipschitz
bounds of Assumption 2.3 and the coupling bounds (2.8), (2.9) at the Dirac mass of the origin,
the coefficient processes along a square-integrable tuple are square integrable: (4.2) for the
interior coefficients, (4.3) for the terminal function.

## Main definitions

* `MVFBSDEJ.PaperSpec.eq_coeffint` — (4.2).
* `MVFBSDEJ.PaperSpec.eq_termg` — (4.3).
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace MVFBSDEJ.PaperSpec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.Law

universe u v

/-- **(4.2).** There is a function `K` of the Lipschitz constant such that: on every filtered
probability space, for `ν` σ-finite on a countably generated space, if the interior bound of
Assumption 2.3 holds with the constant `L` and `Θ : [0, T] → L²(Ω; H)` is `ℱ_t`-measurable and
square integrable at almost every `t ∈ [0, T]`, then for each `ψ ∈ {b, σ, h, f}`, in the norms of
Assumption 2.3 and with `μ_s = Law(Θ_s)`,
`𝔼 ∫_0^T |ψ(s, Θ_s, μ_s)|² ds
  ≤ K(L) 𝔼 ∫_0^T (|X_s|² + |Y_s|² + |Z_s|²_F + ‖U_s‖²_{L²(ν)} + |ψ(s, 0, δ_0)|²) ds`,
the integrals read in `[0, ∞]`. -/
def eq_coeffint : Prop :=
  ∃ K : ℝ → ℝ, ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ) (P : Measure Ω)
    [IsProbabilityMeasure P] {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (n m d : ℕ) (T L : ℝ) (C : Coeffs ν n m d),
    LipInterior ℱ P T L C → ∀ Θ : ℝ → Ω → TupleH ν n m d,
    (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      StronglyMeasurable[ℱ t] (Θ t) ∧ MemLp (Θ t) 2 P) →
    (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ω, ‖C.b t (Θ t ω) (lawP2 P (Θ t))‖ₑ ^ 2 ∂P
      ≤ ENNReal.ofReal (K L) * ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ω, (‖(Θ t ω).1‖ₑ ^ 2
        + ‖(Θ t ω).2.1‖ₑ ^ 2 + ‖(Θ t ω).2.2.1‖ₑ ^ 2 + ‖(Θ t ω).2.2.2‖ₑ ^ 2
        + ‖C.b t 0 (P2.dirac 0)‖ₑ ^ 2) ∂P)
    ∧ (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ω, ‖C.σ t (Θ t ω) (lawP2 P (Θ t))‖ₑ ^ 2 ∂P
      ≤ ENNReal.ofReal (K L) * ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ω, (‖(Θ t ω).1‖ₑ ^ 2
        + ‖(Θ t ω).2.1‖ₑ ^ 2 + ‖(Θ t ω).2.2.1‖ₑ ^ 2 + ‖(Θ t ω).2.2.2‖ₑ ^ 2
        + ‖C.σ t 0 (P2.dirac 0)‖ₑ ^ 2) ∂P)
    ∧ (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ω, ‖C.h t (Θ t ω) (lawP2 P (Θ t))‖ₑ ^ 2 ∂P
      ≤ ENNReal.ofReal (K L) * ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ω, (‖(Θ t ω).1‖ₑ ^ 2
        + ‖(Θ t ω).2.1‖ₑ ^ 2 + ‖(Θ t ω).2.2.1‖ₑ ^ 2 + ‖(Θ t ω).2.2.2‖ₑ ^ 2
        + ‖C.h t 0 (P2.dirac 0)‖ₑ ^ 2) ∂P)
    ∧ (∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ω, ‖C.f t (Θ t ω) (lawP2 P (Θ t))‖ₑ ^ 2 ∂P
      ≤ ENNReal.ofReal (K L) * ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ω, (‖(Θ t ω).1‖ₑ ^ 2
        + ‖(Θ t ω).2.1‖ₑ ^ 2 + ‖(Θ t ω).2.2.1‖ₑ ^ 2 + ‖(Θ t ω).2.2.2‖ₑ ^ 2
        + ‖C.f t 0 (P2.dirac 0)‖ₑ ^ 2) ∂P)

/-- **(4.3).** There is a function `K` of the Lipschitz constant such that: on every filtered
probability space, if the terminal function `g` satisfies the terminal bound (2.6) of
Assumption 2.3 with the constant `L` and `X_T` is `ℱ_T`-measurable and square integrable, then
`𝔼 |g(X_T, Law(X_T))|² ≤ K(L) (𝔼 |X_T|² + |g(0, δ_0)|²)`, the integrals read in `[0, ∞]`. -/
def eq_termg : Prop :=
  ∃ K : ℝ → ℝ, ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ mΩ) (P : Measure Ω)
    [IsProbabilityMeasure P] (n m : ℕ) (T L : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → P2 (EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin m)),
    LipTerminal ℱ P T L g → ∀ XT : Ω → EuclideanSpace ℝ (Fin n),
    StronglyMeasurable[ℱ T] XT → MemLp XT 2 P →
    ∫⁻ ω, ‖g (XT ω) (lawP2 P XT)‖ₑ ^ 2 ∂P
      ≤ ENNReal.ofReal (K L) * (∫⁻ ω, ‖XT ω‖ₑ ^ 2 ∂P + ‖g 0 (P2.dirac 0)‖ₑ ^ 2)

end MVFBSDEJ.PaperSpec
