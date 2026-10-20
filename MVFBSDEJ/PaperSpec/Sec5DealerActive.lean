/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec5Dealer

/-!
# Example 5.5 of the well-posedness paper: the interaction is active

Statement and equation numbers refer to the well-posedness paper at `1f67672`, in the standing
setting of §2 with `n = m = d = 1` and `G = 1`, for the coefficients `ex55Coeffs` of Example 5.5.
Without the exposure term the crowding correction vanishes along the solution; in the explicit
specialisation `β₁ = 1`, `β₂ = 1/2`, `σ_c = 1`, `ξ₀ = 0`, `c_{±1} = (2 − ϱ)/2`, `h_c(ς, q) = ς q`,
`h_x(ς, q) = q` it is active at every interaction strength `ε > 0`.

## Main definitions

* `MVFBSDEJ.PaperSpec.ex55Marks` — the mark measure of the specialisation.
* `MVFBSDEJ.PaperSpec.ex55Linear` — the linear equation of the specialisation.
* `MVFBSDEJ.PaperSpec.ex_dealer_riccati` — the Riccati function `p`.
* `MVFBSDEJ.PaperSpec.ex_dealer_inert` — for `h_x = 0` the interaction is inert.
* `MVFBSDEJ.PaperSpec.ex_dealer_spec_marks` — `‖h_c‖ = ‖h_x‖ = 1`, `⟨h_c, h_x⟩ = 0`.
* `MVFBSDEJ.PaperSpec.ex_dealer_zero` — the linear equation, the solution `Θ⁰` at `ε = 0`
  and its moments.
* `MVFBSDEJ.PaperSpec.ex_dealer_symm` — the symmetrised crowding pairing.
* `MVFBSDEJ.PaperSpec.ex_dealer_active` — the crowding correction along the solution.
* `MVFBSDEJ.PaperSpec.ex_dealer_depends` — the solution depends on `ε`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace MVFBSDEJ.PaperSpec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.Law

universe u v w

/-- The mark measure of the specialisation of Example 5.5: on `E = {−1, +1} × (0, 1]`, for
`0 < ϱ < 2`, `ν(dς, dq) = c_ς q^{−1−ϱ} dq` with `c_{±1} = (2 − ϱ)/2` (counting measure on the
sides). -/
noncomputable abbrev ex55Marks (ϱ : ℝ) : Measure DealerMark :=
  dealerMarks (fun _ => (2 - ϱ) / 2) ϱ

/-- The linear equation of the specialisation of Example 5.5, over the usual augmentation of the
filtration of the driver `D` enlarged at time `0` by `𝒢₀`, on `[0, T]`:

`X0_t = ∫_0^t (−X0_s ds + ½ dW_s) + ½ ∫_0^t ∫_E (h_c(e) + h_x(e) X0_{s−}) Ñ(ds, de)`

with `h_c(ς, q) = ς q` and `h_x(ς, q) = q`, almost surely at each `t ∈ [0, T]`, for an adapted
`X0` with right-continuous paths, the drift and diffusion taken on `[0, T]` and the jump integrand
on `(0, T]`. -/
def ex55Linear {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (ϱ : ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (ex55Marks ϱ)) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T : ℝ) (X : ℝ → Ω → ℝ) : Prop :=
  LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (fun _ => 0)
    (fun ω s => (Set.Icc (0 : ℝ) T).indicator (fun s => -X s ω) s) X
    (fun s _ _ => (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) s)
    (fun s ω e => (Set.Ioc (0 : ℝ) T).indicator (fun s => 1 / 2 * ((if e.1 then 1 else -1)
      * (e.2 : ℝ) + (e.2 : ℝ) * leftLimProc (fun _ : Fin 1 => X) 0 s ω)) s)

/-- Example 5.5, the Riccati function. For `β₁, β₂ > 0` and `T > 0`, there is a `p` with
`p' = β₁ p² − β₂` on `[0, T]`, `p(T) = 1` and `p > 0` on `[0, T]`; and any two functions with
`q' = β₁ q² − β₂` on `[0, T]` and `q(T) = 1` agree on `[0, T]`. -/
def ex_dealer_riccati : Prop :=
  ∀ β₁ β₂ T : ℝ, 0 < β₁ → 0 < β₂ → 0 < T →
    (∃ p : ℝ → ℝ, (∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt p (β₁ * p t ^ 2 - β₂) t) ∧ p T = 1
      ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < p t)
    ∧ ∀ p q : ℝ → ℝ, (∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt p (β₁ * p t ^ 2 - β₂) t) → p T = 1 →
      (∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt q (β₁ * q t ^ 2 - β₂) t) → q T = 1 →
      ∀ t ∈ Set.Icc (0 : ℝ) T, p t = q t

/-- Example 5.5, without the exposure term the interaction is inert. In the standing setting with
`n = m = d = 1`, for `T > 0`, `β₁, β₂ > 0`, `σ_c ∈ ℝ`, `h_c ∈ L²(ν)`, `ε ≥ 0`,
`ξ₀ ∈ L²(Ω, ℱ₀)` and `p` with `p' = β₁ p² − β₂` on `[0, T]`, `p(T) = 1`, `p > 0` on `[0, T]`:
(1.1) with the coefficients of Example 5.5 at `h_x = 0` has a solution, and every solution
`(X, Y, Z, U)` has `Y_t = p(t) X_t` almost surely at each `t ∈ [0, T]`,
`Z = p σ_c / (1 + β₁ p)` and `U = p h_c / (1 + β₁ p)` (for `dt ⊗ dP` on `[0, T]`), so that at
almost every `t` the law of `U_t` is the Dirac mass at `p(t) h_c / (1 + β₁ p(t))` and the crowding
correction `A_{Law(U_t)}(U_t)` vanishes almost surely; and `(X, Y, Z, U)` solves (1.1) at every
interaction strength `ε' ≥ 0`. -/
def ex_dealer_inert : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ →
    ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1)) (hc : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)
      (ε : ℝ), 0 ≤ ε →
    ∀ ξ₀ : Ω → EuclideanSpace ℝ (Fin 1),
    StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₀ → MemLp ξ₀ 2 P →
    ∀ p : ℝ → ℝ, (∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt p (β₁ * p t ^ 2 - β₂) t) → p T = 1 →
      (∀ t ∈ Set.Icc (0 : ℝ) T, 0 < p t) →
    (∃ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U : Fin 1 → ℝ → Ω → E → ℝ),
      Solution D h𝒢₀ hind₀ T (ex55Coeffs ν β₁ β₂ σc hc 0 ε) ξ₀ X Y Z U)
    ∧ ∀ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U : Fin 1 → ℝ → Ω → E → ℝ),
      Solution D h𝒢₀ hind₀ T (ex55Coeffs ν β₁ β₂ σc hc 0 ε) ξ₀ X Y Z U →
      (∀ t ∈ Set.Icc (0 : ℝ) T, Y 0 t =ᵐ[P] fun ω => p t * X 0 t ω)
      ∧ LevyStochCalc.Brownian.Ito.energy P T
          (fun ω s => Z 0 s ω 0 - p s * σc (0, 0) / (1 + β₁ * p s)) = 0
      ∧ (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
          uLift ν (fun e k => U k s ω e) = (p s / (1 + β₁ * p s)) • hc)
      ∧ (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
          (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
            = Measure.dirac ((p s / (1 + β₁ * p s)) • hc)
          ∧ ∀ᵐ ω ∂P, ex55Crowd (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
              (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2 = 0)
      ∧ ∀ ε' : ℝ, 0 ≤ ε' → Solution D h𝒢₀ hind₀ T (ex55Coeffs ν β₁ β₂ σc hc 0 ε') ξ₀ X Y Z U

/-- Example 5.5, the specialisation: for `0 < ϱ < 2` and the mark measure `ex55Marks ϱ`,
`h_c(ς, q) = ς q` and `h_x(ς, q) = q` lie in `L²(ν)`, with `‖h_c‖² = ‖h_x‖² = 1` and
`⟨h_c, h_x⟩ = 0`. -/
def ex_dealer_spec_marks : Prop :=
  ∀ ϱ : ℝ, 0 < ϱ → ϱ < 2 →
    MemLp (fun e : Bool × Set.Ioc (0 : ℝ) 1 => (if e.1 then 1 else -1) * (e.2 : ℝ)) 2
        (ex55Marks ϱ)
      ∧ MemLp (fun e : Bool × Set.Ioc (0 : ℝ) 1 => (e.2 : ℝ)) 2 (ex55Marks ϱ)
      ∧ ∫ e, ((if e.1 then 1 else -1) * (e.2 : ℝ)) ^ 2 ∂ex55Marks ϱ = 1
      ∧ ∫ e, (e.2 : ℝ) ^ 2 ∂ex55Marks ϱ = 1
      ∧ ∫ e, (if e.1 then 1 else -1) * (e.2 : ℝ) * e.2 ∂ex55Marks ϱ = 0

/-- Example 5.5, the solution at `ε = 0` in the specialisation. In the standing setting with
`n = m = d = 1`, the mark measure `ex55Marks ϱ` for `0 < ϱ < 2`, `T > 0`, and `h_c, h_x ∈ L²(ν)`
the classes of `ς q` and `q`: the linear equation `ex55Linear` has a solution `X0` with
`𝔼 sup_{t ≤ T} |X0_t|² < ∞` and left limits on `(0, T]` along every path, and any two
solutions are indistinguishable on `[0, T]`; for every solution `X0`, the tuple
`Θ⁰ = (X0, X0, ½, ½ (h_c + h_x X0_{t−}))` (`U⁰` taken on `(0, T]`) solves (1.1) with the
coefficients of Example 5.5 for `β₁ = 1`, `β₂ = ½`, `σ_c = 1`, `ε = 0` and the initial datum
`0`; `𝔼 X0_t = 0` and `v(t) = 𝔼|X0_t|²` has `v(t) = (2/7)(1 − e^{−7t/4})` and
`v' = −(7/4) v + ½` at each `t ∈ (0, T)`; and at each `t ∈ (0, T]`,
`U⁰_t = ½ (h_c + h_x X0_{t−})` has `𝔼‖U⁰_t − 𝔼 U⁰_t‖² = v(t)/4 = (1/14)(1 − e^{−7t/4})` and
its law is not a Dirac mass. -/
def ex_dealer_zero : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (ϱ : ℝ), 0 < ϱ → ϱ < 2 →
    ∀ (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (ex55Marks ϱ)) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 (ex55Marks ϱ),
    (∀ᵐ e ∂ex55Marks ϱ, hc e = EuclideanSpace.single 0 ((if e.1 then 1 else -1) * (e.2 : ℝ))) →
    (∀ᵐ e ∂ex55Marks ϱ, hx e = EuclideanSpace.single 0 (e.2 : ℝ)) →
    (∃ X0 : ℝ → Ω → ℝ, ex55Linear 𝒢₀ ϱ P D h𝒢₀ hind₀ T X0
      ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal (X0 t ω ^ 2)) ∂P < ⊤
      ∧ ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X0 s ω) (nhdsWithin t (Set.Iio t))
          (nhds l))
    ∧ (∀ X₁ X₂ : ℝ → Ω → ℝ, ex55Linear 𝒢₀ ϱ P D h𝒢₀ hind₀ T X₁ →
        ex55Linear 𝒢₀ ϱ P D h𝒢₀ hind₀ T X₂ → ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ t ω = X₂ t ω)
    ∧ ∀ X0 : ℝ → Ω → ℝ, ex55Linear 𝒢₀ ϱ P D h𝒢₀ hind₀ T X0 →
      (∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X0 s ω) (nhdsWithin t (Set.Iio t))
          (nhds l)) →
      let U0 : ℝ → Ω → Lp (EuclideanSpace ℝ (Fin 1)) 2 (ex55Marks ϱ) := fun t ω =>
        (1 / 2 : ℝ) • (hc + leftLimProc (fun _ : Fin 1 => X0) 0 t ω • hx)
      let v : ℝ → ℝ := fun t => ∫ ω, X0 t ω ^ 2 ∂P
      Solution D h𝒢₀ hind₀ T (ex55Coeffs (ex55Marks ϱ) 1 (1 / 2) (EuclideanSpace.single (0, 0) 1)
          hc hx 0) 0 (fun _ => X0) (fun _ => X0)
          (fun _ s _ _ => (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) s)
          (fun _ s ω e => (Set.Ioc (0 : ℝ) T).indicator (fun s => 1 / 2 * ((if e.1 then 1 else -1)
            * (e.2 : ℝ) + (e.2 : ℝ) * leftLimProc (fun _ : Fin 1 => X0) 0 s ω)) s)
      ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, ∫ ω, X0 t ω ∂P = 0)
      ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, v t = 2 / 7 * (1 - Real.exp (-(7 / 4) * t)))
      ∧ (∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt v (-(7 / 4) * v t + 1 / 2) t)
      ∧ ∀ t ∈ Set.Ioc (0 : ℝ) T,
        ∫ ω, ‖U0 t ω - ∫ ω', U0 t ω' ∂P‖ ^ 2 ∂P = v t / 4
        ∧ v t / 4 = 1 / 14 * (1 - Real.exp (-(7 / 4) * t))
        ∧ ¬ ∃ u, P.map (U0 t) = Measure.dirac u

/-- Example 5.5, the symmetrised crowding pairing. For `ν` σ-finite on a countably generated
space and `λ ∈ P₂(L²(ν))`,
`∫ ⟨A_λ(u), u⟩ λ(du) = ½ ∬ ‖u − v‖² / √(1 + ‖u − v‖²) λ(du) λ(dv)`, and the integral is positive
unless `λ` is a Dirac mass. -/
def ex_dealer_symm : Prop :=
  ∀ {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] (Λ : P2 (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν)),
    ∫ u, inner ℝ (ex55Crowd Λ.law u) u ∂Λ.law
        = 1 / 2 * ∫ u, ∫ v, ‖u - v‖ ^ 2 / Real.sqrt (1 + ‖u - v‖ ^ 2) ∂Λ.law ∂Λ.law
      ∧ ((¬ ∃ u, Λ.law = Measure.dirac u) → 0 < ∫ u, inner ℝ (ex55Crowd Λ.law u) u ∂Λ.law)

/-- Example 5.5, the interaction is active in the specialisation. In the setting of
`ex_dealer_zero`, for every solution `X0` of the linear equation with left limits on `(0, T]`
along every path and every `t ∈ (0, T]`, with `U⁰_t = ½ (h_c + h_x X0_{t−})`, the crowding
correction `A_{Law(U⁰_t)}(U⁰_t)` is nonzero with positive probability; and for every `ε > 0` and
every solution `(X, Y, Z, U)` of (1.1) with the coefficients of Example 5.5 for `β₁ = 1`,
`β₂ = ½`, `σ_c = 1`, the strength `ε` and the initial datum `0`,
`𝔼 ∫_0^T ‖ε A_{Law(U_t)}(U_t)‖²_{L²(ν)} dt > 0`. -/
def ex_dealer_active : Prop :=
  haveI : MeasurableSpace.CountablyGenerated DealerMark := inferInstance
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (ϱ : ℝ), 0 < ϱ → ϱ < 2 →
    ∀ (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (ex55Marks ϱ)) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 (ex55Marks ϱ),
    (∀ᵐ e ∂ex55Marks ϱ, hc e = EuclideanSpace.single 0 ((if e.1 then 1 else -1) * (e.2 : ℝ))) →
    (∀ᵐ e ∂ex55Marks ϱ, hx e = EuclideanSpace.single 0 (e.2 : ℝ)) →
    (∀ X0 : ℝ → Ω → ℝ, ex55Linear 𝒢₀ ϱ P D h𝒢₀ hind₀ T X0 →
      (∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X0 s ω) (nhdsWithin t (Set.Iio t))
          (nhds l)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) T,
        let U0 : Ω → Lp (EuclideanSpace ℝ (Fin 1)) 2 (ex55Marks ϱ) := fun ω =>
          (1 / 2 : ℝ) • (hc + leftLimProc (fun _ : Fin 1 => X0) 0 t ω • hx)
        0 < P {ω | ex55Crowd (P.map U0) (U0 ω) ≠ 0})
    ∧ ∀ ε : ℝ, 0 < ε →
      ∀ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
        (U : Fin 1 → ℝ → Ω → DealerMark → ℝ),
      Solution D h𝒢₀ hind₀ T (ex55Coeffs (ex55Marks ϱ) 1 (1 / 2) (EuclideanSpace.single (0, 0) 1)
          hc hx ε) 0 X Y Z U →
      0 < ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ‖ε • ex55Crowd
            (lawP2 P (tupleAt (ex55Marks ϱ) (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
            (tupleAt (ex55Marks ϱ) (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2‖ₑ ^ 2 ∂volume ∂P

/-- Example 5.5, the solution depends on `ε`. In the standing setting with `n = m = d = 1`, for
`T > 0`, `β₁, β₂ > 0`, `σ_c`, `h_c, h_x ∈ L²(ν)`, `ε, ε' ≥ 0` with `ε ≠ ε'` and an initial datum
`ξ₀`: if a tuple solves (1.1) with the coefficients of Example 5.5 at both strengths `ε` and
`ε'`, the crowding correction along it vanishes for `dt ⊗ dP` on `[0, T]`; and in the
specialisation of `ex_dealer_zero`, no tuple solves (1.1) at two strengths `ε ≠ ε'` in
`[0, ∞)`. -/
def ex_dealer_depends : Prop :=
  (∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ (β₁ β₂ : ℝ), 0 < β₁ → 0 < β₂ → ∀ (σc : EuclideanSpace ℝ (Fin 1 × Fin 1))
      (hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) (ε ε' : ℝ), 0 ≤ ε → 0 ≤ ε' → ε ≠ ε' →
    ∀ (ξ₀ : Ω → EuclideanSpace ℝ (Fin 1)) (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ)
      (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U : Fin 1 → ℝ → Ω → E → ℝ),
      Solution D h𝒢₀ hind₀ T (ex55Coeffs ν β₁ β₂ σc hc hx ε) ξ₀ X Y Z U →
      Solution D h𝒢₀ hind₀ T (ex55Coeffs ν β₁ β₂ σc hc hx ε') ξ₀ X Y Z U →
      ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
        ex55Crowd (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
          (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2 = 0)
  ∧ ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (ϱ : ℝ), 0 < ϱ → ϱ < 2 →
    ∀ (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (ex55Marks ϱ)) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P), ∀ T : ℝ, 0 < T →
    ∀ hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 (ex55Marks ϱ),
    (∀ᵐ e ∂ex55Marks ϱ, hc e = EuclideanSpace.single 0 ((if e.1 then 1 else -1) * (e.2 : ℝ))) →
    (∀ᵐ e ∂ex55Marks ϱ, hx e = EuclideanSpace.single 0 (e.2 : ℝ)) →
    ∀ ε ε' : ℝ, 0 ≤ ε → 0 ≤ ε' → ε ≠ ε' →
    ¬ ∃ (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
        (U : Fin 1 → ℝ → Ω → DealerMark → ℝ),
      Solution D h𝒢₀ hind₀ T (ex55Coeffs (ex55Marks ϱ) 1 (1 / 2) (EuclideanSpace.single (0, 0) 1)
          hc hx ε) 0 X Y Z U
        ∧ Solution D h𝒢₀ hind₀ T (ex55Coeffs (ex55Marks ϱ) 1 (1 / 2)
          (EuclideanSpace.single (0, 0) 1) hc hx ε') 0 X Y Z U

end MVFBSDEJ.PaperSpec
