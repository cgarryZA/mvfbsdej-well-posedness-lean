/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Existence.DriftShift
import MVFBSDEJ.WellPosedness.Existence.ForwardZero
import MVFBSDEJ.WellPosedness.System.CrossEval

/-!
# Well-posedness of the `λ = 0` system: existence

At `λ = 0` the `λ`-forced system (4.1) decouples: its forward equation is the Itô process
`X_t = ξ₀ + ∫_0^t q^b + ∫_0^t q^σ dW + ∫_0^t ∫_E q^h dÑ`, and its backward equation is, in each
coordinate, the linear backward equation with jumps with terminal value `q^g_T` and drift `q^f`.
Both are solved for every forcing: the forward one over a right-continuous filtration, the
backward one over a filtration with the terminal representation property. The solution
predicate `SolvesForced` asks in addition, even at `λ = 0`, for a representative `γ` of the jump
coefficient `e ↦ h(s, Θ_s, e, μ_s)` along the solution. The paper derives such a
representative, and the progressive measurability of all coefficient processes along a tuple
of `𝕊` — its (2.5) — from the joint Borel measurability of the coefficients and Lemma A.1.
Here that measurability is the hypothesis `CoeffRegular`, which `CoeffBorel.coeffRegular`
derives from the joint measurability (2.3) of the coefficients with the evaluation σ-algebra on
`P₂(H)`.

A progressive tuple `ProgTuple` is a family `(X, Y, Z, U)` with `X, Y` adapted with
right-continuous paths and `Z, U` progressively measurable (marked, for `U`), jointly
measurable and of finite energy on `[0, T]`: the regularity of the tuple of a solution of the
linear equations, before any coupling. `CoeffRegular` says that along every progressive tuple
the coefficient processes are jointly and progressively measurable, with a jointly measurable,
marked progressively measurable representative of the jump coefficient (`CrossEval`).

## Main definitions

* `ProgTuple` — a progressive tuple.
* `CoeffRegular` — (2.5) along every progressive tuple.

## Main statements

* `ProgTuple.of_legs`, `SolvesForced.progTuple` — the tuple of solutions of the linear
  equations, or of the `λ`-forced system, is progressive.
* `ProgTuple.measurable_X`, `ProgTuple.measurable_Y`, `ProgTuple.stronglyMeasurable_tupleAt`,
  `ProgTuple.ae_memLp_tupleAt`, `ProgTuple.lintegral_coords_eq` — the measurability and square
  integrability of a progressive tuple.
* `exists_solvesForced_zero` — for every forcing and every square-integrable
  `ℱ_0`-measurable initial datum, the `λ = 0` system has a solution.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.System

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-- **A progressive tuple** `(X, Y, Z, U)` over the filtration `ℱ` on the horizon `[0, T]`: each
coordinate of `X` and `Y` is adapted with right-continuous paths, and each coordinate of `Z` and
`U` is jointly measurable, progressively measurable (marked progressively measurable, for `U`)
and of finite energy on `[0, T]`. -/
structure ProgTuple (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) (ν : Measure E)
    (T : ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ) : Prop where
  /-- Each coordinate of `X` is adapted. -/
  X_adapted : ∀ i, Adapted ℱ (X i)
  /-- Every path of each coordinate of `X` is right-continuous. -/
  X_rightCont : ∀ i ω t, Tendsto (fun s => X i s ω) (𝓝[>] t) (𝓝 (X i t ω))
  /-- Each coordinate of `Y` is adapted. -/
  Y_adapted : ∀ k, Adapted ℱ (Y k)
  /-- Every path of each coordinate of `Y` is right-continuous. -/
  Y_rightCont : ∀ k ω t, Tendsto (fun s => Y k s ω) (𝓝[>] t) (𝓝 (Y k t ω))
  /-- Each coordinate of `Z` is jointly measurable. -/
  Z_meas : ∀ k j, Measurable (Function.uncurry fun ω s => Z k s ω j)
  /-- Each coordinate of `Z` is progressively measurable. -/
  Z_prog : ∀ k j, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => Z k s ω j
  /-- Each coordinate of `Z` has finite energy on the horizon. -/
  Z_sq : ∀ k j, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z k s ω j) ≠ ⊤
  /-- Each coordinate of `U` is jointly measurable in the sample point, the time and the mark. -/
  U_meas : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2
  /-- Each coordinate of `U` is marked progressively measurable. -/
  U_prog : ∀ k,
    LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U k s ω e
  /-- Each coordinate of `U` has finite marked energy on the horizon. -/
  U_sq : ∀ k,
    LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) ≠ ⊤

/-- **(2.5) along every progressive tuple**: for every progressive tuple `(X, Y, Z, U)` the
drift, diffusion and driver processes of `C` along it are jointly and progressively measurable,
and the jump coefficient `e ↦ h(s, Θ_s, e, μ_s)` has a jointly measurable, marked progressively
measurable representative in `L²(ν)`. The paper derives this from the joint Borel measurability
of the coefficients and Lemma A.1; `CoeffBorel.coeffRegular` derives it from the joint
measurability (2.3) with the evaluation σ-algebra on `P₂(H)`. -/
def CoeffRegular (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ) (C : Coeffs ν n m d) : Prop :=
  ∀ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
    (U : Fin m → ℝ → Ω → E → ℝ), ProgTuple ℱ P ν T X Y Z U →
    ∃ γ : Fin n → ℝ → Ω → E → ℝ, CrossEval ℱ P T C X Y Z U γ

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

omit [MeasurableSpace.CountablyGenerated E] in
/-- **The tuple of solutions of the linear equations is progressive**: if each coordinate of `X`
solves a linear forward equation and each coordinate of `(Y, Z, U)` a linear backward equation
over `ℱ`, then `(X, Y, Z, U)` is a progressive tuple. -/
theorem ProgTuple.of_legs {x₀ : Fin n → Ω → ℝ} {b : Fin n → Ω → ℝ → ℝ}
    {σ : Fin n → ℝ → Ω → Fin d → ℝ} {h : Fin n → ℝ → Ω → E → ℝ} {ξ : Fin m → Ω → ℝ}
    {φ : Fin m → Ω → ℝ → ℝ}
    (hX : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (x₀ i) (b i) (X i) (σ i) (h i))
    (hY : ∀ k, LinearBSDEJ D ℱ hℱW hℱN T (ξ k) (φ k) (Y k) (Z k) (U k)) :
    ProgTuple ℱ P ν T X Y Z U where
  X_adapted i := (hX i).X_adapted
  X_rightCont i := (hX i).X_rightCont
  Y_adapted k := (hY k).Y_adapted
  Y_rightCont k := (hY k).Y_rightCont
  Z_meas k := (hY k).Z_meas
  Z_prog k := (hY k).Z_prog
  Z_sq k := (hY k).Z_sq
  U_meas k := (hY k).U_meas
  U_prog k := (hY k).U_prog
  U_sq k := (hY k).U_sq

/-- The tuple of a solution of the `λ`-forced system is progressive. -/
theorem _root_.MVFBSDEJ.WellPosedness.System.SolvesForced.progTuple
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ) :
    ProgTuple ℱ P ν T X Y Z U :=
  ProgTuple.of_legs h.fwd h.bwd

namespace ProgTuple

variable (hΘ : ProgTuple ℱ P ν T X Y Z U)
include hΘ

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] [IsProbabilityMeasure P] in
/-- Each coordinate of `X` of a progressive tuple is jointly measurable. -/
theorem measurable_X (i : Fin n) : Measurable (Function.uncurry fun ω s => X i s ω) :=
  (LevyStochCalc.Probability.measurable_uncurry_of_rightContinuous (hΘ.X_adapted i)
    (hΘ.X_rightCont i)).comp measurable_swap

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] [IsProbabilityMeasure P] in
/-- Each coordinate of `Y` of a progressive tuple is jointly measurable. -/
theorem measurable_Y (k : Fin m) : Measurable (Function.uncurry fun ω s => Y k s ω) :=
  (LevyStochCalc.Probability.measurable_uncurry_of_rightContinuous (hΘ.Y_adapted k)
    (hΘ.Y_rightCont k)).comp measurable_swap

omit [IsProbabilityMeasure P] in
/-- The tuple `Θ_s` of a progressive tuple is strongly `ℱ_s`-measurable. -/
theorem stronglyMeasurable_tupleAt (s : ℝ) : StronglyMeasurable[ℱ s] (tupleAt ν X Y Z U s) :=
  stronglyMeasurable_tupleAt_of (mΩ := ℱ s) (fun i => hΘ.X_adapted i s)
    (fun k => hΘ.Y_adapted k s) (fun k j => (hΘ.Z_prog k j).stronglyMeasurable_eval s)
    (stronglyMeasurable_uLift_of_markedProgressive hΘ.U_prog s)

/-- **The tuple of a progressive tuple is square integrable at almost every time** of `[0, T]`
when the coordinates of `X` and `Y` have finite energy on `[0, T]`. -/
theorem ae_memLp_tupleAt
    (hXe : ∀ i, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => X i s ω) ≠ ⊤)
    (hYe : ∀ k, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Y k s ω) ≠ ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (tupleAt ν X Y Z U s) 2 P :=
  MVFBSDEJ.WellPosedness.System.ae_memLp_tupleAt
    (fun s _ => ((hΘ.stronglyMeasurable_tupleAt s).mono (ℱ.le s)).aestronglyMeasurable)
    hΘ.measurable_X hΘ.measurable_Y hΘ.Z_meas hΘ.U_meas hXe hYe hΘ.Z_sq hΘ.U_sq

omit [MeasurableSpace.CountablyGenerated E] [IsProbabilityMeasure P] in
/-- The expected sum of the squared coordinates of a progressive tuple at a time is the sum of
its sample energies there. -/
theorem lintegral_coords_eq (s : ℝ) :
    ∫⁻ ω, (∑ i, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ k, (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2
        + ∑ k, ∑ j, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P
      = sampleEnergy P (fun i ω s => X i s ω) s
        + (sampleEnergy P (fun k ω s => Y k s ω) s
          + ∑ k, sampleEnergy P (fun j ω s => Z k s ω j) s
          + markedSampleEnergy P ν (fun k ω s e => U k s ω e) s) := by
  have mX : ∀ i, Measurable fun ω => (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 := fun i =>
    ((hΘ.X_adapted i s).mono (ℱ.le s) le_rfl).nnnorm.coe_nnreal_ennreal.pow_const 2
  have mY : ∀ k, Measurable fun ω => (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2 := fun k =>
    ((hΘ.Y_adapted k s).mono (ℱ.le s) le_rfl).nnnorm.coe_nnreal_ennreal.pow_const 2
  have mZ : ∀ k j, Measurable fun ω => (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 := fun k j =>
    (((hΘ.Z_meas k j).comp (measurable_id.prodMk measurable_const)).nnnorm.coe_nnreal_ennreal
      |>.pow_const 2)
  have mU : ∀ k, Measurable fun ω => ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := fun k =>
    (measurable_uncurry_lintegral_sq_mark (φ := fun ω s e => U k s ω e) (hΘ.U_meas k)).comp
      (measurable_id.prodMk measurable_const)
  have sX : Measurable fun ω => ∑ i, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => mX i
  have sXY : Measurable fun ω => ∑ i, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ k, (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2 :=
    sX.add (Finset.measurable_sum _ fun k _ => mY k)
  have sXYZ : Measurable fun ω => ∑ i, (‖X i s ω‖₊ : ℝ≥0∞) ^ 2
      + ∑ k, (‖Y k s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ k, ∑ j, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 :=
    sXY.add (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun j _ => mZ k j)
  rw [lintegral_add_left sXYZ, lintegral_add_left sXY, lintegral_add_left sX,
    lintegral_finsetSum _ fun i _ => mX i, lintegral_finsetSum _ fun k _ => mY k,
    lintegral_finsetSum _ fun k _ => Finset.measurable_sum _ fun j _ => mZ k j,
    lintegral_finsetSum _ fun k _ => mU k]
  simp only [lintegral_finsetSum _ fun j _ => mZ _ j, sampleEnergy, markedSampleEnergy]
  ring

end ProgTuple

/-- **The `λ = 0` system has a solution for every forcing**: over a right-continuous filtration
carrying the driver, whose right-continuation is constant before `0`, whose time-`0` field
contains the null sets and which has the terminal representation property at the horizon
`T ≥ 0`, for coefficients with (2.5) along every progressive tuple, every forcing `q` and every
square-integrable `ℱ_0`-measurable initial datum `ξ₀`, the `λ = 0` forced system (4.1) has a
solution. -/
theorem exists_solvesForced_zero [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hrep : HasTerminalRep D ℱ hℱW hℱN T) (hT : 0 ≤ T) (hreg : CoeffRegular ℱ P T C)
    (hξ : ∀ i, MemLp (ξ₀ i) 2 P) (hξm : ∀ i, Measurable[ℱ 0] (ξ₀ i))
    (hF : Forcing ℱ P ν T qb qσ qh qf qg) :
    ∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
      (U : Fin m → ℝ → Ω → E → ℝ) (γ : Fin n → ℝ → Ω → E → ℝ),
      SolvesForced D ℱ hℱW hℱN T 0 C ξ₀ qb qσ qh qf qg X Y Z U γ := by
  obtain ⟨X, hX⟩ := hF.exists_linearFSDEJ (D := D) (hℱW := hℱW) (hℱN := hℱN) hℱ0 hnull hT hξ hξm
  obtain ⟨Y, Z, U, hY⟩ := hrep.exists_linearBSDEJ_forcing hnull hT hF
  obtain ⟨γ, hγ⟩ := hreg X Y Z U (ProgTuple.of_legs hX hY)
  exact ⟨X, Y, Z, U, γ,
    { forcing := hF
      jump_rep := hγ.jump_rep
      fwd := fun i => by simpa only [zero_mul, zero_add] using hX i
      bwd := fun k => by simpa only [zero_mul, zero_add] using hY k }⟩

end MVFBSDEJ.WellPosedness.Existence
