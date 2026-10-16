/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.Dealer.ExposureSDE
import Dissertation.WellPosedness.Examples.Dealer.ExposureWellPosed

/-!
# Example 5.5: an explicit solution at `ε = 0`

On the dealer mark space with `c_{±1} = (2 − ϱ)/2`, `ϱ < 2`, take `n = d = 1`, `β₁ = 1`,
`β₂ = ½`, `σ_c = 1`, `h_c(ς, q) = ς q` and `h_x(ς, q) = q`, so that
`‖h_c‖_{L²(ν)} = ‖h_x‖_{L²(ν)} = 1` and `⟨h_x, h_c⟩_{L²(ν)} = 0`: the exposure-sensitive dealer
system `activeDealerCoeffs c hϱ ε` of Example 5.5 of the well-posedness paper in which the
interaction is active. Let `X⁰` solve the exposure equation

`X⁰_t = ∫_0^t (−X⁰_s ds + ½ dW_s) + ½ ∫_0^t ∫_E (ς q + q X⁰_s) Ñ(ds, dς, dq)`,   `X⁰_0 = 0`.

Then the tuple

`Y⁰ = X⁰`,   `Z⁰ = ½`,   `U⁰_t = ½ (h_c + h_x X⁰_t)`

solves the system at `ε = 0`. Along it `b = −Y⁰ = −X⁰`, `σ = σ_c − Z⁰ = ½`,
`h = h_c + h_x X⁰ − U⁰ = U⁰`, and, by orthonormality,

`f = ½ X⁰ + ⟨h_x, U⁰⟩_{L²(ν)} = ½ X⁰ + ½ ⟨h_x, h_c⟩_{L²(ν)} + ½ ‖h_x‖² X⁰ = X⁰`,

so the forward equation is the exposure equation and the backward equation for `Y⁰` is the
exposure equation read backward from `Y⁰_T = X⁰_T = g(X⁰_T)`.

The jump channel is evaluated at `X⁰_t`, as in `Solves`, rather than at `X⁰_{t−}`: the two agree
off a countable set of times on almost every path, and the tuple is a solution in the sense of the
paper after passing to predictable versions of `(Z⁰, U⁰)`, equal to them almost everywhere. By
Theorem 3.3, over `enlJoint 𝒢₀ D h𝒢₀`, every solution in `ℍ²_weak` at `ε = 0` with initial datum
`0` coincides with this tuple, and the exposure equation has a unique solution.

## Main definitions

* `unitVol` — the volatility `σ_c = 1 ∈ ℝ^{1×1}`.
* `activeDealerCoeffs` — the exposure-sensitive dealer system with `β₁ = 1`, `β₂ = ½`,
  `σ_c = 1`, `h_c(ς, q) = ς q`, `h_x(ς, q) = q`.

## Main statements

* `uLift_exposureJump` — `U⁰_t = ½ (h_c + h_x X⁰_t)` in `L²(ν; ℝ¹)`.
* `exposurePair_half_smul_dealerJump_add` — `⟨h_x, ½ (h_c + h_x x)⟩_{L²(ν)} = ½ x`.
* `driftProc_activeDealer`, `diffusionProc_activeDealer`, `driverProc_activeDealer`,
  `terminalVal_activeDealer`, `jumpCoeff_activeDealer_zero` — the coefficients along the tuple.
* `solves_activeDealer` — the tuple solves the system at `ε = 0` over any filtration carrying
  the driver over which `X⁰` solves the exposure equation.
* `exists_paperSolutionEnl_activeDealer` — over `enlJoint 𝒢₀ D h𝒢₀`, `X⁰` exists, the tuple
  solves the system at `ε = 0`, and, with predictable versions of `(Z⁰, U⁰)`, it is a solution in
  the sense of the paper.
* `paperWeakSolutionInt_activeDealer_eq` — every solution in `ℍ²_weak` at `ε = 0` over
  `enlJoint 𝒢₀ D h𝒢₀` coincides with the tuple.
* `linearFSDEJ_exposure_unique_enlJoint` — the exposure equation has at most one solution over
  `enlJoint 𝒢₀ D h𝒢₀`, up to indistinguishability on `[0, T]`.
-/

open MeasureTheory Filter ProbabilityTheory Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System Dissertation.WellPosedness.Enlarged LevyStochCalc

universe u w

/-! ### The coefficients -/

/-- The volatility `σ_c = 1 ∈ ℝ^{1×1}`. -/
noncomputable def unitVol : EuclideanSpace ℝ (Fin 1 × Fin 1) :=
  WithLp.toLp 2 fun _ => 1

/-- The exposure-sensitive dealer system of Example 5.5 in which the interaction is active: on the
dealer mark space, with `n = d = 1`, `β₁ = 1`, `β₂ = ½`, `σ_c = 1`, `h_c(ς, q) = ς q` and
`h_x(ς, q) = q`, at interaction strength `ε`. -/
noncomputable abbrev activeDealerCoeffs (c : Bool → ℝ) {ϱ : ℝ} (hϱ : ϱ < 2) (ε : ℝ) :
    Coeffs (dealerMarks c ϱ) 1 1 1 :=
  dealerExpCoeffs 1 (1 / 2) unitVol (dealerJump c hϱ) (dealerSize c hϱ) ε

variable {c : Bool → ℝ} {ϱ : ℝ}

/-- The vector `½ (ς q + q x) ∈ ℝ¹` is `½ (ς q e₀ + q x)`. -/
theorem toLp_half_signedSize_add (e : DealerMark) (x : ℝ) :
    (WithLp.toLp 2 (fun _ : Fin 1 => (signedSize e + (e.2 : ℝ) * x) / 2) :
        EuclideanSpace ℝ (Fin 1))
      = (1 / 2 : ℝ) • (PiLp.single 2 (0 : Fin 1) (signedSize e)
        + (e.2 : ℝ) • (WithLp.toLp 2 fun _ : Fin 1 => x : EuclideanSpace ℝ (Fin 1))) := by
  ext i
  rw [Subsingleton.elim i 0]
  simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.single_apply, smul_eq_mul, if_true]
  ring

/-- **The exposure pairing of half the jump coefficient**: with `c_{±1} = (2 − ϱ)/2`,
`⟨h_x, ½ (h_c + h_x x)⟩_{L²(ν)} = ½ x` for every `x ∈ ℝ¹`. -/
theorem exposurePair_half_smul_dealerJump_add (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2)
    (x : EuclideanSpace ℝ (Fin 1)) :
    exposurePair (dealerSize c hϱ)
        ((1 / 2 : ℝ) • (dealerJump c hϱ + exposureOp (dealerSize c hϱ) x))
      = (1 / 2 : ℝ) • x := by
  rw [map_smul, map_add, exposurePair_dealerSize_dealerJump_eq_zero hϱ hc,
    exposurePair_exposureOp, norm_dealerSize_eq_one hϱ hc, one_pow, one_smul, zero_add]

/-! ### The jump channel of the tuple -/

section Channel

variable {Ω : Type u} {T : ℝ}

/-- On `[0, T]`, the jump integrand `½ (ς q + q X_s)` represents `½ (h_c + h_x X_s)`. -/
theorem exposureJump_ae_eq (hϱ : ϱ < 2) (X : ℝ → Ω → ℝ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ω : Ω) :
    (fun e => (WithLp.toLp 2 fun _ : Fin 1 => exposureJump T X s ω e :
        EuclideanSpace ℝ (Fin 1)))
      =ᵐ[dealerMarks c ϱ] ⇑((1 / 2 : ℝ) • (dealerJump c hϱ
        + exposureOp (dealerSize c hϱ) (WithLp.toLp 2 fun _ : Fin 1 => X s ω))) := by
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (dealerJump c hϱ
      + exposureOp (dealerSize c hϱ) (WithLp.toLp 2 fun _ : Fin 1 => X s ω)),
    coeFn_dealerJump_add_exposureOp hϱ (WithLp.toLp 2 fun _ : Fin 1 => X s ω)] with e h1 h2
  rw [h1, Pi.smul_apply, h2]
  simp only [exposureJump, Set.indicator_of_mem hs]
  exact toLp_half_signedSize_add e (X s ω)

/-- On `[0, T]`, the jump integrand `½ (ς q + q X_s)` is square integrable over the marks. -/
theorem memLp_exposureJump (hϱ : ϱ < 2) (X : ℝ → Ω → ℝ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ω : Ω) :
    MemLp (fun e => (WithLp.toLp 2 fun _ : Fin 1 => exposureJump T X s ω e :
      EuclideanSpace ℝ (Fin 1))) 2 (dealerMarks c ϱ) :=
  (Lp.memLp _).ae_eq (exposureJump_ae_eq hϱ X hs ω).symm

/-- **The jump channel of the tuple**: on `[0, T]`, the class of `U⁰_s = ½ (ς q + q X_s)` in
`L²(ν; ℝ¹)` is `½ (h_c + h_x X_s)`. -/
theorem uLift_exposureJump (hϱ : ϱ < 2) (X : ℝ → Ω → ℝ) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T) (ω : Ω) :
    uLift (dealerMarks c ϱ) (fun e (_ : Fin 1) => exposureJump T X s ω e)
      = (1 / 2 : ℝ) • (dealerJump c hϱ
        + exposureOp (dealerSize c hϱ) (WithLp.toLp 2 fun _ : Fin 1 => X s ω)) := by
  rw [uLift_of_memLp (memLp_exposureJump hϱ X hs ω),
    MemLp.toLp_congr _ (Lp.memLp _) (exposureJump_ae_eq hϱ X hs ω), Lp.toLp_coeFn]

end Channel

/-! ### The coefficients along the tuple -/

section Along

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}

/-- **The drift along the tuple** is `−X_s` on `[0, T]`, at every interaction strength. -/
theorem driftProc_activeDealer (hϱ : ϱ < 2) (ε : ℝ) (X : ℝ → Ω → ℝ) (i : Fin 1) :
    driftProc P T (activeDealerCoeffs c hϱ ε) (fun _ => X) (fun _ => X)
        (fun _ => exposureDiffusion Ω T) (fun _ => exposureJump T X) i
      = exposureDrift T X := by
  funext ω s
  simp only [driftProc, exposureDrift]
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    simp [Coeffs.perturb, affineCoeffs, crowdPert, exposurePert, tupleAt]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]

/-- **The diffusion along the tuple** is `σ_c − Z⁰_s = ½` on `[0, T]`, at every interaction
strength. -/
theorem diffusionProc_activeDealer (hϱ : ϱ < 2) (ε : ℝ) (X : ℝ → Ω → ℝ) (i : Fin 1) :
    diffusionProc P T (activeDealerCoeffs c hϱ ε) (fun _ => X) (fun _ => X)
        (fun _ => exposureDiffusion Ω T) (fun _ => exposureJump T X) i
      = exposureDiffusion Ω T := by
  funext s ω j
  simp only [diffusionProc, exposureDiffusion]
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    simp [Coeffs.perturb, affineCoeffs, crowdPert, exposurePert, tupleAt, unitVol,
      exposureDiffusion, Set.indicator_of_mem hs]
    norm_num
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]

/-- The jump process of the representative `U⁰` is `U⁰`. -/
theorem jumpProc_exposureJump (X : ℝ → Ω → ℝ) (i : Fin 1) :
    jumpProc T (fun _ => exposureJump T X) i = exposureJump T X := by
  funext s ω e
  simp only [jumpProc, exposureJump]
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · simp only [Set.indicator_of_mem hs]
  · simp only [Set.indicator_of_notMem hs]

/-- **The terminal value along the tuple** is `g(X_T) = X_T`, at every interaction strength. -/
theorem terminalVal_activeDealer (hϱ : ϱ < 2) (ε : ℝ) (X : ℝ → Ω → ℝ) (k : Fin 1) :
    terminalVal P T (activeDealerCoeffs c hϱ ε) (fun _ => X) k = X T := by
  funext ω
  simp [terminalVal, affineCoeffs]

/-- **The driver along the tuple** is `f = ½ X_s + ⟨h_x, U⁰_s⟩_{L²(ν)} = X_s` on `[0, T]`, at
every interaction strength, with `c_{±1} = (2 − ϱ)/2`. -/
theorem driverProc_activeDealer (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) (ε : ℝ)
    (X : ℝ → Ω → ℝ) (k : Fin 1) :
    driverProc P T (activeDealerCoeffs c hϱ ε) (fun _ => X) (fun _ => X)
        (fun _ => exposureDiffusion Ω T) (fun _ => exposureJump T X) k
      = fun ω s => -exposureDrift T X ω s := by
  funext ω s
  simp only [driverProc, exposureDrift]
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, dealerExpCoeffs_f]
    change ((1 / 2 : ℝ) • (WithLp.toLp 2 fun _ : Fin 1 => X s ω : EuclideanSpace ℝ (Fin 1))
      + exposurePair (dealerSize c hϱ) (uLift (dealerMarks c ϱ)
        (fun e (_ : Fin 1) => exposureJump T X s ω e))) k = _
    rw [uLift_exposureJump hϱ X hs ω, exposurePair_half_smul_dealerJump_add hϱ hc]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, neg_neg]
    ring
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, neg_zero]

/-- **The jump coefficient at `ε = 0` along the tuple** is `h_c + h_x X_s − U⁰_s = U⁰_s` on
`[0, T]`, whatever the law argument. -/
theorem jumpCoeff_activeDealer_zero (hϱ : ϱ < 2) (X : ℝ → Ω → ℝ) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T) (ω : Ω) (μ : P2 (TupleH (dealerMarks c ϱ) 1 1 1)) :
    (activeDealerCoeffs c hϱ 0).h s
        (tupleAt (dealerMarks c ϱ) (fun _ => X) (fun _ => X) (fun _ => exposureDiffusion Ω T)
          (fun _ => exposureJump T X) s ω) μ
      = uLift (dealerMarks c ϱ) (fun e (_ : Fin 1) => exposureJump T X s ω e) := by
  rw [dealerExpCoeffs_h, zero_smul, sub_zero, one_smul]
  change dealerJump c hϱ + exposureOp (dealerSize c hϱ) (WithLp.toLp 2 fun _ : Fin 1 => X s ω)
      - uLift (dealerMarks c ϱ) (fun e (_ : Fin 1) => exposureJump T X s ω e) = _
  rw [uLift_exposureJump hϱ X hs ω]
  module

end Along

/-! ### The tuple solves the system at `ε = 0` -/

section Solution

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}

/-- **The explicit tuple solves the system at `ε = 0`.** With `c_{±1} = (2 − ϱ)/2`, `ϱ < 2` and
`T ≥ 0`, let `X` solve the exposure equation over a filtration `ℱ` carrying a Lévy driver `D`
with one Brownian coordinate and mark measure `ν`. Then `(X, Y, Z, U) = (X, X, ½, U⁰)`, with
`U⁰_s = ½ (ς q + q X_s)` on `[0, T]` as jump channel and as representative of the jump
coefficient, solves (1.1) for `activeDealerCoeffs c hϱ 0` over `ℱ` with initial datum `0`. -/
theorem solves_activeDealer (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) (hT : 0 ≤ T)
    {D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (dealerMarks c ϱ)}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
    {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {X : ℝ → Ω → ℝ}
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) :
    Solves D ℱ hℱW hℱN T (activeDealerCoeffs c hϱ 0) 0 (fun _ => X) (fun _ => X)
      (fun _ => exposureDiffusion Ω T) (fun _ => exposureJump T X)
      (fun _ => exposureJump T X) := by
  refine Solves.of_linear ?_ (fun i => ?_) (fun k => ?_)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    refine Eventually.of_forall fun ω => ?_
    rw [jumpCoeff_activeDealer_zero hϱ X hs ω _, uLift_of_memLp (memLp_exposureJump hϱ X hs ω)]
    exact (MemLp.coeFn_toLp _).symm
  · rw [driftProc_activeDealer, diffusionProc_activeDealer, jumpProc_exposureJump]
    exact hX
  · rw [terminalVal_activeDealer, driverProc_activeDealer hϱ hc]
    exact hX.linearBSDEJ hT

end Solution

/-! ### The initially enlarged filtration -/

section Enlarged

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **Example 5.5 at `ε = 0`: an explicit solution.** Let `ν` be the dealer mark measure with
`c_{±1} = (2 − ϱ)/2`, `ϱ < 2`, `D` a Lévy driver with one Brownian coordinate and mark measure
`ν`, `𝒢₀` a σ-algebra independent of its joint natural filtration, and `T > 0`. Over
`enlJoint 𝒢₀ D h𝒢₀` the exposure equation has a solution `X` starting at `0`; the tuple
`(X, X, ½, U⁰)`, `U⁰_s = ½ (ς q + q X_s)` on `[0, T]`, solves (1.1) for
`activeDealerCoeffs c hϱ 0` with initial datum `0`; and there are `Z`, `U` equal to `½` and `U⁰`
almost everywhere on `Ω × [0, T]` and `Ω × [0, T] × E` such that `(X, X, Z, U)` is a solution in
the sense of the paper, with `U⁰` as the representative of the jump coefficient. -/
theorem exists_paperSolutionEnl_activeDealer
    (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (dealerMarks c ϱ))
    (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P)
    (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) (hT : 0 < T) :
    ∃ X : ℝ → Ω → ℝ,
      LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
          (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (fun _ => 0) (exposureDrift T X) X
          (exposureDiffusion Ω T) (exposureJump T X)
        ∧ SolvesEnl D h𝒢₀ hind₀ T (activeDealerCoeffs c hϱ 0) 0 (fun _ => X) (fun _ => X)
          (fun _ => exposureDiffusion Ω T) (fun _ => exposureJump T X)
          (fun _ => exposureJump T X)
        ∧ ∃ (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U : Fin 1 → ℝ → Ω → DealerMark → ℝ),
          (∀ k j, ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T),
            exposureDiffusion Ω T p.2 p.1 j = Z k p.2 p.1 j)
          ∧ (∀ k, ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P (dealerMarks c ϱ) T),
            exposureJump T X q.2.1 q.1 q.2.2 = U k q.2.1 q.1 q.2.2)
          ∧ PaperSolutionEnl D h𝒢₀ hind₀ T (activeDealerCoeffs c hϱ 0) 0 (fun _ => X)
            (fun _ => X) Z U (fun _ => exposureJump T X) := by
  obtain ⟨X, hX⟩ := exists_linearFSDEJ_exposure_enlJoint D h𝒢₀ hind₀ hϱ hc hT
  have hs := solves_activeDealer hϱ hc hT.le hX
  obtain ⟨Z, U, hZ, hU, hp⟩ := hs.exists_paperSolution (coeffRegular_dealerExp _ P T)
    (crossWitnessEnl D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs hs0 => measurableSet_enlJoint_of_null D h𝒢₀ hs hs0) hT
  exact ⟨X, hX, hs, Z, U, hZ, hU, hp⟩

/-- **Every solution at `ε = 0` is the explicit one.** Under the hypotheses of
`exists_paperSolutionEnl_activeDealer`, let `X` solve the exposure equation over
`enlJoint 𝒢₀ D h𝒢₀` from `0`, and let `(X', Y', Z', U')` be a solution of (1.1) in `ℍ²_weak` over
`enlJoint 𝒢₀ D h𝒢₀` for `activeDealerCoeffs c hϱ 0` with initial datum `0`, in the sense of
`PaperWeakSolutionInt`. Then `X'` and `Y'` are indistinguishable from `X` on `[0, T]`,
`Z' = ½` almost everywhere on `Ω × [0, T]`, and `U' = U⁰`, `U⁰_s = ½ (ς q + q X_s)`, almost
everywhere on `Ω × [0, T] × E`. -/
theorem paperWeakSolutionInt_activeDealer_eq
    (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (dealerMarks c ϱ))
    (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P)
    (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) (hT : 0 < T) {X : ℝ → Ω → ℝ}
    (hX : LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X))
    {X' Y' : Fin 1 → ℝ → Ω → ℝ} {Z' : Fin 1 → ℝ → Ω → Fin 1 → ℝ}
    {U' γ' : Fin 1 → ℝ → Ω → DealerMark → ℝ}
    (h' : PaperWeakSolutionInt D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (activeDealerCoeffs c hϱ 0) 0 X' Y' Z' U'
      γ') :
    (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X t ω = X' 0 t ω)
      ∧ (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X t ω = Y' 0 t ω)
      ∧ (∀ j, ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T),
          exposureDiffusion Ω T p.2 p.1 j = Z' 0 p.2 p.1 j)
      ∧ ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P (dealerMarks c ϱ) T),
          exposureJump T X q.2.1 q.1 q.2.2 = U' 0 q.2.1 q.1 q.2.2 := by
  have hs := solves_activeDealer hϱ hc hT.le hX
  obtain ⟨Zv, Uv, hZv, hUv, hp⟩ := hs.exists_paperSolution (coeffRegular_dealerExp _ P T)
    (crossWitnessEnl D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs hs0 => measurableSet_enlJoint_of_null D h𝒢₀ hs hs0) hT
  have hβ₂ : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨-, -, -, -, hconst, hM, hMT⟩ :=
    dealerExp_assumptions (ℱ := enlJoint 𝒢₀ D h𝒢₀) (P := P) (σc := unitVol)
      (hc := dealerJump c hϱ) (hx := dealerSize c hϱ) T one_pos hβ₂ le_rfl
  obtain ⟨hXu, hYu, hZu, hUu⟩ := PaperWeakSolutionInt.uniqueness (hp.toWeakInt hT.le) h'
    (crossWitnessEnl D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
    (fun _ hs hs0 => measurableSet_enlJoint_of_null D h𝒢₀ hs hs0) hT
    (diagonalLipschitz_dealerExp one_pos.le hβ₂.le le_rfl) terminalLipschitz_dealerExp
    zero_le_one (fun _ => gCoerciveForward_GX_one) (fun _ => gCoerciveBackward_GX_one) hconst hM
    hMT
  refine ⟨hXu 0, hYu 0, fun j => ?_, ?_⟩
  · have h := ae_eq_of_energy_sub_eq_zero
      (Brownian.Ito.measurable_uncurry_of_predictable (hp.Z_pred 0 j))
      (Brownian.Ito.measurable_uncurry_of_predictable (h'.Z_pred 0 j)) (hZu 0 j)
    filter_upwards [hZv 0 j, h] with p h1 h2
    exact h1.trans h2
  · have h := ae_eq_of_markedEnergy_sub_eq_zero
      ((hp.U_pred 0).mono (Probability.markedPredictableSigma_le _ _) le_rfl)
      ((h'.U_pred 0).mono (Probability.markedPredictableSigma_le _ _) le_rfl) (hUu 0)
    filter_upwards [hUv 0, h] with q h1 h2
    exact h1.trans h2

/-- **The exposure equation has a unique solution over the initially enlarged filtration.**
Under the hypotheses of `exists_paperSolutionEnl_activeDealer`, two solutions `X, X'` of the
exposure equation over `enlJoint 𝒢₀ D h𝒢₀` starting at `0` are indistinguishable on `[0, T]`. -/
theorem linearFSDEJ_exposure_unique_enlJoint
    (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (dealerMarks c ϱ))
    (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P)
    (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2) (hT : 0 < T) {X X' : ℝ → Ω → ℝ}
    (hX : LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X))
    (hX' : LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (fun _ => 0) (exposureDrift T X') X'
      (exposureDiffusion Ω T) (exposureJump T X')) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X t ω = X' t ω := by
  have hξ : ∀ i : Fin 1, MemLp ((0 : Fin 1 → Ω → ℝ) i) 2 P := fun _ => memLp_const 0
  have hξm : ∀ i : Fin 1, Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ((0 : Fin 1 → Ω → ℝ) i) :=
    fun _ => measurable_const
  obtain ⟨-, huniq⟩ := exists_solvesEnl_dealerExp_and_uniqueness (σc := unitVol)
    (hc := dealerJump c hϱ) (hx := dealerSize c hϱ) D h𝒢₀ hind₀ one_pos hT one_pos
    (by norm_num : (0 : ℝ) < 1 / 2) le_rfl hξ hξm
  exact (huniq _ _ _ _ _ _ _ _ _ _ (solves_activeDealer hϱ hc hT.le hX)
    (solves_activeDealer hϱ hc hT.le hX')).1 0

end Enlarged

end Dissertation.WellPosedness.Existence
