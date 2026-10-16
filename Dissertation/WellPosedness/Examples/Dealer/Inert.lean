/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.Dealer.ExposureInteraction
import Dissertation.WellPosedness.Examples.Dealer.InertSDE
import Dissertation.WellPosedness.Examples.Dealer.Monotone
import Dissertation.WellPosedness.Existence.GlobalEnl
import Dissertation.WellPosedness.Robustness.Corollary
import Dissertation.WellPosedness.System.PaperUniquenessInt
import LevyStochCalc.Driver.GaussianInitial

/-!
# Example 5.5: without the exposure term the interaction is inert

For `h_x = 0` the exposure-sensitive dealer system of Example 5.5 of the well-posedness paper is
the dealer system `dealerCoeffs β₁ β₂ σ_c h_c ε` on `H = ℝⁿ × ℝⁿ × ℝ^{n×d} × L²(ν; ℝⁿ)`,

`b = −β₁ y`, `σ = σ_c − β₁ z`, `h = h_c − β₁ u − ε A_{μ^U}(u)`, `f = β₂ x`, `g(x, ρ) = x`,

with `A_λ(u) = ∫ ∇V(u − v) λ(dv)` the crowding operator and `μ^U` the `U`-marginal of the law.
Let `β₁, β₂ ≥ 0`, let `p` be the positive solution of `p' = β₁ p² − β₂`, `p(T) = 1`, and let `X`
solve the forward equation of `exists_linearFSDEJ_inert`,

`dX = −β₁ p X dt + σ_c / (1 + β₁ p) dW + ∫_E h_c(e) / (1 + β₁ p) Ñ(dt, de)`,   `X_0 = ξ₀`.

Then the tuple

`Y_t = p(t) X_t`,   `Z_t = p(t) σ_c / (1 + β₁ p(t))`,   `U_t = p(t) h_c / (1 + β₁ p(t))`

solves the system at `ε = 0`. Along it `b = −β₁ p X`, `σ = σ_c / (1 + β₁ p)`,
`h = h_c / (1 + β₁ p)` and `f = β₂ X`, so the forward equation is that of `X`; and by the product
rule for the deterministic weight `p`,

`d(p X) = (p' − β₁ p²) X dt + p σ_c / (1 + β₁ p) dW + ∫_E p h_c(e) / (1 + β₁ p) Ñ(dt, de)
  = −β₂ X dt + Z dW + ∫_E U(e) Ñ(dt, de)`,

with `p(T) X_T = X_T = g(X_T)`, which is the backward equation.

The jump channel `U_t` is deterministic, so `Law(U_t)` is the Dirac mass at `U_t` and
`A_{Law(U_t)}(U_t) = ∇V(0) = 0`; for a square-integrable tuple `Law(U_t)` is the `U`-marginal of
its law. The jump coefficients at `ε` and at `0` therefore agree along the tuple, and the same
tuple solves the system for every `ε`. Its integrands `Z`, `U` are deterministic, hence
predictable, so it is a solution in the sense of the paper as it stands.

In the statements the weight is read at the time clamped to `[0, T]`, `Y_t = p(t ∧ T ∨ 0) X_t`,
and `U` is cut to `(0, T]`, so `U_0 = 0`: a change on a null set of times that makes `U`
predictable. Neither a Brownian coordinate nor a sign of `ε` is needed for the tuple to be a
solution.

## Main statements

* `uLift_inertU` — the class of `U_t` in `L²(ν; ℝⁿ)` is `1_{(0, T]}(t) p(t) h_c / (1 + β₁ p(t))`.
* `driftProc_dealer_inert`, `diffusionProc_dealer_inert`, `driverProc_dealer_inert`,
  `terminalVal_dealer_inert`, `dealerCoeffs_zero_h_inert` — the coefficients along the tuple.
* `solves_dealer_inert` — the tuple solves the system at `ε = 0` over any filtration carrying
  the driver over which `X` solves the forward equation.
* `map_uLift_inertU` — `Law(U_t)` is a Dirac mass at every time.
* `margU_lawP2_inertU`, `crowdOp_margU_inertU` — the `U`-marginal of the law of a
  square-integrable tuple with this jump channel is that Dirac mass, and the crowding correction
  vanishes along the tuple at every sample point.
* `ae_crowdOp_dealer_inert`, `ae_crowdOp_leftLim_dealer_inert` — along the tuple and along the
  predictable tuple the crowding correction vanishes at almost every time.
* `solves_dealer_inert_of_crossWitness`, `paperSolution_dealer_inert` — the tuple solves the
  system at every interaction strength, for `Solves` and in the sense of the paper.
* `exists_paperSolutionEnl_dealer_inert` — over `enlJoint 𝒢₀ D h𝒢₀`: `X` exists, the tuple is a
  solution at every `ε`, and the crowding correction vanishes along it.
-/

open MeasureTheory Filter Topology ProbabilityTheory Dissertation.Law
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System Dissertation.WellPosedness.Enlarged LevyStochCalc
  LevyStochCalc.BSDEJ.Solves

universe u v w

/-! ### The coefficients along the tuple -/

section Along

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n d : ℕ} {P : Measure Ω}
  [IsProbabilityMeasure P] {T β₁ β₂ : ℝ} {σc : EuclideanSpace ℝ (Fin n × Fin d)}
  {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] [MeasurableSpace Ω] in
/-- **The jump channel of the tuple is deterministic**: at every time `t` and sample point, the
class of `U_t` in `L²(ν; ℝⁿ)` is `1_{(0, T]}(t) p(t) h_c / (1 + β₁ p(t))`. -/
theorem uLift_inertU (t : ℝ) (ω : Ω) :
    uLift ν (fun e k => inertU Ω β₁ β₂ T hc k t ω e)
      = (Set.Ioc (0 : ℝ) T).indicator (inertGain β₁ β₂ T) t • hc := by
  refine uLift_eq_of_ae_eq ?_
  filter_upwards [Lp.coeFn_smul ((Set.Ioc (0 : ℝ) T).indicator (inertGain β₁ β₂ T) t) hc]
    with e he
  rw [he]
  ext k
  simp [inertU]

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] [MeasurableSpace Ω] in
/-- On `(0, T]` the jump integrand `h_c(e) / (1 + β₁ p(t))` represents `h_c / (1 + β₁ p(t))`. -/
theorem inertJump_ae_eq {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) T) (ω : Ω) :
    (fun e => (WithLp.toLp 2 fun i => inertJump Ω β₁ β₂ T hc i t ω e :
        EuclideanSpace ℝ (Fin n)))
      =ᵐ[ν] ⇑((1 + β₁ * inertP β₁ β₂ T t)⁻¹ • hc) := by
  filter_upwards [Lp.coeFn_smul (1 + β₁ * inertP β₁ β₂ T t)⁻¹ hc] with e he
  rw [he]
  ext i
  simp [inertJump, Set.indicator_of_mem ht]

variable (P) in
/-- **The drift along the tuple** is `b = −β₁ Y_t = −β₁ p(t) X_t` on `[0, T]`, at every
interaction strength. -/
theorem driftProc_dealer_inert (ε : ℝ) (X : Fin n → ℝ → Ω → ℝ) (Z : Fin n → ℝ → Ω → Fin d → ℝ)
    (U : Fin n → ℝ → Ω → E → ℝ) (i : Fin n) :
    driftProc P T (dealerCoeffs β₁ β₂ σc hc ε) X
        (fun k t ω => inertP β₁ β₂ T (clampTime T t) * X k t ω) Z U i
      = inertDrift β₁ β₂ T X i := by
  funext ω s
  simp only [driftProc, inertDrift]
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    simp [Coeffs.perturb, affineCoeffs, crowdPert, tupleAt, clampTime_of_mem hs]
    ring
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]

variable (P) in
/-- **The diffusion along the tuple** is `σ = σ_c − β₁ Z_t = σ_c / (1 + β₁ p(t))` on `[0, T]`,
at every interaction strength. -/
theorem diffusionProc_dealer_inert (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (ε : ℝ)
    (X Y : Fin n → ℝ → Ω → ℝ) (U : Fin n → ℝ → Ω → E → ℝ) (i : Fin n) :
    diffusionProc P T (dealerCoeffs β₁ β₂ σc hc ε) X Y (inertZ Ω β₁ β₂ T σc) U i
      = inertDiffusion Ω β₁ β₂ T σc i := by
  funext s ω j
  simp only [diffusionProc, inertDiffusion]
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    have h1 := (one_add_mul_inertP_pos hβ₁ hβ₂ hs.2).ne'
    simp [Coeffs.perturb, affineCoeffs, crowdPert, tupleAt, inertZ, inertGain,
      Set.indicator_of_mem hs]
    field_simp
    ring
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, zero_mul]

variable (P) in
/-- **The driver along the tuple** is `f = β₂ X_t` on `[0, T]`, at every interaction strength. -/
theorem driverProc_dealer_inert (ε : ℝ) (X Y : Fin n → ℝ → Ω → ℝ)
    (Z : Fin n → ℝ → Ω → Fin d → ℝ) (U : Fin n → ℝ → Ω → E → ℝ) (k : Fin n) :
    driverProc P T (dealerCoeffs β₁ β₂ σc hc ε) X Y Z U k
      = fun ω s => (Set.Icc (0 : ℝ) T).indicator (fun s => β₂ * X k s ω) s := by
  funext ω s
  simp only [driverProc]
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    simp [Coeffs.perturb, affineCoeffs, crowdPert, tupleAt]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
variable (P) in
/-- **The terminal value along the tuple** is `g(X_T) = X_T`, at every interaction strength. -/
theorem terminalVal_dealer_inert (ε : ℝ) (X : Fin n → ℝ → Ω → ℝ) (k : Fin n) :
    terminalVal P T (dealerCoeffs β₁ β₂ σc hc ε) X k = X k T := by
  funext ω
  simp [terminalVal, Coeffs.perturb, affineCoeffs, crowdPert]

omit [MeasurableSpace Ω] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The jump process of the representative `h_c / (1 + β₁ p)` is the representative. -/
theorem jumpProc_inertJump (i : Fin n) :
    jumpProc T (inertJump Ω β₁ β₂ T hc) i = inertJump Ω β₁ β₂ T hc i := by
  funext s ω e
  simp only [jumpProc]
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · rw [Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem hs, inertJump,
      Set.indicator_of_notMem (fun h => hs (Set.Ioc_subset_Icc_self h)), zero_mul]

omit [MeasurableSpace Ω] in
/-- **The jump coefficient at `ε = 0` along the tuple** is
`h = h_c − β₁ U_t = h_c / (1 + β₁ p(t))` on `(0, T]`, whatever the rest of the tuple and the
law. -/
theorem dealerCoeffs_zero_h_inert (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) T) (θ : TupleH ν n n d)
    (hθ : θ.2.2.2 = (Set.Ioc (0 : ℝ) T).indicator (inertGain β₁ β₂ T) t • hc)
    (μ : P2 (TupleH ν n n d)) :
    (dealerCoeffs β₁ β₂ σc hc 0).h t θ μ = (1 + β₁ * inertP β₁ β₂ T t)⁻¹ • hc := by
  have h1 := (one_add_mul_inertP_pos hβ₁ hβ₂ ht.2).ne'
  rw [dealerCoeffs_h, hθ, Set.indicator_of_mem ht, zero_smul, sub_zero, smul_smul,
    ← one_smul ℝ hc, smul_smul, smul_smul, mul_one, ← sub_smul]
  congr 1
  simp only [inertGain]
  field_simp
  ring

end Along

/-! ### The tuple solves the dealer system at `ε = 0` -/

section Solution

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n d : ℕ} {P : Measure Ω}
  [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T β₁ β₂ : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}
  {ξ₀ : Fin n → Ω → ℝ} {X : Fin n → ℝ → Ω → ℝ}

/-- Almost every time of `[0, T]` lies in `(0, T]`. -/
theorem ae_restrict_Icc_mem_Ioc (T : ℝ) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Ioc (0 : ℝ) T := by
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [(Ioc_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := T)).mem_iff]
    with s hs hsI
  exact hs.mpr hsI

/-- **The tuple solves the dealer system at `ε = 0`.** Let `β₁, β₂ ≥ 0`, `T ≥ 0`, `p` the
positive solution of `p' = β₁ p² − β₂`, `p(T) = 1`, and let `X` solve, over a filtration `ℱ`
carrying the driver, the forward equation

`X_t = ξ₀ + ∫_0^t (−β₁ p(s) X_s) ds + ∫_0^t σ_c / (1 + β₁ p(s)) dW_s
  + ∫_0^t ∫_E h_c(e) / (1 + β₁ p(s)) Ñ(ds, de)`.

Then `(X, Y, Z, U)` with, for `t ∈ [0, T]`, `Y_t = p(t) X_t`, `Z_t = p(t) σ_c / (1 + β₁ p(t))`
and `U_t = p(t) h_c / (1 + β₁ p(t))`, the last on `(0, T]` and `U_0 = 0`, and with
`h_c / (1 + β₁ p)` on `(0, T]` as representative of the jump coefficient, solves (1.1) for
`dealerCoeffs β₁ β₂ σ_c h_c 0` over `ℱ` with initial datum `ξ₀`. -/
theorem solves_dealer_inert (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hT : 0 ≤ T)
    (hX : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (ξ₀ i) (inertDrift β₁ β₂ T X i) (X i)
      (inertDiffusion Ω β₁ β₂ T σc i) (inertJump Ω β₁ β₂ T hc i)) :
    Solves D ℱ hℱW hℱN T (dealerCoeffs β₁ β₂ σc hc 0) ξ₀ X
      (fun k t ω => inertP β₁ β₂ T (clampTime T t) * X k t ω) (inertZ Ω β₁ β₂ T σc)
      (inertU Ω β₁ β₂ T hc) (inertJump Ω β₁ β₂ T hc) := by
  refine Solves.of_linear ?_ (fun i => ?_) (fun k => ?_)
  · filter_upwards [ae_restrict_Icc_mem_Ioc T] with s hs
    refine Eventually.of_forall fun ω => ?_
    rw [dealerCoeffs_zero_h_inert hβ₁ hβ₂ hs _ (uLift_inertU s ω)]
    exact inertJump_ae_eq hs ω
  · rw [driftProc_dealer_inert, diffusionProc_dealer_inert P hβ₁ hβ₂, jumpProc_inertJump]
    exact hX i
  · have hq : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt (inertP β₁ β₂ T)
        (β₁ * inertP β₁ β₂ T t ^ 2 - β₂) (Set.Icc 0 T) t := fun t ht =>
      (hasDerivAt_inertP hβ₁ hβ₂ ht.2).hasDerivWithinAt
    have hq' : ContinuousOn (fun t => β₁ * inertP β₁ β₂ T t ^ 2 - β₂) (Set.Icc 0 T) :=
      (continuousOn_const.mul
        (((continuousOn_inertP hβ₁ hβ₂).mono Set.Icc_subset_Iic_self).pow 2)).sub
        continuousOn_const
    refine (((hX k).mul_deterministic hT hq hq').linearBSDEJ hT).of_eq ?_ ?_ rfl ?_ ?_
    · rw [terminalVal_dealer_inert]
      funext ω
      rw [clampTime_of_mem ⟨hT, le_rfl⟩, inertP_self, one_mul]
    · rw [driverProc_dealer_inert]
      funext ω s
      simp only [inertDrift]
      by_cases hs : s ∈ Set.Icc (0 : ℝ) T
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, Set.indicator_of_mem hs]
        ring
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, neg_zero]
    · funext s ω j
      simp only [inertDiffusion, inertZ]
      by_cases hs : s ∈ Set.Icc (0 : ℝ) T
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, clampTime_of_mem hs, inertGain,
          div_eq_mul_inv]
        ring
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]
        ring
    · funext s ω e
      simp only [inertJump, inertU]
      by_cases hs : s ∈ Set.Ioc (0 : ℝ) T
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs,
          clampTime_of_mem (Set.Ioc_subset_Icc_self hs), inertGain, div_eq_mul_inv]
        ring
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]
        ring

end Solution

/-! ### The crowding correction vanishes along the tuple -/

section Crowd

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n d : ℕ} {P : Measure Ω}
  [IsProbabilityMeasure P] {T β₁ β₂ : ℝ} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The law of the jump channel is a Dirac mass**: at every time `t`,
`Law(U_t) = δ_{u(t)}` with `u(t) = 1_{(0, T]}(t) p(t) h_c / (1 + β₁ p(t))`. -/
theorem map_uLift_inertU (t : ℝ) :
    P.map (fun ω => uLift ν (fun e k => inertU Ω β₁ β₂ T hc k t ω e))
      = Measure.dirac ((Set.Ioc (0 : ℝ) T).indicator (inertGain β₁ β₂ T) t • hc) := by
  simp_rw [uLift_inertU]
  rw [Measure.map_const, measure_univ, one_smul]

/-- **The `U`-marginal of the law of the tuple is a Dirac mass**: for any square-integrable
tuple `Θ_t = (X_t, Y_t, Z_t, U_t)` with the jump channel of the inert tuple,
`(Law Θ_t)^U = δ_{u(t)}`, `u(t) = 1_{(0, T]}(t) p(t) h_c / (1 + β₁ p(t))`. -/
theorem margU_lawP2_inertU {X Y : Fin n → ℝ → Ω → ℝ} {Z : Fin n → ℝ → Ω → Fin d → ℝ} {t : ℝ}
    (hΘ : MemLp (tupleAt ν X Y Z (inertU Ω β₁ β₂ T hc) t) 2 P) :
    (lawP2 P (tupleAt ν X Y Z (inertU Ω β₁ β₂ T hc) t)).margU.law
      = Measure.dirac ((Set.Ioc (0 : ℝ) T).indicator (inertGain β₁ β₂ T) t • hc) := by
  rw [margU_lawP2 hΘ, lawP2_law hΘ.snd.snd.snd]
  exact map_uLift_inertU t

/-- **The crowding correction vanishes along the tuple**: for any square-integrable tuple `Θ_t`
with the jump channel of the inert tuple, `A_{(Law Θ_t)^U}(U_t) = ∇V(0) = 0` at every sample
point. -/
theorem crowdOp_margU_inertU {X Y : Fin n → ℝ → Ω → ℝ} {Z : Fin n → ℝ → Ω → Fin d → ℝ} {t : ℝ}
    (hΘ : MemLp (tupleAt ν X Y Z (inertU Ω β₁ β₂ T hc) t) 2 P) (ω : Ω) :
    crowdOp (lawP2 P (tupleAt ν X Y Z (inertU Ω β₁ β₂ T hc) t)).margU.law
      (tupleAt ν X Y Z (inertU Ω β₁ β₂ T hc) t ω).2.2.2 = 0 := by
  rw [margU_lawP2_inertU hΘ, crowdOp_dirac]
  change crowdGrad (uLift ν (fun e k => inertU Ω β₁ β₂ T hc k t ω e) - _) = 0
  rw [uLift_inertU, sub_self, crowdGrad_zero]

end Crowd

/-! ### The tuple solves the dealer system at every interaction strength -/

section Strength

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n d : ℕ} {P : Measure Ω}
  [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T β₁ β₂ : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}
  {ξ₀ : Fin n → Ω → ℝ} {X : Fin n → ℝ → Ω → ℝ}

/-- **The crowding correction vanishes along the tuple.** Under the hypotheses of
`solves_dealer_inert`, over a filtration whose null sets lie in its time-`0` field, whose
right-continuation is constant before `0` and which carries a cross witness, for `T > 0`: for
almost every `s ∈ [0, T]`, `A_{μ_s^U}(U_s) = 0` at every sample point, with `μ_s` the law of
`Θ_s = (X_s, Y_s, Z_s, U_s)`. -/
theorem ae_crowdOp_dealer_inert (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hX : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (ξ₀ i) (inertDrift β₁ β₂ T X i) (X i)
      (inertDiffusion Ω β₁ β₂ T σc i) (inertJump Ω β₁ β₂ T hc i)) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ ω,
      crowdOp (lawP2 P (tupleAt ν X (fun k t ω => inertP β₁ β₂ T (clampTime T t) * X k t ω)
          (inertZ Ω β₁ β₂ T σc) (inertU Ω β₁ β₂ T hc) s)).margU.law
        (tupleAt ν X (fun k t ω => inertP β₁ β₂ T (clampTime T t) * X k t ω)
          (inertZ Ω β₁ β₂ T σc) (inertU Ω β₁ β₂ T hc) s ω).2.2.2 = 0 := by
  filter_upwards [SolvesForced.ae_memLp_tupleAt (solves_dealer_inert hβ₁ hβ₂ hT.le hX) 𝒲 hℱ0
    hnull hT] with s hs ω
  exact crowdOp_margU_inertU hs ω

/-- **The tuple solves the dealer system at every interaction strength.** Under the hypotheses
of `ae_crowdOp_dealer_inert`, for every `ε`, `(X, Y, Z, U)` with `Y = p X`,
`Z = p σ_c / (1 + β₁ p)`, `U = p h_c / (1 + β₁ p)` solves (1.1) for
`dealerCoeffs β₁ β₂ σ_c h_c ε` with initial datum `ξ₀`: the crowding correction vanishes along
it, so the jump coefficients at `ε` and at `0` agree there. -/
theorem solves_dealer_inert_of_crossWitness (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hX : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (ξ₀ i) (inertDrift β₁ β₂ T X i) (X i)
      (inertDiffusion Ω β₁ β₂ T σc i) (inertJump Ω β₁ β₂ T hc i)) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (ε : ℝ) :
    Solves D ℱ hℱW hℱN T (dealerCoeffs β₁ β₂ σc hc ε) ξ₀ X
      (fun k t ω => inertP β₁ β₂ T (clampTime T t) * X k t ω) (inertZ Ω β₁ β₂ T σc)
      (inertU Ω β₁ β₂ T hc) (inertJump Ω β₁ β₂ T hc) := by
  refine (solvesForced_iff_of_h_ae_eq (C := dealerCoeffs β₁ β₂ σc hc 0)
    (C' := dealerCoeffs β₁ β₂ σc hc ε) rfl rfl rfl rfl ?_).mp
    (solves_dealer_inert hβ₁ hβ₂ hT.le hX)
  filter_upwards [ae_crowdOp_dealer_inert hβ₁ hβ₂ hX 𝒲 hℱ0 hnull hT] with s hs
  refine Eventually.of_forall fun ω => ?_
  rw [dealerCoeffs_h, dealerCoeffs_h, hs ω, smul_zero, smul_zero]

/-- **The tuple is a solution in the sense of the paper at every interaction strength.** Under
the hypotheses of `solves_dealer_inert_of_crossWitness`, for every `ε`, `(X, Y, Z, U)` is a
solution of (1.1) in the sense of the paper for `dealerCoeffs β₁ β₂ σ_c h_c ε` with initial
datum `ξ₀`: the deterministic integrands `Z` and `U` are predictable. -/
theorem paperSolution_dealer_inert (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hX : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (ξ₀ i) (inertDrift β₁ β₂ T X i) (X i)
      (inertDiffusion Ω β₁ β₂ T σc i) (inertJump Ω β₁ β₂ T hc i)) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (ε : ℝ) :
    PaperSolution D ℱ hℱW hℱN T (dealerCoeffs β₁ β₂ σc hc ε) ξ₀ X
      (fun k t ω => inertP β₁ β₂ T (clampTime T t) * X k t ω) (inertZ Ω β₁ β₂ T σc)
      (inertU Ω β₁ β₂ T hc) (inertJump Ω β₁ β₂ T hc) :=
  Solves.paperSolution (solves_dealer_inert_of_crossWitness hβ₁ hβ₂ hX 𝒲 hℱ0 hnull hT ε)
    (fun k j => predictable_of_measurable_time
      (g := fun s => (Set.Icc (0 : ℝ) T).indicator (inertGain β₁ β₂ T) s * σc.ofLp (k, j))
      ((measurable_inertGain.indicator measurableSet_Icc).mul measurable_const))
    (fun k => markedPredictable_indicator_Ioc_mul measurable_inertGain (measurable_coord_Lp hc k))
    𝒲 hℱ0 hnull hT

/-- **The crowding correction vanishes along the predictable tuple.** Under the hypotheses of
`ae_crowdOp_dealer_inert`: for almost every `s ∈ [0, T]`, `A_{μ⁻_s^U}(U_s) = 0` at every sample
point, with `Θ⁻_s = (X_{s−}, Y_{s−}, Z_s, U_s)` and `μ⁻_s` its law. -/
theorem ae_crowdOp_leftLim_dealer_inert (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hX : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (ξ₀ i) (inertDrift β₁ β₂ T X i) (X i)
      (inertDiffusion Ω β₁ β₂ T σc i) (inertJump Ω β₁ β₂ T hc i)) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ ω,
      crowdOp (lawP2 P (tupleAt ν (leftLimProc X)
          (leftLimProc fun k t ω => inertP β₁ β₂ T (clampTime T t) * X k t ω)
          (inertZ Ω β₁ β₂ T σc) (inertU Ω β₁ β₂ T hc) s)).margU.law
        (tupleAt ν (leftLimProc X)
          (leftLimProc fun k t ω => inertP β₁ β₂ T (clampTime T t) * X k t ω)
          (inertZ Ω β₁ β₂ T σc) (inertU Ω β₁ β₂ T hc) s ω).2.2.2 = 0 := by
  have hp := paperSolution_dealer_inert hβ₁ hβ₂ hX 𝒲 hℱ0 hnull hT 0
  filter_upwards [hp.ae_ae_tupleAt_leftLimProc_eq hT.le,
    SolvesForced.ae_memLp_tupleAt (solves_dealer_inert hβ₁ hβ₂ hT.le hX) 𝒲 hℱ0 hnull hT]
    with s hs hL ω
  exact crowdOp_margU_inertU (hL.ae_eq hs.symm) ω

end Strength

/-! ### The initially enlarged filtration -/

section Enlarged

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {n d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {T β₁ β₂ ε : ℝ}
  {σc : EuclideanSpace ℝ (Fin n × Fin d)} {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν}
  {ξ₀ : Fin n → Ω → ℝ}

/-- **Example 5.5: without the exposure term the interaction is inert.** Let `D` be a Lévy
driver, `𝒢₀` a σ-algebra independent of its joint natural filtration, `T > 0`, `β₁, β₂ ≥ 0`,
`σ_c ∈ ℝ^{n×d}`, `h_c ∈ L²(ν; ℝⁿ)`, `ξ₀` square integrable and measurable for the time-`0` field
of `enlJoint 𝒢₀ D h𝒢₀`, and `p` the positive solution of `p' = β₁ p² − β₂`, `p(T) = 1`. Then
there is `X` solving, over `enlJoint 𝒢₀ D h𝒢₀`, the forward equation
`dX = −β₁ p X dt + σ_c / (1 + β₁ p) dW + h_c / (1 + β₁ p) dÑ`, `X_0 = ξ₀`, such that the tuple

`Y_t = p(t) X_t`,   `Z_t = p(t) σ_c / (1 + β₁ p(t))`,   `U_t = p(t) h_c / (1 + β₁ p(t))`

on `[0, T]`, the last on `(0, T]` with `U_0 = 0`, with the representative `h_c / (1 + β₁ p)` of
the jump coefficient,

* solves (1.1) for `dealerCoeffs β₁ β₂ σ_c h_c ε` with initial datum `ξ₀`, both for `Solves` and
  in the sense of the paper, for every interaction strength `ε`;
* has a deterministic jump channel: at every time `t`, `Law(U_t)` is the Dirac mass at
  `1_{(0, T]}(t) p(t) h_c / (1 + β₁ p(t))`;
* has no crowding correction: for almost every `s ∈ [0, T]`, `A_{μ⁻_s^U}(U_s) = 0` at every
  sample point, with `μ⁻_s` the law of the predictable tuple `Θ⁻_s = (X_{s−}, Y_{s−}, Z_s, U_s)`.
-/
theorem exists_paperSolutionEnl_dealer_inert
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (hT : 0 < T) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hξ : ∀ i, MemLp (ξ₀ i) 2 P) (hξm : ∀ i, Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] (ξ₀ i)) :
    ∃ X : Fin n → ℝ → Ω → ℝ,
      (∀ i, LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
        (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (ξ₀ i) (inertDrift β₁ β₂ T X i) (X i)
        (inertDiffusion Ω β₁ β₂ T σc i) (inertJump Ω β₁ β₂ T hc i))
      ∧ (∀ ε : ℝ, SolvesEnl D h𝒢₀ hind₀ T (dealerCoeffs β₁ β₂ σc hc ε) ξ₀ X
          (fun k t ω => inertP β₁ β₂ T (clampTime T t) * X k t ω) (inertZ Ω β₁ β₂ T σc)
          (inertU Ω β₁ β₂ T hc) (inertJump Ω β₁ β₂ T hc)
        ∧ PaperSolutionEnl D h𝒢₀ hind₀ T (dealerCoeffs β₁ β₂ σc hc ε) ξ₀ X
          (fun k t ω => inertP β₁ β₂ T (clampTime T t) * X k t ω) (inertZ Ω β₁ β₂ T σc)
          (inertU Ω β₁ β₂ T hc) (inertJump Ω β₁ β₂ T hc))
      ∧ (∀ t, P.map (fun ω => uLift ν (fun e k => inertU Ω β₁ β₂ T hc k t ω e))
          = Measure.dirac ((Set.Ioc (0 : ℝ) T).indicator (inertGain β₁ β₂ T) t • hc))
      ∧ ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ ω,
        crowdOp (lawP2 P (tupleAt ν (leftLimProc X)
            (leftLimProc fun k t ω => inertP β₁ β₂ T (clampTime T t) * X k t ω)
            (inertZ Ω β₁ β₂ T σc) (inertU Ω β₁ β₂ T hc) s)).margU.law
          (tupleAt ν (leftLimProc X)
            (leftLimProc fun k t ω => inertP β₁ β₂ T (clampTime T t) * X k t ω)
            (inertZ Ω β₁ β₂ T σc) (inertU Ω β₁ β₂ T hc) s ω).2.2.2 = 0 := by
  obtain ⟨X, hX⟩ := exists_linearFSDEJ_inert (D := D)
    (hℱW := isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
    (hℱN := isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (σc := σc) (hc := hc)
    (hF0_enlJoint D h𝒢₀) (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hβ₁ hβ₂
    hT.le hξ hξm
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0
  exact ⟨X, hX, fun ε =>
    ⟨solves_dealer_inert_of_crossWitness hβ₁ hβ₂ hX (crossWitnessEnl D h𝒢₀ hind₀)
      (hF0_enlJoint D h𝒢₀) hnull hT ε,
    paperSolution_dealer_inert hβ₁ hβ₂ hX (crossWitnessEnl D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
      hnull hT ε⟩, map_uLift_inertU,
    ae_crowdOp_leftLim_dealer_inert hβ₁ hβ₂ hX (crossWitnessEnl D h𝒢₀ hind₀)
      (hF0_enlJoint D h𝒢₀) hnull hT⟩

end Enlarged

end Dissertation.WellPosedness.Existence
