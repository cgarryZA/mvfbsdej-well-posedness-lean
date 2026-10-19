/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.PairDiff
import Dissertation.WellPosedness.System.LawFlow
import Dissertation.WellPosedness.System.Solves

/-!
# The solution notion of the well-posedness paper

In the well-posedness paper a *solution* of (1.1) is a tuple `Θ = (X, Y, Z, U)` of
`ℍ² = S²(ℝⁿ) × S²(ℝᵐ) × H²_W × H²_N` satisfying both identities of (1.1) almost surely for every
`t ∈ [0, T]`, with the jump coefficient `h` evaluated at the predictable tuple
`Θ⁻_t = (X_{t−}, Y_{t−}, Z_t, U_t)` and its law `μ⁻_t`; both sides of each identity are càdlàg in
`t`, so the exceptional null set may be taken independent of `t`. Here `S²` consists of the
càdlàg adapted processes `V` with `𝔼 sup_{t ≤ T} |V_t|² < ∞`, identified when indistinguishable,
`H²_W` of the predictable `Z` with `𝔼 ∫_0^T |Z_t|²_F dt < ∞` and `H²_N` of the predictable
`U` with `𝔼 ∫_0^T ‖U_t‖²_{L²(ν)} dt < ∞`, identified almost everywhere.

`PaperSolution` states this definition for coordinate processes over a filtration `ℱ` carrying
the driver `D`, with `γ` a representative of the jump coefficient along the solution, and asks in
addition that the drift and driver processes along `Θ` have finite energy on `[0, T]`. Under (2.3)
and Assumptions 2.2–2.3 the coefficient processes along a tuple of `ℍ²` have finite energy ((4.2)),
so it is then the paper's notion.

* **`X ∈ S²(ℝⁿ)`, `Y ∈ S²(ℝᵐ)`.** Each coordinate is adapted at every time of `[0, T]`, every
  path is right-continuous at every time of `[0, T)`, almost every path has left limits at every
  time of `(0, T]`, and `𝔼 sup_{t ≤ T} |X_t|² < ∞`, `𝔼 sup_{t ≤ T} |Y_t|² < ∞` (fields
  `X_adapted`, `X_rightCont`, `X_leftLim`, `X_sup` and their `Y` analogues). Nothing is asked of
  `X` and `Y` off `[0, T]`.
* **`Z ∈ H²_W`, `U ∈ H²_N`.** Each coordinate of `Z` is predictable and each coordinate of `U`
  is marked predictable, with finite energy on `[0, T]` (`Z_pred`, `Z_sq`, `U_pred`, `U_sq`).
  Both vanish off `[0, T]` (`Z_vanish`, `U_vanish`), a normalisation: their values off `[0, T]`
  do not enter (1.1).
* **The jump coefficient at the predictable tuple.** `γ` represents
  `e ↦ h(s, Θ⁻_s(ω), e, μ⁻_s)` in `L²(ν)` for almost every `s ∈ [0, T]`, almost surely
  (`jump_rep`), with `Θ⁻_s = tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s` and
  `μ⁻_s = lawP2 P Θ⁻_s`.
* **The identities.** On one set of full measure, at every `t ∈ [0, T]`,

  `X_t = ξ₀ + ∫_{[0, t]} b(s, Θ_s, μ_s) ds + M_t + ∫_0^t ∫_E γ_s(e) Ñ(ds, de)`,

  with `M` a version of `∫_0^t σ(s, Θ_s, μ_s) dW_s` (`fwd`), and

  `Y_t = g(X_T, Law X_T) + ∫_{[t, T]} f(s, Θ_s, μ_s) ds − (M_T − M_t)
    − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`,

  with `M` a version of `∫_0^t Z_s dW_s` (`bwd`). Here `μ_s = lawP2 P Θ_s` is the law of `Θ_s`
  at every time; the paper's `μ_s` is a Borel representative of `t ↦ Law(Θ_t)` (Lemma A.1), and
  coefficient evaluations do not depend on the representative up to `dt ⊗ dP`-null sets.

The encoding takes the following forms.

* **Paths.** Every path of `X` and `Y` is right-continuous on `[0, T)`, as for the càdlàg
  processes of which the paper's classes consist; the left limits are asked only almost surely,
  a condition invariant under indistinguishability. Right-continuity of every path makes an
  adapted process progressively measurable, as the measurability (2.5) of the coefficient
  processes along `Θ` needs of the tuple. An adapted process which is right-continuous only
  almost surely need not even be jointly measurable: for a nonempty null set `N ∈ ℱ_0` and a set
  `A ⊆ [0, T]` which is not Borel, `X_t(ω) = 1_N(ω) 1_A(t)` is adapted and almost surely
  continuous, but not jointly measurable.
* **The Brownian integral.** The canonical integral
  `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral` is defined
  separately at each time, as a representative of an `L²` limit, and has no path regularity, so
  the identities on one set of full measure are stated with a version `M` whose paths are almost
  surely càdlàg on `[0, T]`: such a version exists (`exists_ae_cadlag_brownianIntegral`), and two
  of them, agreeing almost surely at each time, agree at every time of `[0, T]` on one set of
  full measure by right-continuity (as in `ae_forall_Icc_eq_of_ae_rightContinuous`). The
  compensated Poisson integral `LevyStochCalc.Poisson.Compensated.stochasticIntegral` is itself a
  càdlàg version.
* **Existence of the integrals.** The integrals of (1.1) are the `L²` ones, and the remaining
  fields are the conditions under which they exist, on the integrands along `Θ`: the joint
  measurability, the progressive measurability and the finite energy on `[0, T]` of the drift
  process `b(s, Θ_s, μ_s)` (`b_meas`, `b_prog`, `b_sq`), of the diffusion process
  `σ(s, Θ_s, μ_s)` (`σ_meas`, `σ_prog`, `σ_sq`) and of the driver process `f(s, Θ_s, μ_s)`
  (`f_meas`, `f_prog`, `f_sq`), and the joint measurability, the marked progressive measurability
  and the finite marked energy of the jump integrand `γ` cut to `[0, T]` (`γ_meas`, `γ_prog`,
  `γ_sq`). The paper derives them from its assumptions: the measurability from (2.5), the energy
  bounds from Assumptions 2.2–2.3 (Remark 3.2). For `b` and `f` the finite energy is more than
  the existence of the Lebesgue integrals in `ds`, which needs only almost surely integrable
  paths; it is the form of the linear equations `LinearFSDEJ` and `LinearBSDEJ`. The
  representative `γ` is asked marked progressively measurable, as the Poisson integral requires;
  the paper's representative is predictable, (2.5).

The square integrability of `ξ₀` and of `g(X_T, Law X_T)` is not a field: it follows from the
`S²` bounds and the identities at `t = 0` and `t = T` (`PaperSolution.memLp_initial`,
`PaperSolution.memLp_terminal`). The relation to the predicate `Solves` is in
`Dissertation.WellPosedness.System.PaperSolutionSolves`.

## Main definitions

* `PaperSolution` — `(X, Y, Z, U)` is a solution of (1.1) in `ℍ²` whose drift and driver
  processes have finite energy.

## Main statements

* `progressivelyMeasurable_of_predictable`, `progressivelyMeasurable_of_predictable_of_vanish` —
  a predictable process vanishing before `0` is progressively measurable.
* `driftProc_of_notMem`, `diffusionProc_of_notMem`, `driverProc_of_notMem`,
  `jumpProc_of_notMem` — the coefficient processes vanish off `[0, T]`.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

/-! ### Predictable processes vanishing before time `0` -/

section Predictable

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **A predictable process vanishing before time `0` is progressively measurable**, for any
filtration indexed by `ℝ`. -/
theorem progressivelyMeasurable_of_predictable {K : Ω → ℝ → ℝ}
    (hK : Probability.Predictable ℱ K) (h0 : ∀ ω s, s < 0 → K ω s = 0) :
    Probability.ProgressivelyMeasurable ℱ K := by
  let ℱ₀ : Filtration ℝ ‹MeasurableSpace Ω› :=
    ⟨fun t => ℱ (max 0 t), fun _ _ hst => ℱ.mono (max_le_max le_rfl hst), fun _ => ℱ.le _⟩
  have hle : Probability.predictableSigma ℱ ≤ Probability.predictableSigma ℱ₀ := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro - (⟨A, hA, rfl⟩ | ⟨r, A, hA, rfl⟩)
    · exact Probability.measurableSet_predictableSigma_Iic_prod (ℱ := ℱ₀)
        (show MeasurableSet[ℱ (max 0 0)] A by rwa [max_self])
    · exact Probability.measurableSet_predictableSigma_Ioi_prod (ℱ := ℱ₀)
        (show MeasurableSet[ℱ (max 0 r)] A from ℱ.mono (le_max_right 0 r) _ hA)
  have hprog : Probability.ProgressivelyMeasurable ℱ₀ K :=
    Probability.Predictable.progressivelyMeasurable
      (fun t _ => ℱ.mono (max_le (le_max_left 0 t) (le_max_left 0 t)))
      (show Probability.Predictable ℱ₀ K from hK.mono hle)
  intro t
  rcases lt_or_ge t 0 with ht | ht
  · have hzero : (fun p : Ω × ℝ => (Set.Iic t).indicator (K p.1) p.2) = fun _ => 0 := by
      funext p
      by_cases hp : p.2 ∈ Set.Iic t
      · rw [Set.indicator_of_mem hp, h0 p.1 p.2 (lt_of_le_of_lt hp ht)]
      · exact Set.indicator_of_notMem hp _
    rw [hzero]
    exact stronglyMeasurable_const
  · have h := hprog t
    have he : ℱ₀ t = ℱ t := show ℱ (max 0 t) = ℱ t by rw [max_eq_right ht]
    rwa [he] at h

/-- **A predictable integrand vanishing off `[0, T]` is progressively measurable**,
coordinatewise. -/
theorem progressivelyMeasurable_of_predictable_of_vanish {d : ℕ} {T : ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} (hZ : ∀ j, Probability.Predictable ℱ fun ω s => Z s ω j)
    (hv : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0) (j : Fin d) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω j :=
  progressivelyMeasurable_of_predictable (hZ j) fun ω s hs => by
    rw [hv ω s fun h => (not_le.mpr hs) h.1, Pi.zero_apply]

end Predictable

/-! ### The coefficient processes off the horizon -/

variable {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ} {C : Coeffs ν n m d}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- Off the horizon the drift process vanishes. -/
theorem driftProc_of_notMem {s : ℝ} (hs : s ∉ Set.Icc (0 : ℝ) T) (i : Fin n) (ω : Ω) :
    driftProc P T C X Y Z U i ω s = 0 :=
  Set.indicator_of_notMem hs _

/-- Off the horizon the diffusion process vanishes. -/
theorem diffusionProc_of_notMem {s : ℝ} (hs : s ∉ Set.Icc (0 : ℝ) T) (i : Fin n) (ω : Ω) :
    diffusionProc P T C X Y Z U i s ω = 0 :=
  funext fun _ => Set.indicator_of_notMem hs _

/-- Off the horizon the driver process vanishes. -/
theorem driverProc_of_notMem {s : ℝ} (hs : s ∉ Set.Icc (0 : ℝ) T) (k : Fin m) (ω : Ω) :
    driverProc P T C X Y Z U k ω s = 0 :=
  Set.indicator_of_notMem hs _

omit [MeasurableSpace Ω] [MeasurableSpace E] [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] in
/-- Off the horizon the jump process vanishes. -/
theorem jumpProc_of_notMem {s : ℝ} (hs : s ∉ Set.Icc (0 : ℝ) T) (i : Fin n) (ω : Ω) (e : E) :
    jumpProc T γ i s ω e = 0 :=
  Set.indicator_of_notMem hs _

/-! ### The solution predicate -/

/-- **`(X, Y, Z, U)` is a solution of (1.1) in `ℍ²` with drift and driver of finite energy**, with
coefficients `C` and initial datum `ξ₀`, over the filtration `ℱ` carrying the driver `D`, and
with `γ` a representative of the jump coefficient: `X` and `Y` are adapted on `[0, T]` with
right-continuous paths on `[0, T)`, left limits on `(0, T]` almost surely and finite
`𝔼 sup_{t ≤ T} |·|²`; `Z` and `U` are predictable with finite energy and vanish off `[0, T]`;
the drift, diffusion and driver processes along `Θ` and the jump integrand `γ` meet the
conditions for the integrals of (1.1) to exist; `γ` represents `h(s, Θ⁻_s, ·, μ⁻_s)` in `L²(ν)`
at almost every time, almost surely; and both identities of (1.1) hold at every `t ∈ [0, T]` on
one set of full measure, with càdlàg versions of the Brownian integrals. -/
structure PaperSolution (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ) (T : ℝ) (C : Coeffs ν n m d)
    (ξ₀ : Fin n → Ω → ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop where
  /-- Each coordinate of `X` is adapted on the horizon. -/
  X_adapted : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (X i t)
  /-- Every path of each coordinate of `X` is right-continuous on `[0, T)`. -/
  X_rightCont : ∀ i ω, ∀ t ∈ Set.Ico (0 : ℝ) T,
    Tendsto (fun s => X i s ω) (𝓝[>] t) (𝓝 (X i t ω))
  /-- Almost every path of each coordinate of `X` has left limits on `(0, T]`. -/
  X_leftLim : ∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioc (0 : ℝ) T,
    ∃ L : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 L)
  /-- `𝔼 sup_{t ≤ T} |X_t|² < ∞`. -/
  X_sup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P < ⊤
  /-- Each coordinate of `Y` is adapted on the horizon. -/
  Y_adapted : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (Y k t)
  /-- Every path of each coordinate of `Y` is right-continuous on `[0, T)`. -/
  Y_rightCont : ∀ k ω, ∀ t ∈ Set.Ico (0 : ℝ) T,
    Tendsto (fun s => Y k s ω) (𝓝[>] t) (𝓝 (Y k t ω))
  /-- Almost every path of each coordinate of `Y` has left limits on `(0, T]`. -/
  Y_leftLim : ∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioc (0 : ℝ) T,
    ∃ L : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 L)
  /-- `𝔼 sup_{t ≤ T} |Y_t|² < ∞`. -/
  Y_sup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y k t ω)) ∂P < ⊤
  /-- Each coordinate of `Z` is predictable. -/
  Z_pred : ∀ k j, Probability.Predictable ℱ fun ω s => Z k s ω j
  /-- `Z` vanishes off the horizon. -/
  Z_vanish : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) T → Z k s ω = 0
  /-- Each coordinate of `Z` has finite energy on the horizon. -/
  Z_sq : ∀ k j, Brownian.Ito.energy P T (fun ω s => Z k s ω j) ≠ ⊤
  /-- Each coordinate of `U` is marked predictable. -/
  U_pred : ∀ k, Probability.MarkedPredictable ℱ ν fun ω s e => U k s ω e
  /-- `U` vanishes off the horizon. -/
  U_vanish : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → U k s ω e = 0
  /-- Each coordinate of `U` has finite marked energy on the horizon. -/
  U_sq : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) ≠ ⊤
  /-- The drift process is jointly measurable. -/
  b_meas : ∀ i, Measurable (Function.uncurry (driftProc P T C X Y Z U i))
  /-- The drift process is progressively measurable. -/
  b_prog : ∀ i, Probability.ProgressivelyMeasurable ℱ (driftProc P T C X Y Z U i)
  /-- The drift process has finite energy on the horizon. -/
  b_sq : ∀ i, Brownian.Ito.energy P T (driftProc P T C X Y Z U i) ≠ ⊤
  /-- The diffusion process is jointly measurable. -/
  σ_meas : ∀ i j,
    Measurable (Function.uncurry fun ω s => diffusionProc P T C X Y Z U i s ω j)
  /-- The diffusion process is progressively measurable. -/
  σ_prog : ∀ i j,
    Probability.ProgressivelyMeasurable ℱ fun ω s => diffusionProc P T C X Y Z U i s ω j
  /-- The diffusion process has finite energy on the horizon. -/
  σ_sq : ∀ i j,
    Brownian.Ito.energy P T (fun ω s => diffusionProc P T C X Y Z U i s ω j) ≠ ⊤
  /-- The jump integrand is jointly measurable in the sample point, the time and the mark. -/
  γ_meas : ∀ i, Measurable fun p : Ω × ℝ × E => jumpProc T γ i p.2.1 p.1 p.2.2
  /-- The jump integrand is marked progressively measurable. -/
  γ_prog : ∀ i,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => jumpProc T γ i s ω e
  /-- The jump integrand has finite marked energy on the horizon. -/
  γ_sq : ∀ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => jumpProc T γ i s ω e) ≠ ⊤
  /-- The driver process is jointly measurable. -/
  f_meas : ∀ k, Measurable (Function.uncurry (driverProc P T C X Y Z U k))
  /-- The driver process is progressively measurable. -/
  f_prog : ∀ k, Probability.ProgressivelyMeasurable ℱ (driverProc P T C X Y Z U k)
  /-- The driver process has finite energy on the horizon. -/
  f_sq : ∀ k, Brownian.Ito.energy P T (driverProc P T C X Y Z U k) ≠ ⊤
  /-- `γ` represents the jump coefficient at the predictable tuple in `L²(ν)`, at almost every
  time of the horizon, almost surely. -/
  jump_rep : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
    (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
      =ᵐ[ν] C.h s (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
        (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s))
  /-- The forward identity at every time of the horizon on one set of full measure, with a
  càdlàg version `M` of the Brownian integral. -/
  fwd : ∀ i, ∃ M : ℝ → Ω → ℝ,
    (∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P]
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW
        (diffusionProc P T C X Y Z U i) (σ_meas i) (σ_prog i)
        (sq_int_global_of_vanishing (fun ω s hs => diffusionProc_of_notMem hs i ω) (σ_sq i)) t)
    ∧ (∀ᵐ ω ∂P, (∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)))
      ∧ ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L))
    ∧ ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      X i t ω = ξ₀ i ω + (∫ s in Set.Icc (0 : ℝ) t, driftProc P T C X Y Z U i ω s) + M t ω
        + Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
            (fun ω' s e => jumpProc T γ i s ω' e) (γ_meas i) (γ_prog i)
            (marked_sq_int_global_of_vanishing (fun ω s e hs => jumpProc_of_notMem hs i ω e)
              (γ_sq i)) t ω
  /-- The backward identity at every time of the horizon on one set of full measure, with a
  càdlàg version `M` of the Brownian integral. -/
  bwd : ∀ k, ∃ M : ℝ → Ω → ℝ,
    (∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P]
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW (Z k)
        (fun j => Brownian.Ito.measurable_uncurry_of_predictable (Z_pred k j))
        (progressivelyMeasurable_of_predictable_of_vanish (Z_pred k) (Z_vanish k))
        (sq_int_global_of_vanishing (Z_vanish k) (Z_sq k)) t)
    ∧ (∀ᵐ ω ∂P, (∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)))
      ∧ ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L))
    ∧ ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Y k t ω = terminalVal P T C X k ω + (∫ s in Set.Icc t T, driverProc P T C X Y Z U k ω s)
        - (M T ω - M t ω)
        - (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U k s ω' e)
              ((U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl)
              (U_pred k).markedProgressivelyMeasurable
              (marked_sq_int_global_of_vanishing (U_vanish k) (U_sq k)) T ω
            - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U k s ω' e)
              ((U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl)
              (U_pred k).markedProgressivelyMeasurable
              (marked_sq_int_global_of_vanishing (U_vanish k) (U_sq k)) t ω)

end Dissertation.WellPosedness.System
