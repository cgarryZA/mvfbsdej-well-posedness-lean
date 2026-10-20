/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.PaperSolution

/-!
# Solutions of (1.1) in the class `ℍ²_weak`

Besides `ℍ² = S²(ℝⁿ) × S²(ℝᵐ) × H²_W × H²_N`, the well-posedness paper uses the larger class
`ℍ²_weak = L²(ℝⁿ) × L²(ℝᵐ) × H²_W × H²_N`, in which `L²(ℝʲ)` consists of the càdlàg adapted
processes `V` with `𝔼 ∫_0^T |V_t|² dt < ∞`: the `S²` bounds are replaced by finite energy on
`[0, T]`. By Remark 3.2 of the paper a solution of (1.1) in `ℍ²_weak` lies in `ℍ²`
(`PaperWeakSolution.toPaperSolution`, in `MVFBSDEJ.WellPosedness.System.PaperWeakS2`).

`PaperWeakSolution` states the solution notion in `ℍ²_weak` in the encoding of `PaperSolution`:
its fields are those of `PaperSolution`, with `X_sup` and `Y_sup` replaced by `X_sq` and `Y_sq`,
the finiteness of `𝔼 ∫_0^T |X_{i,t}|² dt` and `𝔼 ∫_0^T |Y_{k,t}|² dt`. They fall into three
groups.

* **`Θ ∈ ℍ²_weak`** (`PaperWeakTuple`): each coordinate of `X` and `Y` is adapted at every time of
  `[0, T]`, every path is right-continuous at every time of `[0, T)`, almost every path has left
  limits at every time of `(0, T]`, and each coordinate has finite energy on `[0, T]`; `Z` and
  `U` are predictable, vanish off `[0, T]` and have finite energy on `[0, T]`.
* **The integrals of (1.1) along `Θ` exist** (`PaperAdmissible`): the joint and progressive
  measurability and the finite energy of the drift, diffusion and driver processes along `Θ` and
  of the jump integrand `γ` cut to `[0, T]`, and `γ` represents `h(s, Θ⁻_s, ·, μ⁻_s)` in `L²(ν)`
  at almost every time, almost surely. The paper derives these conditions from (2.5) and
  Assumptions 2.2–2.3 along every `Θ ∈ ℍ²_weak`; so does `PaperWeakTuple.exists_paperAdmissible`,
  in `MVFBSDEJ.WellPosedness.Existence.PaperAdmissible`.
* **The identities** `fwd`, `bwd` of (1.1), on one set of full measure, as in `PaperSolution`.

## Main definitions

* `PaperWeakTuple` — `(X, Y, Z, U)` lies in `ℍ²_weak`.
* `PaperAdmissible` — the integrals of (1.1) along `(X, Y, Z, U)` exist, with a representative
  `γ` of the jump coefficient at the predictable tuple.
* `PaperWeakSolution` — `(X, Y, Z, U)` is a solution of (1.1) in `ℍ²_weak`.

## Main statements

* `energy_ne_top_of_lintegral_biSup_esq_lt_top` — a process of finite `S²`-norm has finite
  energy on `[0, T]`, coordinatewise.
* `PaperSolution.toWeak` — a solution in `ℍ²` is a solution in `ℍ²_weak`.
* `PaperWeakSolution.paperSolution` — a solution in `ℍ²_weak` whose `X` and `Y` have finite
  `S²`-norm is a solution in `ℍ²`.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

/-- **A process of finite `S²`-norm has finite energy on `[0, T]`**, coordinatewise:
`𝔼 ∫_0^T |x_{i,t}|² dt ≤ T 𝔼 sup_{t ≤ T} |x_t|²`. -/
theorem energy_ne_top_of_lintegral_biSup_esq_lt_top {ι : Type*} [Fintype ι] {P : Measure Ω}
    {x : ι → ℝ → Ω → ℝ} {T : ℝ}
    (hsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂P < ⊤) (i : ι) :
    Brownian.Ito.energy P T (fun ω s => x i s ω) ≠ ⊤ := by
  refine (energy_le_of_biSup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_of_le_of_lt (lintegral_mono fun ω => iSup₂_mono fun t _ => ?_) hsup))).ne
  exact Finset.single_le_sum (f := fun i => (‖x i t ω‖₊ : ℝ≥0∞) ^ 2) (fun _ _ => zero_le)
    (Finset.mem_univ i)

variable {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-- **`Θ = (X, Y, Z, U)` lies in `ℍ²_weak`** over the filtration `ℱ` on the horizon `[0, T]`:
each coordinate of `X` and `Y` is adapted at every time of `[0, T]`, has right-continuous paths
on `[0, T)`, left limits on `(0, T]` almost surely and finite `𝔼 ∫_0^T |·|² dt`; each coordinate
of `Z` is predictable and each coordinate of `U` is marked predictable, with finite energy on
`[0, T]`, and both vanish off `[0, T]`. -/
structure PaperWeakTuple (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) (ν : Measure E)
    (T : ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ) : Prop where
  /-- Each coordinate of `X` is adapted on the horizon. -/
  X_adapted : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (X i t)
  /-- Every path of each coordinate of `X` is right-continuous on `[0, T)`. -/
  X_rightCont : ∀ i ω, ∀ t ∈ Set.Ico (0 : ℝ) T,
    Tendsto (fun s => X i s ω) (𝓝[>] t) (𝓝 (X i t ω))
  /-- Almost every path of each coordinate of `X` has left limits on `(0, T]`. -/
  X_leftLim : ∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioc (0 : ℝ) T,
    ∃ L : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 L)
  /-- Each coordinate of `X` has finite energy on the horizon, `𝔼 ∫_0^T |X_{i,t}|² dt < ∞`. -/
  X_sq : ∀ i, Brownian.Ito.energy P T (fun ω s => X i s ω) ≠ ⊤
  /-- Each coordinate of `Y` is adapted on the horizon. -/
  Y_adapted : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (Y k t)
  /-- Every path of each coordinate of `Y` is right-continuous on `[0, T)`. -/
  Y_rightCont : ∀ k ω, ∀ t ∈ Set.Ico (0 : ℝ) T,
    Tendsto (fun s => Y k s ω) (𝓝[>] t) (𝓝 (Y k t ω))
  /-- Almost every path of each coordinate of `Y` has left limits on `(0, T]`. -/
  Y_leftLim : ∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioc (0 : ℝ) T,
    ∃ L : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 L)
  /-- Each coordinate of `Y` has finite energy on the horizon, `𝔼 ∫_0^T |Y_{k,t}|² dt < ∞`. -/
  Y_sq : ∀ k, Brownian.Ito.energy P T (fun ω s => Y k s ω) ≠ ⊤
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

/-- **The integrals of (1.1) along `Θ = (X, Y, Z, U)` exist**, with `γ` a representative of the
jump coefficient at the predictable tuple: the drift, diffusion and driver processes of `C` along
`Θ` are jointly and progressively measurable with finite energy on `[0, T]`, the jump integrand
`γ` cut to `[0, T]` is jointly and marked progressively measurable with finite marked energy on
`[0, T]`, and `γ` represents `e ↦ h(s, Θ⁻_s(ω), e, μ⁻_s)` in `L²(ν)` at almost every time of
`[0, T]`, almost surely. -/
structure PaperAdmissible (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℝ) (C : Coeffs ν n m d) (X : Fin n → ℝ → Ω → ℝ)
    (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop where
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

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`(X, Y, Z, U)` is a solution of (1.1) in `ℍ²_weak`**, with coefficients `C` and initial
datum `ξ₀`, over the filtration `ℱ` carrying the driver `D`, and with `γ` a representative of the
jump coefficient: the conditions of `PaperSolution` with the `S²` bounds on `X` and `Y` replaced
by finite `𝔼 ∫_0^T |·|² dt`. `X` and `Y` are adapted on `[0, T]` with right-continuous paths on
`[0, T)`, left limits on `(0, T]` almost surely and finite energy on `[0, T]`; `Z` and `U` are
predictable with finite energy and vanish off `[0, T]`; the drift, diffusion and driver
processes along `Θ` and the jump integrand `γ` meet the conditions for the integrals of (1.1) to
exist; `γ` represents `h(s, Θ⁻_s, ·, μ⁻_s)` in `L²(ν)` at almost every time, almost surely; and
both identities of (1.1) hold at every `t ∈ [0, T]` on one set of full measure, with càdlàg
versions of the Brownian integrals. -/
structure PaperWeakSolution (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ) (T : ℝ) (C : Coeffs ν n m d)
    (ξ₀ : Fin n → Ω → ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ) : Prop
    extends PaperWeakTuple ℱ P ν T X Y Z U, PaperAdmissible ℱ P T C X Y Z U γ where
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

variable {T : ℝ} {C : Coeffs ν n m d} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {ξ₀ : Fin n → Ω → ℝ}

/-- **A solution in `ℍ²` is a solution in `ℍ²_weak`**: the `S²` bounds on `X` and `Y` give
finite energy on `[0, T]`. -/
theorem PaperSolution.toWeak (h : PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ) :
    PaperWeakSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ where
  X_adapted := h.X_adapted
  X_rightCont := h.X_rightCont
  X_leftLim := h.X_leftLim
  X_sq := energy_ne_top_of_lintegral_biSup_esq_lt_top h.X_sup
  Y_adapted := h.Y_adapted
  Y_rightCont := h.Y_rightCont
  Y_leftLim := h.Y_leftLim
  Y_sq := energy_ne_top_of_lintegral_biSup_esq_lt_top h.Y_sup
  Z_pred := h.Z_pred
  Z_vanish := h.Z_vanish
  Z_sq := h.Z_sq
  U_pred := h.U_pred
  U_vanish := h.U_vanish
  U_sq := h.U_sq
  b_meas := h.b_meas
  b_prog := h.b_prog
  b_sq := h.b_sq
  σ_meas := h.σ_meas
  σ_prog := h.σ_prog
  σ_sq := h.σ_sq
  γ_meas := h.γ_meas
  γ_prog := h.γ_prog
  γ_sq := h.γ_sq
  f_meas := h.f_meas
  f_prog := h.f_prog
  f_sq := h.f_sq
  jump_rep := h.jump_rep
  fwd := h.fwd
  bwd := h.bwd

/-- **A solution in `ℍ²_weak` with `S²` bounds is a solution in `ℍ²`**: if moreover
`𝔼 sup_{t ≤ T} |X_t|² < ∞` and `𝔼 sup_{t ≤ T} |Y_t|² < ∞`, then `(X, Y, Z, U)` is a solution of
(1.1) in the sense of `PaperSolution`, with the same `γ`. -/
theorem PaperWeakSolution.paperSolution (h : PaperWeakSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ)
    (hX : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P < ⊤)
    (hY : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y k t ω)) ∂P < ⊤) :
    PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ where
  X_adapted := h.X_adapted
  X_rightCont := h.X_rightCont
  X_leftLim := h.X_leftLim
  X_sup := hX
  Y_adapted := h.Y_adapted
  Y_rightCont := h.Y_rightCont
  Y_leftLim := h.Y_leftLim
  Y_sup := hY
  Z_pred := h.Z_pred
  Z_vanish := h.Z_vanish
  Z_sq := h.Z_sq
  U_pred := h.U_pred
  U_vanish := h.U_vanish
  U_sq := h.U_sq
  b_meas := h.b_meas
  b_prog := h.b_prog
  b_sq := h.b_sq
  σ_meas := h.σ_meas
  σ_prog := h.σ_prog
  σ_sq := h.σ_sq
  γ_meas := h.γ_meas
  γ_prog := h.γ_prog
  γ_sq := h.γ_sq
  f_meas := h.f_meas
  f_prog := h.f_prog
  f_sq := h.f_sq
  jump_rep := h.jump_rep
  fwd := h.fwd
  bwd := h.bwd

end MVFBSDEJ.WellPosedness.System
