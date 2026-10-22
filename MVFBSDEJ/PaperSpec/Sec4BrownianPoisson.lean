/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec4

/-!
# Steps of the proof of Lemma 4.1 of the well-posedness paper

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The proof of
Lemma 4.1 takes expectations in the Itô identity (4.5) for `e^t |δY_t|²`. Its paragraph on the
zero-mean terms says that the quadratic integrand `e^s |δU_s(e)|²` of the Poisson martingale `M²`
has no square moments, that with `ν(E) = ∞` the jump times do not exhaust `[0, T]`, that the
integrand is predictable and nonnegative, and that the compensation formula gives
`𝔼[M²_T − M²_t] = 0`. The expected identity then gives the bound at every time `t` and (4.6).

## Main definitions

* `MVFBSDEJ.PaperSpec.lem41_M2_no_square_moment` — for `ν ≠ 0`, `δU ∈ H²_N` gives
  `e^s |δU_s(e)|²` no square moment.
* `MVFBSDEJ.PaperSpec.lem41_jump_times` — with `ν(E) = ∞` every `(0, t]` carries infinitely
  many jumps and the jump times, read in `[0, ∞]`, are all `0`.
* `MVFBSDEJ.PaperSpec.lem41_M2_integrand` — `e^s |δU_s(e)|²` is marked predictable and
  nonnegative.
* `MVFBSDEJ.PaperSpec.lem41_M2_zero_mean` — `𝔼[M²_T − M²_t] = 0`, `M²` read pathwise.
* `MVFBSDEJ.PaperSpec.lem41_M2_martingale` — `M²`, read pathwise, is a martingale on
  `[0, T]`, hence a local martingale.
* `MVFBSDEJ.PaperSpec.eq_supE` — the bound at every time and (4.6).
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace MVFBSDEJ.PaperSpec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Spec LevyStochCalc

universe u v w

/-- The `M²` paragraph of the proof of Lemma 4.1, its first clause: in the standing setting with
`ν ≠ 0`, for `m, d ≥ 1` and `T > 0`, some `δU ∈ H²_N(ℝᵐ)` — marked predictable, zero off
`[0, T]`, with `𝔼 ∫_0^T ‖δU_s‖²_{L²(ν)} ds < ∞` — has a quadratic integrand `e^s |δU_s(e)|²` of
`M²` without square moment: `𝔼 ∫_0^T ∫_E (e^s |δU_s(e)|²)² ν(de) ds = ∞`. -/
def lem41_M2_no_square_moment : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P → ν ≠ 0 → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∃ δU : Fin m → ℝ → Ω → E → ℝ,
      (∀ k, Probability.MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) ν fun ω s e => δU k s ω e)
      ∧ (∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → δU k s ω e = 0)
      ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e) ≠ ⊤)
      ∧ Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => Real.exp s * ∑ k, δU k s ω e ^ 2) = ⊤

/-- The `M²` paragraph of the proof of Lemma 4.1, its second clause: if `ν(E) = ∞`, then almost
surely every interval `(0, t]`, `t > 0`, carries infinitely many jumps, `N((0, t] × E) = ∞`; every
jump time `τ_k = inf {t ≥ 0 : N((0, t] × E) ≥ k}`, `k ∈ ℕ`, read in `[0, ∞]` (the infimum of the
empty set being `∞`), is `0`; and so `sup_k τ_k < T` for every `T > 0`: the jump times do not
exhaust `[0, T]`. -/
def lem41_jump_times : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] (d : ℕ)
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν), ν Set.univ = ⊤ →
    ∀ᵐ ω ∂P, (∀ t : ℝ, 0 < t → D.N.N ω (Set.Ioc 0 t ×ˢ Set.univ) = ⊤)
      ∧ (∀ k : ℕ, (⨅ (t : ℝ) (_ : 0 ≤ t ∧ (k : ℝ≥0∞) ≤ D.N.N ω (Set.Ioc 0 t ×ˢ Set.univ)),
          ENNReal.ofReal t) = 0)
      ∧ ∀ T : ℝ, 0 < T →
        (⨆ k : ℕ, ⨅ (t : ℝ) (_ : 0 ≤ t ∧ (k : ℝ≥0∞) ≤ D.N.N ω (Set.Ioc 0 t ×ˢ Set.univ)),
          ENNReal.ofReal t) < ENNReal.ofReal T

/-- The `M²` paragraph of the proof of Lemma 4.1, the integrand of its third clause. Under the
hypotheses of Lemma 4.1 (those of `lem_bpbsde`), the integrand `e^s |δU_s(e)|²` of `M²` is marked
predictable for the filtration of the setting and nonnegative. -/
def lem41_M2_integrand : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (δξ : Ω → EuclideanSpace ℝ (Fin m)) (φ : Fin m → Ω → ℝ → ℝ) (δY : Fin m → ℝ → Ω → ℝ)
      (δZ : Fin m → ℝ → Ω → Fin d → ℝ) (δU : Fin m → ℝ → Ω → E → ℝ)
      (hZ : ∀ k j, Probability.Predictable (enlJoint 𝒢₀ D h𝒢₀) fun ω s => δZ k s ω j)
      (hZv : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) T → δZ k s ω = 0)
      (hZs : ∀ k j, Brownian.Ito.energy P T (fun ω s => δZ k s ω j) ≠ ⊤)
      (hU : ∀ k, Probability.MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) ν
        fun ω s e => δU k s ω e)
      (hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → δU k s ω e = 0)
      (hUs : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e) ≠ ⊤),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ T] δξ → MemLp δξ 2 P →
    (∀ k, Measurable (Function.uncurry (φ k))) → (∀ k, Brownian.Ito.energy P T (φ k) ≠ ⊤) →
    (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[enlJoint 𝒢₀ D h𝒢₀ t] (δY k t)) →
    (∀ k ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => δY k s ω) (𝓝[>] t) (𝓝 (δY k t ω))) →
    (∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => δY k s ω) (𝓝[<] t) (𝓝 l)) →
    (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      δY k t ω = δξ ω k + (∫ s in Set.Icc t T, φ k ω s)
        - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
              (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (δZ k)
              (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
              (progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k))
              (BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k)) T ω
            - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
              (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (δZ k)
              (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
              (progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k))
              (BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k)) t ω)
        - (Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
              (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => δU k s ω' e)
              ((hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
              (hU k).markedProgressivelyMeasurable
              (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) T ω
            - Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
              (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => δU k s ω' e)
              ((hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
              (hU k).markedProgressivelyMeasurable
              (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) t ω)) →
    Probability.MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) ν
        (fun ω s e => Real.exp s * ∑ k, δU k s ω e ^ 2)
      ∧ ∀ ω s e, 0 ≤ Real.exp s * ∑ k, δU k s ω e ^ 2

/-- The `M²` paragraph of the proof of Lemma 4.1, its third clause. Under the hypotheses of
Lemma 4.1 (those of `lem_bpbsde`), `𝔼 ∫_0^T ∫_E e^s |δU_s(e)|² ν(de) ds
≤ e^T 𝔼 ∫_0^T ‖δU_s‖²_{L²(ν)} ds < ∞`, and for every `t ∈ [0, T]` the Poisson integral and the
compensator of `e^s |δU_s(e)|²` over `(t, T] × E` have finite expectation and the increment
`M²_T − M²_t = ∫_{(t, T] × E} e^s |δU_s(e)|² N(ds, de) − ∫_t^T ∫_E e^s |δU_s(e)|² ν(de) ds`
has mean zero. -/
def lem41_M2_zero_mean : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (δξ : Ω → EuclideanSpace ℝ (Fin m)) (φ : Fin m → Ω → ℝ → ℝ) (δY : Fin m → ℝ → Ω → ℝ)
      (δZ : Fin m → ℝ → Ω → Fin d → ℝ) (δU : Fin m → ℝ → Ω → E → ℝ)
      (hZ : ∀ k j, Probability.Predictable (enlJoint 𝒢₀ D h𝒢₀) fun ω s => δZ k s ω j)
      (hZv : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) T → δZ k s ω = 0)
      (hZs : ∀ k j, Brownian.Ito.energy P T (fun ω s => δZ k s ω j) ≠ ⊤)
      (hU : ∀ k, Probability.MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) ν
        fun ω s e => δU k s ω e)
      (hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → δU k s ω e = 0)
      (hUs : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e) ≠ ⊤),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ T] δξ → MemLp δξ 2 P →
    (∀ k, Measurable (Function.uncurry (φ k))) → (∀ k, Brownian.Ito.energy P T (φ k) ≠ ⊤) →
    (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[enlJoint 𝒢₀ D h𝒢₀ t] (δY k t)) →
    (∀ k ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => δY k s ω) (𝓝[>] t) (𝓝 (δY k t ω))) →
    (∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => δY k s ω) (𝓝[<] t) (𝓝 l)) →
    (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      δY k t ω = δξ ω k + (∫ s in Set.Icc t T, φ k ω s)
        - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
              (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (δZ k)
              (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
              (progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k))
              (BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k)) T ω
            - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
              (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (δZ k)
              (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
              (progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k))
              (BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k)) t ω)
        - (Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
              (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => δU k s ω' e)
              ((hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
              (hU k).markedProgressivelyMeasurable
              (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) T ω
            - Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
              (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => δU k s ω' e)
              ((hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
              (hU k).markedProgressivelyMeasurable
              (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) t ω)) →
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        ENNReal.ofReal (Real.exp s * ∑ k, δU k s ω e ^ 2) ∂ν ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp T)
        * ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e))
    ∧ ENNReal.ofReal (Real.exp T)
        * ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e) < ⊤
    ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ∫⁻ p in Set.Ioc t T ×ˢ Set.univ,
          ENNReal.ofReal (Real.exp p.1 * ∑ k, δU k p.1 ω p.2 ^ 2) ∂(D.N.N ω) ∂P < ⊤
      ∧ ∫⁻ ω, ∫⁻ s in Set.Ioc t T, ∫⁻ e,
          ENNReal.ofReal (Real.exp s * ∑ k, δU k s ω e ^ 2) ∂ν ∂volume ∂P < ⊤
      ∧ ∫ ω, ((∫ p in Set.Ioc t T ×ˢ Set.univ, Real.exp p.1 * ∑ k, δU k p.1 ω p.2 ^ 2
            ∂(D.N.N ω))
          - ∫ s in Set.Ioc t T, ∫ e, Real.exp s * ∑ k, δU k s ω e ^ 2 ∂ν) ∂P = 0

/-- The `M²` paragraph of the proof of Lemma 4.1: `M²` is a local martingale. Under the hypotheses
of Lemma 4.1 (those of `lem_bpbsde`), the process `M²`, read pathwise,
`M²_t = ∫_{(0, t] × E} e^s |δU_s(e)|² N(ds, de) − ∫_0^t ∫_E e^s |δU_s(e)|² ν(de) ds`, is a
martingale on `[0, T]` for the filtration of the setting, hence a local martingale: for every
`t ∈ [0, T]` the Poisson integral has finite expectation, and `M²_t` is integrable and almost
surely equal to an `ℱ_t`-measurable random variable; and `𝔼[M²_t | ℱ_s] = M²_s` almost surely
for `0 ≤ s ≤ t ≤ T`. -/
def lem41_M2_martingale : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (δξ : Ω → EuclideanSpace ℝ (Fin m)) (φ : Fin m → Ω → ℝ → ℝ) (δY : Fin m → ℝ → Ω → ℝ)
      (δZ : Fin m → ℝ → Ω → Fin d → ℝ) (δU : Fin m → ℝ → Ω → E → ℝ)
      (hZ : ∀ k j, Probability.Predictable (enlJoint 𝒢₀ D h𝒢₀) fun ω s => δZ k s ω j)
      (hZv : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) T → δZ k s ω = 0)
      (hZs : ∀ k j, Brownian.Ito.energy P T (fun ω s => δZ k s ω j) ≠ ⊤)
      (hU : ∀ k, Probability.MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) ν
        fun ω s e => δU k s ω e)
      (hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → δU k s ω e = 0)
      (hUs : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e) ≠ ⊤),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ T] δξ → MemLp δξ 2 P →
    (∀ k, Measurable (Function.uncurry (φ k))) → (∀ k, Brownian.Ito.energy P T (φ k) ≠ ⊤) →
    (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[enlJoint 𝒢₀ D h𝒢₀ t] (δY k t)) →
    (∀ k ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => δY k s ω) (𝓝[>] t) (𝓝 (δY k t ω))) →
    (∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => δY k s ω) (𝓝[<] t) (𝓝 l)) →
    (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      δY k t ω = δξ ω k + (∫ s in Set.Icc t T, φ k ω s)
        - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
              (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (δZ k)
              (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
              (progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k))
              (BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k)) T ω
            - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
              (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (δZ k)
              (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
              (progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k))
              (BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k)) t ω)
        - (Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
              (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => δU k s ω' e)
              ((hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
              (hU k).markedProgressivelyMeasurable
              (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) T ω
            - Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
              (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => δU k s ω' e)
              ((hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
              (hU k).markedProgressivelyMeasurable
              (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) t ω)) →
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ,
          ENNReal.ofReal (Real.exp p.1 * ∑ k, δU k p.1 ω p.2 ^ 2) ∂(D.N.N ω) ∂P < ⊤
      ∧ Integrable (fun ω =>
          ((∫ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ,
            Real.exp p.1 * ∑ k, δU k p.1 ω p.2 ^ 2 ∂(D.N.N ω))
          - ∫ r in Set.Ioc (0 : ℝ) t, ∫ e, Real.exp r * ∑ k, δU k r ω e ^ 2 ∂ν)) P
      ∧ AEStronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ t] (fun ω =>
          ((∫ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ,
            Real.exp p.1 * ∑ k, δU k p.1 ω p.2 ^ 2 ∂(D.N.N ω))
          - ∫ r in Set.Ioc (0 : ℝ) t, ∫ e, Real.exp r * ∑ k, δU k r ω e ^ 2 ∂ν)) P)
    ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      P[fun ω =>
          ((∫ p in Set.Ioc (0 : ℝ) t ×ˢ Set.univ,
            Real.exp p.1 * ∑ k, δU k p.1 ω p.2 ^ 2 ∂(D.N.N ω))
          - ∫ r in Set.Ioc (0 : ℝ) t, ∫ e, Real.exp r * ∑ k, δU k r ω e ^ 2 ∂ν)
        | enlJoint 𝒢₀ D h𝒢₀ s]
        =ᵐ[P] fun ω =>
          ((∫ p in Set.Ioc (0 : ℝ) s ×ˢ Set.univ,
            Real.exp p.1 * ∑ k, δU k p.1 ω p.2 ^ 2 ∂(D.N.N ω))
          - ∫ r in Set.Ioc (0 : ℝ) s, ∫ e, Real.exp r * ∑ k, δU k r ω e ^ 2 ∂ν)

/-- **The bound at every time and (4.6).** Under the hypotheses of Lemma 4.1 (those of
`lem_bpbsde`), with `R = e^T (𝔼|δξ|² + 𝔼 ∫_0^T |φ_s|² ds)`: for every `t ∈ [0, T]`,
`𝔼|δY_t|² + 𝔼 ∫_t^T (|δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds ≤ R`; and
`sup_{t ≤ T} 𝔼|δY_t|² + 𝔼 ∫_0^T (|δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds
  ≤ 2R = C₀ (𝔼|δξ|² + 𝔼 ∫_0^T |φ_s|² ds)` with `C₀ = 2 e^T`, the expectations read in
`[0, ∞]`. -/
def eq_supE : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (δξ : Ω → EuclideanSpace ℝ (Fin m)) (φ : Fin m → Ω → ℝ → ℝ) (δY : Fin m → ℝ → Ω → ℝ)
      (δZ : Fin m → ℝ → Ω → Fin d → ℝ) (δU : Fin m → ℝ → Ω → E → ℝ)
      (hZ : ∀ k j, Probability.Predictable (enlJoint 𝒢₀ D h𝒢₀) fun ω s => δZ k s ω j)
      (hZv : ∀ k ω s, s ∉ Set.Icc (0 : ℝ) T → δZ k s ω = 0)
      (hZs : ∀ k j, Brownian.Ito.energy P T (fun ω s => δZ k s ω j) ≠ ⊤)
      (hU : ∀ k, Probability.MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) ν
        fun ω s e => δU k s ω e)
      (hUv : ∀ k ω s e, s ∉ Set.Icc (0 : ℝ) T → δU k s ω e = 0)
      (hUs : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e) ≠ ⊤),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ T] δξ → MemLp δξ 2 P →
    (∀ k, Measurable (Function.uncurry (φ k))) → (∀ k, Brownian.Ito.energy P T (φ k) ≠ ⊤) →
    (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[enlJoint 𝒢₀ D h𝒢₀ t] (δY k t)) →
    (∀ k ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => δY k s ω) (𝓝[>] t) (𝓝 (δY k t ω))) →
    (∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => δY k s ω) (𝓝[<] t) (𝓝 l)) →
    (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      δY k t ω = δξ ω k + (∫ s in Set.Icc t T, φ k ω s)
        - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
              (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (δZ k)
              (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
              (progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k))
              (BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k)) T ω
            - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
              (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (δZ k)
              (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hZ k j))
              (progressivelyMeasurable_of_predictable_of_vanish (hZ k) (hZv k))
              (BSDEJ.Solves.sq_int_global_of_vanishing (hZv k) (hZs k)) t ω)
        - (Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
              (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => δU k s ω' e)
              ((hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
              (hU k).markedProgressivelyMeasurable
              (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) T ω
            - Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
              (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => δU k s ω' e)
              ((hU k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
              (hU k).markedProgressivelyMeasurable
              (BSDEJ.Solves.marked_sq_int_global_of_vanishing (hUv k) (hUs k)) t ω)) →
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, esq (fun k => δY k t ω) ∂P
        + ∫⁻ ω, ∫⁻ s in Set.Icc t T, (∑ k, esq (δZ k s ω)
            + ∑ k, ∫⁻ e, (‖δU k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp T)
        * (∫⁻ ω, esq (fun k => δξ ω k) ∂P + ∑ k, Brownian.Ito.energy P T (φ k)))
    ∧ (⨆ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, esq (fun k => δY k t ω) ∂P)
        + ((∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => δZ k s ω j))
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e))
      ≤ ENNReal.ofReal (2 * Real.exp T)
        * (∫⁻ ω, esq (fun k => δξ ω k) ∂P + ∑ k, Brownian.Ito.energy P T (φ k))

end MVFBSDEJ.PaperSpec
