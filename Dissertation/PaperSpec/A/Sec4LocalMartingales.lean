/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4BrownianPoisson
import Dissertation.WellPosedness.Martingale.LocalIntegral

/-!
# The local martingales `M^W` and `M¹` of the proof of Lemma 4.1

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The stochastic
integral terms of (4.5) are the local martingales

`M^W_t = ∫_0^t e^s ⟨δY_{s−}, δZ_s dW_s⟩`, `M¹_t = ∫_0^t ∫_E e^s ⟨δY_{s−}, δU_s(e)⟩ Ñ(ds, de)`,

and `M²` (the third, read pathwise, is `lem41_M2_zero_mean`). Their integrands carry the factor
`δY_{s−}`, which has no moment beyond the second, so they are local stochastic integrals
(`Dissertation.WellPosedness.Martingale.IsLocalBrownianIntegral`,
`Dissertation.WellPosedness.Martingale.IsLocalCompensatedIntegral`): `L²` integrals up to stopping
times that exhaust `[0, T]`. The Burkholder–Davis–Gundy inequality at `p = 1`, in
quadratic-variation form for `M¹`,

`𝔼 sup_{t ≤ T} |M¹_t| ≤ c_BDG 𝔼 (∫_0^T ∫_E e^{2s} |δY_{s−}|² |δU_s(e)|² N(ds, de))^{1/2}`,

and the Cauchy–Schwarz inequality give

`𝔼 sup_{t ≤ T} |M^W_t| ≤ c_BDG e^T (𝔼 sup_{t ≤ T} |δY_t|²)^{1/2} (𝔼 ∫_0^T |δZ_s|²_F ds)^{1/2}`,
`𝔼 sup_{t ≤ T} |M¹_t| ≤ c_BDG e^T (𝔼 sup_{t ≤ T} |δY_t|²)^{1/2} (𝔼 ∫_0^T ‖δU_s‖² ds)^{1/2}`,

both finite, and the supremum criterion gives `𝔼[M_T − M_t] = 0` for `M ∈ {M^W, M¹}`.
`c_BDG` is the constant of the Burkholder–Davis–Gundy inequality fixed in §4; each proposition
asserts its bound for every value of it at least some `c₀ > 0`. In the integrands `δY_{s−}` is the
left limit of `δY` at `s ∈ (0, T]`, and `0` at `s ≤ 0`, a time set of Lebesgue measure zero
within `[0, T]`.

## Main definitions

* `Dissertation.PaperSpec.A.lem41_MW` — `M^W`: its bound and its zero-mean increments.
* `Dissertation.PaperSpec.A.lem41_M1` — `M¹`: its bound and its zero-mean increments.
* `Dissertation.PaperSpec.A.lem41_M1_bdg` — the first link of the chain for `M¹`, the
  Burkholder–Davis–Gundy inequality in quadratic-variation form.
* `Dissertation.PaperSpec.A.lem41_M1_chain` — the links of the chain for `M¹` after its first:
  the Cauchy–Schwarz inequality, the compensation formula (2.1) and the `L²(ν)` norm.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.WellPosedness.Martingale LevyStochCalc

universe u v w

/-- **`M^W` in the proof of Lemma 4.1.** There is `c₀ > 0` such that, for every value `c ≥ c₀`
of the constant `c_BDG`: under the hypotheses of Lemma 4.1 (those of `lem_bpbsde`), the integrand
`e^s ⟨δY_{s−}, δZ_s ·⟩` has a local Itô integral `M^W_t = ∫_0^t e^s ⟨δY_{s−}, δZ_s dW_s⟩` on
`[0, T]`, and every such `M^W` satisfies
`𝔼 sup_{t ≤ T} |M^W_t| ≤ c e^T (𝔼 sup_{t ≤ T} |δY_t|²)^{1/2} (𝔼 ∫_0^T |δZ_s|²_F ds)^{1/2} < ∞`
and, for every `t ∈ [0, T]`, `𝔼[M^W_T − M^W_t] = 0` with `M^W_T − M^W_t` integrable; the
expectations of nonnegative quantities are read in `[0, ∞]`. -/
def lem41_MW : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
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
    (∃ MW : ℝ → Ω → ℝ, IsLocalBrownianIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
        (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) T
        (fun s ω j => Real.exp s
          * ∑ k, (if 0 < s then leftLimProc δY k s ω else 0) * δZ k s ω j) MW)
    ∧ ∀ MW : ℝ → Ω → ℝ, IsLocalBrownianIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
        (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) T
        (fun s ω j => Real.exp s
          * ∑ k, (if 0 < s then leftLimProc δY k s ω else 0) * δZ k s ω j) MW →
      ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖MW t ω‖₊ : ℝ≥0∞) ∂P
          ≤ ENNReal.ofReal (c * Real.exp T)
            * (∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => δY k t ω) ∂P) ^ (1 / 2 : ℝ)
            * (∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => δZ k s ω j)) ^ (1 / 2 : ℝ)
        ∧ ENNReal.ofReal (c * Real.exp T)
            * (∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => δY k t ω) ∂P) ^ (1 / 2 : ℝ)
            * (∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => δZ k s ω j)) ^ (1 / 2 : ℝ) < ⊤
        ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun ω => MW T ω - MW t ω) P
          ∧ ∫ ω, (MW T ω - MW t ω) ∂P = 0

/-- **`M¹` in the proof of Lemma 4.1.** There is `c₀ > 0` such that, for every value `c ≥ c₀`
of the constant `c_BDG`: under the hypotheses of Lemma 4.1 (those of `lem_bpbsde`), the marked
integrand `e^s ⟨δY_{s−}, δU_s(e)⟩` has a local compensated Poisson integral
`M¹_t = ∫_0^t ∫_E e^s ⟨δY_{s−}, δU_s(e)⟩ Ñ(ds, de)` on `[0, T]`, and every such `M¹` satisfies
`𝔼 sup_{t ≤ T} |M¹_t| ≤ c e^T (𝔼 sup_{t ≤ T} |δY_t|²)^{1/2} (𝔼 ∫_0^T ‖δU_s‖²_{L²(ν)} ds)^{1/2}
< ∞` and, for every `t ∈ [0, T]`, `𝔼[M¹_T − M¹_t] = 0` with `M¹_T − M¹_t` integrable; the
expectations of nonnegative quantities are read in `[0, ∞]`. -/
def lem41_M1 : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
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
    (∃ M1 : ℝ → Ω → ℝ, IsLocalCompensatedIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
        (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T
        (fun ω s e => Real.exp s
          * ∑ k, (if 0 < s then leftLimProc δY k s ω else 0) * δU k s ω e) M1)
    ∧ ∀ M1 : ℝ → Ω → ℝ, IsLocalCompensatedIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
        (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T
        (fun ω s e => Real.exp s
          * ∑ k, (if 0 < s then leftLimProc δY k s ω else 0) * δU k s ω e) M1 →
      ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M1 t ω‖₊ : ℝ≥0∞) ∂P
          ≤ ENNReal.ofReal (c * Real.exp T)
            * (∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => δY k t ω) ∂P) ^ (1 / 2 : ℝ)
            * (∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e))
              ^ (1 / 2 : ℝ)
        ∧ ENNReal.ofReal (c * Real.exp T)
            * (∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => δY k t ω) ∂P) ^ (1 / 2 : ℝ)
            * (∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e))
              ^ (1 / 2 : ℝ) < ⊤
        ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun ω => M1 T ω - M1 t ω) P
          ∧ ∫ ω, (M1 T ω - M1 t ω) ∂P = 0

/-- **The first link of the chain for `M¹` in the proof of Lemma 4.1**, the
Burkholder–Davis–Gundy inequality at `p = 1` in quadratic-variation form. There is `c₀ > 0` such
that, for every value `c ≥ c₀` of the constant `c_BDG`: under the hypotheses of Lemma 4.1 (those of
`lem_bpbsde`), every local compensated Poisson integral
`M¹_t = ∫_0^t ∫_E e^s ⟨δY_{s−}, δU_s(e)⟩ Ñ(ds, de)` on `[0, T]` satisfies
`𝔼 sup_{t ≤ T} |M¹_t| ≤ c 𝔼 (∫_0^T ∫_E e^{2s} |δY_{s−}|² |δU_s(e)|² N(ds, de))^{1/2}`,
with the Poisson integral over `(0, T] × E`; the expectations are read in `[0, ∞]`. -/
def lem41_M1_bdg : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
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
    ∀ M1 : ℝ → Ω → ℝ, IsLocalCompensatedIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
        (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T
        (fun ω s e => Real.exp s
          * ∑ k, (if 0 < s then leftLimProc δY k s ω else 0) * δU k s ω e) M1 →
      ∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M1 t ω‖₊ : ℝ≥0∞) ∂P
        ≤ ENNReal.ofReal c * ∫⁻ ω, (∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ,
            ENNReal.ofReal (Real.exp (2 * p.1)
              * (∑ k, (if 0 < p.1 then leftLimProc δY k p.1 ω else 0) ^ 2)
              * ∑ k, δU k p.1 ω p.2 ^ 2) ∂(D.N.N ω)) ^ (1 / 2 : ℝ) ∂P

/-- **The chain after the bound on `M¹` in the proof of Lemma 4.1**, its links after the first.
Under the hypotheses of Lemma 4.1 (those of `lem_bpbsde`), with the Poisson integrals over
`(0, T] × E`:
`𝔼 (∫_0^T ∫_E e^{2s} |δY_{s−}|² |δU_s(e)|² N(ds, de))^{1/2}
  ≤ e^T (𝔼 sup_{t ≤ T} |δY_t|²)^{1/2} (𝔼 ∫_0^T ∫_E |δU_s(e)|² N(ds, de))^{1/2}`,
`𝔼 ∫_0^T ∫_E |δU_s(e)|² N(ds, de) = 𝔼 ∫_0^T ∫_E |δU_s(e)|² ν(de) ds` (by (2.1)), and the latter
is `𝔼 ∫_0^T ‖δU_s‖²_{L²(ν)} ds`; the expectations are read in `[0, ∞]`. -/
def lem41_M1_chain : Prop :=
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
    ∫⁻ ω, (∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ,
        ENNReal.ofReal (Real.exp (2 * p.1)
          * (∑ k, (if 0 < p.1 then leftLimProc δY k p.1 ω else 0) ^ 2)
          * ∑ k, δU k p.1 ω p.2 ^ 2) ∂(D.N.N ω)) ^ (1 / 2 : ℝ) ∂P
      ≤ ENNReal.ofReal (Real.exp T)
        * (∫⁻ ω, ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => δY k t ω) ∂P) ^ (1 / 2 : ℝ)
        * (∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ,
            ENNReal.ofReal (∑ k, δU k p.1 ω p.2 ^ 2) ∂(D.N.N ω) ∂P) ^ (1 / 2 : ℝ)
    ∧ ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ Set.univ,
          ENNReal.ofReal (∑ k, δU k p.1 ω p.2 ^ 2) ∂(D.N.N ω) ∂P
        = ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (∑ k, δU k s ω e ^ 2)
            ∂ν ∂volume ∂P
    ∧ ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, ENNReal.ofReal (∑ k, δU k s ω e ^ 2)
          ∂ν ∂volume ∂P
        = ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => δU k s ω e)

end Dissertation.PaperSpec.A
