/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Setting

/-!
# The norm of the solution space and the càdlàg integrals of §3 of the well-posedness paper

Statement numbers refer to the well-posedness paper at `1f67672`, in the standing setting of §2.
§3 states that, after the identification of tuples of `𝕊` that agree up to indistinguishability
(`X, Y`) and almost-everywhere equality (`Z, U`), `‖·‖_𝕊` is a norm rather than a seminorm, and,
in the solution definition, that both sides of each identity of (1.1) are càdlàg in `t`. The
Brownian integral `∫_0^t Z_s dW_s` is an `L²`-limit taken separately at each time, with no path
regularity, and the compensated Poisson integral has càdlàg paths only almost surely, so the
càdlàg paths of the stochastic integrals of (1.1) are those of versions.

## Main definitions

* `Dissertation.PaperSpec.A.sec3_cadlag_versions` — the stochastic integrals of (1.1) along a
  tuple of `ℍ²` have adapted versions whose every path is càdlàg on `[0, T]`.
* `Dissertation.PaperSpec.A.sec3_HH_norm` — `‖·‖_𝕊` satisfies the triangle inequality and is
  absolutely homogeneous.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Enlarged LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

/-- §3, the solution definition: the stochastic integrals of (1.1) are càdlàg in `t`. In the
standing setting, let `Θ = (X, Y, Z, U)` be a tuple of `ℍ²` (adapted `X, Y` with
right-continuous paths, predictable `Z, U` with finite energies vanishing off `[0, T]`) along which
the integrals of (1.1) exist, with `γ` a representative of the jump coefficient. Then each
coordinate of each stochastic integral of (1.1), the Brownian integral `∫_0^t σ(s, Θ_s, μ_s) dW_s`
and the Poisson integral `∫_0^t ∫_E γ_s(e) Ñ(ds, de)` of the forward identity, and
`∫_0^t Z_s dW_s` and `∫_0^t ∫_E U_s(e) Ñ(ds, de)` of the backward identity, has a version `M`:
a process adapted to the filtration of §2, equal almost surely to the integral at every
`t ∈ [0, T]`, whose path at every sample point is càdlàg on `[0, T]`, right-continuous on `[0, T)`
with left limits on `(0, T]`. -/
def sec3_cadlag_versions : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T : ℝ) (C : Coeffs ν n m d)
    (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ) (γ : Fin n → ℝ → Ω → E → ℝ)
    (hΘ : PaperWeakTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X Y Z U)
    (hA : PaperAdmissibleInt (enlJoint 𝒢₀ D h𝒢₀) P T C X Y Z U γ),
    (∀ i : Fin n, ∃ M : ℝ → Ω → ℝ, Adapted (enlJoint 𝒢₀ D h𝒢₀) M
      ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P]
          Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
            (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (diffusionProc P T C X Y Z U i)
            (hA.σ_meas i) (hA.σ_prog i)
            (sq_int_global_of_vanishing (fun ω _ hs => diffusionProc_of_notMem hs i ω)
              (hA.σ_sq i)) t)
      ∧ (∀ ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)))
      ∧ ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L))
    ∧ (∀ i : Fin n, ∃ M : ℝ → Ω → ℝ, Adapted (enlJoint 𝒢₀ D h𝒢₀) M
      ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P]
          Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
            (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => jumpProc T γ i s ω' e)
            (hA.γ_meas i) (hA.γ_prog i)
            (marked_sq_int_global_of_vanishing (fun ω _ e hs => jumpProc_of_notMem hs i ω e)
              (hA.γ_sq i)) t)
      ∧ (∀ ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)))
      ∧ ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L))
    ∧ (∀ k : Fin m, ∃ M : ℝ → Ω → ℝ, Adapted (enlJoint 𝒢₀ D h𝒢₀) M
      ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P]
          Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (enlJoint 𝒢₀ D h𝒢₀)
            (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (Z k)
            (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hΘ.Z_pred k j))
            (progressivelyMeasurable_of_predictable_of_vanish (hΘ.Z_pred k) (hΘ.Z_vanish k))
            (sq_int_global_of_vanishing (hΘ.Z_vanish k) (hΘ.Z_sq k)) t)
      ∧ (∀ ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)))
      ∧ ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L))
    ∧ ∀ k : Fin m, ∃ M : ℝ → Ω → ℝ, Adapted (enlJoint 𝒢₀ D h𝒢₀) M
      ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P]
          Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
            (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => U k s ω' e)
            ((hΘ.U_pred k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
            (hΘ.U_pred k).markedProgressivelyMeasurable
            (marked_sq_int_global_of_vanishing (hΘ.U_vanish k) (hΘ.U_sq k)) t)
      ∧ (∀ ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)))
      ∧ ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L)

/-- §3, the solution space, `‖·‖_𝕊` is a norm rather than a seminorm, the triangle inequality and
the absolute homogeneity (the definiteness is `sec3_HH_definite`): over the filtration of §2, for
tuples `Θ = (X, Y, Z, U)` and `Θ' = (X', Y', Z', U')` of `ℍ²` and `c ∈ ℝ`, with
`‖Θ‖_𝕊 = (𝔼 sup|X|² + 𝔼 sup|Y|² + 𝔼 ∫ (|Z|² + ‖U‖²_{L²(ν)}))^{1/2}` in `[0, ∞]` and sums and
scalar multiples taken coordinatewise, `‖Θ + Θ'‖_𝕊 ≤ ‖Θ‖_𝕊 + ‖Θ'‖_𝕊` and
`‖c Θ‖_𝕊 = |c| ‖Θ‖_𝕊`. -/
def sec3_HH_norm : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ) (T : ℝ)
    (X X' : Fin n → ℝ → Ω → ℝ) (Y Y' : Fin m → ℝ → Ω → ℝ) (Z Z' : Fin m → ℝ → Ω → Fin d → ℝ)
    (U U' : Fin m → ℝ → Ω → E → ℝ),
    PaperWeakTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X Y Z U →
    PaperWeakTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X' Y' Z' U' →
    supSize P ν T (fun i t ω => X i t ω + X' i t ω) (fun k t ω => Y k t ω + Y' k t ω)
        (fun k t ω j => Z k t ω j + Z' k t ω j) (fun k t ω e => U k t ω e + U' k t ω e)
        ^ (1 / 2 : ℝ)
      ≤ supSize P ν T X Y Z U ^ (1 / 2 : ℝ) + supSize P ν T X' Y' Z' U' ^ (1 / 2 : ℝ)
    ∧ ∀ c : ℝ, supSize P ν T (fun i t ω => c * X i t ω) (fun k t ω => c * Y k t ω)
        (fun k t ω j => c * Z k t ω j) (fun k t ω e => c * U k t ω e) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal |c| * supSize P ν T X Y Z U ^ (1 / 2 : ℝ)

end Dissertation.PaperSpec.A
