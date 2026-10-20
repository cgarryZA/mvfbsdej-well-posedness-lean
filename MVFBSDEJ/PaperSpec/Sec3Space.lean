/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Setting

/-!
# The solution space and the solution definition of §3 of the well-posedness paper

Statement numbers refer to the well-posedness paper at `1f67672`, in the standing setting of §2.
§3 identifies the elements of `ℍ` up to indistinguishability (`X, Y`) and almost-everywhere
equality (`Z, U`), states that `‖·‖_ℍ` is then a norm, that `(ℍ, ‖·‖_ℍ)` is a Banach space and that
`ℍ ⊂ ℍ_weak`, and observes that,
both sides of each identity of (1.1) being càdlàg in `t`, the exceptional null set of a solution may
be taken independent of `t`.

## Main definitions

* `MVFBSDEJ.PaperSpec.sec3_one_null_set` — the identities of (1.1) for every `t` almost
  surely hold off one null set for all `t`.
* `MVFBSDEJ.PaperSpec.sec3_HH_inclusion` — `𝔼 ∫_0^T |V|² ≤ T 𝔼 sup |V|²`, so `ℍ ⊂ ℍ_weak`.
* `MVFBSDEJ.PaperSpec.sec3_HH_definite` — `‖Θ‖_ℍ = 0` exactly for the zero class.
* `MVFBSDEJ.PaperSpec.sec3_HH_complete` — `(ℍ, ‖·‖_ℍ)` is complete.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace MVFBSDEJ.PaperSpec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Enlarged LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

/-- §3, the solution definition: both sides of each identity of (1.1) are càdlàg in `t`, so the
exceptional null set may be taken independent of `t`. In the standing setting, let
`Θ = (X, Y, Z, U)` be a tuple of `ℍ_weak` (adapted `X, Y` with right-continuous paths, predictable
`Z, U`, finite energies) along which the integrals of (1.1) exist, with `γ` a representative of
the jump coefficient, and let `M` be a process with almost surely right-continuous paths on
`[0, T)`, such as a càdlàg version of a Brownian integral. Then the forward identity
`X_t = ξ₀ + ∫_0^t b + M_t + ∫_0^t ∫_E γ Ñ` holds almost surely for every `t ∈ [0, T]` if and only if
it holds off one null set for all `t ∈ [0, T]`; likewise the backward identity
`Y_t = g + ∫_t^T f − (M_T − M_t) − ∫_t^T ∫_E U Ñ`. -/
def sec3_one_null_set : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T : ℝ) (C : Coeffs ν n m d)
    (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ) (γ : Fin n → ℝ → Ω → E → ℝ)
    (hΘ : PaperWeakTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X Y Z U)
    (hA : PaperAdmissibleInt (enlJoint 𝒢₀ D h𝒢₀) P T C X Y Z U γ),
    (∀ (i : Fin n) (M : ℝ → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) →
      ((∀ t ∈ Set.Icc (0 : ℝ) T, X i t =ᵐ[P] fun ω => ξ₀ ω i
          + (∫ s in Set.Icc (0 : ℝ) t, driftProc P T C X Y Z U i ω s) + M t ω
          + Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
              (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => jumpProc T γ i s ω' e)
              (hA.γ_meas i) (hA.γ_prog i)
              (marked_sq_int_global_of_vanishing (fun ω _ e hs => jumpProc_of_notMem hs i ω e)
                (hA.γ_sq i)) t ω)
        ↔ ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X i t ω = ξ₀ ω i
          + (∫ s in Set.Icc (0 : ℝ) t, driftProc P T C X Y Z U i ω s) + M t ω
          + Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
              (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => jumpProc T γ i s ω' e)
              (hA.γ_meas i) (hA.γ_prog i)
              (marked_sq_int_global_of_vanishing (fun ω _ e hs => jumpProc_of_notMem hs i ω e)
                (hA.γ_sq i)) t ω))
    ∧ ∀ (k : Fin m) (M : ℝ → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) →
      ((∀ t ∈ Set.Icc (0 : ℝ) T, Y k t =ᵐ[P] fun ω => terminalVal P T C X k ω
          + (∫ s in Set.Icc t T, driverProc P T C X Y Z U k ω s) - (M T ω - M t ω)
          - (Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
                (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => U k s ω' e)
                ((hΘ.U_pred k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
                (hΘ.U_pred k).markedProgressivelyMeasurable
                (marked_sq_int_global_of_vanishing (hΘ.U_vanish k) (hΘ.U_sq k)) T ω
            - Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
                (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => U k s ω' e)
                ((hΘ.U_pred k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
                (hΘ.U_pred k).markedProgressivelyMeasurable
                (marked_sq_int_global_of_vanishing (hΘ.U_vanish k) (hΘ.U_sq k)) t ω))
        ↔ ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y k t ω = terminalVal P T C X k ω
          + (∫ s in Set.Icc t T, driverProc P T C X Y Z U k ω s) - (M T ω - M t ω)
          - (Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
                (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => U k s ω' e)
                ((hΘ.U_pred k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
                (hΘ.U_pred k).markedProgressivelyMeasurable
                (marked_sq_int_global_of_vanishing (hΘ.U_vanish k) (hΘ.U_sq k)) T ω
            - Poisson.Compensated.stochasticIntegral D.N (enlJoint 𝒢₀ D h𝒢₀)
                (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => U k s ω' e)
                ((hΘ.U_pred k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
                (hΘ.U_pred k).markedProgressivelyMeasurable
                (marked_sq_int_global_of_vanishing (hΘ.U_vanish k) (hΘ.U_sq k)) t ω))

/-- §3, the solution space, the inclusion `ℍ ⊂ ℍ_weak`: for `T ≥ 0` and a process `V` with values
in `ℝⁿ`, `𝔼 ∫_0^T |V_t|² dt ≤ T 𝔼 sup_{t ≤ T} |V_t|²`; in particular `𝔼 sup_{t ≤ T} |V_t|² < ∞`
gives `𝔼 ∫_0^T |V_{i,t}|² dt < ∞` for every coordinate. -/
def sec3_HH_inclusion : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ) (T : ℝ), 0 ≤ T →
    ∀ V : Fin n → ℝ → Ω → ℝ,
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, esq (fun i => V i s ω) ∂volume ∂P
          ≤ ENNReal.ofReal T * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => V i t ω)) ∂P
        ∧ (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => V i t ω)) ∂P < ⊤ →
          ∀ i, Brownian.Ito.energy P T (fun ω s => V i s ω) ≠ ⊤)

/-- §3, the solution space, `‖·‖_ℍ` is a norm: for a tuple `Θ = (X, Y, Z, U)` of `ℍ_weak` over the
filtration of §2, `‖Θ‖²_ℍ = 𝔼 sup|X|² + 𝔼 sup|Y|² + 𝔼 ∫ (|Z|² + ‖U‖²_{L²(ν)})` vanishes if and
only if `Θ` is the zero class: `X` and `Y` are indistinguishable from `0` on `[0, T]`, `Z = 0`
`dt ⊗ dP`-almost everywhere on `[0, T]` and `U = 0` `dt ⊗ dP ⊗ ν`-almost everywhere. -/
def sec3_HH_definite : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ) (T : ℝ)
    (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
    (U : Fin m → ℝ → Ω → E → ℝ), PaperWeakTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X Y Z U →
    (supSize P ν T X Y Z U = 0 ↔
      (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, X i t ω = 0)
      ∧ (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, Y k t ω = 0)
      ∧ (∀ k j, ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T), Z k p.2 p.1 j = 0)
      ∧ ∀ k, ∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P ν T), U k p.2.1 p.1 p.2.2 = 0)

/-- §3, the solution space, `(ℍ, ‖·‖_ℍ)` is complete: over the filtration of §2, let
`Θ_j = (X_j, Y_j, Z_j, U_j)` be tuples of `ℍ_weak` with `‖Θ_j‖_ℍ < ∞` that are Cauchy for
`‖·‖_ℍ`, `‖Θ_j − Θ_k‖²_ℍ = 𝔼 sup|X_j − X_k|² + 𝔼 sup|Y_j − Y_k|²
+ 𝔼 ∫ (|Z_j − Z_k|² + ‖U_j − U_k‖²_{L²(ν)}) → 0` as `j, k → ∞`. Then there is a tuple
`Θ = (X, Y, Z, U)` of `ℍ_weak` with `‖Θ‖_ℍ < ∞`, every path of `X` and of `Y` càdlàg on
`[0, T]`, and `‖Θ_j − Θ‖_ℍ → 0`. -/
def sec3_HH_complete : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ) (T : ℝ)
    (X : ℕ → Fin n → ℝ → Ω → ℝ) (Y : ℕ → Fin m → ℝ → Ω → ℝ)
    (Z : ℕ → Fin m → ℝ → Ω → Fin d → ℝ) (U : ℕ → Fin m → ℝ → Ω → E → ℝ),
    (∀ j, PaperWeakTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T (X j) (Y j) (Z j) (U j)) →
    (∀ j, supSize P ν T (X j) (Y j) (Z j) (U j) ≠ ⊤) →
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      supSize P ν T (fun i t ω => X j i t ω - X k i t ω) (fun l t ω => Y j l t ω - Y k l t ω)
        (fun l t ω a => Z j l t ω a - Z k l t ω a) (fun l t ω e => U j l t ω e - U k l t ω e)
        < ε) →
    ∃ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ) (Z' : Fin m → ℝ → Ω → Fin d → ℝ)
      (U' : Fin m → ℝ → Ω → E → ℝ),
      PaperWeakTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X' Y' Z' U'
      ∧ (∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X' i s ω) (𝓝[<] t) (𝓝 l))
      ∧ (∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y' k s ω) (𝓝[<] t) (𝓝 l))
      ∧ supSize P ν T X' Y' Z' U' ≠ ⊤
      ∧ Tendsto (fun j => supSize P ν T (fun i t ω => X j i t ω - X' i t ω)
          (fun l t ω => Y j l t ω - Y' l t ω) (fun l t ω a => Z j l t ω a - Z' l t ω a)
          (fun l t ω e => U j l t ω e - U' l t ω e)) atTop (𝓝 0)

end MVFBSDEJ.PaperSpec
