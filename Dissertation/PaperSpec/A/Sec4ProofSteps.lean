/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4BrownianPoisson
import Dissertation.PaperSpec.A.Sec4Contraction
import Dissertation.PaperSpec.A.Sec4Estimates

/-!
# Further steps of the proofs of Lemmas 4.1–4.3 of the well-posedness paper

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The proof of
Lemma 4.1 takes expectations in (4.5) and bounds the drift term by Young's inequality:

`𝔼 e^t |δY_t|² + 𝔼 ∫_t^T e^s (|δZ_s|²_F + ‖δU_s‖²) ds ≤ 𝔼 e^T |δξ|² + 𝔼 ∫_t^T e^s |φ_s|² ds`.

The proof of Lemma 4.2 bounds the coefficient differences at almost every time,

`𝔼 S_s² ≤ 10 L² 𝔼[|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²]`,

takes the difference of (4.8) at two trials,

`δȲ_t = δξ̄ + ∫_t^T λ δf_s ds − ∫_t^T δZ̄_s dW_s − ∫_t^T ∫_E δŪ_s(e) Ñ(ds, de)`,

which is (4.4) with `δξ = δξ̄` and `φ_s = λ δf_s`, and sets `λ_* = (2 √C_Φ)⁻¹ ∈ (0, 1/2]`, at which
`C_Φ λ² ≤ 1/4` and `‖Φ_λ(Θ¹) − Φ_λ(Θ²)‖_ℍ ≤ (1/2) ‖Θ¹ − Θ²‖_ℍ` for `λ ∈ [0, λ_*]`. Step 3 of the
proof of Lemma 4.3 bounds, at every `t ≤ T`,

`𝔼 sup_{s ≤ t} |δX_s|² ≤ C (𝔼|δξ₀|² + 𝔼 ∫_0^t (|δb_s|² + |δσ_s|²_F + ‖δh_s‖²) ds + P)
  ≤ C (𝔼|δξ₀|² + 𝔼 ∫_0^t (|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²) ds + P)
  ≤ C (∫_0^t 𝔼 sup_{r ≤ s} |δX_r|² ds + 𝔼 ∫_0^T (|δY_s|² + |δZ_s|²_F + ‖δU_s‖²) ds + P)`,

a nondecreasing and finite function of `t`. Step 4 inserts (4.25) in (4.24),

`𝔼 e^{κt} |δY_t|² + 𝔼 ∫_t^T e^{κs} ((κ − C/ε) |δY_s|² + (1 − ε) (|δZ_s|²_F + ‖δU_s‖²)) ds
  ≤ 𝔼 e^{κT} |λ δg_T + q^g_T|² + (C/ε) 𝔼 ∫_t^T e^{κs} (|δX_s|² + |q^f_s|²) ds`,

takes `ε < 1` and `κ > C/ε`, and obtains at every `t`

`𝔼|δY_t|² + 𝔼 ∫_t^T (|δZ_s|²_F + ‖δU_s‖²) ds
  ≤ C (𝔼|λ δg_T + q^g_T|² + 𝔼 ∫_t^T (|δX_s|² + |q^f_s|²) ds)`;

it bounds the terminal difference by `𝔼|δg_T|² ≤ C 𝔼|δX_T|²` and, after (4.26), writes (4.16)
forward from `δY_0`:

`𝔼 sup_{t ≤ T} |δY_t|² ≤ C (𝔼|δY_0|² + 𝔼 ∫_0^T |λ δf_s + q^f_s|² ds
    + 𝔼 ∫_0^T (|δZ_s|²_F + ‖δU_s‖²) ds)
  ≤ C (𝔼|δY_0|² + 𝔼 ∫_0^T (|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²) ds + P)`.

## Main definitions

* `Dissertation.PaperSpec.A.eq_supE_weighted` — the weighted inequality in the proof of Lemma 4.1.
* `Dissertation.PaperSpec.A.eq_coeffdiff_ae` — the bound before (4.9), at almost every time.
* `Dissertation.PaperSpec.A.eq_bwddiff_identity` — the backward difference before (4.12).
* `Dissertation.PaperSpec.A.eq_contract_half` — `λ_*` and the contraction by `1/2`.
* `Dissertation.PaperSpec.A.eq_fwd_chain` — the chain before (4.23), at every time.
* `Dissertation.PaperSpec.A.eq_wgt_insert` — (4.25) inserted in (4.24), and the backward bound
  at every time.
* `Dissertation.PaperSpec.A.eq_wgt_terminal` — the terminal bound before (4.26).
* `Dissertation.PaperSpec.A.eq_bwd_chain` — the first two links of the chain before (4.27).
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.WellPosedness.BrownianPoisson Dissertation.Law
  LevyStochCalc

universe u v w

/-- **The weighted inequality in the proof of Lemma 4.1.** Under the hypotheses of Lemma 4.1
(those of `lem_bpbsde`), for every `t ∈ [0, T]`,
`𝔼 e^t |δY_t|² + 𝔼 ∫_t^T e^s (|δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds
  ≤ 𝔼 e^T |δξ|² + 𝔼 ∫_t^T e^s |φ_s|² ds`,
the expectations read in `[0, ∞]`. -/
def eq_supE_weighted : Prop :=
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
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ENNReal.ofReal (Real.exp t) * ∫⁻ ω, esq (fun k => δY k t ω) ∂P
        + ∫⁻ ω, ∫⁻ s in Set.Icc t T, ENNReal.ofReal (Real.exp s) * (∑ k, esq (δZ k s ω)
            + ∑ k, ∫⁻ e, (‖δU k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp T) * ∫⁻ ω, esq (fun k => δξ ω k) ∂P
        + ∫⁻ ω, ∫⁻ s in Set.Icc t T,
          ENNReal.ofReal (Real.exp s) * esq (fun k => φ k ω s) ∂volume ∂P

/-- **The bound before (4.9), at almost every time.** In the standing setting, under the
hypotheses of Lemma 4.2 — `T > 0`, coefficients with (2.3) and Assumptions 2.2–2.3 with constant
`L` and initial datum `ξ₀` — for two trial tuples `Θ¹, Θ²` of `ℍ`, with `S_s` the sum of the norms
of the coefficient differences at `(Θ^k_s, Law(Θ^k_s))`, for almost every `s ∈ [0, T]`,
`𝔼 S_s² ≤ 10 L² 𝔼[|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²_{L²(ν)}]`, read in `[0, ∞]`. -/
def eq_coeffdiff_ae : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ),
    Indep 𝒢₀ (⨆ t, D.filtration t) P →
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d) (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₁ Y₁ Z₁ U₁ → HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₂ Y₂ Z₂ U₂ →
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∫⁻ ω, coeffDiffNorm P C (tupleAt ν X₁ Y₁ Z₁ U₁) (tupleAt ν X₂ Y₂ Z₂ U₂) s ω ^ 2 ∂P
        ≤ ENNReal.ofReal (10 * L ^ 2) * ∫⁻ ω,
          (esq (fun i => X₁ i s ω - X₂ i s ω) + esq (fun k => Y₁ k s ω - Y₂ k s ω)
            + ∑ k, esq (fun j => Z₁ k s ω j - Z₂ k s ω j)
            + ∑ k, ∫⁻ e, (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P

/-- **The backward difference before (4.12).** In the standing setting, under the hypotheses of
Lemma 4.2 — `T > 0`, coefficients with (2.3) and Assumptions 2.2–2.3 with constant `L` and initial
datum `ξ₀` — for `λ ∈ [0, 1]`, a forcing `q` of the class of (4.1), two trial tuples `Θ¹, Θ²` of
`ℍ` and their frozen steps `Θ̄ᵏ = Φ_λ(Θᵏ)` (`FrozenStep`, with the same `λ`, `ξ₀` and `q`), each
coordinate `k` of `(δȲ, δZ̄, δŪ)` solves the linear backward equation (4.4) (`LinearBSDEJ`) with
terminal value `δξ̄ = λ [g(X̄¹_T, Law(X̄¹_T)) − g(X̄²_T, Law(X̄²_T))]` and drift `φ_s = λ δf_s`,
`δf_s` the driver difference at `(Θᵏ_s, Law(Θᵏ_s))`: almost surely at each `t ∈ [0, T]`,
`δȲ_t = δξ̄ + ∫_t^T λ δf_s ds − ∫_t^T δZ̄_s dW_s − ∫_t^T ∫_E δŪ_s(e) Ñ(ds, de)`, with `δZ̄`, `δŪ`
and `λ δf` progressive, of finite energy on `[0, T]` and vanishing off it, `δξ̄` square integrable
and `δȲ` adapted with right-continuous paths. -/
def eq_bwddiff_identity : Prop :=
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d) (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
    ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    ∀ (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
      (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb qσ qh qf qg →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₁ Y₁ Z₁ U₁ → HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₂ Y₂ Z₂ U₂ →
    ∀ (X₁' X₂' : Fin n → ℝ → Ω → ℝ) (Y₁' Y₂' : Fin m → ℝ → Ω → ℝ)
      (Z₁' Z₂' : Fin m → ℝ → Ω → Fin d → ℝ) (U₁' U₂' : Fin m → ℝ → Ω → E → ℝ),
    FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₁ Y₁ Z₁ U₁ X₁' Y₁' Z₁' U₁' →
    FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₂ Y₂ Z₂ U₂ X₂' Y₂' Z₂' U₂' →
    ∀ k, LinearBSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T
      (fun ω => lam * (terminalVal P T C X₁' k ω - terminalVal P T C X₂' k ω))
      (fun ω s => lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s))
      (fun t ω => Y₁' k t ω - Y₂' k t ω) (fun s ω j => Z₁' k s ω j - Z₂' k s ω j)
      (fun s ω e => U₁' k s ω e - U₂' k s ω e)

/-- **`λ_*` and the contraction by `1/2`, after (4.13).** There is `c₀ > 0` such that, for every
value `c ≥ c₀` of the constant `c_BDG`: in the standing setting, under the hypotheses of Lemma 4.2
— `T > 0`, coefficients with (2.3) and Assumptions 2.2–2.3 with constant `L` and initial datum
`ξ₀` — with `C_Φ = max{1, C_X + C_Y}` the constant of (4.13) (`L⋆² = 10 L² max{T, 1}`,
`C_X = 3 max{T, c} L⋆²`, `C_BP = 2 e^T (5 + 4c) + 4T`, `C_Y = C_BP (4 L² C_X + L⋆²)`) and
`λ_* = (2 √C_Φ)⁻¹`: `λ_* ∈ (0, 1/2]`; and for every `λ ∈ [0, λ_*]`, `C_Φ λ² ≤ 1/4`, and for a
forcing `q` of the class of (4.1), two trial tuples `Θ¹, Θ²` of `ℍ` and their frozen steps
`Θ̄ᵏ = Φ_λ(Θᵏ)` (`FrozenStep`, with the same `λ`, `ξ₀` and `q`),
`‖Φ_λ(Θ¹) − Φ_λ(Θ²)‖_ℍ ≤ (1/2) ‖Θ¹ − Θ²‖_ℍ`, `‖·‖_ℍ` the square root of `supSize` in
`[0, ∞]`. -/
def eq_contract_half : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L : ℝ) (C : Coeffs ν n m d) (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)),
    JointBorel T C → Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀ →
    Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C →
    ∀ CΦ lamStar : ℝ, CΦ = max 1 (3 * max T c * (10 * L ^ 2 * max T 1)
            + (2 * Real.exp T * (5 + 4 * c) + 4 * T)
              * (4 * L ^ 2 * (3 * max T c * (10 * L ^ 2 * max T 1)) + 10 * L ^ 2 * max T 1)) →
    lamStar = (2 * Real.sqrt CΦ)⁻¹ →
    (0 < lamStar ∧ lamStar ≤ 1 / 2)
    ∧ ∀ lam : ℝ, 0 ≤ lam → lam ≤ lamStar → CΦ * lam ^ 2 ≤ 1 / 4
      ∧ ∀ (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
        (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ),
      PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb qσ qh qf qg →
      ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
        (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
      HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₁ Y₁ Z₁ U₁ → HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X₂ Y₂ Z₂ U₂ →
      ∀ (X₁' X₂' : Fin n → ℝ → Ω → ℝ) (Y₁' Y₂' : Fin m → ℝ → Ω → ℝ)
        (Z₁' Z₂' : Fin m → ℝ → Ω → Fin d → ℝ) (U₁' U₂' : Fin m → ℝ → Ω → E → ℝ),
      FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₁ Y₁ Z₁ U₁ X₁' Y₁' Z₁' U₁' →
      FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X₂ Y₂ Z₂ U₂ X₂' Y₂' Z₂' U₂' →
      supSize P ν T (fun i t ω => X₁' i t ω - X₂' i t ω) (fun k t ω => Y₁' k t ω - Y₂' k t ω)
          (fun k t ω j => Z₁' k t ω j - Z₂' k t ω j) (fun k t ω e => U₁' k t ω e - U₂' k t ω e)
          ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (1 / 2)
          * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
            (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
            ^ (1 / 2 : ℝ)

/-- **The chain before (4.23), at every time.** There are functions `K₁`, `K₂`, `K₃` of
`(T, L, ‖G‖, c_G, α, β₁, β₂)` such that: in the standing setting, under the hypotheses of Lemma 4.3
— `T > 0`, coefficients with (2.3) and Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and
coupling matrix `G`, `λ̲ ∈ (0, 1]`, `λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak`
with `X^k_T ∈ L²`, `ℱ₀`-measurable initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` — for
every `t ∈ [0, T]`,
`𝔼 sup_{s ≤ t} |δX_s|²
  ≤ C₁ (𝔼|δξ₀|² + 𝔼 ∫_0^t (|δb_s|² + |δσ_s|²_F + ‖δh_s‖²_{L²(ν)}) ds + P)
  ≤ C₂ (𝔼|δξ₀|² + 𝔼 ∫_0^t (|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds + P)
  ≤ C₃ (∫_0^t 𝔼 sup_{r ≤ s} |δX_r|² ds
    + 𝔼 ∫_0^T (|δY_s|² + |δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds + P)`,
and `t ↦ 𝔼 sup_{s ≤ t} |δX_s|²` is nondecreasing and finite on `[0, T]`; here
`C_i = K_i(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂)`, `δb_s`, `δσ_s` are the coefficient differences at
`(Θᵏ_s, Law(Θᵏ_s))`, `δh_s = h(s, Θ¹⁻_s, ·, μ¹⁻_s) − h(s, Θ²⁻_s, ·, μ²⁻_s)` is the jump coefficient
difference at the predictable tuples, read through the canonical representative `coeffJump`, `P`
is the data size of (4.14) of the differences of the data, and the expectations are read in
`[0, ∞]`. -/
def eq_fwd_chain : Prop :=
  ∃ K₁ K₂ K₃ : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ lamLow lam : ℝ, 0 < lamLow → lamLow ≤ 1 → lamLow ≤ lam → lam ≤ 1 →
    ∀ (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₁ → Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₂ →
    ∀ (qb₁ qb₂ : Fin n → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ)
      (qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ) (qf₁ qf₂ : Fin m → Ω → ℝ → ℝ)
      (qg₁ qg₂ : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₁ qσ₁ qh₁ qf₁ qg₁ →
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₂ qσ₂ qh₂ qf₂ qg₂ →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ →
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤ →
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) t, esq (fun i => X₁ i s ω - X₂ i s ω)) ∂P
          ≤ ENNReal.ofReal (K₁ T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
            * (∫⁻ ω, esq (fun i => ξ₁ ω i - ξ₂ ω i) ∂P
              + (∑ i, Brownian.Ito.energy P t (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
                  - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
                + ∑ i, ∑ j, Brownian.Ito.energy P t (fun ω s =>
                  diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
                    - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
                + ∑ i, Poisson.Compensated.markedEnergy P ν t (fun ω s e =>
                  jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i s ω e
                    - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e))
              + dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
              (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
              (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
              (fun k ω => qg₁ k ω - qg₂ k ω))
        ∧ ENNReal.ofReal (K₁ T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
            * (∫⁻ ω, esq (fun i => ξ₁ ω i - ξ₂ ω i) ∂P
              + (∑ i, Brownian.Ito.energy P t (fun ω s => driftProc P T C X₁ Y₁ Z₁ U₁ i ω s
                  - driftProc P T C X₂ Y₂ Z₂ U₂ i ω s)
                + ∑ i, ∑ j, Brownian.Ito.energy P t (fun ω s =>
                  diffusionProc P T C X₁ Y₁ Z₁ U₁ i s ω j
                    - diffusionProc P T C X₂ Y₂ Z₂ U₂ i s ω j)
                + ∑ i, Poisson.Compensated.markedEnergy P ν t (fun ω s e =>
                  jumpProc T (coeffJump P T C (leftLimProc X₁) (leftLimProc Y₁) Z₁ U₁) i s ω e
                    - jumpProc T (coeffJump P T C (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e))
              + dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
              (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
              (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
              (fun k ω => qg₁ k ω - qg₂ k ω))
          ≤ ENNReal.ofReal (K₂ T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
            * (∫⁻ ω, esq (fun i => ξ₁ ω i - ξ₂ ω i) ∂P
              + (∑ i, Brownian.Ito.energy P t (fun ω s => X₁ i s ω - X₂ i s ω)
                + ∑ k, Brownian.Ito.energy P t (fun ω s => Y₁ k s ω - Y₂ k s ω)
                + ∑ k, ∑ j, Brownian.Ito.energy P t (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
                + ∑ k, Poisson.Compensated.markedEnergy P ν t
                  (fun ω s e => U₁ k s ω e - U₂ k s ω e))
              + dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
              (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
              (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
              (fun k ω => qg₁ k ω - qg₂ k ω))
        ∧ ENNReal.ofReal (K₂ T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
            * (∫⁻ ω, esq (fun i => ξ₁ ω i - ξ₂ ω i) ∂P
              + (∑ i, Brownian.Ito.energy P t (fun ω s => X₁ i s ω - X₂ i s ω)
                + ∑ k, Brownian.Ito.energy P t (fun ω s => Y₁ k s ω - Y₂ k s ω)
                + ∑ k, ∑ j, Brownian.Ito.energy P t (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
                + ∑ k, Poisson.Compensated.markedEnergy P ν t
                  (fun ω s e => U₁ k s ω e - U₂ k s ω e))
              + dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
              (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
              (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
              (fun k ω => qg₁ k ω - qg₂ k ω))
          ≤ ENNReal.ofReal (K₃ T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
            * ((∫⁻ s in Set.Icc (0 : ℝ) t,
                ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) s, esq (fun i => X₁ i r ω - X₂ i r ω)) ∂P)
              + (∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω)
                + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
                + ∑ k, Poisson.Compensated.markedEnergy P ν T
                  (fun ω s e => U₁ k s ω e - U₂ k s ω e))
              + dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
              (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
              (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
              (fun k ω => qg₁ k ω - qg₂ k ω)))
    ∧ MonotoneOn (fun t => ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) t,
        esq (fun i => X₁ i s ω - X₂ i s ω)) ∂P) (Set.Icc (0 : ℝ) T)
    ∧ ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) t, esq (fun i => X₁ i s ω - X₂ i s ω)) ∂P < ⊤

/-- **(4.25) inserted in (4.24), and the backward bound at every time.** There are functions `K`
of `(T, L, ‖G‖, c_G, α, β₁, β₂)` and `K'` of `(ε, κ, T, L, ‖G‖, c_G, α, β₁, β₂)` such that: in the
standing setting, under the hypotheses of Lemma 4.3 — `T > 0`, coefficients with (2.3) and
Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and coupling matrix `G`, `λ̲ ∈ (0, 1]`,
`λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak` with `X^k_T ∈ L²`, `ℱ₀`-measurable
initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` — with `C = K(T, L, ‖G‖, s_min(G)⁻², α, β₁,
β₂)`: for every `ε ∈ (0, 1]`, `κ > 0` and `t ∈ [0, T]`, the functions `|δY_t|²`,
`|λ δg_T + q^g_T|²` (on `Ω`), `e^{κs} ((κ − C/ε) |δY_s|² + (1 − ε) (|δZ_s|²_F + ‖δU_s‖²_{L²(ν)}))`
and `e^{κs} (|δX_s|² + |q^f_s|²)` (on `Ω × [t, T]`) are integrable and
`𝔼 e^{κt} |δY_t|² + 𝔼 ∫_t^T e^{κs} ((κ − C/ε) |δY_s|² + (1 − ε) (|δZ_s|²_F + ‖δU_s‖²_{L²(ν)})) ds
  ≤ 𝔼 e^{κT} |λ δg_T + q^g_T|² + (C/ε) 𝔼 ∫_t^T e^{κs} (|δX_s|² + |q^f_s|²) ds`;
and for every `ε ∈ (0, 1)`, `κ > C/ε` and `t ∈ [0, T]`, the functions
`|δZ_s|²_F + ‖δU_s‖²_{L²(ν)}` and `|δX_s|² + |q^f_s|²` are integrable on `Ω × [t, T]` and
`𝔼|δY_t|² + 𝔼 ∫_t^T (|δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds
  ≤ C' (𝔼|λ δg_T + q^g_T|² + 𝔼 ∫_t^T (|δX_s|² + |q^f_s|²) ds)`
with `C' = K'(ε, κ, T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂)`; here `q = δq`,
`δg_T = g(X¹_T, Law X¹_T) − g(X²_T, Law X²_T)` and `δf_s = f(s, Θ¹_s, μ¹_s) − f(s, Θ²_s, μ²_s)`. -/
def eq_wgt_insert : Prop :=
  ∃ (K : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (K' : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ),
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ lamLow lam : ℝ, 0 < lamLow → lamLow ≤ 1 → lamLow ≤ lam → lam ≤ 1 →
    ∀ (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₁ → Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₂ →
    ∀ (qb₁ qb₂ : Fin n → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ)
      (qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ) (qf₁ qf₂ : Fin m → Ω → ℝ → ℝ)
      (qg₁ qg₂ : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₁ qσ₁ qh₁ qf₁ qg₁ →
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₂ qσ₂ qh₂ qf₂ qg₂ →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ →
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤ →
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ κ : ℝ, 0 < κ → ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun ω => ∑ k, (Y₁ k t ω - Y₂ k t ω) ^ 2) P
      ∧ Integrable (fun ω => ∑ k, (lam * (terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
          + (qg₁ k ω - qg₂ k ω)) ^ 2) P
      ∧ Integrable (fun p : Ω × ℝ => Real.exp (κ * p.2)
          * ((κ - K T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ / ε)
              * ∑ k, (Y₁ k p.2 p.1 - Y₂ k p.2 p.1) ^ 2
            + (1 - ε) * (∑ k, ∑ j, (Z₁ k p.2 p.1 j - Z₂ k p.2 p.1 j) ^ 2
              + ∑ k, ∫ e, (U₁ k p.2 p.1 e - U₂ k p.2 p.1 e) ^ 2 ∂ν)))
        (P.prod (volume.restrict (Set.Icc t T)))
      ∧ Integrable (fun p : Ω × ℝ => Real.exp (κ * p.2)
          * (∑ i, (X₁ i p.2 p.1 - X₂ i p.2 p.1) ^ 2 + ∑ k, (qf₁ k p.1 p.2 - qf₂ k p.1 p.2) ^ 2))
        (P.prod (volume.restrict (Set.Icc t T)))
      ∧ Real.exp (κ * t) * ∫ ω, ∑ k, (Y₁ k t ω - Y₂ k t ω) ^ 2 ∂P
          + ∫ ω, ∫ s in Set.Icc t T, Real.exp (κ * s)
            * ((κ - K T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ / ε)
                * ∑ k, (Y₁ k s ω - Y₂ k s ω) ^ 2
              + (1 - ε) * (∑ k, ∑ j, (Z₁ k s ω j - Z₂ k s ω j) ^ 2
                + ∑ k, ∫ e, (U₁ k s ω e - U₂ k s ω e) ^ 2 ∂ν)) ∂volume ∂P
        ≤ Real.exp (κ * T) * ∫ ω, ∑ k, (lam * (terminalVal P T C X₁ k ω
            - terminalVal P T C X₂ k ω) + (qg₁ k ω - qg₂ k ω)) ^ 2 ∂P
          + K T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ / ε
            * ∫ ω, ∫ s in Set.Icc t T, Real.exp (κ * s)
              * (∑ i, (X₁ i s ω - X₂ i s ω) ^ 2 + ∑ k, (qf₁ k ω s - qf₂ k ω s) ^ 2) ∂volume ∂P)
    ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ κ : ℝ, K T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂ / ε < κ →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun p : Ω × ℝ => ∑ k, ∑ j, (Z₁ k p.2 p.1 j - Z₂ k p.2 p.1 j) ^ 2
          + ∑ k, ∫ e, (U₁ k p.2 p.1 e - U₂ k p.2 p.1 e) ^ 2 ∂ν)
        (P.prod (volume.restrict (Set.Icc t T)))
      ∧ Integrable (fun p : Ω × ℝ => ∑ i, (X₁ i p.2 p.1 - X₂ i p.2 p.1) ^ 2
          + ∑ k, (qf₁ k p.1 p.2 - qf₂ k p.1 p.2) ^ 2)
        (P.prod (volume.restrict (Set.Icc t T)))
      ∧ ∫ ω, ∑ k, (Y₁ k t ω - Y₂ k t ω) ^ 2 ∂P
          + ∫ ω, ∫ s in Set.Icc t T, (∑ k, ∑ j, (Z₁ k s ω j - Z₂ k s ω j) ^ 2
            + ∑ k, ∫ e, (U₁ k s ω e - U₂ k s ω e) ^ 2 ∂ν) ∂volume ∂P
        ≤ K' ε κ T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂
          * (∫ ω, ∑ k, (lam * (terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω)
              + (qg₁ k ω - qg₂ k ω)) ^ 2 ∂P
            + ∫ ω, ∫ s in Set.Icc t T, (∑ i, (X₁ i s ω - X₂ i s ω) ^ 2
              + ∑ k, (qf₁ k ω s - qf₂ k ω s) ^ 2) ∂volume ∂P)

/-- **The terminal bound before (4.26).** There is a function `K` of
`(T, L, ‖G‖, c_G, α, β₁, β₂)` such that: in the standing setting, under the hypotheses of Lemma 4.3
— `T > 0`, coefficients with (2.3) and Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and
coupling matrix `G`, `λ̲ ∈ (0, 1]`, `λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak`
with `X^k_T ∈ L²`, `ℱ₀`-measurable initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` —
`𝔼|δg_T|² ≤ C 𝔼|δX_T|²` with `C = K(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂)`,
`δg_T = g(X¹_T, Law X¹_T) − g(X²_T, Law X²_T)` and `δX_T = X¹_T − X²_T`; the expectations are
read in `[0, ∞]`. -/
def eq_wgt_terminal : Prop :=
  ∃ K : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ lamLow lam : ℝ, 0 < lamLow → lamLow ≤ 1 → lamLow ≤ lam → lam ≤ 1 →
    ∀ (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₁ → Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₂ →
    ∀ (qb₁ qb₂ : Fin n → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ)
      (qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ) (qf₁ qf₂ : Fin m → Ω → ℝ → ℝ)
      (qg₁ qg₂ : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₁ qσ₁ qh₁ qf₁ qg₁ →
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₂ qσ₂ qh₂ qf₂ qg₂ →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ →
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤ →
    ∫⁻ ω, esq (fun k => terminalVal P T C X₁ k ω - terminalVal P T C X₂ k ω) ∂P
      ≤ ENNReal.ofReal (K T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
        * ∫⁻ ω, esq (fun i => X₁ i T ω - X₂ i T ω) ∂P

/-- **The first two links of the chain before (4.27).** There are functions `K₁`, `K₂` of
`(T, L, ‖G‖, c_G, α, β₁, β₂)` such that: in the standing setting, under the hypotheses of Lemma 4.3
— `T > 0`, coefficients with (2.3) and Assumptions 2.3–2.5 with constants `L, α, β₁, β₂` and
coupling matrix `G`, `λ̲ ∈ (0, 1]`, `λ ∈ [λ̲, 1]`, and `Θ¹, Θ²` solving (4.1) at `λ` in `ℍ_weak`
with `X^k_T ∈ L²`, `ℱ₀`-measurable initial data `ξ₀^k`, forcings `q^k` and `Θ¹ − Θ² ∈ ℍ` —
`𝔼 sup_{t ≤ T} |δY_t|² ≤ C₁ (𝔼|δY_0|² + 𝔼 ∫_0^T |λ δf_s + q^f_s|² ds
    + 𝔼 ∫_0^T (|δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds)
  ≤ C₂ (𝔼|δY_0|² + 𝔼 ∫_0^T (|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds + P)`
with `C_i = K_i(T, L, ‖G‖, s_min(G)⁻², α, β₁, β₂)`, `q = δq`, `δf_s` the driver difference at
`(Θᵏ_s, Law(Θᵏ_s))`, `P` the data size of (4.14) of the differences of the data, and the
expectations read in `[0, ∞]`. -/
def eq_bwd_chain : Prop :=
  ∃ K₁ K₂ : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ,
  ∀ {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    (n m d : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P),
    0 < n → 0 < m → 0 < d → ∀ T : ℝ, 0 < T →
    ∀ (L α β₁ β₂ : ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d),
    JointBorel T C → Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C → G.rank = min m n →
    Assumption25 (enlJoint 𝒢₀ D h𝒢₀) P T G α β₁ β₂ C →
    ∀ lamLow lam : ℝ, 0 < lamLow → lamLow ≤ 1 → lamLow ≤ lam → lam ≤ 1 →
    ∀ (ξ₁ ξ₂ : Ω → EuclideanSpace ℝ (Fin n)),
    Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₁ → Measurable[enlJoint 𝒢₀ D h𝒢₀ 0] ξ₂ →
    ∀ (qb₁ qb₂ : Fin n → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ)
      (qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ) (qf₁ qf₂ : Fin m → Ω → ℝ → ℝ)
      (qg₁ qg₂ : Fin m → Ω → ℝ),
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₁ qσ₁ qh₁ qf₁ qg₁ →
    PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb₂ qσ₂ qh₂ qf₂ qg₂ →
    ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ),
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ →
    WeakForcedSolution D h𝒢₀ hind₀ T lam C ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) < ⊤ →
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω)) ∂P
        ≤ ENNReal.ofReal (K₁ T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
          * (∫⁻ ω, esq (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P
            + ∑ k, Brownian.Ito.energy P T (fun ω s => lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
                - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) + (qf₁ k ω s - qf₂ k ω s))
            + ((∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j))
              + ∑ k, Poisson.Compensated.markedEnergy P ν T
                (fun ω s e => U₁ k s ω e - U₂ k s ω e)))
      ∧ ENNReal.ofReal (K₁ T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
          * (∫⁻ ω, esq (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P
            + ∑ k, Brownian.Ito.energy P T (fun ω s => lam * (driverProc P T C X₁ Y₁ Z₁ U₁ k ω s
                - driverProc P T C X₂ Y₂ Z₂ U₂ k ω s) + (qf₁ k ω s - qf₂ k ω s))
            + ((∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j))
              + ∑ k, Poisson.Compensated.markedEnergy P ν T
                (fun ω s e => U₁ k s ω e - U₂ k s ω e)))
        ≤ ENNReal.ofReal (K₂ T L ‖GX G‖ (sMin G ^ 2)⁻¹ α β₁ β₂)
          * (∫⁻ ω, esq (fun k => Y₁ k 0 ω - Y₂ k 0 ω) ∂P
            + (∑ i, Brownian.Ito.energy P T (fun ω s => X₁ i s ω - X₂ i s ω)
              + ∑ k, Brownian.Ito.energy P T (fun ω s => Y₁ k s ω - Y₂ k s ω)
              + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
              + ∑ k, Poisson.Compensated.markedEnergy P ν T
                (fun ω s e => U₁ k s ω e - U₂ k s ω e))
            + dataSize P ν T (fun i ω => ξ₁ ω i - ξ₂ ω i) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
              (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
              (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e) (fun k ω s => qf₁ k ω s - qf₂ k ω s)
              (fun k ω => qg₁ k ω - qg₂ k ω))

end Dissertation.PaperSpec.A
