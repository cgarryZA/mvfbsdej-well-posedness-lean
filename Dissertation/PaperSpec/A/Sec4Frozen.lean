/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4

/-!
# The frozen step and the coefficient differences in the proof of Lemma 4.2

Statement and equation numbers refer to the well-posedness paper at `1f67672`. The proof of
Lemma 4.2 fixes `λ ∈ [0, 1]` and a forcing `q`, and sends a trial tuple `Θ = (X, Y, Z, U) ∈ 𝕊`,
with `μ_t = Law(Θ_t)` and `μ⁻_t = Law(Θ⁻_t)`, to `Φ_λ(Θ) = Θ̄ = (X̄, Ȳ, Z̄, Ū)`:

`X̄_t = ξ₀ + λ ∫_0^t b(s, Θ_s, μ_s) ds + λ ∫_0^t σ(s, Θ_s, μ_s) dW_s
  + λ ∫_0^t ∫_E h(s, Θ⁻_s, e, μ⁻_s) Ñ(ds, de) + ∫_0^t q^b_s ds + ∫_0^t q^σ_s dW_s
  + ∫_0^t ∫_E q^h_s(e) Ñ(ds, de)`, (4.7)

`Ȳ_t = λ g(X̄_T, Law(X̄_T)) + q^g_T + ∫_t^T (λ f(s, Θ_s, μ_s) + q^f_s) ds − ∫_t^T Z̄_s dW_s
  − ∫_t^T ∫_E Ū_s(e) Ñ(ds, de)`, (4.8)

and, for two trials `Θ¹, Θ²` and `S_s = |δb_s| + |δσ_s|_F + ‖δh_s‖_{L²(ν)} + |δf_s|`,

`𝔼 ∫_0^T S_s² ds ≤ 10 L² 𝔼 ∫_0^T (|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²) ds
  ≤ 10 L² (T 𝔼 sup_{t ≤ T} |δX_t|² + T 𝔼 sup_{t ≤ T} |δY_t|²
    + 𝔼 ∫_0^T (|δZ_s|²_F + ‖δU_s‖²) ds) ≤ L⋆² ‖Θ¹ − Θ²‖²_𝕊`,   `L⋆² = 10 L² max{T, 1}`. (4.9)

## Main definitions

* `Dissertation.PaperSpec.A.HTuple` — a tuple of `𝕊`.
* `Dissertation.PaperSpec.A.FrozenForward` — `X̄` solves (4.7).
* `Dissertation.PaperSpec.A.FrozenStep` — `Θ̄ = Φ_λ(Θ)`: (4.7), (4.8) and `Θ̄ ∈ 𝕊`.
* `Dissertation.PaperSpec.A.coeffDiffNorm` — `S_s`.
* `Dissertation.PaperSpec.A.eq_frozenfwd` — (4.7).
* `Dissertation.PaperSpec.A.eq_frozenbwd` — (4.8).
* `Dissertation.PaperSpec.A.eq_coeffdiff` — (4.9).
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace Dissertation.PaperSpec.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.WellPosedness.BrownianPoisson Dissertation.Law
  LevyStochCalc

universe u v w

section Defs

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {n m d : ℕ}

/-- `Θ = (X, Y, Z, U)` is a tuple of `𝕊` over the filtration `ℱ`: a tuple of `ℍ²`
(`PaperWeakTuple`) every path of whose `X` and `Y` has left limits at every time of `(0, T]`,
with `𝔼 sup_{t ≤ T} |X_t|² < ∞` and `𝔼 sup_{t ≤ T} |Y_t|² < ∞`. -/
def HTuple (ℱ : Filtration ℝ mΩ) (P : Measure Ω) (ν : Measure E) (T : ℝ)
    (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
    (U : Fin m → ℝ → Ω → E → ℝ) : Prop :=
  PaperWeakTuple ℱ P ν T X Y Z U
  ∧ (∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 l))
  ∧ (∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l))
  ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P < ⊤
  ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y k t ω)) ∂P < ⊤

/-- `S_s(ω) = |δb_s| + |δσ_s|_F + ‖δh_s‖_{L²(ν)} + |δf_s|` along two random tuples `Θ¹, Θ²`, with
`δψ_s = ψ(s, Θ¹_s(ω), Law(Θ¹_s)) − ψ(s, Θ²_s(ω), Law(Θ²_s))` for `ψ ∈ {b, σ, h, f}`, in
`[0, ∞]`. -/
noncomputable def coeffDiffNorm (P : Measure Ω) [IsProbabilityMeasure P] (C : Coeffs ν n m d)
    (Θ₁ Θ₂ : ℝ → Ω → TupleH ν n m d) (s : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ‖C.b s (Θ₁ s ω) (lawP2 P (Θ₁ s)) - C.b s (Θ₂ s ω) (lawP2 P (Θ₂ s))‖ₑ
    + ‖C.σ s (Θ₁ s ω) (lawP2 P (Θ₁ s)) - C.σ s (Θ₂ s ω) (lawP2 P (Θ₂ s))‖ₑ
    + ‖C.h s (Θ₁ s ω) (lawP2 P (Θ₁ s)) - C.h s (Θ₂ s ω) (lawP2 P (Θ₂ s))‖ₑ
    + ‖C.f s (Θ₁ s ω) (lawP2 P (Θ₁ s)) - C.f s (Θ₂ s ω) (lawP2 P (Θ₂ s))‖ₑ

/-- `X'` solves the frozen forward equation (4.7) of Lemma 4.2 for the trial `Θ = (X, Y, Z, U)`,
over the filtration of §2: there is a representative `γ` of the jump coefficient at the
predictable tuple, `e ↦ γ_s(ω, e)` equal to `h(s, Θ⁻_s(ω), ·, μ⁻_s)` in `L²(ν)` for almost every
`s ∈ [0, T]`, almost surely, with which each coordinate satisfies, almost surely at every
`t ∈ [0, T]`,
`X'_t = ξ₀ + ∫_0^t (λ b(s, Θ_s, μ_s) + q^b_s) ds + ∫_0^t (λ σ(s, Θ_s, μ_s) + q^σ_s) dW_s
  + ∫_0^t ∫_E (λ γ_s(e) + q^h_s(e)) Ñ(ds, de)`,
with `X'` adapted with right-continuous paths and the integrands meeting the conditions of the
integrals (`LinearFSDEJ`). -/
def FrozenForward {P : Measure Ω} [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T lam : ℝ) (C : Coeffs ν n m d)
    (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)) (qb : Fin n → Ω → ℝ → ℝ)
    (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ) (X : Fin n → ℝ → Ω → ℝ)
    (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (X' : Fin n → ℝ → Ω → ℝ) : Prop :=
  ∃ γ : Fin n → ℝ → Ω → E → ℝ,
    (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      (fun e => (WithLp.toLp 2 fun i => γ i s ω e : EuclideanSpace ℝ (Fin n)))
        =ᵐ[ν] C.h s (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
          (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)))
    ∧ ∀ i, LinearFSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T (fun ω => ξ₀ ω i)
      (fun ω s => lam * driftProc P T C X Y Z U i ω s + qb i ω s) (X' i)
      (fun s ω j => lam * diffusionProc P T C X Y Z U i s ω j + qσ i s ω j)
      (fun s ω e => lam * jumpProc T γ i s ω e + qh i s ω e)

/-- The frozen step `Φ_λ(Θ) = Θ̄` of Lemma 4.2 for the trial `Θ = (X, Y, Z, U)`, over the
filtration of §2: `X'` solves (4.7) (`FrozenForward`); each coordinate of `(Y', Z', U')` solves
(4.8), `Y'_t = λ g(X'_T, Law(X'_T)) + q^g_T + ∫_t^T (λ f(s, Θ_s, μ_s) + q^f_s) ds
− ∫_t^T Z'_s dW_s − ∫_t^T ∫_E U'_s(e) Ñ(ds, de)` almost surely at every `t ∈ [0, T]`
(`LinearBSDEJ`); and `Θ̄ = (X', Y', Z', U')` is a tuple of `𝕊`. -/
def FrozenStep {P : Measure Ω} [IsProbabilityMeasure P]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (T lam : ℝ) (C : Coeffs ν n m d)
    (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)) (qb : Fin n → Ω → ℝ → ℝ)
    (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ) (qf : Fin m → Ω → ℝ → ℝ)
    (qg : Fin m → Ω → ℝ) (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ)
    (Z' : Fin m → ℝ → Ω → Fin d → ℝ) (U' : Fin m → ℝ → Ω → E → ℝ) : Prop :=
  FrozenForward D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh X Y Z U X'
  ∧ (∀ k, LinearBSDEJ D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T
      (fun ω => lam * terminalVal P T C X' k ω + qg k ω)
      (fun ω s => lam * driverProc P T C X Y Z U k ω s + qf k ω s) (Y' k) (Z' k) (U' k))
  ∧ HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X' Y' Z' U'

end Defs

/-- **(4.7).** In the standing setting, under the hypotheses of Lemma 4.2 — `T > 0`, coefficients
with (2.3) and Assumptions 2.2–2.3 with constant `L` and initial datum `ξ₀` — for `λ ∈ [0, 1]`, a
forcing `q` of the class of (4.1) and a trial tuple `Θ = (X, Y, Z, U)` of `𝕊`, with
`μ_s = Law(Θ_s)`: `𝔼 ∫_0^T |ψ(s, Θ_s, μ_s)|² ds < ∞` for `ψ ∈ {b, σ, h}`, in the norms of
Assumption 2.3; (4.7) has a solution `X̄ ∈ S²(0, T; ℝⁿ)`, adapted with every path right-continuous
with left limits on `(0, T]` and `𝔼 sup_{t ≤ T} |X̄_t|² < ∞`; and any two solutions of (4.7) are
indistinguishable on `[0, T]`. The expectations are read in `[0, ∞]`. -/
def eq_frozenfwd : Prop :=
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
    ∀ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
      (U : Fin m → ℝ → Ω → E → ℝ),
    HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X Y Z U →
    (∫⁻ s in Set.Icc (0 : ℝ) T,
        ∫⁻ ω, ‖C.b s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))‖ₑ ^ 2 ∂P < ⊤)
    ∧ (∫⁻ s in Set.Icc (0 : ℝ) T,
        ∫⁻ ω, ‖C.σ s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))‖ₑ ^ 2 ∂P < ⊤)
    ∧ (∫⁻ s in Set.Icc (0 : ℝ) T,
        ∫⁻ ω, ‖C.h s (tupleAt ν X Y Z U s ω) (lawP2 P (tupleAt ν X Y Z U s))‖ₑ ^ 2 ∂P < ⊤)
    ∧ (∃ X' : Fin n → ℝ → Ω → ℝ, FrozenForward D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh X Y Z U X'
        ∧ (∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X' i s ω) (𝓝[<] t) (𝓝 l))
        ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X' i t ω)) ∂P < ⊤)
    ∧ ∀ X₁' X₂' : Fin n → ℝ → Ω → ℝ,
      FrozenForward D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh X Y Z U X₁' →
      FrozenForward D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh X Y Z U X₂' →
      ∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁' i t ω = X₂' i t ω

/-- **(4.8).** In the standing setting, under the hypotheses of Lemma 4.2 — `T > 0`, coefficients
with (2.3) and Assumptions 2.2–2.3 with constant `L` and initial datum `ξ₀` — for `λ ∈ [0, 1]`, a
forcing `q` of the class of (4.1) and a trial tuple `Θ = (X, Y, Z, U)` of `𝕊`, with
`μ_s = Law(Θ_s)`: for every solution `X̄` of (4.7), each coordinate of
`Ξ = λ g(X̄_T, Law(X̄_T)) + q^g_T + ∫_0^T (λ f(s, Θ_s, μ_s) + q^f_s) ds` is `ℱ_T`-measurable and
square integrable; there is `Θ̄ = (X̄, Ȳ, Z̄, Ū)` with `X̄` solving (4.7), `(Ȳ, Z̄, Ū)` solving
(4.8) and `Θ̄ ∈ 𝕊` (`FrozenStep`); and any two such `Θ̄` are equal in `𝕊`: their `X̄` and their
`Ȳ` are indistinguishable on `[0, T]`, and the differences of their `Z̄` and of their `Ū` have zero
energy on `[0, T]`. -/
def eq_frozenbwd : Prop :=
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
    ∀ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
      (U : Fin m → ℝ → Ω → E → ℝ),
    HTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X Y Z U →
    (∀ X' : Fin n → ℝ → Ω → ℝ, FrozenForward D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh X Y Z U X' →
      ∀ k, StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ T] (fun ω => lam * terminalVal P T C X' k ω
          + qg k ω + ∫ s in Set.Icc (0 : ℝ) T, (lam * driverProc P T C X Y Z U k ω s + qf k ω s))
        ∧ MemLp (fun ω => lam * terminalVal P T C X' k ω + qg k ω
          + ∫ s in Set.Icc (0 : ℝ) T, (lam * driverProc P T C X Y Z U k ω s + qf k ω s)) 2 P)
    ∧ (∃ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ) (Z' : Fin m → ℝ → Ω → Fin d → ℝ)
        (U' : Fin m → ℝ → Ω → E → ℝ),
        FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X Y Z U X' Y' Z' U')
    ∧ ∀ (X₁' X₂' : Fin n → ℝ → Ω → ℝ) (Y₁' Y₂' : Fin m → ℝ → Ω → ℝ)
      (Z₁' Z₂' : Fin m → ℝ → Ω → Fin d → ℝ) (U₁' U₂' : Fin m → ℝ → Ω → E → ℝ),
      FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X Y Z U X₁' Y₁' Z₁' U₁' →
      FrozenStep D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh qf qg X Y Z U X₂' Y₂' Z₂' U₂' →
      (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁' i t ω = X₂' i t ω)
      ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁' k t ω = Y₂' k t ω)
      ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁' k s ω j - Z₂' k s ω j) = 0)
      ∧ ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁' k s ω e - U₂' k s ω e) = 0

/-- **(4.9).** In the standing setting, under the hypotheses of Lemma 4.2 — `T > 0`, coefficients
with (2.3) and Assumptions 2.2–2.3 with constant `L` and initial datum `ξ₀` — for two trial tuples
`Θ¹, Θ²` of `𝕊`, with `S_s` the sum of the norms of the coefficient differences at
`(Θ^k_s, Law(Θ^k_s))`,
`𝔼 ∫_0^T S_s² ds ≤ 10 L² 𝔼 ∫_0^T (|δX_s|² + |δY_s|² + |δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds
  ≤ 10 L² (T 𝔼 sup_{t ≤ T} |δX_t|² + T 𝔼 sup_{t ≤ T} |δY_t|²
    + 𝔼 ∫_0^T (|δZ_s|²_F + ‖δU_s‖²_{L²(ν)}) ds) ≤ 10 L² max{T, 1} ‖Θ¹ − Θ²‖²_𝕊`,
read in `[0, ∞]`. -/
def eq_coeffdiff : Prop :=
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
    (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω,
        coeffDiffNorm P C (tupleAt ν X₁ Y₁ Z₁ U₁) (tupleAt ν X₂ Y₂ Z₂ U₂) s ω ^ 2 ∂P
      ≤ ENNReal.ofReal (10 * L ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω,
        (esq (fun i => X₁ i s ω - X₂ i s ω) + esq (fun k => Y₁ k s ω - Y₂ k s ω)
          + ∑ k, esq (fun j => Z₁ k s ω j - Z₂ k s ω j)
          + ∑ k, ∫⁻ e, (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P)
    ∧ (ENNReal.ofReal (10 * L ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω,
        (esq (fun i => X₁ i s ω - X₂ i s ω) + esq (fun k => Y₁ k s ω - Y₂ k s ω)
          + ∑ k, esq (fun j => Z₁ k s ω j - Z₂ k s ω j)
          + ∑ k, ∫⁻ e, (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P
      ≤ ENNReal.ofReal (10 * L ^ 2)
        * (ENNReal.ofReal T * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁ i t ω - X₂ i t ω)) ∂P
          + ENNReal.ofReal T
            * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω)) ∂P
          + ((∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j))
            + ∑ k, Poisson.Compensated.markedEnergy P ν T
              (fun ω s e => U₁ k s ω e - U₂ k s ω e))))
    ∧ ENNReal.ofReal (10 * L ^ 2)
        * (ENNReal.ofReal T * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁ i t ω - X₂ i t ω)) ∂P
          + ENNReal.ofReal T
            * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω)) ∂P
          + ((∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j))
            + ∑ k, Poisson.Compensated.markedEnergy P ν T
              (fun ω s e => U₁ k s ω e - U₂ k s ω e)))
      ≤ ENNReal.ofReal (10 * L ^ 2 * max T 1)
        * supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
          (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)

end Dissertation.PaperSpec.A
