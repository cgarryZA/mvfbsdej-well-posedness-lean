/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.Congr
import Dissertation.WellPosedness.Existence.Contraction
import Dissertation.WellPosedness.Existence.Iterates

/-!
# The continuation step

The step of the continuation argument behind Lemmas 4.2 and 4.4 of the well-posedness paper. Fix
`λ₀`, a real `ζ`, an initial datum `ξ₀` and a forcing `q`. Suppose that the `λ₀`-forced system
(4.1) has a solution `Θ(F)` for every forcing `q + F`, that it is stable with constant `C_s`,
`supSize(Θ¹ − Θ²) ≤ C_s dataSize(q¹ − q²)`, and that the coefficient processes `Ψ(Θ)` along its
solutions are forcings. The map `Φ(F) = ζ Ψ(Θ(F))` on forcings then satisfies, by the expected
Lipschitz bounds of Assumption 2.3,

`dataSize(Φ F − Φ F') ≤ ζ² K_L C_s dataSize(F − F')`,   `K_L = 10 L² max(T, 1) + 4 L²`,

a contraction by `1/4` once `ζ² K_L C_s ≤ 1/4`. Its iterates from `0` are Cauchy for the data
size and converge to a forcing `F*`, and `dataSize(Φ F* − F*) = 0`. The solution `Θ* = Θ(F*)` of
the `λ₀`-system with forcing `q + F*` is then a solution with forcing `q + ζ Ψ(Θ*)`, since the
two forcings differ by zero data size, and

`λ₀ ψ(Θ*) + q^ψ + ζ ψ(Θ*) = (λ₀ + ζ) ψ(Θ*) + q^ψ`,

so `Θ*` solves the `(λ₀ + ζ)`-system with forcing `q`. The fixed point is taken on the space of
forcings, which is complete, not on a space of solutions: the solution at the limit forcing is
produced by the solvability at `λ₀`. The solvability is the existence half of `WP(λ)`;
uniqueness follows from the stability estimate.

## Main definitions

* `ForcedSolvable` — the `λ`-system has a solution for every forcing.
* `ForcedStable` — the `λ`-system is stable with constant `C_s`.
* `CoeffForcingAlong` — the coefficient processes along the solutions of the `λ`-system are
  forcings.

## Main statements

* `SolvesForced.add_coeff` — a solution with forcing `q + ζ Ψ(Θ)` at `λ` solves the system at
  `λ + ζ` with forcing `q`.
* `ForcedSolvable.add` — the continuation step.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### Solvability, stability and the coefficient forcings -/

section Predicates

variable (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ)

/-- **The existence half of `WP(λ)`**: for the initial datum `ξ₀`, the `λ`-forced system (4.1)
with coefficients `C` has a solution for every forcing. -/
def ForcedSolvable (T lam : ℝ) (C : Coeffs ν n m d) (ξ₀ : Fin n → Ω → ℝ) : Prop :=
  ∀ (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
    (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ), Forcing ℱ P ν T qb qσ qh qf qg →
    ∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
      (U : Fin m → ℝ → Ω → E → ℝ) (γ : Fin n → ℝ → Ω → E → ℝ),
      SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ

/-- **Stability of the `λ`-system with constant `C_s`**: two solutions `Θ¹, Θ²` of the
`λ`-forced system (4.1) with coefficients `C` and initial datum `ξ₀`, for forcings `q¹, q²`,
satisfy `supSize(Θ¹ − Θ²) ≤ C_s dataSize(q¹ − q²)`, the data size with zero initial datum. -/
def ForcedStable (T lam : ℝ) (C : Coeffs ν n m d) (ξ₀ : Fin n → Ω → ℝ) (Cs : ℝ) : Prop :=
  ∀ (qb₁ qb₂ : Fin n → Ω → ℝ → ℝ) (qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ)
    (qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ) (qf₁ qf₂ : Fin m → Ω → ℝ → ℝ) (qg₁ qg₂ : Fin m → Ω → ℝ)
    (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
    (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ)
    (γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ),
    SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁ →
    SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂ →
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      ≤ ENNReal.ofReal Cs * dataSize P ν T 0 (fun i ω s => qb₁ i ω s - qb₂ i ω s)
          (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
          (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω)

/-- **The coefficient processes along the solutions of the `λ`-system are forcings**: every
solution `Θ = (X, Y, Z, U)` of the `λ`-forced system (4.1) with coefficients `C` and initial
datum `ξ₀` is a solution with a representative `γ'` of the jump coefficient for which
`(b(s, Θ_s, μ_s), σ(s, Θ_s, μ_s), γ', f(s, Θ_s, μ_s), g(X_T, Law X_T))` is a forcing. -/
def CoeffForcingAlong (T lam : ℝ) (C : Coeffs ν n m d) (ξ₀ : Fin n → Ω → ℝ) : Prop :=
  ∀ (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
    (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ) (X : Fin n → ℝ → Ω → ℝ)
    (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ)
    (γ : Fin n → ℝ → Ω → E → ℝ),
    SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ →
    ∃ γ' : Fin n → ℝ → Ω → E → ℝ, SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ'
      ∧ Forcing ℱ P ν T (driftProc P T C X Y Z U) (diffusionProc P T C X Y Z U) (jumpProc T γ')
        (driverProc P T C X Y Z U) (terminalVal P T C X)

end Predicates

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam ζ L Cs : ℝ}
  {C : Coeffs ν n m d} {ξ₀ : Fin n → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-! ### The continuation step -/

/-- **A forcing along the solution moves into the coefficients**: a solution `Θ` of the
`λ`-forced system (4.1) with forcing `q + ζ Ψ(Θ)`, `Ψ(Θ)` the coefficient processes along `Θ`
itself, solves the `(λ + ζ)`-forced system with forcing `q`. -/
theorem _root_.Dissertation.WellPosedness.System.SolvesForced.add_coeff
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀
      (fun i ω s => qb i ω s + ζ * driftProc P T C X Y Z U i ω s)
      (fun i s ω j => qσ i s ω j + ζ * diffusionProc P T C X Y Z U i s ω j)
      (fun i s ω e => qh i s ω e + ζ * jumpProc T γ i s ω e)
      (fun k ω s => qf k ω s + ζ * driverProc P T C X Y Z U k ω s)
      (fun k ω => qg k ω + ζ * terminalVal P T C X k ω) X Y Z U γ)
    (hq : Forcing ℱ P ν T qb qσ qh qf qg) :
    SolvesForced D ℱ hℱW hℱN T (lam + ζ) C ξ₀ qb qσ qh qf qg X Y Z U γ where
  forcing := hq
  jump_rep := h.jump_rep
  fwd i := by
    have e₁ : (fun ω s => (lam + ζ) * driftProc P T C X Y Z U i ω s + qb i ω s)
        = fun ω s => lam * driftProc P T C X Y Z U i ω s
          + (qb i ω s + ζ * driftProc P T C X Y Z U i ω s) := by
      funext ω s
      ring
    have e₂ : (fun s ω j => (lam + ζ) * diffusionProc P T C X Y Z U i s ω j + qσ i s ω j)
        = fun s ω j => lam * diffusionProc P T C X Y Z U i s ω j
          + (qσ i s ω j + ζ * diffusionProc P T C X Y Z U i s ω j) := by
      funext s ω j
      ring
    have e₃ : (fun s ω e => (lam + ζ) * jumpProc T γ i s ω e + qh i s ω e)
        = fun s ω e => lam * jumpProc T γ i s ω e + (qh i s ω e + ζ * jumpProc T γ i s ω e) := by
      funext s ω e
      ring
    rw [e₁, e₂, e₃]
    exact h.fwd i
  bwd k := by
    have e₁ : (fun ω => (lam + ζ) * terminalVal P T C X k ω + qg k ω)
        = fun ω => lam * terminalVal P T C X k ω + (qg k ω + ζ * terminalVal P T C X k ω) := by
      funext ω
      ring
    have e₂ : (fun ω s => (lam + ζ) * driverProc P T C X Y Z U k ω s + qf k ω s)
        = fun ω s => lam * driverProc P T C X Y Z U k ω s
          + (qf k ω s + ζ * driverProc P T C X Y Z U k ω s) := by
      funext ω s
      ring
    rw [e₁, e₂]
    exact h.bwd k

/-- **The continuation step** (Lemma 4.4; Lemma 4.2 at `λ = 0`). Let the coefficients `C` satisfy
Assumption 2.3 along the diagonal with constant `L`, over a filtration whose null sets lie in its
time-`0` field, whose right-continuation is constant before `0` and which admits a cross
witness. If the `λ`-system with initial datum `ξ₀` has a solution for every forcing, is stable
with constant `C_s`, and the coefficient processes along its solutions are forcings, then the
`(λ + ζ)`-system with initial datum `ξ₀` has a solution for every forcing, for every real `ζ`
with `ζ² K_L C_s ≤ 1/4`, `K_L = 10 L² max(T, 1) + 4 L²`. -/
theorem ForcedSolvable.add (hWP : ForcedSolvable D ℱ hℱW hℱN T lam C ξ₀)
    (hΨ : CoeffForcingAlong D ℱ hℱW hℱN T lam C ξ₀)
    (hSt : ForcedStable D ℱ hℱW hℱN T lam C ξ₀ Cs) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g)
    (hsmall : ζ ^ 2 * lipConst T L * Cs ≤ 4⁻¹) :
    ForcedSolvable D ℱ hℱW hℱN T (lam + ζ) C ξ₀ := by
  intro qb qσ qh qf qg hq
  -- a solution `Θ(F)` of the `λ`-system with forcing `q + F`, chosen for every forcing `F`
  have hsel : ∀ F : (Fin n → Ω → ℝ → ℝ) × (Fin n → ℝ → Ω → Fin d → ℝ)
      × (Fin n → ℝ → Ω → E → ℝ) × (Fin m → Ω → ℝ → ℝ) × (Fin m → Ω → ℝ),
      ∃ S : (Fin n → ℝ → Ω → ℝ) × (Fin m → ℝ → Ω → ℝ) × (Fin m → ℝ → Ω → Fin d → ℝ)
          × (Fin m → ℝ → Ω → E → ℝ) × (Fin n → ℝ → Ω → E → ℝ),
        Forcing ℱ P ν T F.1 F.2.1 F.2.2.1 F.2.2.2.1 F.2.2.2.2 →
          SolvesForced D ℱ hℱW hℱN T lam C ξ₀ (fun i ω s => qb i ω s + F.1 i ω s)
              (fun i s ω j => qσ i s ω j + F.2.1 i s ω j)
              (fun i s ω e => qh i s ω e + F.2.2.1 i s ω e)
              (fun k ω s => qf k ω s + F.2.2.2.1 k ω s) (fun k ω => qg k ω + F.2.2.2.2 k ω)
              S.1 S.2.1 S.2.2.1 S.2.2.2.1 S.2.2.2.2
            ∧ Forcing ℱ P ν T (driftProc P T C S.1 S.2.1 S.2.2.1 S.2.2.2.1)
              (diffusionProc P T C S.1 S.2.1 S.2.2.1 S.2.2.2.1) (jumpProc T S.2.2.2.2)
              (driverProc P T C S.1 S.2.1 S.2.2.1 S.2.2.2.1) (terminalVal P T C S.1) := by
    intro F
    by_cases hF : Forcing ℱ P ν T F.1 F.2.1 F.2.2.1 F.2.2.2.1 F.2.2.2.2
    · obtain ⟨X, Y, Z, U, γ, h⟩ := hWP _ _ _ _ _ (hq.add hF)
      obtain ⟨γ', h', hψ⟩ := hΨ _ _ _ _ _ _ _ _ _ _ h
      exact ⟨(X, Y, Z, U, γ'), fun _ => ⟨h', hψ⟩⟩
    · exact ⟨0, fun h => absurd h hF⟩
  choose S hS using hsel
  -- the forcings, the data size of their differences, and the map `F ↦ ζ Ψ(Θ(F))`
  set 𝒮 : Set ((Fin n → Ω → ℝ → ℝ) × (Fin n → ℝ → Ω → Fin d → ℝ)
      × (Fin n → ℝ → Ω → E → ℝ) × (Fin m → Ω → ℝ → ℝ) × (Fin m → Ω → ℝ)) :=
    {F | Forcing ℱ P ν T F.1 F.2.1 F.2.2.1 F.2.2.2.1 F.2.2.2.2} with h𝒮
  set δ : ((Fin n → Ω → ℝ → ℝ) × (Fin n → ℝ → Ω → Fin d → ℝ)
      × (Fin n → ℝ → Ω → E → ℝ) × (Fin m → Ω → ℝ → ℝ) × (Fin m → Ω → ℝ)) →
      ((Fin n → Ω → ℝ → ℝ) × (Fin n → ℝ → Ω → Fin d → ℝ)
      × (Fin n → ℝ → Ω → E → ℝ) × (Fin m → Ω → ℝ → ℝ) × (Fin m → Ω → ℝ)) → ℝ≥0∞ :=
    fun F F' => dataSize P ν T 0 (fun i ω s => F.1 i ω s - F'.1 i ω s)
      (fun i s ω j => F.2.1 i s ω j - F'.2.1 i s ω j)
      (fun i s ω e => F.2.2.1 i s ω e - F'.2.2.1 i s ω e)
      (fun k ω s => F.2.2.2.1 k ω s - F'.2.2.2.1 k ω s)
      (fun k ω => F.2.2.2.2 k ω - F'.2.2.2.2 k ω) with hδ
  set Φ : ((Fin n → Ω → ℝ → ℝ) × (Fin n → ℝ → Ω → Fin d → ℝ)
      × (Fin n → ℝ → Ω → E → ℝ) × (Fin m → Ω → ℝ → ℝ) × (Fin m → Ω → ℝ)) →
      ((Fin n → Ω → ℝ → ℝ) × (Fin n → ℝ → Ω → Fin d → ℝ)
      × (Fin n → ℝ → Ω → E → ℝ) × (Fin m → Ω → ℝ → ℝ) × (Fin m → Ω → ℝ)) :=
    fun F => (fun i ω s => ζ * driftProc P T C (S F).1 (S F).2.1 (S F).2.2.1 (S F).2.2.2.1 i ω s,
      fun i s ω j => ζ * diffusionProc P T C (S F).1 (S F).2.1 (S F).2.2.1 (S F).2.2.2.1 i s ω j,
      fun i s ω e => ζ * jumpProc T (S F).2.2.2.2 i s ω e,
      fun k ω s => ζ * driverProc P T C (S F).1 (S F).2.1 (S F).2.2.1 (S F).2.2.2.1 k ω s,
      fun k ω => ζ * terminalVal P T C (S F).1 k ω) with hΦ
  have hmap : ∀ F ∈ 𝒮, Φ F ∈ 𝒮 := fun F hF => (hS F hF).2.smul ζ
  -- `Φ` contracts the data size by `1/4`
  have h4 : ENNReal.ofReal (ζ ^ 2 * lipConst T L * Cs) ≤ 4⁻¹ := by
    refine (ENNReal.ofReal_le_ofReal hsmall).trans_eq ?_
    rw [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have hc : ∀ F ∈ 𝒮, ∀ F' ∈ 𝒮, δ (Φ F) (Φ F') ≤ 4⁻¹ * δ F F' := by
    intro F hF F' hF'
    have h := (hS F hF).1.dataSize_smul_coeff_sub_le (hS F' hF').1 (hS F hF).2 (hS F' hF').2 𝒲
      hℱ0 hnull hT hL hLT (hSt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hS F hF).1 (hS F' hF').1)
      ζ
    simp only [add_sub_add_left_eq_sub] at h
    exact h.trans (by gcongr)
  -- the data size as a quasi-distance on the forcings
  have hself : ∀ F, δ F F = 0 := fun F => dataSize_sub_self _ _ _ _ _
  have htri : ∀ F ∈ 𝒮, ∀ F' ∈ 𝒮, ∀ F'' ∈ 𝒮, δ F F'' ≤ 2 * δ F F' + 2 * δ F' F'' :=
    fun F hF F' hF' F'' _ => Forcing.dataSize_sub_le hF hF' _ _ _ _ _
  have hsymm : ∀ F F', δ F F' = δ F' F := fun F F' => dataSize_sub_comm _ _ _ _ _ _ _ _ _ _ _
  have h₀ : (0 : (Fin n → Ω → ℝ → ℝ) × (Fin n → ℝ → Ω → Fin d → ℝ)
      × (Fin n → ℝ → Ω → E → ℝ) × (Fin m → Ω → ℝ → ℝ) × (Fin m → Ω → ℝ)) ∈ 𝒮 := Forcing.zero
  have hW : δ (Φ 0) 0 ≠ ⊤ := Forcing.dataSize_ne_top (Forcing.sub (hmap 0 h₀) h₀)
  -- the iterates from `0` converge to a forcing `F*`, and `Φ F*` is at zero distance from it
  obtain ⟨qb', qσ', qh', qf', qg', hF', hlim⟩ := exists_forcing_limit
    (qb := fun a => (Φ^[a] 0).1) (qσ := fun a => (Φ^[a] 0).2.1) (qh := fun a => (Φ^[a] 0).2.2.1)
    (qf := fun a => (Φ^[a] 0).2.2.2.1) (qg := fun a => (Φ^[a] 0).2.2.2.2)
    (fun a => iterate_mem hmap h₀ a) (exists_dist_iterate_lt hmap hc hself htri hsymm h₀ hW)
  have hF'm : (qb', qσ', qh', qf', qg') ∈ 𝒮 := hF'
  have hfix := dist_map_eq_zero_of_tendsto hmap hc htri hsymm h₀ hF'm hlim
  -- the solution at `q + F*` solves the system with forcing `q + ζ Ψ`, hence at `λ + ζ`
  have h0 := (hsymm (qb', qσ', qh', qf', qg') (Φ (qb', qσ', qh', qf', qg'))).trans hfix
  have hsol := (hS _ hF'm).1.congr_of_dataSize (δξ := 0) (Forcing.add hq (hmap _ hF'm)) (by
    simp only [add_sub_add_left_eq_sub]
    exact h0)
  exact ⟨_, _, _, _, _, hsol.add_coeff hq⟩

end Dissertation.WellPosedness.Existence
