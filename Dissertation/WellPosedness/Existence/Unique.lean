/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.CoeffBorelW2
import Dissertation.WellPosedness.Existence.Global
import Dissertation.WellPosedness.System.SolvesS2

/-!
# The uniqueness half of `WP(λ)`

The paper calls the forced system (4.1) well posed at `λ`, `WP(λ)`, if it has a unique solution
in `𝕊` for every forcing `q`. `ForcedSolvable` is the existence half; `ForcedUnique` is the
uniqueness half, in the sense of Theorem 3.3: two solutions with the same coefficients, initial
datum and forcing have indistinguishable `X` and `Y` on `[0, T]`, and `Z`, `U` differing by zero
energy. `ForcedWP` is their conjunction.

Stability of the `λ`-system gives uniqueness at `λ`, since two solutions with the same forcing
have zero data difference. It also gives uniqueness at `λ + ζ` once `ζ² K_L C_s ≤ 1/4`, by the
argument of the continuation step. A solution `Θ` of the `(λ + ζ)`-system with forcing `q` is a
solution of the `λ`-system with forcing `q + ζ Ψ(Θ)`, `Ψ(Θ)` the coefficient processes along
`Θ`, which are forcings when `λ + ζ ≠ 0` and `g` is Borel measurable in the state. For two such
solutions `Θ¹, Θ²`, stability at `λ` and the Lipschitz bounds of Assumption 2.3 give

`N ≤ C_s dataSize(ζ Ψ(Θ¹) − ζ Ψ(Θ²)) ≤ ζ² K_L C_s N ≤ N / 4`,   `N = supSize(Θ¹ − Θ²)`,

and `N` is finite since both solutions have finite `𝕊`-norm, so `N = 0`. This is the
contraction argument by which the paper's Lemmas 4.2 and 4.4 identify every solution at
`λ₀ + ζ` with the unique fixed point of `Φ`: at `λ₀ = 0`, with the stability constant `C₀(T)`,
it is the uniqueness half of Lemma 4.2 and uses Assumption 2.3 but no monotonicity; at
`λ₀ ∈ [λ̲, 1]`, with the constant `C_B(λ̲)` of (4.14), it is the uniqueness half of Lemma 4.4.
At `λ + ζ = 0` uniqueness is the stability of the `λ = 0` system.

The existence half of Lemma 4.2 takes the joint Borel measurability (2.3) of the coefficients,
`CoeffBorelW2`, with `P₂(H)` carrying the Hilbert-norm `W₂`; it gives (2.5) along every
progressive tuple, `CoeffRegular`, through `CoeffBorelW2.toCoeffBorel` and
`CoeffBorel.coeffRegular`.

## Main definitions

* `ForcedUnique` — the uniqueness half of `WP(λ)`.
* `ForcedWP` — `WP(λ)`: existence and uniqueness for every forcing.
* `smallCoupling` — the threshold `λ* = 1 / (2 (1 + K_L C₀(T)))` of Lemma 4.2.

## Main statements

* `SolvesForced.eq_of_supSize_sub_eq_zero` — zero `𝕊`-size of the difference is uniqueness in
  the sense of Theorem 3.3.
* `SolvesForced.sub_coeff` — a solution at `λ + ζ` with forcing `q` solves the system at `λ` with
  forcing `q + ζ Ψ(Θ)`.
* `ForcedStable.forcedUnique` — stability gives uniqueness.
* `ForcedStable.forcedUnique_add` — stability at `λ` gives uniqueness at `λ + ζ`.
* `forcedWP_of_sq_le`, `forcedWP_of_le_smallCoupling` — Lemma 4.2: `WP(λ)` for
  `λ ∈ [0, λ*]`.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System LevyStochCalc

universe u v w

/-- **A contraction of a finite quantity vanishes**: `S ≤ c S` with `c < 1` and `S < ∞` forces
`S = 0`. -/
theorem eq_zero_of_le_ofReal_mul {S : ℝ≥0∞} {c : ℝ} (hS : S ≠ ⊤) (hc : c < 1)
    (h : S ≤ ENNReal.ofReal c * S) : S = 0 := by
  by_contra hne
  have hlt : ENNReal.ofReal c * S < 1 * S :=
    ENNReal.mul_lt_mul_left hne hS (ENNReal.ofReal_lt_one.mpr hc)
  rw [one_mul] at hlt
  exact (h.trans_lt hlt).false

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The uniqueness half of `WP(λ)` -/

section Predicates

variable (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ)

/-- **The uniqueness half of `WP(λ)`**: any two solutions of the `λ`-forced system (4.1) with
coefficients `C`, initial datum `ξ₀` and the same forcing coincide: `X¹, X²` and `Y¹, Y²` are
indistinguishable on `[0, T]`, and `𝔼 ∫_0^T |Z¹ − Z²|²_F = 0`, `𝔼 ∫_0^T ‖U¹ − U²‖²_{L²(ν)} = 0`,
coordinatewise. -/
def ForcedUnique (T lam : ℝ) (C : Coeffs ν n m d) (ξ₀ : Fin n → Ω → ℝ) : Prop :=
  ∀ (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ)
    (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ) (X₁ X₂ : Fin n → ℝ → Ω → ℝ)
    (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ) (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ)
    (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ) (γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ),
    SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X₁ Y₁ Z₁ U₁ γ₁ →
    SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X₂ Y₂ Z₂ U₂ γ₂ →
    (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
      ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
      ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
      ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0)

/-- **`WP(λ)`**: for the initial datum `ξ₀`, the `λ`-forced system (4.1) with coefficients `C`
has a solution for every forcing, and any two solutions with the same forcing coincide. -/
def ForcedWP (T lam : ℝ) (C : Coeffs ν n m d) (ξ₀ : Fin n → Ω → ℝ) : Prop :=
  ForcedSolvable D ℱ hℱW hℱN T lam C ξ₀ ∧ ForcedUnique D ℱ hℱW hℱN T lam C ξ₀

end Predicates

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam lam₁ lam₂ ζ L Cs : ℝ}
  {C C₁ C₂ : Coeffs ν n m d} {ξ₀ ξ₁ ξ₂ : Fin n → Ω → ℝ}
  {qb qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf qf₁ qf₂ : Fin m → Ω → ℝ → ℝ}
  {qg qg₁ qg₂ : Fin m → Ω → ℝ}
  {X X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ}

/-- **Zero `𝕊`-size of a difference is uniqueness.** For solutions `Θ¹, Θ²` of the forced system
(4.1), at any parameters and with any coefficients, initial data and forcings, if
`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²) = 0`, then `X¹, X²`
and `Y¹, Y²` are indistinguishable on `[0, T]`, and `δZ`, `δU` have zero energy,
coordinatewise. -/
theorem _root_.Dissertation.WellPosedness.System.SolvesForced.eq_of_supSize_sub_eq_zero
    (h₁ : SolvesForced D ℱ hℱW hℱN T lam₁ C₁ ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : SolvesForced D ℱ hℱW hℱN T lam₂ C₂ ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ X₂ Y₂ Z₂ U₂ γ₂) (hT : 0 ≤ T)
    (h0 : supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
      (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) = 0) :
    (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
      ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
      ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
      ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0) := by
  have hX := fun i => (h₁.fwd i).sub (h₂.fwd i) hT
  have hY := fun k => (h₁.bwd k).sub (h₂.bwd k)
  unfold supSize at h0
  simp only [add_eq_zero, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies] at h0
  obtain ⟨⟨⟨h0X, h0Y⟩, hZ⟩, hU⟩ := h0
  refine ⟨fun i => ?_, fun k => ?_, hZ, hU⟩
  · filter_upwards [ae_forall_eq_zero_of_lintegral_biSup_esq hT
      (fun i t => ((hX i).X_adapted t).mono (ℱ.le t) le_rfl) (fun i => (hX i).X_rightCont) h0X i]
      with ω hω t ht
    exact sub_eq_zero.mp (hω t ht)
  · filter_upwards [ae_forall_eq_zero_of_lintegral_biSup_esq hT
      (fun k t => ((hY k).Y_adapted t).mono (ℱ.le t) le_rfl) (fun k => (hY k).Y_rightCont) h0Y k]
      with ω hω t ht
    exact sub_eq_zero.mp (hω t ht)

/-- **Stability gives uniqueness**: if the `λ`-system is stable with some constant, two
solutions with the same forcing coincide. -/
theorem ForcedStable.forcedUnique (hSt : ForcedStable D ℱ hℱW hℱN T lam C ξ₀ Cs) (hT : 0 ≤ T) :
    ForcedUnique D ℱ hℱW hℱN T lam C ξ₀ := by
  intro qb qσ qh qf qg X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ γ₁ γ₂ h₁ h₂
  have h := hSt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂
  rw [dataSize_sub_self, mul_zero, nonpos_iff_eq_zero] at h
  exact h₁.eq_of_supSize_sub_eq_zero h₂ hT h

/-- **The coefficients move into the forcing**: a solution `Θ` of the `(λ + ζ)`-forced system
(4.1) with forcing `q`, whose coefficient processes `Ψ(Θ)` form a forcing, solves the `λ`-forced
system with forcing `q + ζ Ψ(Θ)`. -/
theorem _root_.Dissertation.WellPosedness.System.SolvesForced.sub_coeff
    (h : SolvesForced D ℱ hℱW hℱN T (lam + ζ) C ξ₀ qb qσ qh qf qg X Y Z U γ)
    (hΨ : Forcing ℱ P ν T (driftProc P T C X Y Z U) (diffusionProc P T C X Y Z U)
      (jumpProc T γ) (driverProc P T C X Y Z U) (terminalVal P T C X)) :
    SolvesForced D ℱ hℱW hℱN T lam C ξ₀
      (fun i ω s => qb i ω s + ζ * driftProc P T C X Y Z U i ω s)
      (fun i s ω j => qσ i s ω j + ζ * diffusionProc P T C X Y Z U i s ω j)
      (fun i s ω e => qh i s ω e + ζ * jumpProc T γ i s ω e)
      (fun k ω s => qf k ω s + ζ * driverProc P T C X Y Z U k ω s)
      (fun k ω => qg k ω + ζ * terminalVal P T C X k ω) X Y Z U γ where
  forcing := h.forcing.add (hΨ.smul ζ)
  jump_rep := h.jump_rep
  fwd i := by
    have e₁ : (fun ω s => lam * driftProc P T C X Y Z U i ω s
          + (qb i ω s + ζ * driftProc P T C X Y Z U i ω s))
        = fun ω s => (lam + ζ) * driftProc P T C X Y Z U i ω s + qb i ω s := by
      funext ω s
      ring
    have e₂ : (fun s ω j => lam * diffusionProc P T C X Y Z U i s ω j
          + (qσ i s ω j + ζ * diffusionProc P T C X Y Z U i s ω j))
        = fun s ω j => (lam + ζ) * diffusionProc P T C X Y Z U i s ω j + qσ i s ω j := by
      funext s ω j
      ring
    have e₃ : (fun s ω e => lam * jumpProc T γ i s ω e + (qh i s ω e + ζ * jumpProc T γ i s ω e))
        = fun s ω e => (lam + ζ) * jumpProc T γ i s ω e + qh i s ω e := by
      funext s ω e
      ring
    rw [e₁, e₂, e₃]
    exact h.fwd i
  bwd k := by
    have e₁ : (fun ω => lam * terminalVal P T C X k ω + (qg k ω + ζ * terminalVal P T C X k ω))
        = fun ω => (lam + ζ) * terminalVal P T C X k ω + qg k ω := by
      funext ω
      ring
    have e₂ : (fun ω s => lam * driverProc P T C X Y Z U k ω s
          + (qf k ω s + ζ * driverProc P T C X Y Z U k ω s))
        = fun ω s => (lam + ζ) * driverProc P T C X Y Z U k ω s + qf k ω s := by
      funext ω s
      ring
    rw [e₁, e₂]
    exact h.bwd k

/-- **Uniqueness along the continuation step.** Let the coefficients satisfy Assumption 2.3
along the diagonal with constant `L`, with `g` Borel measurable in the state, over a filtration
whose null sets lie in its time-`0` field, whose right-continuation is constant before `0` and
which admits a cross witness. If the `λ`-system with initial datum `ξ₀` is stable with constant
`C_s`, then the `(λ + ζ)`-system has at most one solution for every forcing, for every real `ζ`
with `ζ² K_L C_s ≤ 1/4`, `K_L = 10 L² max(T, 1) + 4 L²`. -/
theorem ForcedStable.forcedUnique_add (hSt : ForcedStable D ℱ hℱW hℱN T lam C ξ₀ Cs)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hL : DiagonalLipschitz ℱ P T L C) (hLT : TerminalLipschitz ℱ P T L C.g)
    (hg : ∀ ρ, Measurable fun x => C.g x ρ) (hsmall : ζ ^ 2 * lipConst T L * Cs ≤ 4⁻¹) :
    ForcedUnique D ℱ hℱW hℱN T (lam + ζ) C ξ₀ := by
  by_cases hz : lam + ζ = 0
  · rw [hz]
    exact (forcedStable_zero 𝒲 hℱ0 hnull hT).forcedUnique hT.le
  intro qb qσ qh qf qg X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ γ₁ γ₂ h₁ h₂
  have hΨ₁ := h₁.forcing_coeff hz hg
  have hΨ₂ := h₂.forcing_coeff hz hg
  have hS := hSt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h₁.sub_coeff hΨ₁) (h₂.sub_coeff hΨ₂)
  simp only [add_sub_add_left_eq_sub] at hS
  set N := supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
    (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) with hN
  have hC := h₁.dataSize_smul_coeff_sub_le h₂ hΨ₁ hΨ₂ 𝒲 hℱ0 hnull hT hL hLT (Cs := 1) (Δ := N)
    (by rw [ENNReal.ofReal_one, one_mul]) ζ
  have hK : 0 ≤ ζ ^ 2 * lipConst T L * 1 := by
    have := lipConst_nonneg T L
    positivity
  refine h₁.eq_of_supSize_sub_eq_zero h₂ hT.le
    (eq_zero_of_le_ofReal_mul (c := Cs * (ζ ^ 2 * lipConst T L * 1))
      (h₁.supSize_sub_lt_top h₂ 𝒲 hℱ0 hnull hT).ne (by linarith) ?_)
  calc N ≤ _ := hS
    _ ≤ ENNReal.ofReal Cs * (ENNReal.ofReal (ζ ^ 2 * lipConst T L * 1) * N) := by gcongr
    _ = ENNReal.ofReal (Cs * (ζ ^ 2 * lipConst T L * 1)) * N := by
        rw [ENNReal.ofReal_mul' hK]
        exact (mul_assoc _ _ _).symm

/-! ### Lemma 4.2 -/

variable {cG α β₁ β₂ lamLow : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}

/-- **Lemma 4.2, `WP(λ)` at small coupling.** Over a right-continuous filtration carrying the
driver, whose null sets lie in its time-`0` field, whose right-continuation is constant before
`0`, which admits a cross witness and has the terminal representation property at the horizon
`T > 0`, let the coefficients be jointly Borel measurable on `[0, T] × H × P₂(H)`, (2.3) with the
Hilbert-norm `W₂` on `P₂(H)`, and satisfy Assumption 2.2 and Assumption 2.3 along the diagonal
with constant `L`, with `g` Borel measurable in the state, and let `ξ₀` be square integrable and
`ℱ_0`-measurable. Then for every real `ζ` with
`ζ² K_L C₀(T) ≤ 1/4` the `ζ`-system with initial datum `ξ₀` is well posed: it has a solution for
every forcing, and any two solutions with the same forcing coincide. -/
theorem forcedWP_of_sq_le [ℱ.IsRightContinuous] (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hrep : HasTerminalRep D ℱ hℱW hℱN T) (hT : 0 < T) (hmeas : CoeffBorelW2 T C)
    (horig : CoeffOrigin T C) (hL : DiagonalLipschitz ℱ P T L C)
    (hLT : TerminalLipschitz ℱ P T L C.g) (hg : ∀ ρ, Measurable fun x => C.g x ρ)
    (hξ : ∀ i, MemLp (ξ₀ i) 2 P) (hξm : ∀ i, Measurable[ℱ 0] (ξ₀ i))
    (hsmall : ζ ^ 2 * lipConst T L * zeroConst T ≤ 4⁻¹) :
    ForcedWP D ℱ hℱW hℱN T ζ C ξ₀ :=
  ⟨forcedSolvable_of_sq_le 𝒲 hℱ0 hnull hrep hT (hmeas.toCoeffBorel.coeffRegular ℱ P) horig hL
    hLT hg hξ hξm hsmall, by
    simpa only [zero_add] using
      (forcedStable_zero (C := C) (ξ₀ := ξ₀) 𝒲 hℱ0 hnull hT).forcedUnique_add 𝒲 hℱ0 hnull hT
        hL hLT hg hsmall⟩

/-- The small-coupling threshold `λ* = 1 / (2 (1 + K_L C₀(T)))` of Lemma 4.2, a function of the
horizon `T` and the Lipschitz constant `L` alone. -/
noncomputable def smallCoupling (T L : ℝ) : ℝ := 1 / (2 * (1 + lipConst T L * zeroConst T))

/-- The small-coupling threshold lies in `(0, 1]`. -/
theorem smallCoupling_mem (hT : 0 ≤ T) (L : ℝ) :
    0 < smallCoupling T L ∧ smallCoupling T L ≤ 1 :=
  one_div_two_mul_mem (lipConst_nonneg T L) (zeroConst_pos hT).le

/-- **Lemma 4.2.** Under the hypotheses of `forcedWP_of_sq_le`, `WP(λ)` holds for every
`λ ∈ [0, λ*]`, with `λ* = 1 / (2 (1 + K_L C₀(T))) ∈ (0, 1]` depending only on `T` and `L`. -/
theorem forcedWP_of_le_smallCoupling [ℱ.IsRightContinuous] (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hrep : HasTerminalRep D ℱ hℱW hℱN T) (hT : 0 < T) (hmeas : CoeffBorelW2 T C)
    (horig : CoeffOrigin T C) (hL : DiagonalLipschitz ℱ P T L C)
    (hLT : TerminalLipschitz ℱ P T L C.g) (hg : ∀ ρ, Measurable fun x => C.g x ρ)
    (hξ : ∀ i, MemLp (ξ₀ i) 2 P) (hξm : ∀ i, Measurable[ℱ 0] (ξ₀ i)) (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ smallCoupling T L) :
    ForcedWP D ℱ hℱW hℱN T lam C ξ₀ := by
  refine forcedWP_of_sq_le 𝒲 hℱ0 hnull hrep hT hmeas horig hL hLT hg hξ hξm ?_
  have hK := lipConst_nonneg T L
  have hC₀ := (zeroConst_pos hT.le).le
  refine le_trans ?_ (sq_one_div_two_mul_le hK hC₀)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlam0 hlam 2) hK) hC₀

end Dissertation.WellPosedness.Existence
