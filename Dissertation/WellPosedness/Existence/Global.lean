/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.Continuation
import Dissertation.WellPosedness.System.Uniqueness

/-!
# Theorem 3.5: global well-posedness

Theorem 3.5 of the well-posedness paper: for every horizon `T > 0`, under Assumptions 2.2–2.5
the system (1.1) has a solution, unique by Theorem 3.3. The proof of §4.6 is a monotone
continuation in `λ ∈ [0, 1]`. By Lemma 4.2, `WP(λ)` holds for `λ ∈ [0, λ*]`; by Lemma 4.4, with an
increment `ζ₀ > 0` depending on `λ*` but not on the base point, `WP(λ₀)` passes to `WP(λ₀ + ζ)`
for every `λ₀ ∈ [λ*, 1]` and `ζ ∈ [0, ζ₀]`. Along `λ_k = min(λ* + k ζ₀, 1)` this reaches `WP(1)`
in finitely many steps, and `WP(1)` with zero forcing is a solution of (1.1).

The two increments are chosen without square roots: for `K = K_L ≥ 0` and `C > 0`,
`ζ = 1 / (2 (1 + K C))` satisfies `ζ² K C ≤ 1/4` and `ζ ≤ 1/2`. With `C = C₀(T)` this is `λ*`,
and with `C = C_B(λ*)`, the constant of (4.14) at `λ̲ = λ*`, it is `ζ₀`.

The solutions are those of `Solves` over a filtration carrying the driver whose null sets lie in
its time-`0` field, whose right-continuation is constant before `0`, which admits a cross witness
and which has the terminal representation property at the horizon; the coefficients satisfy
(2.5) along every progressive tuple (`CoeffRegular`) and `g` is Borel measurable in the state.
The joint measurability (2.3) of the coefficients, with the evaluation σ-algebra on `P₂(H)`,
gives (2.5) along every progressive tuple (`CoeffBorel.coeffRegular`).
The continuous dependence on the coefficients and data, (3.1) of Theorem 3.1, is
`Solves.supSize_sub_le`.

## Main statements

* `continuation_to_one` — a property holding at `λ̲ ≤ 1` and passing from every `λ ∈ [λ̲, 1]` to
  `λ + ζ`, `0 ≤ ζ ≤ ζ₀`, holds at `1`.
* `forcedSolvable_one` — `WP(1)`: the forced system at `λ = 1` has a solution for every forcing.
* `exists_solves` — Theorem 3.5, existence.
* `exists_solves_and_uniqueness` — Theorem 3.5: existence, and uniqueness in the sense of
  Theorem 3.3.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System LevyStochCalc

universe u v w

/-! ### Continuation on the reals -/

/-- **Continuation by bounded increments.** Let `p` hold at `λ̲ ≤ 1` and pass from every
`λ ∈ [λ̲, 1]` to `λ + ζ` for every `ζ ∈ [0, ζ₀]`, `ζ₀ > 0`. Then `p` holds at `1`: it holds along
`λ_k = min(λ̲ + k ζ₀, 1)`, and `λ_k = 1` once `k ζ₀ ≥ 1 − λ̲`. -/
theorem continuation_to_one {p : ℝ → Prop} {lamLow ζ₀ : ℝ} (hζ₀ : 0 < ζ₀) (hlow1 : lamLow ≤ 1)
    (h0 : p lamLow)
    (hstep : ∀ lam, lamLow ≤ lam → lam ≤ 1 → ∀ ζ, 0 ≤ ζ → ζ ≤ ζ₀ → p lam → p (lam + ζ)) :
    p 1 := by
  have hk : ∀ k : ℕ, p (min (lamLow + k * ζ₀) 1) := by
    intro k
    induction k with
    | zero => simpa [min_eq_left hlow1] using h0
    | succ k ih =>
      have hk0 : (0 : ℝ) ≤ k * ζ₀ := mul_nonneg k.cast_nonneg hζ₀.le
      have e : lamLow + ((k + 1 : ℕ) : ℝ) * ζ₀ = lamLow + k * ζ₀ + ζ₀ := by
        push_cast
        ring
      rw [e]
      have h := hstep (min (lamLow + k * ζ₀) 1) (le_min (by linarith) hlow1) (min_le_right _ _)
        (min (lamLow + k * ζ₀ + ζ₀) 1 - min (lamLow + k * ζ₀) 1)
        (sub_nonneg.mpr (min_le_min (by linarith) le_rfl))
        (by simp only [min_def]; split_ifs <;> linarith) ih
      rwa [add_sub_cancel] at h
  obtain ⟨k, hk'⟩ := exists_nat_ge ((1 - lamLow) / ζ₀)
  have h1 : 1 ≤ lamLow + k * ζ₀ := by
    rw [div_le_iff₀ hζ₀] at hk'
    linarith
  simpa [min_eq_right h1] using hk k

/-- `ζ = 1 / (2 (1 + K C))` satisfies `ζ² K C ≤ 1/4` for `K, C ≥ 0`. -/
theorem sq_one_div_two_mul_le {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    (1 / (2 * (1 + K * C))) ^ 2 * K * C ≤ 4⁻¹ := by
  have hx : 0 ≤ K * C := mul_nonneg hK hC
  have e : (1 / (2 * (1 + K * C))) ^ 2 * K * C = K * C / (4 * (1 + K * C) ^ 2) := by
    field_simp
    ring
  rw [e, div_le_iff₀ (by positivity)]
  nlinarith

/-- `ζ = 1 / (2 (1 + K C))` lies in `(0, 1]` for `K, C ≥ 0`. -/
theorem one_div_two_mul_mem {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) :
    0 < 1 / (2 * (1 + K * C)) ∧ 1 / (2 * (1 + K * C)) ≤ 1 := by
  have hx : 0 ≤ K * C := mul_nonneg hK hC
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  linarith

/-! ### `WP(1)` and Theorem 3.5 -/

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T L cG α β₁ β₂ : ℝ}
  {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d} {ξ₀ : Fin n → Ω → ℝ}

/-- **`WP(1)`, the existence half.** Over a right-continuous filtration carrying the driver,
whose null sets lie in its time-`0` field, whose right-continuation is constant before `0`,
which admits a cross witness and has the terminal representation property at the horizon
`T > 0`, let the coefficients have (2.5) along every progressive tuple, satisfy Assumption 2.2,
Assumption 2.3 along the diagonal with constant `L` and `g` Borel measurable in the state,
Assumption 2.4 with coupling matrix `G` and constant `c_G ≥ 0` and Assumption 2.5 along the
diagonal with admissible constants `α, β₁, β₂`, and let `ξ₀` be square integrable and
`ℱ_0`-measurable. Then the forced system (4.1) at `λ = 1` with initial datum `ξ₀` has a solution
for every forcing. -/
theorem forcedSolvable_one [ℱ.IsRightContinuous] (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hrep : HasTerminalRep D ℱ hℱW hℱN T) (hT : 0 < T) (hreg : CoeffRegular ℱ P T C)
    (horig : CoeffOrigin T C) (hL : DiagonalLipschitz ℱ P T L C)
    (hLT : TerminalLipschitz ℱ P T L C.g) (hg : ∀ ρ, Measurable fun x => C.g x ρ) (hcG : 0 ≤ cG)
    (hGf : n ≤ m → GCoerciveForward (GX G) cG) (hGb : m ≤ n → GCoerciveBackward (GX G) cG)
    (hconst : Constants n m α β₁ β₂) (hM : DiagonalMonotone ℱ P T G β₁ β₂ C)
    (hMT : TerminalMonotone ℱ P T G α C.g) (hξ : ∀ i, MemLp (ξ₀ i) 2 P)
    (hξm : ∀ i, Measurable[ℱ 0] (ξ₀ i)) :
    ForcedSolvable D ℱ hℱW hℱN T 1 C ξ₀ := by
  have hK : 0 ≤ lipConst T L := lipConst_nonneg T L
  have hC₀ : 0 ≤ zeroConst T := (zeroConst_pos hT.le).le
  obtain ⟨hpos, hle1⟩ := one_div_two_mul_mem hK hC₀
  have hCB : 0 ≤ aprioriConst T (10 * L ^ 2) (4 * L ^ 2) ‖GX G‖ cG α β₁ β₂
      (1 / (2 * (1 + lipConst T L * zeroConst T))) :=
    (aprioriConst_pos hT.le (by positivity) (by positivity) hcG hconst.α_nonneg
      hconst.β₁_nonneg hconst.β₂_nonneg hpos).le
  refine continuation_to_one (p := fun lam => ForcedSolvable D ℱ hℱW hℱN T lam C ξ₀)
    (one_div_two_mul_mem hK hCB).1 hle1
    (forcedSolvable_of_sq_le 𝒲 hℱ0 hnull hrep hT hreg horig hL hLT hg hξ hξm
      (sq_one_div_two_mul_le hK hC₀)) ?_
  intro lam hlam hlam1 ζ hζ hζ₀ hWP
  refine hWP.add_of_le 𝒲 hℱ0 hnull hT hpos hlam hlam1 hL hLT hg hcG hGf hGb hconst hM hMT
    (le_trans ?_ (sq_one_div_two_mul_le hK hCB))
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hζ hζ₀ 2) hK) hCB

/-- **Theorem 3.5, existence.** Under the hypotheses of `forcedSolvable_one` — Assumptions
2.2–2.5, (2.5) along every progressive tuple, `g` Borel measurable in the state, a
square-integrable `ℱ_0`-measurable `ξ₀`, and a filtration with the properties listed there — the
system (1.1) with initial datum `ξ₀` has a solution. -/
theorem exists_solves [ℱ.IsRightContinuous] (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hrep : HasTerminalRep D ℱ hℱW hℱN T) (hT : 0 < T) (hreg : CoeffRegular ℱ P T C)
    (horig : CoeffOrigin T C) (hL : DiagonalLipschitz ℱ P T L C)
    (hLT : TerminalLipschitz ℱ P T L C.g) (hg : ∀ ρ, Measurable fun x => C.g x ρ) (hcG : 0 ≤ cG)
    (hGf : n ≤ m → GCoerciveForward (GX G) cG) (hGb : m ≤ n → GCoerciveBackward (GX G) cG)
    (hconst : Constants n m α β₁ β₂) (hM : DiagonalMonotone ℱ P T G β₁ β₂ C)
    (hMT : TerminalMonotone ℱ P T G α C.g) (hξ : ∀ i, MemLp (ξ₀ i) 2 P)
    (hξm : ∀ i, Measurable[ℱ 0] (ξ₀ i)) :
    ∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
      (U : Fin m → ℝ → Ω → E → ℝ) (γ : Fin n → ℝ → Ω → E → ℝ),
      Solves D ℱ hℱW hℱN T C ξ₀ X Y Z U γ :=
  forcedSolvable_one 𝒲 hℱ0 hnull hrep hT hreg horig hL hLT hg hcG hGf hGb hconst hM hMT hξ hξm
    0 0 0 0 0 Forcing.zero

/-- **Theorem 3.5, global well-posedness.** Under the hypotheses of `forcedSolvable_one` —
Assumptions 2.2–2.5, (2.5) along every progressive tuple, `g` Borel measurable in the state, a
square-integrable `ℱ_0`-measurable `ξ₀`, and a filtration with the properties listed there — the
system (1.1) with initial datum `ξ₀` has a solution, and any two solutions coincide: `X¹, X²` and
`Y¹, Y²` are indistinguishable on `[0, T]`, and `𝔼 ∫_0^T |Z¹ − Z²|²_F = 0`,
`𝔼 ∫_0^T ‖U¹ − U²‖²_{L²(ν)} = 0`, coordinatewise. -/
theorem exists_solves_and_uniqueness [ℱ.IsRightContinuous] (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hrep : HasTerminalRep D ℱ hℱW hℱN T) (hT : 0 < T) (hreg : CoeffRegular ℱ P T C)
    (horig : CoeffOrigin T C) (hL : DiagonalLipschitz ℱ P T L C)
    (hLT : TerminalLipschitz ℱ P T L C.g) (hg : ∀ ρ, Measurable fun x => C.g x ρ) (hcG : 0 ≤ cG)
    (hGf : n ≤ m → GCoerciveForward (GX G) cG) (hGb : m ≤ n → GCoerciveBackward (GX G) cG)
    (hconst : Constants n m α β₁ β₂) (hM : DiagonalMonotone ℱ P T G β₁ β₂ C)
    (hMT : TerminalMonotone ℱ P T G α C.g) (hξ : ∀ i, MemLp (ξ₀ i) 2 P)
    (hξm : ∀ i, Measurable[ℱ 0] (ξ₀ i)) :
    (∃ (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
      (U : Fin m → ℝ → Ω → E → ℝ) (γ : Fin n → ℝ → Ω → E → ℝ),
      Solves D ℱ hℱW hℱN T C ξ₀ X Y Z U γ)
    ∧ ∀ (X₁ X₂ : Fin n → ℝ → Ω → ℝ) (Y₁ Y₂ : Fin m → ℝ → Ω → ℝ)
      (Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ) (U₁ U₂ : Fin m → ℝ → Ω → E → ℝ)
      (γ₁ γ₂ : Fin n → ℝ → Ω → E → ℝ),
      Solves D ℱ hℱW hℱN T C ξ₀ X₁ Y₁ Z₁ U₁ γ₁ → Solves D ℱ hℱW hℱN T C ξ₀ X₂ Y₂ Z₂ U₂ γ₂ →
      (∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω)
        ∧ (∀ k, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ k t ω = Y₂ k t ω)
        ∧ (∀ k j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j) = 0)
        ∧ (∀ k, Poisson.Compensated.markedEnergy P ν T
            (fun ω s e => U₁ k s ω e - U₂ k s ω e) = 0) :=
  ⟨exists_solves 𝒲 hℱ0 hnull hrep hT hreg horig hL hLT hg hcG hGf hGb hconst hM hMT hξ hξm,
    fun _ _ _ _ _ _ _ _ _ _ h₁ h₂ =>
      h₁.uniqueness h₂ 𝒲 hℱ0 hnull hT hL hLT hcG hGf hGb hconst hM hMT⟩

end Dissertation.WellPosedness.Existence
