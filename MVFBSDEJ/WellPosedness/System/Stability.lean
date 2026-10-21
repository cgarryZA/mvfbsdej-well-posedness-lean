/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.CrossEval

/-!
# Stability under coefficient and data perturbation

Theorem 3.1 of the paper. Let the coefficient system `C¹ = (b¹, σ¹, h¹, f¹, g¹)` satisfy
Assumption 2.3 along the diagonal with constant `L`, Assumption 2.4 with coupling matrix `G` and
constant `c_G`, and Assumption 2.5 with constants `α, β₁, β₂`; let `C²` be a second coefficient
system, and let `Θᵏ` solve (1.1) for `Cᵏ` with initial datum `ξ₀ᵏ`. With the coefficient
differences evaluated along solution 2,

`(δψ)(t) = ψ¹(t, Θ²_t, μ²_t) − ψ²(t, Θ²_t, μ²_t)` (`ψ ∈ {b, σ, h, f}`),
`δ̂g_T = g¹(X²_T, Law X²_T) − g²(X²_T, Law X²_T)`,

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ_t|²_F + ‖δU_t‖²_{L²(ν)}) dt
  ≤ C_stab (𝔼|δξ₀|² + 𝔼|δ̂g_T|²
    + 𝔼 ∫_0^T (|(δb)(t)|² + |(δσ)(t)|²_F + ‖(δh)(t)‖²_{L²(ν)} + |(δf)(t)|²) dt)`,   (3.1)

with `C_stab = aprioriConst T (10 L²) (4 L²) ‖G‖ c_G α β₁ β₂ 1`, Lemma 4.3's constant at
`λ̲ = 1`. It depends on system 1 alone and is free of the dimensions, of `ν(E)` and of the
Burkholder–Davis–Gundy constant. When the right-hand side is finite, `Θ²` solves the forced
system (4.1) for `C¹` at `λ = 1` with forcing `−(δψ)`, `−δ̂g_T`, and Lemma 4.3 at `λ = λ̲ = 1`
applied to `Θ¹` and `Θ²` gives (3.1); otherwise (3.1) is trivial. Of system 2 only its
solution and the Borel measurability of `g²` in the state enter: its Assumptions 2.2–2.3, as the
paper remarks, serve only to make the right-hand side finite. When the two systems share
`b, σ, h, f`, (3.1) is continuous dependence on the initial and terminal data.

Besides the conditions of `Solves` that go beyond the paper (the coefficient processes along each
solution jointly and progressively measurable and square integrable), the statements ask:

* `g¹` and `g²` Borel measurable in the state, which the paper's standing joint measurability of
  the coefficients gives;
* in the general case, `CrossEval`: the coefficient processes of system 1 along solution 2 are
  jointly and progressively measurable, with a jointly measurable, marked progressively
  measurable representative `γ` of the jump coefficient `h¹` along solution 2. The paper derives
  this from Lemma A.1. For `C¹` jointly measurable with the evaluation σ-algebra on `P₂(H)` it
  holds with a canonical `γ` (`MVFBSDEJ.WellPosedness.Existence.CoeffBorel.crossEval`).

The filtration is one on which Lemma 4.1 applies: its null sets lie in its time-`0` field, its
right-continuation is constant before `0`, and it admits a cross witness.

## Main statements

* `Solves.supSize_sub_le` — Theorem 3.1.
-/

open MeasureTheory Filter Matrix MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {C₁ C₂ : Coeffs ν n m d}
  {ξ₁ ξ₂ : Fin n → Ω → ℝ} {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ γ : Fin n → ℝ → Ω → E → ℝ} {L cG α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}

/-- **Theorem 3.1, stability under coefficient and data perturbation.** Let `C¹` satisfy
Assumption 2.3 along the diagonal with constant `L`, Assumption 2.4 with coupling matrix `G` and
constant `c_G ≥ 0` and Assumption 2.5 along the diagonal with admissible constants
`α, β₁, β₂`, let `g¹, g²` be Borel measurable in the state, and let `Θᵏ` solve (1.1) for `Cᵏ`
— solutions whose coefficient processes are jointly and progressively measurable and square
integrable — such that the coefficient processes of `C¹` along `Θ²` are jointly and progressively
measurable, with a jointly measurable, marked progressively measurable representative `γ` of
`h¹` along `Θ²`. Then

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)
  ≤ C_stab (𝔼|δξ₀|² + 𝔼|δ̂g_T|² + 𝔼 ∫_0^T (|δb|² + |δσ|²_F + ‖δh‖² + |δf|²))`,

the coefficient differences `ψ¹ − ψ²` evaluated along `Θ²`, the jump coefficients through their
representatives `γ` and `γ²` along `Θ²`, and
`C_stab = aprioriConst T (10 L²) (4 L²) ‖G‖ c_G α β₁ β₂ 1`, over a filtration whose null sets lie
in its time-`0` field, whose right-continuation is constant before `0` and which admits a cross
witness. -/
theorem Solves.supSize_sub_le (h₁ : Solves D ℱ hℱW hℱN T C₁ ξ₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : Solves D ℱ hℱW hℱN T C₂ ξ₂ X₂ Y₂ Z₂ U₂ γ₂) (hX : CrossEval ℱ P T C₁ X₂ Y₂ Z₂ U₂ γ)
    (hg₁ : ∀ ρ, Measurable fun x => C₁.g x ρ) (hg₂ : ∀ ρ, Measurable fun x => C₂.g x ρ)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hL : DiagonalLipschitz ℱ P T L C₁) (hLT : TerminalLipschitz ℱ P T L C₁.g) (hcG : 0 ≤ cG)
    (hGf : n ≤ m → GCoerciveForward (GX G) cG) (hGb : m ≤ n → GCoerciveBackward (GX G) cG)
    (hconst : Constants n m α β₁ β₂) (hM : DiagonalMonotone ℱ P T G β₁ β₂ C₁)
    (hMT : TerminalMonotone ℱ P T G α C₁.g) :
    supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      ≤ ENNReal.ofReal (aprioriConst T (10 * L ^ 2) (4 * L ^ 2) ‖GX G‖ cG α β₁ β₂ 1)
        * dataSize P ν T (fun i ω => ξ₁ i ω - ξ₂ i ω)
          (fun i ω s => driftProc P T C₁ X₂ Y₂ Z₂ U₂ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
          (fun i s ω j => diffusionProc P T C₁ X₂ Y₂ Z₂ U₂ i s ω j
            - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
          (fun i s ω e => jumpProc T γ i s ω e - jumpProc T γ₂ i s ω e)
          (fun k ω s => driverProc P T C₁ X₂ Y₂ Z₂ U₂ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
          (fun k ω => terminalVal P T C₁ X₂ k ω - terminalVal P T C₂ X₂ k ω) := by
  by_cases hP : dataSize P ν T (fun i ω => ξ₁ i ω - ξ₂ i ω)
      (fun i ω s => driftProc P T C₁ X₂ Y₂ Z₂ U₂ i ω s - driftProc P T C₂ X₂ Y₂ Z₂ U₂ i ω s)
      (fun i s ω j => diffusionProc P T C₁ X₂ Y₂ Z₂ U₂ i s ω j
        - diffusionProc P T C₂ X₂ Y₂ Z₂ U₂ i s ω j)
      (fun i s ω e => jumpProc T γ i s ω e - jumpProc T γ₂ i s ω e)
      (fun k ω s => driverProc P T C₁ X₂ Y₂ Z₂ U₂ k ω s - driverProc P T C₂ X₂ Y₂ Z₂ U₂ k ω s)
      (fun k ω => terminalVal P T C₁ X₂ k ω - terminalVal P T C₂ X₂ k ω) = ⊤
  · rw [hP, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (aprioriConst_pos hT.le (by positivity)
      (by positivity) hcG hconst.α_nonneg hconst.β₁_nonneg hconst.β₂_nonneg one_pos)).ne']
    exact le_top
  have hfin := hP
  simp only [dataSize, ENNReal.add_ne_top, ENNReal.sum_ne_top, Finset.mem_univ,
    forall_const] at hfin
  obtain ⟨⟨⟨⟨⟨_, hg⟩, hb⟩, hσ⟩, hh⟩, hf⟩ := hfin
  have hgk : ∀ k, ∫⁻ ω, (‖terminalVal P T C₁ X₂ k ω - terminalVal P T C₂ X₂ k ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≠ ⊤ := fun k => ne_top_of_le_ne_top hg (lintegral_mono fun ω =>
    Finset.single_le_sum (f := fun k => (‖terminalVal P T C₁ X₂ k ω
      - terminalVal P T C₂ X₂ k ω‖₊ : ℝ≥0∞) ^ 2) (fun _ _ => zero_le) (Finset.mem_univ k))
  have h₂' := h₂.solvesForced_of_crossEval hX hg₁ hg₂ hb hσ hh hf hgk
  have h := SolvesForced.supSize_sub_le h₁ h₂' 𝒲 hℱ0 hnull hT one_pos le_rfl le_rfl hL hLT hcG
    hGf hGb hconst hM hMT
  simpa only [Pi.zero_apply, zero_sub, neg_sub] using h

end MVFBSDEJ.WellPosedness.System
