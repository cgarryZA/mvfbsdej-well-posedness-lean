/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.Stability
import MVFBSDEJ.WellPosedness.System.Uniqueness
import MVFBSDEJ.WellPosedness.System.PaperSolutionSolves

/-!
# Theorem 3.1 for solutions in the sense of the paper

Theorem 3.1 of the paper compares solutions `Θ¹, Θ²` of (1.1) in `ℍ²` for two coefficient
systems `C¹, C²`:

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ_t|²_F + ‖δU_t‖²_{L²(ν)}) dt
  ≤ C_stab (𝔼|δξ₀|² + 𝔼|δ̂g_T|²
    + 𝔼 ∫_0^T (|(δb)(t)|² + |(δσ)(t)|²_F + ‖(δh)(t)‖²_{L²(ν)} + |(δf)(t)|²) dt)`,   (3.1)

the coefficient differences evaluated along `Θ²`. `Solves.supSize_sub_le` states it for the
predicate `Solves`; this file states it for the paper's solution notion `PaperSolution`, under the
same hypotheses and with the same two sides.

A solution in the sense of the paper, extended off `[0, T]`, is a solution of `Solves` with the
same `Z`, `U`, `γ` and the same values of `X`, `Y` on `[0, T]` (`PaperSolution.exists_solves`).
Both sides of (3.1) see `X` and `Y` only on `[0, T]`:

* the left-hand side takes suprema over `[0, T]` and energies on `[0, T]`
  (`supSize_eq_of_eqOn`);
* on the right-hand side the drift, diffusion and driver processes along `Θ²` evaluate the tuple
  `Θ²_s` and its law at times `s ∈ [0, T]` and vanish off `[0, T]` (`driftProc_eq_of_eqOn` and its
  analogues), the terminal term sees `X²` only at `T` (`terminalVal_eq_of_eq`), and the jump terms
  are the representatives `γ` and `γ²` cut to `[0, T]`, which the extension leaves unchanged;
* the cross-evaluation hypothesis `CrossEval` of `C¹` along `Θ²` sees `X²`, `Y²` only on `[0, T]`
  (`CrossEval.of_eqOn`).

So (3.1) for the extensions is (3.1) for the solutions in the sense of the paper. The
representative `γ²` of a solution in the sense of the paper represents `h²` at the predictable
tuple `(Θ²⁻_s, μ²⁻_s)`; for almost every `s` this is `h²` at `(Θ²_s, μ²_s)` almost surely
(`PaperSolution.jump_rep_tupleAt`).

## Main statements

* `supSize_eq_of_eqOn` — the `𝕊`-size sees `X` and `Y` only on `[0, T]`.
* `CrossEval.of_eqOn` — the cross-evaluation sees the tuple only on `[0, T]`.
* `PaperSolution.supSize_sub_le` — Theorem 3.1 in the sense of the paper.
-/

open MeasureTheory Filter Matrix MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open MVFBSDEJ.WellPosedness.BrownianPoisson MVFBSDEJ.WellPosedness.Stability
  LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}

/-! ### Changing a tuple off the horizon -/

section Congr

omit [IsProbabilityMeasure P] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- **The `𝕊`-size sees `X` and `Y` only on `[0, T]`**: if `X' = X` and `Y' = Y` at every time
of `[0, T]`, then
`𝔼 sup_{t ≤ T} |X'_t|² + 𝔼 sup_{t ≤ T} |Y'_t|² + 𝔼 ∫_0^T (|Z|²_F + ‖U‖²)` equals the same
quantity for `X` and `Y`. -/
theorem supSize_eq_of_eqOn {X X' : Fin n → ℝ → Ω → ℝ} {Y Y' : Fin m → ℝ → Ω → ℝ}
    (hX : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X i t)
    (hY : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y k t) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
    (U : Fin m → ℝ → Ω → E → ℝ) :
    supSize P ν T X' Y' Z U = supSize P ν T X Y Z U := by
  have hX' : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X' i t ω))
      = ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω) := fun ω =>
    iSup_congr fun t => iSup_congr fun ht => by simp only [fun i => congrFun (hX i t ht) ω]
  have hY' : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y' k t ω))
      = ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y k t ω) := fun ω =>
    iSup_congr fun t => iSup_congr fun ht => by simp only [fun k => congrFun (hY k t ht) ω]
  simp only [supSize, hX', hY']

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {C : Coeffs ν n m d}
  {X X' : Fin n → ℝ → Ω → ℝ} {Y Y' : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- **The cross-evaluation sees the tuple only on `[0, T]`**: if `X' = X` and `Y' = Y` at every
time of `[0, T]`, the cross-evaluation of `C` along `(X, Y, Z, U)` with jump representative `γ`
is one along `(X', Y', Z, U)` with the same `γ`. -/
theorem CrossEval.of_eqOn (h : CrossEval ℱ P T C X Y Z U γ)
    (hX : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X i t)
    (hY : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y k t) :
    CrossEval ℱ P T C X' Y' Z U γ := by
  have hb := driftProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hX hY
  have hσ := diffusionProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hX hY
  have hf := driverProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hX hY
  exact
    { jump_rep := by
        filter_upwards [h.jump_rep, ae_restrict_mem measurableSet_Icc] with s hs hsI
        rw [tupleAt_eq_of_eqOn hX hY hsI]
        exact hs
      b_meas := by rw [hb]; exact h.b_meas
      b_prog := by rw [hb]; exact h.b_prog
      σ_meas := by rw [hσ]; exact h.σ_meas
      σ_prog := by rw [hσ]; exact h.σ_prog
      h_meas := h.h_meas
      h_prog := h.h_prog
      f_meas := by rw [hf]; exact h.f_meas
      f_prog := by rw [hf]; exact h.f_prog }

end Congr

/-! ### Theorem 3.1 -/

variable {C₁ C₂ : Coeffs ν n m d}
  {ξ₁ ξ₂ : Fin n → Ω → ℝ} {X₁ X₂ : Fin n → ℝ → Ω → ℝ} {Y₁ Y₂ : Fin m → ℝ → Ω → ℝ}
  {Z₁ Z₂ : Fin m → ℝ → Ω → Fin d → ℝ} {U₁ U₂ : Fin m → ℝ → Ω → E → ℝ}
  {γ₁ γ₂ γ : Fin n → ℝ → Ω → E → ℝ} {L cG α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}

section General

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}

omit [IsProbabilityMeasure P] [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The `𝕊`-size of a difference sees the four processes `X¹, X², Y¹, Y²` only on `[0, T]`. -/
private theorem supSize_sub_eq_of_eqOn {X₁' X₂' : Fin n → ℝ → Ω → ℝ} {Y₁' Y₂' : Fin m → ℝ → Ω → ℝ}
    (hX₁ : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁' i t = X₁ i t)
    (hX₂ : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X₂' i t = X₂ i t)
    (hY₁ : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁' k t = Y₁ k t)
    (hY₂ : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₂' k t = Y₂ k t) :
    supSize P ν T (fun i t ω => X₁' i t ω - X₂' i t ω) (fun k t ω => Y₁' k t ω - Y₂' k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      = supSize P ν T (fun i t ω => X₁ i t ω - X₂ i t ω) (fun k t ω => Y₁ k t ω - Y₂ k t ω)
        (fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (fun k t ω e => U₁ k t ω e - U₂ k t ω e) :=
  supSize_eq_of_eqOn
    (fun i t ht => funext fun ω => by
      simp only [congrFun (hX₁ i t ht) ω, congrFun (hX₂ i t ht) ω])
    (fun k t ht => funext fun ω => by
      simp only [congrFun (hY₁ k t ht) ω, congrFun (hY₂ k t ht) ω]) _ _

/-- **Theorem 3.1 for solutions in the sense of the paper.** Let `C¹` satisfy Assumption 2.3 along
the diagonal with constant `L`, Assumption 2.4 with coupling matrix `G` and constant `c_G ≥ 0`
and Assumption 2.5 along the diagonal with admissible constants `α, β₁, β₂`, let `g¹, g²` be
Borel measurable in the state, and let `Θᵏ` be a solution of (1.1) for `Cᵏ` in the sense of the
paper, with jump representative `γᵏ`, such that the coefficient processes of `C¹` along `Θ²` are
jointly and progressively measurable, with a jointly measurable, marked progressively measurable
representative `γ` of `h¹` along `Θ²`. Then

`𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²)
  ≤ C_stab (𝔼|δξ₀|² + 𝔼|δ̂g_T|² + 𝔼 ∫_0^T (|δb|² + |δσ|²_F + ‖δh‖² + |δf|²))`,

the coefficient differences `ψ¹ − ψ²` evaluated along `Θ²`, the jump coefficients through their
representatives `γ` and `γ²`, and `C_stab = aprioriConst T (10 L²) (4 L²) ‖G‖ c_G α β₁ β₂ 1`,
over a filtration whose null sets lie in its time-`0` field, whose right-continuation is constant
before `0` and which admits a cross witness. -/
theorem PaperSolution.supSize_sub_le (h₁ : PaperSolution D ℱ hℱW hℱN T C₁ ξ₁ X₁ Y₁ Z₁ U₁ γ₁)
    (h₂ : PaperSolution D ℱ hℱW hℱN T C₂ ξ₂ X₂ Y₂ Z₂ U₂ γ₂)
    (hX : CrossEval ℱ P T C₁ X₂ Y₂ Z₂ U₂ γ)
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
  obtain ⟨X₁', Y₁', hX₁, hY₁, hs₁⟩ := h₁.exists_solves hT.le
  obtain ⟨X₂', Y₂', hX₂, hY₂, hs₂⟩ := h₂.exists_solves hT.le
  have h := hs₁.supSize_sub_le hs₂ (hX.of_eqOn hX₂ hY₂) hg₁ hg₂ 𝒲 hℱ0 hnull hT hL hLT hcG hGf
    hGb hconst hM hMT
  rwa [supSize_sub_eq_of_eqOn hX₁ hX₂ hY₁ hY₂, driftProc_eq_of_eqOn (C := C₁) hX₂ hY₂,
    driftProc_eq_of_eqOn (C := C₂) hX₂ hY₂, diffusionProc_eq_of_eqOn (C := C₁) hX₂ hY₂,
    diffusionProc_eq_of_eqOn (C := C₂) hX₂ hY₂, driverProc_eq_of_eqOn (C := C₁) hX₂ hY₂,
    driverProc_eq_of_eqOn (C := C₂) hX₂ hY₂,
    terminalVal_eq_of_eq (C := C₁) fun i => hX₂ i T ⟨hT.le, le_rfl⟩,
    terminalVal_eq_of_eq (C := C₂) fun i => hX₂ i T ⟨hT.le, le_rfl⟩] at h

end General

end MVFBSDEJ.WellPosedness.System
