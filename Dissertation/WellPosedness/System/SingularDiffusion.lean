/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.SingularDriftAnalytic
import Dissertation.WellPosedness.Existence.AffineExample
import Dissertation.WellPosedness.System.PaperWeakSolutionInt

/-!
# A singular diffusion: no solution without Assumption 2.2

For `n = m = 1` and `d ≥ 1`, add the deterministic diffusion `t ↦ t^{-1/2}` to the first column
of `σ` in the affine system of Example 5.1(i) with `β₁ = 1`, `β₂ = 0`, `σ_c = 0` and `h_c = 0`:

`b(t, x, y, z, u) = −y`, `σ(t, x, y, z, u) = t^{-1/2} e₁₁ − z`, `h = −u`, `f = 0`, `g(x, ρ) = x`.

* **The assumptions.** The added diffusion cancels in every difference of coefficients, so
  Assumption 2.3 holds along the diagonal with `L = 1`, and Assumption 2.5 along the diagonal
  with `G = 1`, `α = 1`, `β₁ = 1`, `β₂ = 0`; the coefficients are Borel measurable. Assumption 2.2
  fails: the origin value `σ(t, 0, δ₀) = t^{-1/2} e₁₁` of the diffusion is not square integrable
  on `[0, T]`.
* **No solution.** Along a tuple `(X, Y, Z, U)` the entry `(1, 1)` of the diffusion process on
  `[0, T]` is `s^{-1/2} − Z_{1,1,s}`. Since `|s^{-1/2}|² ≤ 2 |s^{-1/2} − Z_s|² + 2 |Z_s|²` and
  `∫_0^T s^{-1} ds = ∞`, this entry and `Z_{1,1}` cannot both have finite energy on `[0, T]`, and
  a tuple of `ℍ²_weak` satisfying (1.1) asks for both.

## Main definitions

* `singularDiffusionCoeffs` — the system above.

## Main statements

* `diagonalLipschitz_singularDiffusionCoeffs`, `terminalLipschitz_singularDiffusionCoeffs`,
  `diagonalMonotone_singularDiffusionCoeffs`, `terminalMonotone_singularDiffusionCoeffs`,
  `coeffBorelW2_singularDiffusionCoeffs` — Assumptions 2.3 and 2.5 along the diagonal, and the
  Borel measurability of the coefficients.
* `not_coeffOrigin_singularDiffusionCoeffs` — Assumption 2.2 fails.
* `energy_add_energy_eq_top` — two processes adding up to `t^{-1/2}` on `[0, T]` do not both have
  finite energy.
* `diffusionProc_singularDiffusionCoeffs` — the diffusion process along a tuple.
* `not_paperWeakSolutionInt_singularDiffusionCoeffs` — no tuple solves the system in the sense of
  `PaperWeakSolutionInt`, over any filtration.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.Existence Dissertation.Law

/-! ### The coefficients -/

section Coefficients

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {d : ℕ}

/-- The system of Example 5.1(i) at `n = m = 1`, `β₁ = 1`, `β₂ = 0`, `σ_c = 0`, `h_c = 0` with the
deterministic diffusion `(√t)⁻¹` (`t^{-1/2}` for `t > 0`, `0` for `t ≤ 0`) added to the first
column of `σ`: `b = −y`, `σ(t, θ, μ) = t^{-1/2} e₁₁ − z`, `h = −u`, `f = 0`, `g(x, ρ) = x`. -/
noncomputable def singularDiffusionCoeffs : Coeffs ν 1 1 d :=
  { affineCoeffs 1 0 0 0 with
    σ := fun t θ μ =>
      WithLp.toLp 2 (fun p : Fin 1 × Fin d => if (p.2 : ℕ) = 0 then (Real.sqrt t)⁻¹ else 0)
        + (affineCoeffs 1 0 0 0 : Coeffs ν 1 1 d).σ t θ μ }

/-- The deterministic diffusion `t ↦ (√t)⁻¹ e₁₁` is measurable. -/
theorem measurable_singularDiffusion :
    Measurable fun t : ℝ =>
      (WithLp.toLp 2 (fun p : Fin 1 × Fin d => if (p.2 : ℕ) = 0 then (Real.sqrt t)⁻¹ else 0) :
        EuclideanSpace ℝ (Fin 1 × Fin d)) :=
  measurable_toLp_of_forall
    (x := fun (p : Fin 1 × Fin d) (t : ℝ) => if (p.2 : ℕ) = 0 then (Real.sqrt t)⁻¹ else 0)
    fun _ => Measurable.ite (MeasurableSet.const _) Real.continuous_sqrt.measurable.inv
      measurable_const

/-- The deterministic diffusion cancels in the channel differences. -/
theorem diagDiff_singularDiffusionCoeffs (t : ℝ) (θ θ' : TupleH ν 1 1 d)
    (μ μ' : P2 (TupleH ν 1 1 d)) :
    diagDiff (singularDiffusionCoeffs (ν := ν) (d := d)) t θ θ' μ μ'
      = diagDiff (affineCoeffs 1 0 0 0) t θ θ' μ μ' := by
  simp only [diagDiff, singularDiffusionCoeffs, add_sub_add_left_eq_sub]

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- The terminal function `g(x, ρ) = x` of `singularDiffusionCoeffs` meets Assumption 2.3 with
`L = 1`. -/
theorem terminalLipschitz_singularDiffusionCoeffs :
    TerminalLipschitz ℱ P T 1 (singularDiffusionCoeffs (ν := ν) (d := d)).g :=
  terminalLipschitz_affine (ν := ν) (d := d) (β₁ := 1) (β₂ := 0) (σc := 0) (hc := 0) le_rfl

/-- The terminal function `g(x, ρ) = x` of `singularDiffusionCoeffs` meets Assumption 2.5 with
`G = 1` and `α = 1`. -/
theorem terminalMonotone_singularDiffusionCoeffs :
    TerminalMonotone ℱ P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1
      (singularDiffusionCoeffs (ν := ν) (d := d)).g :=
  terminalMonotone_affine (ν := ν) (d := d) (β₁ := 1) (β₂ := 0) (σc := 0) (hc := 0)

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-- The coefficients `singularDiffusionCoeffs` meet Assumption 2.3 along the diagonal with
`L = 1`. -/
theorem diagonalLipschitz_singularDiffusionCoeffs :
    DiagonalLipschitz ℱ P T 1 (singularDiffusionCoeffs (ν := ν) (d := d)) := by
  filter_upwards [diagonalLipschitz_affine (ℱ := ℱ) (P := P) (T := T) (ν := ν) (n := 1) (d := d)
    (β₁ := 1) (β₂ := 0) (σc := 0) (hc := 0) (L := 1) zero_le_one le_rfl (by simp)]
    with t ht Θ Θ' h1 h2 h3 h4
  simpa only [singularDiffusionCoeffs, add_sub_add_left_eq_sub] using ht Θ Θ' h1 h2 h3 h4

/-- The coefficients `singularDiffusionCoeffs` meet Assumption 2.5 along the diagonal with `G = 1`,
`β₁ = 1` and `β₂ = 0`. -/
theorem diagonalMonotone_singularDiffusionCoeffs :
    DiagonalMonotone ℱ P T (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 0
      (singularDiffusionCoeffs (ν := ν) (d := d)) := by
  filter_upwards [diagonalMonotone_affine (ℱ := ℱ) (P := P) (T := T) (ν := ν) (n := 1) (d := d)
    (β₁ := 1) (β₂ := 0) (σc := 0) (hc := 0)] with t ht Θ Θ' h1 h2 h3 h4
  simpa only [diagDiff_singularDiffusionCoeffs] using ht Θ Θ' h1 h2 h3 h4

/-- The coefficients `b, σ, h, f` of `singularDiffusionCoeffs` are Borel measurable on
`[0, T] × H × P₂(H)`. -/
theorem coeffBorelW2_singularDiffusionCoeffs (T : ℝ) :
    CoeffBorelW2 T (singularDiffusionCoeffs (ν := ν) (d := d)) where
  b_meas := (coeffBorelW2_affine (ν := ν) (n := 1) (d := d) (β₁ := 1) (β₂ := 0) (σc := 0)
    (hc := 0) T).b_meas
  σ_meas := by
    have hσ := (coeffBorelW2_affine (ν := ν) (n := 1) (d := d) (β₁ := 1) (β₂ := 0) (σc := 0)
      (hc := 0) T).σ_meas
    rw [← BorelSpace.measurable_eq (α := EuclideanSpace ℝ (Fin 1 × Fin d)),
      ← BorelSpace.measurable_eq
        (α := Set.Icc (0 : ℝ) T × TupleH ν 1 1 d × TupleP2WH ν 1 1 d)] at hσ ⊢
    exact (measurable_singularDiffusion.comp (measurable_subtype_coe.comp measurable_fst)).add hσ
  h_meas := (coeffBorelW2_affine (ν := ν) (n := 1) (d := d) (β₁ := 1) (β₂ := 0) (σc := 0)
    (hc := 0) T).h_meas
  f_meas := (coeffBorelW2_affine (ν := ν) (n := 1) (d := d) (β₁ := 1) (β₂ := 0) (σc := 0)
    (hc := 0) T).f_meas

/-- **Assumption 2.2 fails for `singularDiffusionCoeffs`**, for `d ≥ 1` and `T > 0`: the entry
`(1, 1)` of the origin value `σ(t, 0, δ₀)` of the diffusion is `t^{-1/2}`, which is not square
integrable on `[0, T]`. -/
theorem not_coeffOrigin_singularDiffusionCoeffs (hd : 0 < d) (hT : 0 < T) :
    ¬ CoeffOrigin T (singularDiffusionCoeffs (ν := ν) (d := d)) := by
  intro h
  have hlt := lintegral_enorm_sq_lt_top h.σ_memLp
  have hle : ∀ t, (‖(Real.sqrt t)⁻¹ - (fun _ => (0 : ℝ)) t‖₊ : ℝ≥0∞) ^ 2
      ≤ ‖(singularDiffusionCoeffs (ν := ν) (d := d)).σ t 0 (P2.dirac 0)‖ₑ ^ 2 := fun t => by
    have e : (singularDiffusionCoeffs (ν := ν) (d := d)).σ t 0 (P2.dirac 0) (0, ⟨0, hd⟩)
        = (Real.sqrt t)⁻¹ := by
      simp [singularDiffusionCoeffs, affineCoeffs]
    rw [sub_zero, ← e, enorm_eq_nnnorm]
    gcongr
    exact PiLp.nnnorm_apply_le _ _
  have h2 := lintegral_mono (μ := volume.restrict (Icc (0 : ℝ) T)) hle
  rw [lintegral_sq_inv_sqrt_sub_eq_top tendsto_const_nhds hT] at h2
  exact lt_irrefl _ (h2.trans_lt hlt)

end Coefficients

/-! ### Energy -/

section Energy

open LevyStochCalc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}

/-- **Two processes adding up to `t^{-1/2}` do not both have finite energy**: for `T > 0`, if
`H_s + K_s = s^{-1/2}` on `[0, T]` and `K` is jointly measurable, then
`𝔼 ∫_0^T |H_s|² ds + 𝔼 ∫_0^T |K_s|² ds = ∞`. -/
theorem energy_add_energy_eq_top {H K : Ω → ℝ → ℝ} (hK : Measurable (Function.uncurry K))
    (hT : 0 < T) (hHK : ∀ ω, ∀ s ∈ Icc (0 : ℝ) T, H ω s + K ω s = (Real.sqrt s)⁻¹) :
    Brownian.Ito.energy P T H + Brownian.Ito.energy P T K = ⊤ := by
  have hsq : ∀ a b : ℝ,
      (‖a + b‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := fun a b => by
    have h : ‖a + b‖₊ ^ 2 ≤ 2 * ‖a‖₊ ^ 2 + 2 * ‖b‖₊ ^ 2 := by
      rw [← NNReal.coe_le_coe]
      push_cast
      simp only [Real.norm_eq_abs, sq_abs]
      nlinarith [sq_nonneg (a - b)]
    exact_mod_cast h
  have hpath : ∀ ω, (∫⁻ s in Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2)
      + ∫⁻ s in Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 = ⊤ := fun ω => by
    have htop := lintegral_sq_inv_sqrt_sub_eq_top (y := fun _ => (0 : ℝ)) tendsto_const_nhds hT
    simp only [sub_zero] at htop
    have hm : Measurable fun s => 2 * (‖K ω s‖₊ : ℝ≥0∞) ^ 2 := by
      have : Measurable (K ω) := hK.of_uncurry_left
      fun_prop
    have hle : ∫⁻ s in Icc (0 : ℝ) T, (‖(Real.sqrt s)⁻¹‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * (∫⁻ s in Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2)
          + 2 * ∫⁻ s in Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 := by
      calc ∫⁻ s in Icc (0 : ℝ) T, (‖(Real.sqrt s)⁻¹‖₊ : ℝ≥0∞) ^ 2
          ≤ ∫⁻ s in Icc (0 : ℝ) T,
              (2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖K ω s‖₊ : ℝ≥0∞) ^ 2) := by
            refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
            rw [← hHK ω s hs]
            exact hsq _ _
        _ = _ := by
            rw [lintegral_add_right _ hm, lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    rw [htop, top_le_iff, ← mul_add, ENNReal.mul_eq_top] at hle
    rcases hle with h | h
    · exact h.2
    · exact absurd h.1 ENNReal.ofNat_ne_top
  have hB : Measurable fun ω => ∫⁻ s in Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 :=
    (hK.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  calc Brownian.Ito.energy P T H + Brownian.Ito.energy P T K
      = ∫⁻ ω, ((∫⁻ s in Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2)
          + ∫⁻ s in Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2) ∂P := (lintegral_add_right _ hB).symm
    _ = ∫⁻ _, (⊤ : ℝ≥0∞) ∂P := lintegral_congr hpath
    _ = ⊤ := by simp

end Energy

/-! ### No solution -/

open LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω} [IsProbabilityMeasure P]
  {d : ℕ} {T : ℝ}

/-- On `[0, T]` the entry `(1, j)` of the diffusion process of `singularDiffusionCoeffs` along
`(X, Y, Z, U)` is `s^{-1/2} − Z_{1,j,s}` for the first column and `−Z_{1,j,s}` for the others. -/
theorem diffusionProc_singularDiffusionCoeffs (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ)
    (Z : Fin 1 → ℝ → Ω → Fin d → ℝ) (U : Fin 1 → ℝ → Ω → E → ℝ) (ω : Ω) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (j : Fin d) :
    diffusionProc P T (singularDiffusionCoeffs (ν := ν) (d := d)) X Y Z U 0 s ω j
      = (if (j : ℕ) = 0 then (Real.sqrt s)⁻¹ else 0) - Z 0 s ω j := by
  simp [diffusionProc, hs, singularDiffusionCoeffs, affineCoeffs, tupleAt]
  ring

/-- **`singularDiffusionCoeffs` has no solution in `ℍ²_weak`**: for `d ≥ 1` and `T > 0`, over any
filtration carrying the driver `D`, no tuple solves it in the sense of `PaperWeakSolutionInt`,
from any initial datum: the entry `(1, 1)` of the diffusion process and `Z_{1,1}` would both have
finite energy on `[0, T]`, while they add up to `s^{-1/2}` there. -/
theorem not_paperWeakSolutionInt_singularDiffusionCoeffs
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
    {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} (hd : 0 < d) (hT : 0 < T)
    {ξ₀ : Fin 1 → Ω → ℝ} {X : Fin 1 → ℝ → Ω → ℝ} {Y : Fin 1 → ℝ → Ω → ℝ}
    {Z : Fin 1 → ℝ → Ω → Fin d → ℝ} {U : Fin 1 → ℝ → Ω → E → ℝ} {γ : Fin 1 → ℝ → Ω → E → ℝ} :
    ¬ PaperWeakSolutionInt D ℱ hℱW hℱN T (singularDiffusionCoeffs (ν := ν) (d := d)) ξ₀ X Y Z U
      γ := by
  intro h
  have hZ := Brownian.Ito.measurable_uncurry_of_predictable (h.Z_pred 0 ⟨0, hd⟩)
  have key := energy_add_energy_eq_top (P := P)
    (H := fun ω s => diffusionProc P T (singularDiffusionCoeffs (ν := ν) (d := d)) X Y Z U 0 s ω
      ⟨0, hd⟩) hZ hT fun ω s hs => by
        rw [diffusionProc_singularDiffusionCoeffs X Y Z U ω hs]
        simp
  exact ENNReal.add_ne_top.mpr ⟨h.σ_sq 0 ⟨0, hd⟩, h.Z_sq 0 ⟨0, hd⟩⟩ key

end Dissertation.WellPosedness.System
