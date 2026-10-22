/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.BridgeDiff

/-!
# Square integrability of the tuple of a solution

Let `(X, Y, Z, U)` solve the `λ`-forced system (4.1). Its integrands `Z` and `U` are jointly
measurable with finite energy on `[0, T]`. Over a filtration carrying the driver whose null sets
lie in its time-`0` field, whose right-continuation is constant before `0` and which admits a
cross witness, the coordinates of `X` and `Y` lie in `S²(0, T)` by Lemma 4.1 (each coordinate of
`X` solves a linear backward equation from `X_T`), so they have finite energy on `[0, T]` too.
By Tonelli's theorem, at almost every time `s ∈ [0, T]`:

* almost surely, each `e ↦ U_{k,s}(ω, e)` lies in `L²(ν)`;
* the tuple `Θ_s = (X_s, Y_s, Z_s, U_s)` is square integrable, so, being strongly
  `ℱ_s`-measurable, it lies in `L²(Ω, ℱ_s; H)`.

So `(Θ_s, Law Θ_s)` is a diagonal input at almost every time, as for a solution in `𝕊` in the
well-posedness paper.

## Main statements

* `ae_ae_memLp_of_markedEnergy_ne_top` — a jointly measurable marked integrand with finite
  energy on `[0, T]` is square integrable in the mark at almost every time, almost surely.
* `SolvesForced.ae_ae_memLp_jump` — the jump channel of a solution, likewise.
* `SolvesForced.ae_memLp_tupleAt` — the tuple of a solution is square integrable at almost every
  time of `[0, T]`.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.System

open LevyStochCalc LevyStochCalc.BSDEJ.Solves MVFBSDEJ.WellPosedness.BrownianPoisson
  MVFBSDEJ.WellPosedness.Stability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {P : Measure Ω}

/-- **A marked integrand of finite energy is square integrable in the mark** at almost every time
of `[0, T]`, almost surely, when it is jointly measurable in the sample point, the time and the
mark. -/
theorem ae_ae_memLp_of_markedEnergy_ne_top [SFinite P] [SFinite ν] {T : ℝ}
    {U : ℝ → Ω → E → ℝ} (hU : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hUe : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, MemLp (fun e => U s ω e) 2 ν := by
  have hUm : Measurable (Function.uncurry fun ω s => ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) :=
    ((hU.nnnorm.coe_nnreal_ennreal.pow_const 2).comp (by fun_prop :
      Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))).lintegral_prod_right'
  filter_upwards [ae_lintegral_lt_top hUm hUe] with s hs
  have hms : Measurable fun ω => ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
    hUm.comp (measurable_id.prodMk measurable_const)
  filter_upwards [ae_lt_top hms hs.ne] with ω hω
  have hme : Measurable fun e => U s ω e :=
    hU.comp (by fun_prop : Measurable fun e : E => ((ω, s, e) : Ω × ℝ × E))
  refine ⟨hme.aestronglyMeasurable, lt_top_iff_ne_top.mpr fun htop => hω.ne ?_⟩
  have h2 := eLpNorm_two_sq (ν := ν) fun e => U s ω e
  rw [htop, ENNReal.top_pow two_ne_zero] at h2
  simpa only [enorm_eq_nnnorm] using h2.symm

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Fin n → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- **The jump channel of a solution is square integrable in the mark**: at almost every time of
`[0, T]`, almost surely, each `e ↦ U_{k,s}(ω, e)` lies in `L²(ν)`. -/
theorem SolvesForced.ae_ae_memLp_jump
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, ∀ k,
      MemLp (fun e => U k s ω e) 2 ν := by
  filter_upwards [ae_all_iff.mpr fun k =>
    ae_ae_memLp_of_markedEnergy_ne_top (h.bwd k).U_meas (h.bwd k).U_sq] with s hs
  exact ae_all_iff.mpr hs

/-- **The tuple of a solution is square integrable at almost every time** of `[0, T]`, over a
filtration whose null sets lie in its time-`0` field, whose right-continuation is constant
before `0` and which admits a cross witness. -/
theorem SolvesForced.ae_memLp_tupleAt
    (h : SolvesForced D ℱ hℱW hℱN T lam C ξ₀ qb qσ qh qf qg X Y Z U γ) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (tupleAt ν X Y Z U s) 2 P :=
  MVFBSDEJ.WellPosedness.System.ae_memLp_tupleAt
    (fun s _ => ((h.stronglyMeasurable_tupleAt s).mono (ℱ.le s)).aestronglyMeasurable)
    (fun i => ((h.fwd i).linearBSDEJ hT.le).measurable_uncurry.comp measurable_swap)
    (fun k => (h.bwd k).measurable_uncurry.comp measurable_swap)
    (fun k j => (h.bwd k).Z_meas j) (fun k => (h.bwd k).U_meas)
    (fun i => (energy_le_of_biSup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (((h.fwd i).linearBSDEJ hT.le).lintegral_biSup_sq_lt_top 𝒲 hℱ0 hnull hT))).ne)
    (fun k => (energy_le_of_biSup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((h.bwd k).lintegral_biSup_sq_lt_top 𝒲 hℱ0 hnull hT))).ne)
    (fun k j => (h.bwd k).Z_sq j) (fun k => (h.bwd k).U_sq)

end MVFBSDEJ.WellPosedness.System
