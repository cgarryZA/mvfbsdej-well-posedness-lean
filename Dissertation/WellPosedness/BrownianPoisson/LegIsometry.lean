/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.ItoLevy

/-!
# The càdlàg martingale sum of the two stochastic legs and its isometry

For the integrands `Z`, `U` of a solution of the linear backward equation (4.4), the sum
`M_t = ∫_0^t Z_s dW_s + ∫_0^t ∫_E U_s(e) Ñ(ds, de)` of the two canonical stochastic integrals has,
over a filtration whose null sets lie in its time-`0` field and whose right-continuation is
constant before `0`, a version that is jointly measurable, right-continuous at every sample point
and a martingale for the right-continuous filtration. The Brownian and the compensated Poisson
legs are orthogonal, so its second moment at the horizon is the joint isometry

`𝔼[M_T²] = ∑_j 𝔼 ∫_0^T Z_j(s)² ds + 𝔼 ∫_0^T ∫_E U_s(e)² ν(de) ds`.

## Main statements

* `LinearBSDEJ.exists_cadlag_legSum` — the version of the leg sum and its isometry.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.BrownianPoisson

open LevyStochCalc.BSDEJ.Solves LevyStochCalc LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {T : ℝ} {ξ : Ω → ℝ} {φ : Ω → ℝ → ℝ} {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
  {U : ℝ → Ω → E → ℝ}

namespace LinearBSDEJ

/-- **The càdlàg leg sum and its isometry.** The sum of the two canonical stochastic integrals of
the integrands of a solution of the linear backward equation has a version that is jointly
measurable, right-continuous at every sample point and a martingale for the right-continuous
filtration, whose second moment at the horizon is the sum of the energies of `Z` and `U`. -/
theorem exists_cadlag_legSum (h : LinearBSDEJ D ℱ hℱW hℱN T ξ φ Y Z U) (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T) :
    ∃ M : ℝ → Ω → ℝ, Measurable (Function.uncurry M) ∧
      (∀ t : ℝ, M t =ᵐ[P] fun ω =>
        Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z h.Z_meas
            h.Z_prog (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) t ω
          + Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) h.U_meas
            h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) t ω) ∧
      (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) ∧
      Martingale M ℱ.rightCont P ∧
      ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        = (∑ j : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω j))
          + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) := by
  classical
  obtain ⟨MW, -, hWme, hWae, hWcd, hWmart, -, -⟩ :=
    exists_cadlag_vectorIntegral_supBound D.W ℱ hℱW Z h.Z_meas h.Z_prog
      (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) hℱ0 hnull T hT.le
  obtain ⟨MN, -, hNme, hNae, hNcd, hNmart, -, -⟩ :=
    exists_cadlag_compensatedIntegral_supBound D.N ℱ hℱN (fun ω s e => U s ω e) h.U_meas
      h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) hℱ0 hnull T hT.le
  have hMae : ∀ t : ℝ, (fun ω => MW t ω + MN t ω) =ᵐ[P] fun ω =>
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z h.Z_meas
          h.Z_prog (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) t ω
        + Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω' s e => U s ω' e) h.U_meas
          h.U_prog (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) t ω := fun t => by
    filter_upwards [hWae t, hNae t] with ω h1 h2
    rw [h1, h2]
  -- the leg sum is an Itô–Lévy process with zero initial value and zero drift
  have hL : Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN (fun t ω => MW t ω + MN t ω)
      (fun _ => 0) (fun _ _ => 0) Z (fun ω s e => U s ω e) :=
    { measurable_path := hWme.add hNme
      σ_meas := h.Z_meas
      σ_prog := h.Z_prog
      σ_sq := sq_int_global_of_vanishing h.Z_vanish h.Z_sq
      γ_meas := h.U_meas
      γ_prog := h.U_prog
      γ_sq := marked_sq_int_global_of_vanishing h.U_vanish h.U_sq
      decomposition := fun t _ => by
        filter_upwards [hMae t] with ω hω
        rw [hω]
        simp }
  have hbq : ∀ T' : ℝ, 0 < T' → ∫⁻ _ω, ∫⁻ _s in Set.Icc (0 : ℝ) T',
      (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun _ _ => by simp
  have hiso := integral_mul_self_eq_of_isItoLevyProcess hL 𝒲 stronglyMeasurable_const
    (memLp_const 0) measurable_const (Probability.progressivelyMeasurable_zero ℱ) hbq hT
  have hMT : MemLp (fun ω => MW T ω + MN T ω) 2 P :=
    memLp_two_of_isItoLevyProcess hL (memLp_const 0) measurable_const hbq hT.le
  simp only [mul_zero, integral_zero, add_zero, zero_add] at hiso
  rw [integral_mul_self_eq_toReal hMT] at hiso
  have hσf : ∀ j ∈ Finset.univ, Brownian.Ito.energy P T (fun ω s => Z s ω j) ≠ ⊤ :=
    fun j _ => h.Z_sq j
  refine ⟨fun t ω => MW t ω + MN t ω, hWme.add hNme, hMae, fun ω t =>
    (hWcd ω t).1.add (hNcd ω t).1, hWmart.add hNmart, ?_⟩
  rw [← ENNReal.toReal_eq_toReal_iff' (lintegral_sq_lt_top_of_memLp_two hMT).ne
    (ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr hσf, h.U_sq⟩),
    ENNReal.toReal_add (ENNReal.sum_ne_top.mpr hσf) h.U_sq, ENNReal.toReal_sum hσf]
  exact hiso

end LinearBSDEJ

end Dissertation.WellPosedness.BrownianPoisson
