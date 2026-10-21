/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.CoeffBorelW2
import Dissertation.WellPosedness.Existence.OriginBound
import Dissertation.WellPosedness.System.DiagonalLipschitzH
import Dissertation.WellPosedness.System.PaperWeakS2

/-!
# The integrals of (1.1) along a tuple of `ℍ²` exist

A solution of (1.1) in the sense of the well-posedness paper, in `𝕊` or in `ℍ²`, is asked
the conditions under which the integrals of (1.1) exist along it (`PaperAdmissible`): the joint
and progressive measurability and the finite energy on `[0, T]` of the drift, diffusion and
driver processes `ψ(s, Θ_s, μ_s)` and of the jump integrand `γ`, a representative of
`h(s, Θ⁻_s, ·, μ⁻_s)` in `L²(ν)`. The paper derives them from its assumptions along every
`Θ ∈ ℍ²`: the measurability from (2.5), a consequence of the joint Borel measurability (2.3)
by Lemma A.1, and the energy bounds from Assumptions 2.2–2.3. Here they follow from (2.5),
Assumption 2.2 and Assumption 2.3 along the diagonal.

* **Measurability.** Extended off `[0, T]` by `0` before `0` and by `X_T`, `Y_T` after `T`
  (`exists_adapted_rightCont_extension`), `Θ` is a progressive tuple, and (2.5) along it,
  `CoeffRegular`, gives the joint and progressive measurability of the coefficient processes
  along it, with a representative `γ` of `h(s, Θ_s, ·, μ_s)`; the coefficient processes see `Θ`
  only on `[0, T]`, so they are those along `Θ`.
* **Energy.** (4.2) (`ProgTuple.coeffEnergy_le`), from Assumption 2.2 and Assumption 2.3 along
  the diagonal, bounds the energy of the coefficient processes by that of `Θ` and of the origin
  values. The square integrability of `X_T`, which the terminal bound (4.3) asks, does not enter.
* **The predictable tuple.** Almost every path of `X` and `Y` has left limits on `(0, T]`, so
  `Θ⁻_s = Θ_s` almost surely at almost every time (`PaperWeakTuple.ae_ae_tupleAt_leftLimProc_eq`)
  and `γ` also represents `h(s, Θ⁻_s, ·, μ⁻_s)`.

## Main statements

* `PaperWeakTuple.exists_paperAdmissible` — under (2.5), Assumption 2.2 and Assumption 2.3
  along the diagonal, the integrals of (1.1) along a tuple of `ℍ²` exist.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Existence LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {T L : ℝ} {C : Coeffs ν n m d} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}

namespace PaperWeakTuple

variable (hΘ : PaperWeakTuple ℱ P ν T X Y Z U)
include hΘ

/-- **The integrals of (1.1) along a tuple of `ℍ²` exist.** For `T ≥ 0`, coefficients with
(2.5) along every progressive tuple satisfying Assumption 2.2 and Assumption 2.3 along the
diagonal with constant `L`, and `Θ = (X, Y, Z, U) ∈ ℍ²`, there is a representative `γ` of
the jump coefficient such that the drift, diffusion and driver processes along `Θ` and the jump
integrand `γ` are jointly and progressively measurable with finite energy on `[0, T]`, and `γ`
represents `h(s, Θ⁻_s, ·, μ⁻_s)` in `L²(ν)` at almost every time of `[0, T]`, almost surely. -/
theorem exists_paperAdmissible (hT : 0 ≤ T) (hreg : CoeffRegular ℱ P T C)
    (horig : CoeffOrigin T C) (hL : DiagonalLipschitz ℱ P T L C) :
    ∃ γ : Fin n → ℝ → Ω → E → ℝ, PaperAdmissible ℱ P T C X Y Z U γ := by
  obtain ⟨X', hXe, hXa, hXr⟩ := exists_adapted_rightCont_extension hT hΘ.X_adapted hΘ.X_rightCont
  obtain ⟨Y', hYe, hYa, hYr⟩ := exists_adapted_rightCont_extension hT hΘ.Y_adapted hΘ.Y_rightCont
  have hΘ' : ProgTuple ℱ P ν T X' Y' Z U :=
    { X_adapted := hXa
      X_rightCont := hXr
      Y_adapted := hYa
      Y_rightCont := hYr
      Z_meas := fun k j => Brownian.Ito.measurable_uncurry_of_predictable (hΘ.Z_pred k j)
      Z_prog := fun k =>
        progressivelyMeasurable_of_predictable_of_vanish (hΘ.Z_pred k) (hΘ.Z_vanish k)
      Z_sq := hΘ.Z_sq
      U_meas := fun k => (hΘ.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
      U_prog := fun k => (hΘ.U_pred k).markedProgressivelyMeasurable
      U_sq := hΘ.U_sq }
  have hXe' : ∀ i, Brownian.Ito.energy P T (fun ω s => X' i s ω) ≠ ⊤ := fun i => by
    rw [energy_eq_of_eqOn (hXe i)]
    exact hΘ.X_sq i
  have hYe' : ∀ k, Brownian.Ito.energy P T (fun ω s => Y' k s ω) ≠ ⊤ := fun k => by
    rw [energy_eq_of_eqOn (hYe k)]
    exact hΘ.Y_sq k
  obtain ⟨γ, hγ⟩ := hreg X' Y' Z U hΘ'
  have hdrift := driftProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hdiff := diffusionProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hdriver := driverProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  -- (4.2) along the extension
  have hfin : ENNReal.ofReal (20 * L ^ 2) * (∑ i, Brownian.Ito.energy P T (fun ω s => X' i s ω)
      + (∑ k, Brownian.Ito.energy P T (fun ω s => Y' k s ω)
        + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)))
      + 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, originSq C s ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_,
      ENNReal.mul_ne_top (by norm_num) (lintegral_originSq_lt_top horig).ne⟩
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun i _ => hXe' i,
      ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun k _ => hYe' k,
        ENNReal.sum_ne_top.mpr fun k _ => ENNReal.sum_ne_top.mpr fun j _ => hΘ.Z_sq k j⟩,
        ENNReal.sum_ne_top.mpr fun k _ => hΘ.U_sq k⟩⟩
  have hbound := hΘ'.coeffEnergy_le hXe' hYe' hγ hL
  rw [hdrift, hdiff, hdriver] at hbound
  obtain ⟨hBSH, hF⟩ := ENNReal.add_ne_top.mp (ne_top_of_le_ne_top hfin hbound)
  obtain ⟨hBS, hH⟩ := ENNReal.add_ne_top.mp hBSH
  obtain ⟨hB, hS⟩ := ENNReal.add_ne_top.mp hBS
  refine ⟨γ,
    { b_meas := hdrift ▸ hγ.b_meas
      b_prog := hdrift ▸ hγ.b_prog
      b_sq := fun i => ENNReal.sum_ne_top.mp hB i (Finset.mem_univ i)
      σ_meas := hdiff ▸ hγ.σ_meas
      σ_prog := hdiff ▸ hγ.σ_prog
      σ_sq := fun i j => ENNReal.sum_ne_top.mp (ENNReal.sum_ne_top.mp hS i (Finset.mem_univ i)) j
        (Finset.mem_univ j)
      γ_meas := hγ.h_meas
      γ_prog := hγ.h_prog
      γ_sq := fun i => ENNReal.sum_ne_top.mp hH i (Finset.mem_univ i)
      f_meas := hdriver ▸ hγ.f_meas
      f_prog := hdriver ▸ hγ.f_prog
      f_sq := fun k => ENNReal.sum_ne_top.mp hF k (Finset.mem_univ k)
      jump_rep := ?_ }⟩
  filter_upwards [hγ.jump_rep, hΘ.ae_ae_tupleAt_leftLimProc_eq hT,
    ae_restrict_mem measurableSet_Icc] with s hs heq hsI
  rw [tupleAt_eq_of_eqOn hXe hYe hsI] at hs
  filter_upwards [hs, heq] with ω hω hωeq
  rw [hωeq, lawP2_congr heq]
  exact hω

end PaperWeakTuple

end Dissertation.WellPosedness.System
