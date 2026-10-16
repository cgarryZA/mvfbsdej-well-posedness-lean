/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.BrownianPoisson.Estimate
import Dissertation.WellPosedness.MarkCoding.Coding
import Dissertation.WellPosedness.BrownianPoisson.Hypotheses
import Dissertation.WellPosedness.MarkCoding.Integral
import LevyStochCalc.Driver.Existence
import LevyStochCalc.Driver.AugJointRightCont

/-!
# The constant solution of the linear backward equation

Over every Lévy driver `D` and horizon `T > 0`, the constant triple `Y ≡ c`, `Z ≡ 0`, `U ≡ 0`
solves the linear backward equation with jumps (4.4) with terminal value `ξ ≡ c` and drift
`φ ≡ 0` over the augmented joint filtration `augJoint D`: both canonical stochastic integrals of
the zero integrand vanish almost surely.

## Main statements

* `multidimStochasticIntegral_zero_ae` — the multidimensional Itô integral of the zero integrand
  vanishes almost surely.
* `linearBSDEJAug_const` — the constant triple solves the equation.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.BrownianPoisson

open LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- The multidimensional Itô integral of the zero integrand vanishes almost surely. -/
theorem multidimStochasticIntegral_zero_ae (W : Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : ∀ i, Brownian.IsBrownianFiltration (W.W i) ℱ)
    (hm : ∀ i : Fin d, Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) =>
      (0 : Fin d → ℝ) i))
    (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) =>
      (0 : Fin d → ℝ) i)
    (hq : ∀ i : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ _ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, (‖(0 : Fin d → ℝ) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (r : ℝ) :
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ (fun _ _ => 0) hm hp hq r
      =ᵐ[P] 0 := by
  have h : ∀ i : Fin d, ∀ᵐ ω ∂P, Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱ i)
      (fun _ _ => (0 : ℝ)) (hm i) (hp i) (hq i) r ω = 0 := fun i =>
    Brownian.Ito.stochasticIntegralBrownian_ae_zero (W.W i) ℱ (hℱ i) (hm i) (hp i) (hq i) r
  filter_upwards [ae_all_iff.2 h] with ω hω
  exact Finset.sum_eq_zero fun i _ => hω i

/-- The constant triple `Y ≡ c`, `Z ≡ 0`, `U ≡ 0` solves the linear backward equation with
terminal value `c` and drift `0` over the augmented joint filtration of any Lévy driver. -/
theorem linearBSDEJAug_const (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) {T : ℝ}
    (hT : 0 < T) (c : ℝ) :
    LinearBSDEJAug D T (fun _ => c) (fun _ _ => 0) (fun _ _ => c) (fun _ _ => 0)
      (fun _ _ _ => 0) where
  Z_meas := fun _ => measurable_const
  Z_prog := fun _ => Probability.progressivelyMeasurable_zero _
  Z_vanish := fun _ _ _ => rfl
  Z_sq := fun _ => by simp [Brownian.Ito.energy]
  U_meas := measurable_const
  U_prog := markedProgressivelyMeasurable_zero _
  U_vanish := fun _ _ _ _ => rfl
  U_sq := by simp [Poisson.Compensated.markedEnergy]
  φ_meas := measurable_const
  φ_prog := Probability.progressivelyMeasurable_zero _
  φ_vanish := fun _ _ _ => rfl
  φ_sq := by simp [Brownian.Ito.energy]
  ξ_sq := memLp_const c
  Y_adapted := fun _ => measurable_const
  Y_rightCont := fun _ _ => tendsto_const_nhds
  eqn := by
    intro t ht
    have hN : ∀ r : ℝ, 0 ≤ r → Poisson.Compensated.stochasticIntegral D.N (augJoint D)
        D.isPoissonFiltration_aug (fun _ _ _ => (0 : ℝ)) measurable_const
        (markedProgressivelyMeasurable_zero _) (fun _ _ => by simp) r =ᵐ[P] 0 := fun r hr =>
      Poisson.Compensated.stochasticIntegral_ae_zero_of_vanishing D.N D.isPoissonFiltration_aug
        _ _ _ _ hr fun _ _ _ _ => rfl
    have hW := multidimStochasticIntegral_zero_ae D.W (augJoint D) D.isBrownianFiltration_aug
      (fun _ => measurable_const) (fun _ => Probability.progressivelyMeasurable_zero _)
      (fun _ _ _ => by simp)
    filter_upwards [hW T, hW t, hN T hT.le, hN t ht.1] with ω h1 h2 h3 h4
    simp only [Pi.zero_apply] at h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    simp

end Dissertation.WellPosedness.BrownianPoisson
