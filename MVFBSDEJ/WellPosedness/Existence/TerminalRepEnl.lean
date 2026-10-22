/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Existence.TerminalRep
import MVFBSDEJ.WellPosedness.Enlarged.Representation

/-!
# The terminal representation property from martingale representation

Let `ℱ` be a right-continuous filtration carrying a Lévy driver `D = (W, N)`, whose null sets
lie in its time-`0` field and whose right-continuation is constant before time `0`. Suppose
every square-integrable `ℱ_T`-measurable `ζ` is

`ζ = E[ζ | ℱ_0] + ∑ i ∫₀ᵀ Gⁱ dWⁱ + ∫₀ᵀ ∫ K dÑ`

for integrands `G`, `K` admissible for `ℱ`. Then `ℱ` has the terminal representation property
at `T`: with `Z`, `U` the processes of `G`, `K` and `M` the sum of the everywhere-càdlàg versions
of the two stochastic integrals, the triple

`Y_t = E[ξ | ℱ_0] + M_t`,   `Z`,   `U`

solves the linear backward equation with jumps with drift `0` and terminal value `ξ`. The
time-`0` field lies in every `ℱ_t`, before time `0` by the constancy of the right-continuation,
so `Y` is adapted, and every path of `Y` is right-continuous since every path of `M` is.

The enlarged filtration `enlJoint 𝒢₀ D h𝒢₀` of a Lévy driver with an independent initial
σ-algebra `𝒢₀` has all these properties, so it has the terminal representation property at
every horizon `T > 0`. Its time-`0` field contains `𝒢₀`, so the initial value `Y_0` is random
in general.

## Main statements

* `HasTerminalRep.of_rep` — martingale representation with the time-`0` conditional expectation
  gives the terminal representation property.
* `hasTerminalRep_enlJoint` — the enlarged filtration has the terminal representation property.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.BrownianPoisson LevyStochCalc LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.Driver LevyStochCalc.Driver.LevyDriver
open LevyStochCalc.Brownian.Ito LevyStochCalc.Poisson.Compensated

universe u v w

section General

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

/-- For a right-continuous filtration whose right-continuation is constant before time `0`, the
time-`0` field lies in the field at every time. -/
theorem filtration_zero_le_of_rightCont [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t) (t : ℝ) : ℱ 0 ≤ ℱ t := by
  rcases le_total 0 t with ht | ht
  · exact ℱ.mono ht
  · have h := hℱ0 t ht
    rwa [Filtration.IsRightContinuous.eq] at h

/-- **Terminal representation from martingale representation.** Let `ℱ` be a right-continuous
filtration carrying the driver, whose null sets lie in its time-`0` field and whose
right-continuation is constant before time `0`. If every square-integrable weight measurable for
`ℱ_T` is its conditional expectation given `ℱ_0` plus a joint integral over `[0, T]` of
integrands admissible for `ℱ`, then `ℱ` has the terminal representation property at `T`. -/
theorem HasTerminalRep.of_rep [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hrep : ∀ ζ : Ω → ℝ, MemLp ζ 2 P → AEStronglyMeasurable[ℱ T] ζ P →
      ∃ (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) (K : MarkedHorizonIntegrand P ν ℱ T),
        ζ =ᵐ[P] fun ω => P[ζ | ℱ 0] ω + jointIntegral hℱW hℱN G K ω) :
    HasTerminalRep D ℱ hℱW hℱN T := by
  intro ξ hξ2 hξm
  obtain ⟨G, K, hξrep⟩ := hrep ξ hξ2 hξm
  have hZq := sq_int_global_of_vanishing (coordOfHorizonIntegrand_vanish G)
    (energy_coordOfHorizonIntegrand_ne_top G)
  have hUq := marked_sq_int_global_of_vanishing (processOfMarkedHorizonIntegrand_vanish K)
    (markedEnergy_processOfMarkedHorizonIntegrand_ne_top K)
  obtain ⟨MW, hMWad, -, hMWae, hMWcd, -, -, -⟩ := exists_cadlag_vectorIntegral_supBound D.W ℱ
    hℱW (coordOfHorizonIntegrand G) (measurable_coordOfHorizonIntegrand G)
    (progressive_coordOfHorizonIntegrand G) hZq hℱ0 hnull 0 le_rfl
  obtain ⟨MN, hMNad, -, hMNae, hMNcd, -, -, -⟩ := exists_cadlag_compensatedIntegral_supBound
    D.N ℱ hℱN (fun ω s e => processOfMarkedHorizonIntegrand K s ω e)
    (measurable_processOfMarkedHorizonIntegrand K) (progressive_processOfMarkedHorizonIntegrand K)
    hUq hℱ0 hnull 0 le_rfl
  have hrc : ℱ.rightCont = ℱ := Filtration.IsRightContinuous.eq
  rw [hrc] at hMWad hMNad
  have hc : StronglyMeasurable[ℱ 0] (P[ξ | ℱ 0]) := stronglyMeasurable_condExp
  refine ⟨fun t ω => P[ξ | ℱ 0] ω + (MW t ω + MN t ω), coordOfHorizonIntegrand G,
    processOfMarkedHorizonIntegrand K, ?_⟩
  exact
    { Z_meas := measurable_coordOfHorizonIntegrand G
      Z_prog := progressive_coordOfHorizonIntegrand G
      Z_vanish := coordOfHorizonIntegrand_vanish G
      Z_sq := energy_coordOfHorizonIntegrand_ne_top G
      U_meas := measurable_processOfMarkedHorizonIntegrand K
      U_prog := progressive_processOfMarkedHorizonIntegrand K
      U_vanish := processOfMarkedHorizonIntegrand_vanish K
      U_sq := markedEnergy_processOfMarkedHorizonIntegrand_ne_top K
      φ_meas := measurable_const
      φ_prog := Probability.progressivelyMeasurable_zero _
      φ_vanish := fun _ _ _ => rfl
      φ_sq := by simp [Brownian.Ito.energy]
      ξ_sq := hξ2
      Y_adapted := fun t =>
        (hc.measurable.mono (filtration_zero_le_of_rightCont hℱ0 t) le_rfl).add
          ((hMWad t).add (hMNad t))
      Y_rightCont := fun ω t => tendsto_const_nhds.add ((hMWcd ω t).1.add (hMNcd ω t).1)
      eqn := by
        intro t _
        filter_upwards [hξrep, hMWae t, hMNae t] with ω e0 e1 e2
        rw [e1, e2, e0, jointIntegral_eq D hℱW hℱN G K (measurable_coordOfHorizonIntegrand G)
          (progressive_coordOfHorizonIntegrand G) hZq
          (measurable_processOfMarkedHorizonIntegrand K)
          (progressive_processOfMarkedHorizonIntegrand K) hUq]
        simp only [integral_zero]
        ring }

end General

section Enlarged

open MVFBSDEJ.WellPosedness.Enlarged

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {d : ℕ}

/-- **The enlarged filtration has the terminal representation property.** For a σ-algebra `𝒢₀`
independent of the joint natural filtration of a Lévy driver with `d > 0` Brownian coordinates,
the usual augmentation of the joint filtration enlarged at time `0` by `𝒢₀` has the terminal
representation property at every horizon `T > 0`. -/
theorem hasTerminalRep_enlJoint [MeasurableSpace.CountablyGenerated E]
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (h𝒢₀ : 𝒢₀ ≤ mΩ) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) (hd : 0 < d) {T : ℝ}
    (hT : 0 < T) :
    HasTerminalRep D (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) T :=
  HasTerminalRep.of_rep (hF0_enlJoint D h𝒢₀)
    (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0)
    (fun _ h2 hm => exists_jointIntegral_enlJoint D h𝒢₀ hind₀ hd hT h2 hm)

end Enlarged

end MVFBSDEJ.WellPosedness.Existence
