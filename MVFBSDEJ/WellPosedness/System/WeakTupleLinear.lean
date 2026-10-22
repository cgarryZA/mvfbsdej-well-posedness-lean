/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.PaperSolutionSolves

/-!
# The linear structure of `ℍ²`

The tuples `Θ = (X, Y, Z, U)` of `ℍ²` (`PaperWeakTuple`) form a real vector space under
coordinatewise addition and multiplication by constants: adaptedness on `[0, T]`, right-continuous
paths on `[0, T)`, almost sure left limits on `(0, T]`, predictability, vanishing off `[0, T]` and
finite energy on `[0, T]` pass to sums and to multiples. The energy of `X` and `Y` is controlled
through jointly measurable processes equal to them on `[0, T]`.

## Main statements

* `exists_measurable_eqOn_of_rightCont` — a process adapted on `[0, T]` with right-continuous
  paths on `[0, T)` agrees on `[0, T]` with a jointly measurable process.
* `energy_add_ne_top_of_eqOn`, `energy_const_mul_ne_top_of_eqOn` — finite energy on `[0, T]` of a
  sum and of a multiple of processes agreeing on `[0, T]` with jointly measurable ones.
* `PaperWeakTuple.add` — `ℍ²` is closed under addition.
* `PaperWeakTuple.const_mul` — `ℍ²` is closed under multiplication by a constant.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

open LevyStochCalc

section Energy

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℝ}

/-- **A process adapted on `[0, T]` with right-continuous paths on `[0, T)` agrees on `[0, T]`
with a jointly measurable process.** -/
theorem exists_measurable_eqOn_of_rightCont {ι : Type*} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {x : ι → ℝ → Ω → ℝ} (hadapt : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (x i t))
    (hrc : ∀ i ω, ∀ t ∈ Set.Ico (0 : ℝ) T,
      Tendsto (fun s => x i s ω) (𝓝[>] t) (𝓝 (x i t ω))) :
    ∃ x' : ι → ℝ → Ω → ℝ, (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, x' i t = x i t)
      ∧ ∀ i, Measurable (Function.uncurry fun ω s => x' i s ω) := by
  rcases le_or_gt 0 T with hT | hT
  · obtain ⟨x', hxe, hxa, hxr⟩ := exists_adapted_rightCont_extension hT hadapt hrc
    exact ⟨x', hxe, fun i =>
      (Probability.measurable_uncurry_of_rightContinuous (hxa i) (hxr i)).comp measurable_swap⟩
  · exact ⟨fun _ _ _ => 0, fun _ t ht => absurd (ht.1.trans ht.2) (not_le.mpr hT),
      fun _ => measurable_const⟩

/-- The energy on `[0, T]` of a sum of two processes of finite energy is finite, when each agrees
on `[0, T]` with a jointly measurable process. -/
theorem energy_add_ne_top_of_eqOn {x₁ x₂ x₁' x₂' : ℝ → Ω → ℝ}
    (h₁ : ∀ t ∈ Set.Icc (0 : ℝ) T, x₁' t = x₁ t) (h₂ : ∀ t ∈ Set.Icc (0 : ℝ) T, x₂' t = x₂ t)
    (hm₁ : Measurable (Function.uncurry fun ω s => x₁' s ω))
    (hm₂ : Measurable (Function.uncurry fun ω s => x₂' s ω))
    (hx₁ : Brownian.Ito.energy P T (fun ω s => x₁ s ω) ≠ ⊤)
    (hx₂ : Brownian.Ito.energy P T (fun ω s => x₂ s ω) ≠ ⊤) :
    Brownian.Ito.energy P T (fun ω s => x₁ s ω + x₂ s ω) ≠ ⊤ := by
  have e : Brownian.Ito.energy P T (fun ω s => x₁' s ω + x₂' s ω)
      = Brownian.Ito.energy P T (fun ω s => x₁ s ω + x₂ s ω) :=
    energy_eq_of_eqOn (x := fun s ω => x₁ s ω + x₂ s ω) (x' := fun s ω => x₁' s ω + x₂' s ω)
      fun t ht => by funext ω; simp only [h₁ t ht, h₂ t ht]
  rw [← energy_eq_of_eqOn h₁] at hx₁
  rw [← energy_eq_of_eqOn h₂] at hx₂
  rw [← e]
  exact Brownian.Ito.energy_add_ne_top hm₁ hm₂ hx₁ hx₂

/-- The energy on `[0, T]` of a multiple of a process of finite energy is finite, when the
process agrees on `[0, T]` with a jointly measurable process. -/
theorem energy_const_mul_ne_top_of_eqOn {x x' : ℝ → Ω → ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, x' t = x t)
    (hm : Measurable (Function.uncurry fun ω s => x' s ω))
    (hx : Brownian.Ito.energy P T (fun ω s => x s ω) ≠ ⊤) (c : ℝ) :
    Brownian.Ito.energy P T (fun ω s => c * x s ω) ≠ ⊤ := by
  have e : Brownian.Ito.energy P T (fun ω s => c * x' s ω)
      = Brownian.Ito.energy P T (fun ω s => c * x s ω) :=
    energy_eq_of_eqOn (x := fun s ω => c * x s ω) (x' := fun s ω => c * x' s ω)
      fun t ht => by funext ω; simp only [h t ht]
  rw [← energy_eq_of_eqOn h] at hx
  rw [← e]
  exact Brownian.Ito.energy_const_mul_ne_top hm hx c

end Energy

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] {n m d : ℕ} {P : Measure Ω} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  {X X' : Fin n → ℝ → Ω → ℝ} {Y Y' : Fin m → ℝ → Ω → ℝ} {Z Z' : Fin m → ℝ → Ω → Fin d → ℝ}
  {U U' : Fin m → ℝ → Ω → E → ℝ}

namespace PaperWeakTuple

/-- **`ℍ²` is closed under addition**: the coordinatewise sum of two tuples of `ℍ²` is a tuple
of `ℍ²`. -/
theorem add (hΘ : PaperWeakTuple ℱ P ν T X Y Z U) (hΘ' : PaperWeakTuple ℱ P ν T X' Y' Z' U') :
    PaperWeakTuple ℱ P ν T (fun i t ω => X i t ω + X' i t ω) (fun k t ω => Y k t ω + Y' k t ω)
      (fun k t ω j => Z k t ω j + Z' k t ω j) (fun k t ω e => U k t ω e + U' k t ω e) := by
  obtain ⟨Xe, hXe, hXm⟩ := exists_measurable_eqOn_of_rightCont hΘ.X_adapted hΘ.X_rightCont
  obtain ⟨Xe', hXe', hXm'⟩ := exists_measurable_eqOn_of_rightCont hΘ'.X_adapted hΘ'.X_rightCont
  obtain ⟨Ye, hYe, hYm⟩ := exists_measurable_eqOn_of_rightCont hΘ.Y_adapted hΘ.Y_rightCont
  obtain ⟨Ye', hYe', hYm'⟩ := exists_measurable_eqOn_of_rightCont hΘ'.Y_adapted hΘ'.Y_rightCont
  exact
    { X_adapted := fun i t ht => (hΘ.X_adapted i t ht).add (hΘ'.X_adapted i t ht)
      X_rightCont := fun i ω t ht => (hΘ.X_rightCont i ω t ht).add (hΘ'.X_rightCont i ω t ht)
      X_leftLim := fun i => by
        filter_upwards [hΘ.X_leftLim i, hΘ'.X_leftLim i] with ω h₁ h₂ t ht
        obtain ⟨L₁, hL₁⟩ := h₁ t ht
        obtain ⟨L₂, hL₂⟩ := h₂ t ht
        exact ⟨L₁ + L₂, hL₁.add hL₂⟩
      X_sq := fun i =>
        energy_add_ne_top_of_eqOn (hXe i) (hXe' i) (hXm i) (hXm' i) (hΘ.X_sq i) (hΘ'.X_sq i)
      Y_adapted := fun k t ht => (hΘ.Y_adapted k t ht).add (hΘ'.Y_adapted k t ht)
      Y_rightCont := fun k ω t ht => (hΘ.Y_rightCont k ω t ht).add (hΘ'.Y_rightCont k ω t ht)
      Y_leftLim := fun k => by
        filter_upwards [hΘ.Y_leftLim k, hΘ'.Y_leftLim k] with ω h₁ h₂ t ht
        obtain ⟨L₁, hL₁⟩ := h₁ t ht
        obtain ⟨L₂, hL₂⟩ := h₂ t ht
        exact ⟨L₁ + L₂, hL₁.add hL₂⟩
      Y_sq := fun k =>
        energy_add_ne_top_of_eqOn (hYe k) (hYe' k) (hYm k) (hYm' k) (hΘ.Y_sq k) (hΘ'.Y_sq k)
      Z_pred := fun k j => (hΘ.Z_pred k j).add (hΘ'.Z_pred k j)
      Z_vanish := fun k ω s hs => by
        funext j
        simp [hΘ.Z_vanish k ω s hs, hΘ'.Z_vanish k ω s hs]
      Z_sq := fun k j => Brownian.Ito.energy_add_ne_top
        (Brownian.Ito.measurable_uncurry_of_predictable (hΘ.Z_pred k j))
        (Brownian.Ito.measurable_uncurry_of_predictable (hΘ'.Z_pred k j)) (hΘ.Z_sq k j)
        (hΘ'.Z_sq k j)
      U_pred := fun k => (hΘ.U_pred k).add (hΘ'.U_pred k)
      U_vanish := fun k ω s e hs => by
        simp [hΘ.U_vanish k ω s e hs, hΘ'.U_vanish k ω s e hs]
      U_sq := fun k => Poisson.Compensated.markedEnergy_add_ne_top
        ((hΘ.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl)
        ((hΘ'.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl) (hΘ.U_sq k)
        (hΘ'.U_sq k) }

/-- **`ℍ²` is closed under multiplication by a constant**: the coordinatewise multiple `c Θ` of
a tuple `Θ` of `ℍ²` is a tuple of `ℍ²`. -/
theorem const_mul (hΘ : PaperWeakTuple ℱ P ν T X Y Z U) (c : ℝ) :
    PaperWeakTuple ℱ P ν T (fun i t ω => c * X i t ω) (fun k t ω => c * Y k t ω)
      (fun k t ω j => c * Z k t ω j) (fun k t ω e => c * U k t ω e) := by
  obtain ⟨Xe, hXe, hXm⟩ := exists_measurable_eqOn_of_rightCont hΘ.X_adapted hΘ.X_rightCont
  obtain ⟨Ye, hYe, hYm⟩ := exists_measurable_eqOn_of_rightCont hΘ.Y_adapted hΘ.Y_rightCont
  exact
    { X_adapted := fun i t ht => (hΘ.X_adapted i t ht).const_mul c
      X_rightCont := fun i ω t ht => (hΘ.X_rightCont i ω t ht).const_mul c
      X_leftLim := fun i => by
        filter_upwards [hΘ.X_leftLim i] with ω h t ht
        obtain ⟨L, hL⟩ := h t ht
        exact ⟨c * L, hL.const_mul c⟩
      X_sq := fun i => energy_const_mul_ne_top_of_eqOn (hXe i) (hXm i) (hΘ.X_sq i) c
      Y_adapted := fun k t ht => (hΘ.Y_adapted k t ht).const_mul c
      Y_rightCont := fun k ω t ht => (hΘ.Y_rightCont k ω t ht).const_mul c
      Y_leftLim := fun k => by
        filter_upwards [hΘ.Y_leftLim k] with ω h t ht
        obtain ⟨L, hL⟩ := h t ht
        exact ⟨c * L, hL.const_mul c⟩
      Y_sq := fun k => energy_const_mul_ne_top_of_eqOn (hYe k) (hYm k) (hΘ.Y_sq k) c
      Z_pred := fun k j => (hΘ.Z_pred k j).const_mul c
      Z_vanish := fun k ω s hs => by
        funext j
        simp [hΘ.Z_vanish k ω s hs]
      Z_sq := fun k j => Brownian.Ito.energy_const_mul_ne_top
        (Brownian.Ito.measurable_uncurry_of_predictable (hΘ.Z_pred k j)) (hΘ.Z_sq k j) c
      U_pred := fun k => (hΘ.U_pred k).const_mul c
      U_vanish := fun k ω s e hs => by simp [hΘ.U_vanish k ω s e hs]
      U_sq := fun k => Poisson.Compensated.markedEnergy_const_mul_ne_top
        ((hΘ.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl) (hΘ.U_sq k) c }

end PaperWeakTuple

end MVFBSDEJ.WellPosedness.System
