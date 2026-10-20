/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.AppASteps
import Dissertation.Acceptance.A.WitnessNonzero
import Dissertation.WellPosedness.System.HilbertW2Polish
import Dissertation.WellPosedness.System.LawFlowL2

/-!
# Steps of the proof of Lemma A.1 of the well-posedness paper: proofs

## Main statements

* `Dissertation.Acceptance.A.lemA1_L2` — the left-limit tuple agrees `dt ⊗ dP`-almost everywhere
  with the tuple, whose squared Hilbert norm integrates to the sum of the coordinate energies.
* `Dissertation.Acceptance.A.lemA1_fubini` — the section map is a linear isometric equivalence
  for any probability space, its strong measurability given by
  `Dissertation.Law.stronglyMeasurable_lp_of_section`.
* `Dissertation.Acceptance.A.lemA1_pettis` — the section map of the left-limit tuple; its range
  is separable, and the closure of its span is the closed separable subspace.
* `Dissertation.Acceptance.A.lemA1_polish` — `μ ↦ toL2 # μ` is an isometric bijection onto the
  2-Wasserstein space of the Hilbert space, which is separable, separated by `W₂`
  (`Dissertation.Law.P2W.instT0Space`) and complete (`Dissertation.Law.P2W.instCompleteSpace`).
* `Dissertation.Acceptance.A.lemA1_hypotheses` — the hypotheses of Lemma A.1 at a tuple on the
  fair coin whose `X` and `Y` jump at `t = 1/2` by a random sign.
* `Dissertation.Acceptance.A.lemA1_fubini_hypotheses`, `lemA1_polish_hypotheses` — their
  hypotheses at `ν = δ₀` and at Lebesgue measure on `ℝ`.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.Law

universe u v

/-- Lemma A.1, Step 1: `Θ⁻ ∈ L²([0, T] × Ω; H)`. -/
theorem lemA1_L2 : PaperSpec.A.lemA1_L2.{u, v} := by
  intro Ω mΩ ℱ P _ E _ ν _ _ n m d T X Y Z U hΘ
  exact ⟨hΘ.stronglyMeasurable_toL2_tupleAt_leftLim, hΘ.memLp_toL2_tupleAt_leftLim⟩

/-- Lemma A.1, Step 1: the Fubini isometry. -/
theorem lemA1_fubini : PaperSpec.A.lemA1_fubini.{u, v} := by
  intro Ω _ P _ E _ ν _ _ n m d T
  exact ⟨fubiniEquiv, ae_coeFn_fubiniEquiv⟩

/-- Lemma A.1, Step 1: a Borel version of `t ↦ Θ⁻_t ∈ L²(Ω; H)`. -/
theorem lemA1_pettis : PaperSpec.A.lemA1_pettis.{u, v} := by
  intro Ω mΩ ℱ P _ E _ ν _ _ n m d T X Y Z U hΘ
  obtain ⟨F, hF, hrep⟩ := hΘ.exists_stronglyMeasurable_lp_leftLim
  exact ⟨F, hF, exists_isClosed_isSeparable_submodule_of_stronglyMeasurable hF,
    measurable_borel_of_stronglyMeasurable hF, hrep⟩

/-- Lemma A.1, Step 2: `(P₂(H), W₂)` is Polish. -/
theorem lemA1_polish : PaperSpec.A.lemA1_polish.{v} := by
  intro E _ ν _ _ n m d
  refine ⟨inferInstance, fun μ μ' h => ?_, inferInstance, inferInstance, inferInstance⟩
  exact (Metric.inseparable_iff.mpr h).eq

/-! ### Witnesses -/

section Witness

/-- The uniform law on `Bool`. -/
local notation "P𝔹" => PMF.toMeasure (PMF.uniformOfFintype Bool)

/-- A fair sign revealed at time `1/2`: `ξ(ω) 1_{t ≥ 1/2}` with `ξ(true) = 1`,
`ξ(false) = −1`. -/
noncomputable def coinStep (_ : Fin 1) (t : ℝ) (ω : Bool) : ℝ :=
  if 1 / 2 ≤ t then (if ω then 1 else -1) else 0

/-- From time `1/2` on, `coinStep` is the sign. -/
theorem coinStep_of_le (i : Fin 1) (ω : Bool) {t : ℝ} (ht : 1 / 2 ≤ t) :
    coinStep i t ω = if ω then 1 else -1 := by
  unfold coinStep
  rw [if_pos ht]

/-- Before time `1/2`, `coinStep` vanishes. -/
theorem coinStep_of_lt (i : Fin 1) (ω : Bool) {t : ℝ} (ht : t < 1 / 2) : coinStep i t ω = 0 := by
  unfold coinStep
  rw [if_neg (not_le.mpr ht)]

/-- Every path of `coinStep` is right-continuous. -/
theorem coinStep_rightCont (i : Fin 1) (ω : Bool) (t : ℝ) :
    Tendsto (fun s => coinStep i s ω) (𝓝[>] t) (𝓝 (coinStep i t ω)) := by
  rcases le_or_gt (1 / 2 : ℝ) t with ht | ht
  · rw [coinStep_of_le i ω ht]
    exact tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs =>
      (coinStep_of_le i ω (ht.trans (le_of_lt hs))).symm)
  · rw [coinStep_of_lt i ω ht]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT ht] with s hs
    exact (coinStep_of_lt i ω hs.2).symm

/-- Every path of `coinStep` has a left limit at every time. -/
theorem coinStep_leftLim (i : Fin 1) (ω : Bool) (t : ℝ) :
    ∃ L : ℝ, Tendsto (fun s => coinStep i s ω) (𝓝[<] t) (𝓝 L) := by
  rcases le_or_gt t (1 / 2 : ℝ) with ht | ht
  · exact ⟨0, tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs =>
      (coinStep_of_lt i ω (lt_of_lt_of_le hs ht)).symm)⟩
  · refine ⟨if ω then 1 else -1, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    exact (coinStep_of_le i ω hs.1.le).symm

/-- The energy over `[0, 1]` of a process bounded by `1` is finite. -/
theorem energy_ne_top_of_abs_le_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {H : Ω → ℝ → ℝ} (h : ∀ ω s, |H ω s| ≤ 1) :
    LevyStochCalc.Brownian.Ito.energy P 1 H ≠ ⊤ := by
  have hle : ∀ ω s, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ≤ 1 := fun ω s => by
    have h1 : ‖H ω s‖₊ ≤ 1 := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
      exact h ω s
    calc (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ≤ 1 ^ 2 := by gcongr; exact_mod_cast h1
      _ = 1 := one_pow 2
  refine ne_top_of_le_ne_top (b := ∫⁻ _, ∫⁻ _ in Set.Icc (0 : ℝ) 1, 1 ∂volume ∂P) ?_
    (lintegral_mono fun ω => lintegral_mono fun s => hle ω s)
  simp

/-- **The hypotheses of Lemma A.1 hold at a tuple that moves and jumps.** On `Bool` with the
uniform law and the full filtration, with `n = m = d = 1`, `ν = δ₀` on `ℝ` and `T = 1`:
`X = Y = ξ 1_{t ≥ 1/2}` for the fair sign `ξ`, `Z = U = 1_{(0, 1]}`. The paths of `X` jump at
`t = 1/2`, where the left limit `0` differs from the value `1` at `ω = true`, and `X_1` is not
almost surely constant. -/
theorem lemA1_hypotheses :
    CadlagPredTuple (⊤ : Filtration ℝ (inferInstance : MeasurableSpace Bool)) P𝔹
      (Measure.dirac (0 : ℝ)) 1 (n := 1) (m := 1) (d := 1) coinStep coinStep
      (fun _ s _ _ => unitWindow s) (fun _ s _ _ => unitWindow s)
    ∧ leftLimProc coinStep 0 (1 / 2) true ≠ coinStep 0 (1 / 2) true
    ∧ coinStep 0 1 true ≠ coinStep 0 1 false := by
  have habs : ∀ i ω s, |coinStep i s ω| ≤ 1 := fun i ω s => by
    unfold coinStep
    split_ifs <;> simp
  have hwin : ∀ s, |unitWindow s| ≤ 1 := fun s => by
    unfold unitWindow
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1 <;> simp [hs]
  refine ⟨⟨fun i t => measurable_from_top,
    fun i ω t => coinStep_rightCont i ω t, fun i ω t => coinStep_leftLim i ω t,
    fun k t => measurable_from_top,
    fun k ω t => coinStep_rightCont k ω t, fun k ω t => coinStep_leftLim k ω t,
    fun k j => predictable_unitWindow _, fun k => markedPredictable_unitWindow _ _,
    fun i => energy_ne_top_of_abs_le_one fun ω s => habs i ω s,
    fun k => energy_ne_top_of_abs_le_one fun ω s => habs k ω s,
    fun k j => energy_ne_top_of_abs_le_one fun ω s => hwin s, fun k => ?_⟩, ?_, ?_⟩
  · have h := energy_ne_top_of_abs_le_one (P := P𝔹) (H := fun _ s => unitWindow s)
      fun ω s => hwin s
    refine ne_top_of_le_ne_top h (le_of_eq ?_)
    unfold LevyStochCalc.Poisson.Compensated.markedEnergy LevyStochCalc.Brownian.Ito.energy
    simp
  · have hlim : Tendsto (fun r => coinStep 0 r true) (𝓝[<] (1 / 2)) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs =>
        (coinStep_of_lt 0 true (show s < 1 / 2 from hs)).symm)
    rw [leftLimProc, leftLim_eq_of_tendsto hlim,
      coinStep_of_le 0 true le_rfl]
    norm_num
  · rw [coinStep_of_le 0 true (by norm_num), coinStep_of_le 0 false (by norm_num)]
    norm_num

/-- **The hypotheses of the Fubini isometry of Lemma A.1 hold** at the uniform law on `Bool` and
`ν = δ₀` on `ℝ`. -/
theorem lemA1_fubini_hypotheses :
    IsProbabilityMeasure P𝔹 ∧ SigmaFinite (Measure.dirac (0 : ℝ)) ∧ Measure.dirac (0 : ℝ) ≠ 0
      ∧ MeasurableSpace.CountablyGenerated ℝ :=
  ⟨inferInstance, inferInstance, Measure.dirac_ne_zero, inferInstance⟩

/-- **The hypotheses of the Polish claim hold** at Lebesgue measure on `ℝ`, σ-finite of infinite
mass on a countably generated space, for which `L²(ν; ℝᵐ)` is infinite-dimensional. -/
theorem lemA1_polish_hypotheses :
    SigmaFinite (volume : Measure ℝ) ∧ MeasurableSpace.CountablyGenerated ℝ
      ∧ (volume : Measure ℝ) Set.univ = ⊤ :=
  ⟨inferInstance, inferInstance, Real.volume_univ⟩

end Witness

end Dissertation.Acceptance.A
