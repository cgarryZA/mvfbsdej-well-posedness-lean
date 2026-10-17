/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec4Horizon
import Dissertation.WellPosedness.Spec.Examples
import Dissertation.WellPosedness.Examples.BrownianSolves
import Dissertation.WellPosedness.Stability.LinearCongr
import Dissertation.WellPosedness.Enlarged.CrossWitness
import Dissertation.WellPosedness.BrownianPoisson.SupBound
import Dissertation.WellPosedness.BrownianPoisson.Example
import Dissertation.WellPosedness.BrownianPoisson.FrozenCell
import Dissertation.Acceptance.A.Sec3Space

/-!
# The horizon remark of §4 of the well-posedness paper: proof

On a scalar Brownian driver without jumps, the system of Example 5.1(i) with `σ_c = h_c = 0` has
`σ = −β₁ z`. Its frozen map at `λ = 1` sends the trial `(0, 0, 1_{[0, T]}, 0)` to
`(−β₁ W, −β₁ W, −β₁ 1_{[0, T]}, 0)`, whose `Z`-energy `β₁² T` is at least the trial's norm `T`,
whatever `T > 0`.

## Main definitions

* `Dissertation.Acceptance.A.bmNull`, `bmStop` — a measurable null set off which a Brownian path
  is continuous and starts at `0`, and the path stopped at `T`, frozen before `0` and set to `0`
  on that set.
* `Dissertation.Acceptance.A.cutConst` — a constant cut to `[0, T]`.

## Main statements

* `Dissertation.Acceptance.A.multidimStochasticIntegral_cutConst` — the Brownian integral of a
  constant row cut to `[0, T]` is `∑ⱼ cⱼ Wʲ_t` on `[0, T]`.
* `Dissertation.Acceptance.A.linearFSDE_horizon`, `linearBSDE_horizon` — `c W` stopped at `T` solves
  the forward and the backward linear equation with the diffusion `c` cut to `[0, T]`.
* `Dissertation.Acceptance.A.sec4_horizon_not_contractive`, with the witness
  `sec4_horizon_hypotheses`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Spec Dissertation.WellPosedness.BrownianPoisson LevyStochCalc
  LevyStochCalc.BSDEJ.Solves Dissertation.WellPosedness

universe u w

section Version

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A measurable null set off which the path of a Brownian motion is continuous and starts at
`0`. -/
noncomputable def bmNull (W : Brownian.BrownianMotion P) : Set Ω :=
  toMeasurable P {ω | ¬ (Continuous (fun t => W.W t ω) ∧ W.W 0 ω = 0)}

/-- The exceptional set of a Brownian motion is measurable. -/
theorem measurableSet_bmNull (W : Brownian.BrownianMotion P) : MeasurableSet (bmNull W) :=
  measurableSet_toMeasurable _ _

/-- The exceptional set of a Brownian motion is null. -/
theorem measure_bmNull (W : Brownian.BrownianMotion P) : P (bmNull W) = 0 := by
  rw [bmNull, measure_toMeasurable, ← ae_iff]
  filter_upwards [W.continuous_paths, W.initial_zero] with ω h1 h2
  exact ⟨h1, h2⟩

/-- Off the exceptional set the Brownian path is continuous and starts at `0`. -/
theorem good_of_notMem_bmNull {W : Brownian.BrownianMotion P} {ω : Ω} (hω : ω ∉ bmNull W) :
    Continuous (fun t => W.W t ω) ∧ W.W 0 ω = 0 := by
  by_contra h
  exact hω (subset_toMeasurable _ _ h)

/-- The path of `W` stopped at `T` and frozen before `0`, set to `0` on `bmNull W`:
`W_{0 ∨ (t ∧ T)}`. -/
noncomputable def bmStop (W : Brownian.BrownianMotion P) (T t : ℝ) (ω : Ω) : ℝ :=
  (bmNull W)ᶜ.indicator (fun ω => W.W (max 0 (min t T)) ω) ω

/-- Every path of the stopped Brownian motion is continuous. -/
theorem continuous_bmStop (W : Brownian.BrownianMotion P) (T : ℝ) (ω : Ω) :
    Continuous fun t => bmStop W T t ω := by
  by_cases hω : ω ∈ bmNull W
  · simp only [bmStop, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hω)]
    exact continuous_const
  · simp only [bmStop, Set.indicator_of_mem (Set.mem_compl hω)]
    exact (good_of_notMem_bmNull hω).1.comp
      (continuous_const.max (continuous_id.min continuous_const))

/-- The stopped Brownian motion vanishes at time `0` on every path. -/
theorem bmStop_zero (W : Brownian.BrownianMotion P) (T : ℝ) (ω : Ω) : bmStop W T 0 ω = 0 := by
  by_cases hω : ω ∈ bmNull W
  · simp [bmStop, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hω)]
  · simp only [bmStop, Set.indicator_of_mem (Set.mem_compl hω)]
    rw [show max 0 (min 0 T) = (0 : ℝ) from max_eq_left (min_le_left _ _)]
    exact (good_of_notMem_bmNull hω).2

/-- Almost surely the stopped Brownian motion is `W` on `[0, T]`. -/
theorem ae_bmStop_eq (W : Brownian.BrownianMotion P) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, bmStop W T t ω = W.W t ω := by
  have h : ∀ᵐ ω ∂P, ω ∉ bmNull W := by
    rw [ae_iff]; simpa using measure_bmNull W
  filter_upwards [h] with ω hω t ht
  simp only [bmStop, Set.indicator_of_mem (Set.mem_compl hω)]
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-- The stopped Brownian motion is adapted to a Brownian filtration that contains the exceptional
set at time `0` and is constant before `0`. -/
theorem measurable_bmStop {ℱ : Filtration ℝ mΩ} {W : Brownian.BrownianMotion P}
    (hW : Brownian.IsBrownianFiltration W ℱ) (hneg : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : MeasurableSet[ℱ 0] (bmNull W)) (T t : ℝ) :
    Measurable[ℱ t] (bmStop W T t) := by
  have hN : MeasurableSet[ℱ t] (bmNull W) := by
    rcases le_total t 0 with h | h
    · exact hneg t h _ hnull
    · exact ℱ.mono h _ hnull
  have hle : ℱ (max 0 (min t T)) ≤ ℱ t := by
    rcases le_total t 0 with h | h
    · rw [max_eq_left ((min_le_left _ _).trans h)]; exact hneg t h
    · exact ℱ.mono (max_le h (min_le_left _ _))
  exact ((hW.measurable _).mono hle le_rfl).indicator hN.compl

end Version

section Cut

/-- The constant `c` cut to `[0, T]`: `1_{[0, T]}(s) c`. -/
noncomputable def cutConst (T c s : ℝ) : ℝ := (Set.Icc (0 : ℝ) T).indicator (fun _ => c) s

/-- A cut constant is measurable. -/
theorem measurable_cutConst (T c : ℝ) : Measurable (cutConst T c) :=
  measurable_const.indicator measurableSet_Icc

/-- On `[0, T]` the cut constant is the constant. -/
theorem cutConst_of_mem {T c s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) : cutConst T c s = c :=
  Set.indicator_of_mem hs _

/-- Off `[0, T]` the cut constant vanishes. -/
theorem cutConst_of_notMem {T c s : ℝ} (hs : s ∉ Set.Icc (0 : ℝ) T) : cutConst T c s = 0 :=
  Set.indicator_of_notMem hs _

/-- A cut constant is predictable. -/
theorem predictable_cutConst {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ mΩ)
    (T c : ℝ) : Probability.Predictable ℱ fun (_ : Ω) s => cutConst T c s :=
  predictable_of_measurable_time (measurable_cutConst T c)

/-- A cut constant is progressively measurable for a filtration constant before `0`. -/
theorem progressivelyMeasurable_cutConst {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℝ mΩ) (hneg : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t) (T c : ℝ) :
    Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) s => cutConst T c s :=
  (predictable_cutConst ℱ T c).progressivelyMeasurable hneg

/-- The energy of the constant `c` cut to `[0, T]` is `|c|² T`. -/
theorem energy_cutConst {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T c : ℝ) :
    Brownian.Ito.energy P T (fun (_ : Ω) s => cutConst T c s)
      = (‖c‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal T := by
  have h : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖cutConst T c s‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = (‖c‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal T := by
    rw [setLIntegral_congr_fun measurableSet_Icc fun s hs => by rw [cutConst_of_mem hs]]
    simp [Real.volume_Icc]
  simp only [Brownian.Ito.energy, h, lintegral_const, measure_univ, mul_one]

end Cut

section Integral

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
  (W : Brownian.Multidim.MultidimBrownianMotion P d) (ℱ : Filtration ℝ mΩ)
  (hℱ : ∀ j, Brownian.IsBrownianFiltration (W.W j) ℱ)

include hℱ in
/-- The Brownian integral of a constant row `c` cut to `[0, T]` is `∑ⱼ cⱼ Wʲ_t` almost surely at
each `t ∈ [0, T]`. -/
theorem multidimStochasticIntegral_cutConst {T : ℝ} (hT : 0 < T) (c : Fin d → ℝ)
    (hm : ∀ j, Measurable (Function.uncurry fun (_ : Ω) s => cutConst T (c j) s))
    (hp : ∀ j, Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) s => cutConst T (c j) s)
    (hq : ∀ j, ∀ T', 0 < T' → ∫⁻ _ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖cutConst T (c j) s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ
        (fun s (_ : Ω) j => cutConst T (c j) s) hm hp hq t
      =ᵐ[P] fun ω => ∑ j, c j * (W.W j).W t ω := by
  have h0 : ∀ j, ∀ᵐ ω ∂P, (W.W j).W 0 ω = 0 := fun j => (W.W j).initial_zero
  rcases eq_or_lt_of_le ht.1 with rfl | htpos
  · filter_upwards [Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos
      W ℱ hℱ _ hm hp hq le_rfl, ae_all_iff.2 h0] with ω h1 h2
    rw [h1]
    simp [h2]
  · have hcm : ∀ j, MemLp (fun (_ : Ω) => c j) 2 P := fun j => memLp_const _
    have hca : ∀ j, StronglyMeasurable[ℱ 0] fun (_ : Ω) => c j := fun j => stronglyMeasurable_const
    have hm' : ∀ j, Measurable (Function.uncurry fun ω r =>
        frozenCellVec 0 T (fun (_ : Ω) => c) r ω j) :=
      measurable_frozenCellVec 0 T (z := fun (_ : Ω) => c) fun j => measurable_const
    have hp' : ∀ j, Probability.ProgressivelyMeasurable ℱ fun ω r =>
        frozenCellVec 0 T (fun (_ : Ω) => c) r ω j :=
      progressivelyMeasurable_frozenCellVec (z := fun (_ : Ω) => c) fun j => measurable_const
    have hq' := frozenCellVec_sq_int (P := P) 0 T (z := fun (_ : Ω) => c) hcm
    have hs0 : ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) t), s ≠ 0 := by
      refine ae_restrict_of_ae ?_
      rw [ae_iff]
      simp
    have hcongr := Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_congr_ae W ℱ hℱ
      hm hp hq hm' hp' hq' htpos (ae_of_all _ fun ω => by
        filter_upwards [ae_restrict_mem measurableSet_Icc, hs0] with s hs hs0
        funext j
        have hpos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
        simp [frozenCellVec, frozenCell, cutConst_of_mem
          (show s ∈ Set.Icc (0 : ℝ) T from ⟨hs.1, hs.2.trans ht.2⟩),
          Set.indicator_of_mem (show s ∈ Set.Ioc (0 : ℝ) T from ⟨hpos, hs.2.trans ht.2⟩)])
    filter_upwards [hcongr, multidimStochasticIntegral_frozenCell W ℱ hℱ le_rfl hT hcm hca hm'
      hp' hq' ht.1, ae_all_iff.2 h0] with ω h1 h2 h3
    rw [h1, h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [min_eq_right ht.2, min_eq_left ht.1, h3 j, sub_zero]

end Integral

section Affine

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {T β₁ β₂ : ℝ}

/-- The drift process of Example 5.1(i) for `n = d = 1`, `σ_c = h_c = 0`, `ν = 0`:
`1_{[0, T]}(s) (−β₁ Y_s)`. -/
theorem driftProc_affine_one (X Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
    (U : Fin 1 → ℝ → Ω → Unit → ℝ) (i : Fin 1) (ω : Ω) (s : ℝ) :
    driftProc P T (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1) β₁ β₂ 0 0)
      X Y Z U i ω s = (Set.Icc (0 : ℝ) T).indicator (fun s => -(β₁ * Y i s ω)) s := by
  simp [driftProc, affineCoeffs, tupleAt]

/-- The diffusion process of Example 5.1(i) for `n = d = 1`, `σ_c = h_c = 0`, `ν = 0`:
`1_{[0, T]}(s) (−β₁ Z_s)`. -/
theorem diffusionProc_affine_one (X Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
    (U : Fin 1 → ℝ → Ω → Unit → ℝ) (i : Fin 1) (s : ℝ) (ω : Ω) (j : Fin 1) :
    diffusionProc P T (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1) β₁ β₂ 0 0)
      X Y Z U i s ω j = (Set.Icc (0 : ℝ) T).indicator (fun s => -(β₁ * Z i s ω j)) s := by
  simp [diffusionProc, affineCoeffs, tupleAt]

/-- The driver process of Example 5.1(i) for `n = d = 1`, `σ_c = h_c = 0`, `ν = 0`:
`1_{[0, T]}(s) β₂ X_s`. -/
theorem driverProc_affine_one (X Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
    (U : Fin 1 → ℝ → Ω → Unit → ℝ) (k : Fin 1) (ω : Ω) (s : ℝ) :
    driverProc P T (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1) β₁ β₂ 0 0)
      X Y Z U k ω s = (Set.Icc (0 : ℝ) T).indicator (fun s => β₂ * X k s ω) s := by
  simp [driverProc, affineCoeffs, tupleAt]

/-- The terminal value of Example 5.1(i) is `X_T`. -/
theorem terminalVal_affine_one (X : Fin 1 → ℝ → Ω → ℝ) (k : Fin 1) (ω : Ω) :
    terminalVal P T (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1) β₁ β₂ 0 0)
      X k ω = X k T ω := by
  simp [terminalVal, affineCoeffs]

end Affine

section Zero

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
  (W : Brownian.Multidim.MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j, Brownian.IsBrownianFiltration (W.W j) ℱ)

/-- The zero process solves the linear forward Brownian equation with zero data. -/
theorem linearFSDE_zero (T : ℝ) :
    LinearFSDE W ℱ hℱW T (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) where
  σ_meas _ := measurable_const
  σ_prog _ := Probability.progressivelyMeasurable_zero _
  σ_vanish _ _ _ := rfl
  σ_sq _ := by simp [Brownian.Ito.energy]
  b_meas := measurable_const
  b_prog := Probability.progressivelyMeasurable_zero _
  b_vanish _ _ _ := rfl
  b_sq := by simp [Brownian.Ito.energy]
  ξ₀_sq := memLp_const 0
  X_adapted _ := measurable_const
  X_rightCont _ _ := tendsto_const_nhds
  eqn t _ := by
    filter_upwards [multidimStochasticIntegral_zero_ae W ℱ hℱW (fun _ => measurable_const)
      (fun _ => Probability.progressivelyMeasurable_zero _) (fun _ _ _ => by simp) t] with ω h
    simp only [Pi.zero_apply] at h
    rw [h]
    simp

/-- The zero pair solves the linear backward Brownian equation with zero data. -/
theorem linearBSDE_zero (T : ℝ) :
    LinearBSDE W ℱ hℱW T (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) where
  Z_meas _ := measurable_const
  Z_prog _ := Probability.progressivelyMeasurable_zero _
  Z_vanish _ _ _ := rfl
  Z_sq _ := by simp [Brownian.Ito.energy]
  φ_meas := measurable_const
  φ_prog := Probability.progressivelyMeasurable_zero _
  φ_vanish _ _ _ := rfl
  φ_sq := by simp [Brownian.Ito.energy]
  ξ_sq := memLp_const 0
  Y_adapted _ := measurable_const
  Y_rightCont _ _ := tendsto_const_nhds
  eqn t _ := by
    have hW := multidimStochasticIntegral_zero_ae W ℱ hℱW (fun _ => measurable_const)
      (fun _ => Probability.progressivelyMeasurable_zero _) (fun _ _ _ => by simp)
    filter_upwards [hW T, hW t] with ω h1 h2
    simp only [Pi.zero_apply] at h1 h2
    rw [h1, h2]
    simp

end Zero

section Horizon

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] (D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (0 : Measure Unit))
  (h𝒢₀ : 𝒢₀ ≤ mΩ) (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P)

include hind₀ in
/-- The stopped Brownian motion is adapted to the filtration of §2. -/
theorem measurable_bmStop_enlJoint (T t : ℝ) :
    Measurable[enlJoint 𝒢₀ D h𝒢₀ t] (bmStop (D.W.W 0) T t) :=
  measurable_bmStop (isBrownianFiltration_enlJoint D h𝒢₀ hind₀ 0)
    (fun _ ht => enlJoint_le_of_nonpos D h𝒢₀ ht)
    (measurableSet_enlJoint_of_null D h𝒢₀ (measurableSet_bmNull _) (measure_bmNull _)) T t

/-- A multiple of the stopped Brownian motion is continuous in time along every path. -/
theorem tendsto_mul_bmStop (c T t : ℝ) (ω : Ω) (l : Filter ℝ) (hl : l ≤ 𝓝 t) :
    Tendsto (fun s => c * bmStop (D.W.W 0) T s ω) l (𝓝 (c * bmStop (D.W.W 0) T t ω)) :=
  ((continuous_const.mul (continuous_bmStop _ T ω)).tendsto t).mono_left hl

/-- `c W_t`, stopped at `T`, solves the forward equation with zero drift and the diffusion `c`
cut to `[0, T]`. -/
theorem linearFSDE_horizon {T : ℝ} (hT : 0 < T) (c : ℝ) :
    LinearFSDE D.W (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) T
      (fun _ => 0) (fun _ _ => 0) (fun t ω => c * bmStop (D.W.W 0) T t ω)
      (fun s _ _ => cutConst T c s) where
  σ_meas _ := (measurable_cutConst T c).comp measurable_snd
  σ_prog _ := progressivelyMeasurable_cutConst _ (fun _ ht => enlJoint_le_of_nonpos D h𝒢₀ ht) T c
  σ_vanish _ _ hs := funext fun _ => cutConst_of_notMem hs
  σ_sq _ := by
    rw [energy_cutConst]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  b_meas := measurable_const
  b_prog := Probability.progressivelyMeasurable_zero _
  b_vanish _ _ _ := rfl
  b_sq := by simp [Brownian.Ito.energy]
  ξ₀_sq := memLp_const 0
  X_adapted t := (measurable_bmStop_enlJoint D h𝒢₀ hind₀ T t).const_mul c
  X_rightCont ω t := tendsto_mul_bmStop D c T t ω _ nhdsWithin_le_nhds
  eqn t ht := by
    filter_upwards [multidimStochasticIntegral_cutConst D.W _
      (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) hT (fun _ => c) _ _ _ ht,
      ae_bmStop_eq (D.W.W 0) T] with ω h1 h2
    rw [h1, h2 t ht]
    simp

/-- `c W_t`, stopped at `T`, with `Z = c` on `[0, T]`, solves the backward equation with the
terminal value `c W_T` and zero drift. -/
theorem linearBSDE_horizon {T : ℝ} (hT : 0 < T) (c : ℝ) :
    LinearBSDE D.W (enlJoint 𝒢₀ D h𝒢₀) (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) T
      (fun ω => c * bmStop (D.W.W 0) T T ω) (fun _ _ => 0)
      (fun t ω => c * bmStop (D.W.W 0) T t ω) (fun s _ _ => cutConst T c s) where
  Z_meas _ := (measurable_cutConst T c).comp measurable_snd
  Z_prog _ := progressivelyMeasurable_cutConst _ (fun _ ht => enlJoint_le_of_nonpos D h𝒢₀ ht) T c
  Z_vanish _ _ hs := funext fun _ => cutConst_of_notMem hs
  Z_sq _ := by
    rw [energy_cutConst]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  φ_meas := measurable_const
  φ_prog := Probability.progressivelyMeasurable_zero _
  φ_vanish _ _ _ := rfl
  φ_sq := by simp [Brownian.Ito.energy]
  ξ_sq := by
    have hinc := Brownian.Ito.memLp_increment (D.W.W 0) (le_refl (0 : ℝ)) hT 2 (by simp)
    refine (hinc.ae_eq ?_).const_mul c
    filter_upwards [ae_bmStop_eq (D.W.W 0) T, (D.W.W 0).initial_zero] with ω h1 h2
    rw [h1 T ⟨hT.le, le_rfl⟩, h2, sub_zero]
  Y_adapted t := (measurable_bmStop_enlJoint D h𝒢₀ hind₀ T t).const_mul c
  Y_rightCont ω t := tendsto_mul_bmStop D c T t ω _ nhdsWithin_le_nhds
  eqn t ht := by
    have hI := fun r (hr : r ∈ Set.Icc (0 : ℝ) T) => multidimStochasticIntegral_cutConst D.W _
      (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) hT (fun _ => c)
      (fun _ => (measurable_cutConst T c).comp measurable_snd)
      (fun _ => progressivelyMeasurable_cutConst _
        (fun _ ht => enlJoint_le_of_nonpos D h𝒢₀ ht) T c)
      (sq_int_global_of_vanishing (fun _ _ hs => funext fun _ => cutConst_of_notMem hs)
        fun _ => by
          rw [energy_cutConst]
          exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hr
    filter_upwards [hI T ⟨hT.le, le_rfl⟩, hI t ht, ae_bmStop_eq (D.W.W 0) T] with ω h1 h2 h3
    rw [h1, h2, h3 t ht, h3 T ⟨hT.le, le_rfl⟩]
    simp

end Horizon

/-- §4, the horizon: on every horizon, the frozen map of Lemma 4.2 for a system of Example 5.1(i)
does not decrease the distance of the trial `(0, 0, 1_{[0, T]}, 0)` from `0`. -/
theorem sec4_horizon_not_contractive : PaperSpec.A.sec4_horizon_not_contractive.{u, w} := by
  intro Ω 𝒢₀ mΩ P _ D h𝒢₀ hind₀ T β₁ β₂ hT hβ₁ hβ₂
  have hW := isBrownianFiltration_enlJoint D h𝒢₀ hind₀
  have hN := isPoissonFiltration_enlJoint D h𝒢₀ hind₀
  obtain ⟨hJ, h22, -, hG, h25⟩ := affine_assumptions (ν := (0 : Measure Unit)) (n := 1) (d := 1)
    (ℱ := enlJoint 𝒢₀ D h𝒢₀) (P := P) (T := T) (σc := 0) (hc := 0) (β₁ := β₁) (β₂ := β₂)
    (by linarith) hβ₂ 0
  have h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T (β₁ + β₂)
      (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1) β₁ β₂ 0 0) :=
    ⟨by linarith, LipInterior.of_diagonalLipschitz (diagonalLipschitz_affine (by linarith)
      hβ₂.le (max_le (by linarith) (by linarith))), terminalLipschitz_affine (by linarith)⟩
  have hzero : PaperSpec.A.BrownianFrozenStep 𝒢₀ D h𝒢₀ hind₀ T
      (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1) β₁ β₂ 0 0) 0 0 0 0 0 0 0 0 := by
    refine ⟨fun i => ?_, fun k => ?_⟩
    · have e1 : driftProc P T (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1)
          β₁ β₂ 0 0) 0 0 0 0 i = fun _ _ => 0 := by
        funext ω s; simp [driftProc_affine_one]
      have e2 : diffusionProc P T (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1)
          β₁ β₂ 0 0) 0 0 0 0 i = fun _ _ => 0 := by
        funext s ω j; simp [diffusionProc_affine_one]
      rw [e1, e2]
      exact (linearFSDE_zero D.W _ hW T).linearFSDEJ
    · have e1 : terminalVal P T (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1)
          β₁ β₂ 0 0) 0 k = fun _ => 0 := by
        funext ω; simp [terminalVal_affine_one]
      have e2 : driverProc P T (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1)
          β₁ β₂ 0 0) 0 0 0 0 k = fun _ _ => 0 := by
        funext ω s; simp [driverProc_affine_one]
      rw [e1, e2]
      exact (linearBSDE_zero D.W _ hW T).linearBSDEJ
  have hfwd := (linearFSDE_horizon D h𝒢₀ hind₀ hT (-β₁)).linearFSDEJ (hℱN := hN)
  have hbwd := (linearBSDE_horizon D h𝒢₀ hind₀ hT (-β₁)).linearBSDEJ (hℱN := hN)
  have hEZ : Brownian.Ito.energy P T (fun (_ : Ω) s => cutConst T (-β₁) s) ≠ ⊤ := by
    rw [energy_cutConst]
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  -- the supremum of the output is finite
  have hsupY : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
      esq (fun (_ : Fin 1) => -β₁ * bmStop (D.W.W 0) T t ω)) ∂P < ⊤ := by
    have h := hbwd.lintegral_biSup_sq_le (crossWitnessEnl D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀)
      (fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0) hT
    simp only [bmStop_zero, mul_zero, nnnorm_zero, ENNReal.coe_zero] at h
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt h ?_)
    · simp [esq]
    · simp only [Fin.sum_univ_one, markedEnergy_nu_zero]
      have hφ : Brownian.Ito.energy P T (fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) = 0 := by
        simp [Brownian.Ito.energy]
      rw [hφ]
      simpa using ENNReal.mul_lt_top (by simp) hEZ.lt_top
  have hsqY : Brownian.Ito.energy P T (fun ω s => -β₁ * bmStop (D.W.W 0) T s ω) ≠ ⊤ :=
    (Dissertation.Acceptance.A.sec3_HH_inclusion P 1 T hT.le
      (fun (_ : Fin 1) t ω => -β₁ * bmStop (D.W.W 0) T t ω)).2 hsupY 0
  have hβ : (1 : ℝ≥0∞) ≤ (‖-β₁‖₊ : ℝ≥0∞) ^ 2 := by
    refine one_le_pow₀ ?_
    rw [← ENNReal.coe_one, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one,
      norm_neg, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact hβ₁
  have htrial : PaperSpec.A.BrownianFrozenStep 𝒢₀ D h𝒢₀ hind₀ T
      (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1) β₁ β₂ 0 0) 0 0
      (fun _ s _ _ => cutConst T 1 s) 0
      (fun _ t ω => -β₁ * bmStop (D.W.W 0) T t ω) (fun _ t ω => -β₁ * bmStop (D.W.W 0) T t ω)
      (fun _ s _ _ => cutConst T (-β₁) s) (fun _ _ _ _ => 0) := by
    refine ⟨fun i => ?_, fun k => ?_⟩
    · have e1 : driftProc P T (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1)
          β₁ β₂ 0 0) 0 0 (fun _ s _ _ => cutConst T 1 s) 0 i = fun _ _ => 0 := by
        funext ω s; simp [driftProc_affine_one]
      have e2 : diffusionProc P T (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1)
          β₁ β₂ 0 0) 0 0 (fun _ s _ _ => cutConst T 1 s) 0 i
          = fun s _ _ => cutConst T (-β₁) s := by
        funext s ω j
        rw [diffusionProc_affine_one]
        by_cases hs : s ∈ Set.Icc (0 : ℝ) T
        · simp [Set.indicator_of_mem hs, cutConst_of_mem hs]
        · simp [Set.indicator_of_notMem hs, cutConst_of_notMem hs]
      rw [e1, e2]
      exact hfwd
    · have e1 : terminalVal P T (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1)
          β₁ β₂ 0 0) (fun _ t ω => -β₁ * bmStop (D.W.W 0) T t ω) k
          = fun ω => -β₁ * bmStop (D.W.W 0) T T ω := by
        funext ω; simp [terminalVal_affine_one]
      have e2 : driverProc P T (affineCoeffs (ν := (0 : Measure Unit)) (n := 1) (d := 1)
          β₁ β₂ 0 0) 0 0 (fun _ s _ _ => cutConst T 1 s) 0 k = fun _ _ => 0 := by
        funext ω s; simp [driverProc_affine_one]
      rw [e1, e2]
      exact hbwd
  have hst : supSize (n := 1) (m := 1) (d := 1) P (0 : Measure Unit) T 0 0
      (fun _ s _ _ => cutConst T 1 s) 0
      = ENNReal.ofReal T := by
    simp [supSize, esq, energy_cutConst, markedEnergy_nu_zero]
  refine ⟨hJ, h22, h23, hG, h25, hzero, fun _ s _ _ => cutConst T 1 s,
    fun _ t ω => -β₁ * bmStop (D.W.W 0) T t ω, fun _ t ω => -β₁ * bmStop (D.W.W 0) T t ω,
    fun _ s _ _ => cutConst T (-β₁) s, fun _ _ _ _ => 0, ?_, fun t ht ω => cutConst_of_mem ht,
    ?_, htrial, ?_, fun t ht ω => ⟨cutConst_of_mem ht, rfl⟩, ?_, ?_, ?_⟩
  · exact
      { X_adapted := fun _ _ _ => measurable_const
        X_rightCont := fun _ _ _ _ => tendsto_const_nhds
        X_leftLim := fun _ => ae_of_all _ fun _ _ _ => ⟨0, tendsto_const_nhds⟩
        X_sq := fun _ => by simp [Brownian.Ito.energy]
        Y_adapted := fun _ _ _ => measurable_const
        Y_rightCont := fun _ _ _ _ => tendsto_const_nhds
        Y_leftLim := fun _ => ae_of_all _ fun _ _ _ => ⟨0, tendsto_const_nhds⟩
        Y_sq := fun _ => by simp [Brownian.Ito.energy]
        Z_pred := fun _ _ => predictable_cutConst _ T 1
        Z_vanish := fun _ _ _ hs => funext fun _ => cutConst_of_notMem hs
        Z_sq := fun _ _ => by
          rw [energy_cutConst]
          exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
        U_pred := fun _ => measurable_const
        U_vanish := fun _ _ _ _ _ => rfl
        U_sq := fun _ => by rw [markedEnergy_nu_zero]; exact ENNReal.zero_ne_top }
  · exact
      { X_adapted := fun _ t _ => (measurable_bmStop_enlJoint D h𝒢₀ hind₀ T t).const_mul _
        X_rightCont := fun _ ω t _ => tendsto_mul_bmStop D _ T t ω _ nhdsWithin_le_nhds
        X_leftLim := fun _ => ae_of_all _ fun ω t _ =>
          ⟨_, tendsto_mul_bmStop D (-β₁) T t ω _ nhdsWithin_le_nhds⟩
        X_sq := fun _ => hsqY
        Y_adapted := fun _ t _ => (measurable_bmStop_enlJoint D h𝒢₀ hind₀ T t).const_mul _
        Y_rightCont := fun _ ω t _ => tendsto_mul_bmStop D _ T t ω _ nhdsWithin_le_nhds
        Y_leftLim := fun _ => ae_of_all _ fun ω t _ =>
          ⟨_, tendsto_mul_bmStop D (-β₁) T t ω _ nhdsWithin_le_nhds⟩
        Y_sq := fun _ => hsqY
        Z_pred := fun _ _ => predictable_cutConst _ T (-β₁)
        Z_vanish := fun _ _ _ hs => funext fun _ => cutConst_of_notMem hs
        Z_sq := fun _ _ => hEZ
        U_pred := fun _ => measurable_const
        U_vanish := fun _ _ _ _ _ => rfl
        U_sq := fun _ => by rw [markedEnergy_nu_zero]; exact ENNReal.zero_ne_top }
  · filter_upwards [ae_bmStop_eq (D.W.W 0) T] with ω h t ht
    exact ⟨by rw [h t ht], by rw [h t ht]⟩
  · rw [hst]
    exact ENNReal.ofReal_pos.2 hT
  · rw [hst]
    simp only [supSize, Fin.sum_univ_one, energy_cutConst, markedEnergy_nu_zero, add_zero]
    exact (le_mul_of_one_le_left' hβ).trans le_add_self
  · simp only [supSize, Fin.sum_univ_one, energy_cutConst, markedEnergy_nu_zero, add_zero]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hsupY.ne, hsupY.ne⟩,
      ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top⟩

/-- **The hypotheses of the horizon remark hold.** There are a probability space, a Lévy driver on
it with `d = 1` and `ν = 0` on a point, the trivial initial σ-field, and `T = β₁ = β₂ = 1`. -/
theorem sec4_horizon_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (0 : Measure Unit))
      (_ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P),
      (0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 1 ∧ (0 : ℝ) < 1 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 Unit (0 : Measure Unit)
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, one_pos, le_rfl, one_pos⟩

end Dissertation.Acceptance.A
