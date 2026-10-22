/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec4Frozen
import MVFBSDEJ.Acceptance.Sec4Coeff
import MVFBSDEJ.WellPosedness.Spec.CoeffDiff
import MVFBSDEJ.WellPosedness.Existence.CoeffPredictable
import MVFBSDEJ.WellPosedness.System.FrozenLegs

/-!
# The frozen step and the coefficient differences in the proof of Lemma 4.2: proofs

Statement and equation numbers refer to the well-posedness paper at `1f67672`.

* (4.7): the coefficient processes along the trial have finite energy by (4.2)
  (`MVFBSDEJ.Acceptance.eq_coeffint`). Along the trial the integrals of (1.1) exist
  (`MVFBSDEJ.WellPosedness.System.PaperWeakTuple.exists_paperAdmissible`), with a jump
  representative `γ` of the coefficient at the predictable tuple, and `λ Ψ(Θ) + q` is a forcing
  (`MVFBSDEJ.WellPosedness.System.PaperAdmissible.forcing`); the linear forward equation from
  `ξ₀` with these integrands has a solution
  (`MVFBSDEJ.WellPosedness.System.Forcing.exists_linearFSDEJ`), which set to `0` off a null set
  has càdlàg paths (`MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ.indicator`), in `S²`
  (`MVFBSDEJ.WellPosedness.System.lintegral_biSup_esq_lt_top_of_linearFSDEJ`). Two
  representatives of the jump coefficient give integrands that agree for the marked energy measure
  (`MVFBSDEJ.WellPosedness.System.ae_forcedJump_eq_of_rep`), so two solutions are
  indistinguishable on `[0, T]`
  (`MVFBSDEJ.WellPosedness.Stability.LinearFSDEJ.ae_forall_Icc_eq`).
* (4.8): the terminal value is `ℱ_T`-measurable and square integrable by (4.3)
  (`MVFBSDEJ.WellPosedness.Existence.lintegral_esq_terminalVal_le`), and so is the drift
  integral. Along the càdlàg solution of (4.7), the terminal representation of the filtration of §2
  (`MVFBSDEJ.WellPosedness.Existence.hasTerminalRep_enlJoint`) solves the backward equation
  (`MVFBSDEJ.WellPosedness.Existence.HasTerminalRep.exists_linearBSDEJ`), with predictable
  integrands (`MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.exists_predictable`) and `Ȳ`
  set to `0` off a null set (`MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.indicator`).
  Two images agree in `𝕊`: their forward coordinates by (4.7), and then their terminal values almost
  surely, so Lemma 4.1 applied to the difference of the backward coordinates
  (`MVFBSDEJ.WellPosedness.BrownianPoisson.LinearBSDEJ.eq_of_ae_eq_terminal`) gives the rest.
* (4.9): at almost every time the two trials are diagonal inputs, and the interior bound of
  Assumption 2.3 in mean square
  (`MVFBSDEJ.WellPosedness.Spec.LipInteriorAt.lintegral_sq_coeffDiff_le`, with the Hilbert-norm
  `W₂` and (2.8)) gives the first link; the second dominates the `X`- and `Y`-slots by their suprema
  and reads the `Z`- and `U`-slots by Tonelli
  (`MVFBSDEJ.WellPosedness.System.setLIntegral_lintegral_coords_le`) along the progressive
  extensions of the trials (`MVFBSDEJ.WellPosedness.System.PaperWeakTuple.exists_progTuple`);
  the third is `T ≤ max{T, 1}` and `1 ≤ max{T, 1}`.

## Main statements

* `MVFBSDEJ.Acceptance.FrozenForward.ae_forall_Icc_eq` — uniqueness for (4.7).
* `MVFBSDEJ.Acceptance.FrozenForward.exists_leftLim` — a càdlàg solution of (4.7).
* `MVFBSDEJ.Acceptance.eq_frozenfwd` — (4.7).
* `MVFBSDEJ.Acceptance.eq_frozenbwd` — (4.8).
* `MVFBSDEJ.Acceptance.eq_coeffdiff` — (4.9).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.WellPosedness.BrownianPoisson
  MVFBSDEJ.PaperSpec MVFBSDEJ.Law LevyStochCalc

universe u v w

/-- (4.9). -/
theorem eq_coeffdiff : PaperSpec.eq_coeffdiff.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ _ _ _ _ T hT L C ξ₀ _ _ h23 X₁ X₂ Y₁ Y₂ Z₁ Z₂
    U₁ U₂ ⟨hw₁, -, -, -, -⟩ ⟨hw₂, -, -, -, -⟩
  obtain ⟨X₁', Y₁', hXe₁, hYe₁, hP₁, -, -⟩ := hw₁.exists_progTuple hT.le
  obtain ⟨X₂', Y₂', hXe₂, hYe₂, hP₂, -, -⟩ := hw₂.exists_progTuple hT.le
  refine ⟨?_, ?_, ?_⟩
  -- the first link, at almost every time
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [h23.interior, hw₁.ae_memLp_tupleAt hT.le, hw₂.ae_memLp_tupleAt hT.le,
      hw₁.ae_ae_memLp_jump, hw₂.ae_ae_memLp_jump, ae_restrict_mem measurableSet_Icc]
      with s hLs hm₁ hm₂ hU₁ hU₂ hs
    refine (hLs.lintegral_sq_coeffDiff_le (hw₁.stronglyMeasurable_tupleAt hs) hm₁
      (hw₂.stronglyMeasurable_tupleAt hs) hm₂).trans ?_
    gcongr ENNReal.ofReal (10 * L ^ 2) * ?_
    refine lintegral_mono_ae ?_
    filter_upwards [hU₁, hU₂] with ω h₁ h₂
    rw [tupleAt_sub h₁ h₂]
    exact ofReal_channelSq_tupleAt_le s ω
  -- the second link, through the progressive extensions
  · gcongr ENNReal.ofReal (10 * L ^ 2) * ?_
    have eX : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω i,
        X₁' i s ω - X₂' i s ω = X₁ i s ω - X₂ i s ω := fun s hs ω i => by
      rw [congrFun (hXe₁ i s hs) ω, congrFun (hXe₂ i s hs) ω]
    have eY : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω k,
        Y₁' k s ω - Y₂' k s ω = Y₁ k s ω - Y₂ k s ω := fun s hs ω k => by
      rw [congrFun (hYe₁ k s hs) ω, congrFun (hYe₂ k s hs) ω]
    have key := setLIntegral_lintegral_coords_le (P := P) (ν := ν) (T := T)
      (X := fun i t ω => X₁' i t ω - X₂' i t ω) (Y := fun k t ω => Y₁' k t ω - Y₂' k t ω)
      (Z := fun k t ω j => Z₁ k t ω j - Z₂ k t ω j) (U := fun k t ω e => U₁ k t ω e - U₂ k t ω e)
      (fun i => (hP₁.measurable_X i).sub (hP₂.measurable_X i))
      (fun k => (hP₁.measurable_Y k).sub (hP₂.measurable_Y k))
      (fun k j => (hP₁.Z_meas k j).sub (hP₂.Z_meas k j))
      (fun k => (hP₁.U_meas k).sub (hP₂.U_meas k))
    have e1 : ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, (esq (fun i => X₁ i s ω - X₂ i s ω)
          + esq (fun k => Y₁ k s ω - Y₂ k s ω) + ∑ k, esq (fun j => Z₁ k s ω j - Z₂ k s ω j)
          + ∑ k, ∫⁻ e, (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P
        = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, (esq (fun i => X₁' i s ω - X₂' i s ω)
          + esq (fun k => Y₁' k s ω - Y₂' k s ω) + ∑ k, esq (fun j => Z₁ k s ω j - Z₂ k s ω j)
          + ∑ k, ∫⁻ e, (‖U₁ k s ω e - U₂ k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P :=
      setLIntegral_congr_fun measurableSet_Icc fun s hs => lintegral_congr fun ω => by
        simp only [eX s hs ω, eY s hs ω]
    have e2 : ∀ {ι : Type} [Fintype ι] {x x' : ι → ℝ → Ω → ℝ},
        (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω i, x' i s ω = x i s ω) →
        ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x' i t ω)) ∂P
          = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂P := by
      intro ι _ x x' h
      refine lintegral_congr fun ω => iSup_congr fun t => iSup_congr fun ht => ?_
      simp only [h t ht ω]
    rw [e1]
    refine key.trans_eq ?_
    rw [e2 (x := fun i t ω => X₁ i t ω - X₂ i t ω) eX,
      e2 (x := fun k t ω => Y₁ k t ω - Y₂ k t ω) eY]
  -- the third link
  · have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max T 1) := ENNReal.one_le_ofReal.mpr (le_max_right _ _)
    have hT1 : ENNReal.ofReal T ≤ ENNReal.ofReal (max T 1) :=
      ENNReal.ofReal_le_ofReal (le_max_left _ _)
    rw [ENNReal.ofReal_mul (p := 10 * L ^ 2) (q := max T 1) (by positivity), mul_assoc]
    gcongr ENNReal.ofReal (10 * L ^ 2) * ?_
    unfold supSize
    set A := ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X₁ i t ω - X₂ i t ω)) ∂P
    set B := ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y₁ k t ω - Y₂ k t ω)) ∂P
    set J₁ := ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z₁ k s ω j - Z₂ k s ω j)
    set J₂ := ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ k s ω e - U₂ k s ω e)
    calc ENNReal.ofReal T * A + ENNReal.ofReal T * B + (J₁ + J₂)
        ≤ ENNReal.ofReal (max T 1) * A + ENNReal.ofReal (max T 1) * B
          + (ENNReal.ofReal (max T 1) * J₁ + ENNReal.ofReal (max T 1) * J₂) := by
          gcongr
          · exact le_mul_of_one_le_left' h1
          · exact le_mul_of_one_le_left' h1
      _ = ENNReal.ofReal (max T 1) * (A + B + J₁ + J₂) := by ring

/-! ### The frozen forward equation -/

section Frozen

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
  {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {h𝒢₀ : 𝒢₀ ≤ mΩ}
  {hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P} {T lam : ℝ} {C : Coeffs ν n m d}
  {ξ₀ : Ω → EuclideanSpace ℝ (Fin n)} {qb : Fin n → Ω → ℝ → ℝ}
  {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ} {X : Fin n → ℝ → Ω → ℝ}
  {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}

/-- Two solutions of the frozen forward equation (4.7) are indistinguishable on `[0, T]`. -/
theorem FrozenForward.ae_forall_Icc_eq {X₁ X₂ : Fin n → ℝ → Ω → ℝ}
    (h₁ : FrozenForward D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh X Y Z U X₁)
    (h₂ : FrozenForward D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh X Y Z U X₂) (hT : 0 ≤ T) (i : Fin n) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X₁ i t ω = X₂ i t ω := by
  obtain ⟨γ₁, hr₁, h₁⟩ := h₁
  obtain ⟨γ₂, hr₂, h₂⟩ := h₂
  exact (h₁ i).ae_forall_Icc_eq (h₂ i) (ae_forcedJump_eq_of_rep
    (F := fun s ω => ⇑(C.h s (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
      (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)))) lam qh i hr₁ hr₂
    (measurableSet_eq_fun (h₁ i).γ_meas (h₂ i).γ_meas)) hT

/-- Under the hypotheses of Lemma 4.2, the frozen forward equation (4.7) of a trial of `ℍ²`
has a solution every path of which has left limits on `(0, T]`. -/
theorem FrozenForward.exists_leftLim {L : ℝ} {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}
    (hT : 0 ≤ T) (hJ : JointBorel T C) (h22 : Assumption22 (enlJoint 𝒢₀ D h𝒢₀) P T C ξ₀)
    (h23 : Assumption23 (enlJoint 𝒢₀ D h𝒢₀) P T L C)
    (hq : PredForcing (enlJoint 𝒢₀ D h𝒢₀) P ν T qb qσ qh qf qg)
    (hw : PaperWeakTuple (enlJoint 𝒢₀ D h𝒢₀) P ν T X Y Z U) :
    ∃ X' : Fin n → ℝ → Ω → ℝ, FrozenForward D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh X Y Z U X'
      ∧ ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
        Tendsto (fun s => X' i s ω) (𝓝[<] t) (𝓝 l) := by
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0
  have hnullAll : ∀ s : Set Ω, MeasurableSet s → P s = 0 →
      ∀ t, MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ t] s := fun s hs h0 t => by
    rcases le_total 0 t with ht | ht
    · exact (enlJoint 𝒢₀ D h𝒢₀).mono ht _ (hnull s hs h0)
    · exact enlJoint_le_of_nonpos D h𝒢₀ ht _ (hnull s hs h0)
  -- a solution, from the forcing `λ Ψ(Θ) + q`
  obtain ⟨γ, hγ⟩ := hw.exists_paperAdmissible hT (hJ.coeffRegular _ P)
    (originValues_iff_coeffOrigin.mp h22.origin) h23.interior.diagonalLipschitz_two_mul
  have hF := (hγ.forcing.smul lam).add hq.toForcing
  obtain ⟨X0, hX0⟩ := hF.exists_linearFSDEJ (D := D)
    (hℱW := isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
    (hℱN := isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀) hnull hT
    (memLp_iff_forall_coord.mp h22.initial_memLp)
    (stronglyMeasurable_iff_forall_coord.mp h22.initial_meas)
  -- its paths, set to `0` off a null set
  obtain ⟨S, hSae, hSm, hSsub⟩ :=
    (ae_all_iff.mpr fun i => (hX0 i).ae_leftLim hT).exists_measurable_mem
  have hSae' : ∀ᵐ ω ∂P, ω ∈ S := hSae
  have hSt : ∀ t, MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ t] S := fun t => by
    simpa using (hnullAll Sᶜ hSm.compl (mem_ae_iff.mp hSae) t).compl
  set X' : Fin n → ℝ → Ω → ℝ := fun i t => S.indicator (X0 i t) with hX'def
  refine ⟨X', ⟨γ, hγ.jump_rep, fun i => (hX0 i).indicator hSt hSae'⟩, fun i ω => ?_⟩
  by_cases hω : ω ∈ S
  · simp only [hX'def, Set.indicator_of_mem hω]
    exact hSsub ω hω i
  · intro t _
    refine ⟨0, ?_⟩
    simp only [hX'def, Set.indicator_of_notMem hω]
    exact tendsto_const_nhds

end Frozen

/-- (4.7). -/
theorem eq_frozenfwd : PaperSpec.eq_frozenfwd.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ _ T hT L C ξ₀ hJ h22 h23 lam _ _
    qb qσ qh qf qg hq X Y Z U ⟨hw, -, -, hXs, hYs⟩
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0
  have horig := originValues_iff_coeffOrigin.mp h22.origin
  -- the coefficient processes along the trial, through (4.2)
  obtain ⟨K, hK⟩ := MVFBSDEJ.Acceptance.eq_coeffint.{u, v}
  have hΘm : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ t] (tupleAt ν X Y Z U t)
        ∧ MemLp (tupleAt ν X Y Z U t) 2 P := by
    filter_upwards [hw.ae_memLp_tupleAt hT.le, ae_restrict_mem measurableSet_Icc] with t h2 ht
    exact ⟨hw.stronglyMeasurable_tupleAt ht, h2⟩
  obtain ⟨hb, hσ, hh, -⟩ := hK (enlJoint 𝒢₀ D h𝒢₀) P ν n m d T L C h23.interior
    (tupleAt ν X Y Z U) hΘm
  have hch := hw.setLIntegral_lintegral_channels_lt_top hT.le hXs hYs
  have hO := lintegral_originSq_lt_top horig
  have hOb : ∫⁻ t in Set.Icc (0 : ℝ) T, ‖C.b t 0 (P2.dirac 0)‖ₑ ^ 2 < ⊤ :=
    (lintegral_mono fun t => (le_self_add.trans le_self_add).trans le_self_add).trans_lt hO
  have hOσ : ∫⁻ t in Set.Icc (0 : ℝ) T, ‖C.σ t 0 (P2.dirac 0)‖ₑ ^ 2 < ⊤ :=
    (lintegral_mono fun t => (le_add_self.trans le_self_add).trans le_self_add).trans_lt hO
  have hOh : ∫⁻ t in Set.Icc (0 : ℝ) T, ‖C.h t 0 (P2.dirac 0)‖ₑ ^ 2 < ⊤ :=
    (lintegral_mono fun t => le_add_self.trans le_self_add).trans_lt hO
  refine ⟨hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (setLIntegral_lintegral_add_lt_top hch
        (horig.b_memLp.aestronglyMeasurable.enorm.pow_const 2) hOb)),
    hσ.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (setLIntegral_lintegral_add_lt_top hch
        (horig.σ_memLp.aestronglyMeasurable.enorm.pow_const 2) hOσ)),
    hh.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (setLIntegral_lintegral_add_lt_top hch
        (horig.h_memLp.aestronglyMeasurable.enorm.pow_const 2) hOh)), ?_,
    fun X₁ X₂ h₁ h₂ i => FrozenForward.ae_forall_Icc_eq h₁ h₂ hT.le i⟩
  -- a solution with left limits, in `S²` by Lemma 4.1
  obtain ⟨X', hfwd, hX'l⟩ :=
    FrozenForward.exists_leftLim (hind₀ := hind₀) (lam := lam) hT.le hJ h22 h23 hq hw
  obtain ⟨γ', -, hX'⟩ := id hfwd
  exact ⟨X', hfwd, hX'l, lintegral_biSup_esq_lt_top_of_linearFSDEJ hX'
    (crossWitnessEnl D h𝒢₀ hind₀) (hF0_enlJoint D h𝒢₀) hnull hT⟩

/-- (4.8). -/
theorem eq_frozenbwd : PaperSpec.eq_frozenbwd.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ _ _ hd T hT L C ξ₀ hJ h22 h23 lam _ _
    qb qσ qh qf qg hq X Y Z U ⟨hw, -, -, -, -⟩
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ 0] s :=
    fun _ hs h0 => measurableSet_enlJoint_of_null D h𝒢₀ hs h0
  have hnullAll : ∀ s : Set Ω, MeasurableSet s → P s = 0 →
      ∀ t, MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ t] s := fun s hs h0 t => by
    rcases le_total 0 t with ht | ht
    · exact (enlJoint 𝒢₀ D h𝒢₀).mono ht _ (hnull s hs h0)
    · exact enlJoint_le_of_nonpos D h𝒢₀ ht _ (hnull s hs h0)
  have 𝒲 := crossWitnessEnl D h𝒢₀ hind₀
  have hℱ0 := hF0_enlJoint D h𝒢₀
  have horig := originValues_iff_coeffOrigin.mp h22.origin
  have hLT := lipTerminal_iff_terminalLipschitz.mp h23.terminal
  obtain ⟨γ, hγ⟩ := hw.exists_paperAdmissible hT.le (hJ.coeffRegular _ P) horig
    h23.interior.diagonalLipschitz_two_mul
  have hF := (hγ.forcing.smul lam).add hq.toForcing
  -- the terminal value of the backward equation along a solution of (4.7)
  have hξ : ∀ X' : Fin n → ℝ → Ω → ℝ, FrozenForward D h𝒢₀ hind₀ T lam C ξ₀ qb qσ qh X Y Z U X' →
      ∀ k, StronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ T]
          (fun ω => lam * terminalVal P T C X' k ω + qg k ω)
        ∧ MemLp (fun ω => lam * terminalVal P T C X' k ω + qg k ω) 2 P := by
    rintro X' ⟨γ', -, hX'⟩ k
    have hXm : ∀ i, Measurable[enlJoint 𝒢₀ D h𝒢₀ T] (X' i T) := fun i => (hX' i).X_adapted T
    have hX2 : ∀ i, MemLp (X' i T) 2 P := fun i => (hX' i).memLp_terminal hT.le
    have hsm := stronglyMeasurable_terminalVal (P := P) hJ.measurable_g_section hXm k
    have hG : ∫⁻ ω, esq (fun k => terminalVal P T C X' k ω) ∂P ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_esq_lt_top hX2).ne,
          ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top enorm_ne_top)⟩)
        (lintegral_esq_terminalVal_le hLT hXm hX2)
    have hmem : MemLp (terminalVal P T C X' k) 2 P :=
      Brownian.Ito.memLp_two_of_lintegral_sq_lt_top
        ((hsm.mono ((enlJoint 𝒢₀ D h𝒢₀).le T)).aestronglyMeasurable)
        ((lintegral_mono fun ω => Finset.single_le_sum
          (f := fun k => (‖terminalVal P T C X' k ω‖₊ : ℝ≥0∞) ^ 2) (fun _ _ => zero_le)
          (Finset.mem_univ k)).trans_lt (lt_top_iff_ne_top.mpr hG))
    exact ⟨(hsm.const_mul lam).add (hq.qg_meas k), (hmem.const_mul lam).add (hq.qg_sq k)⟩
  refine ⟨fun X' hX' k => ⟨((hξ X' hX' k).1.add
      ((hF.qf_prog k).stronglyMeasurable_setIntegral measurableSet_Icc Set.Icc_subset_Iic_self
        volume)),
      (hξ X' hX' k).2.add
        (Ito.SecondMoment.memLp_two_setIntegral (hF.qf_meas k) hT.le (hF.qf_sq k).lt_top)⟩,
    ?_, ?_⟩
  -- a solution: the forward equation, with left limits
  · obtain ⟨X', hfwd, hX'l⟩ :=
      FrozenForward.exists_leftLim (hind₀ := hind₀) (lam := lam) hT.le hJ h22 h23 hq hw
    obtain ⟨γ', -, hX'⟩ := id hfwd
    -- the backward equation, with predictable integrands and paths set to `0` off a null set
    have hrep := hasTerminalRep_enlJoint D h𝒢₀ hind₀ hd hT
    choose Y0 Z0 U0 hY0 using fun k => hrep.exists_linearBSDEJ hnull hT.le (hξ X' hfwd k).2
      (hξ X' hfwd k).1.aestronglyMeasurable (hF.qf_meas k) (hF.qf_prog k) (hF.qf_vanish k)
      (hF.qf_sq k)
    choose Z' U' hZp hUp hY1 using fun k => (hY0 k).exists_predictable hT
    obtain ⟨S', hS'ae, hS'm, hS'sub⟩ :=
      (ae_all_iff.mpr fun k => (hY1 k).ae_leftLim hT.le).exists_measurable_mem
    have hS'ae' : ∀ᵐ ω ∂P, ω ∈ S' := hS'ae
    have hS't : ∀ t, MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ t] S' := fun t => by
      simpa using (hnullAll S'ᶜ hS'm.compl (mem_ae_iff.mp hS'ae) t).compl
    set Y' : Fin m → ℝ → Ω → ℝ := fun k t => S'.indicator (Y0 k t) with hY'def
    have hY' := fun k => (hY1 k).indicator hS't hS'ae'
    have hY'l : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
        Tendsto (fun s => Y' k s ω) (𝓝[<] t) (𝓝 l) := fun k ω => by
      by_cases hω : ω ∈ S'
      · simp only [hY'def, Set.indicator_of_mem hω]
        exact hS'sub ω hω k
      · intro t _
        refine ⟨0, ?_⟩
        simp only [hY'def, Set.indicator_of_notMem hω]
        exact tendsto_const_nhds
    have hXsup := lintegral_biSup_esq_lt_top_of_linearFSDEJ hX' 𝒲 hℱ0 hnull hT
    have hYsup := lintegral_biSup_esq_lt_top_of_linearBSDEJ hY' 𝒲 hℱ0 hnull hT
    exact ⟨X', Y', Z', U', hfwd, hY',
      ⟨{ X_adapted := fun i t _ => (hX' i).X_adapted t
         X_rightCont := fun i ω t _ => (hX' i).X_rightCont ω t
         X_leftLim := fun i => ae_of_all _ (hX'l i)
         X_sq := energy_ne_top_of_lintegral_biSup_esq_lt_top hXsup
         Y_adapted := fun k t _ => (hY' k).Y_adapted t
         Y_rightCont := fun k ω t _ => (hY' k).Y_rightCont ω t
         Y_leftLim := fun k => ae_of_all _ (hY'l k)
         Y_sq := energy_ne_top_of_lintegral_biSup_esq_lt_top hYsup
         Z_pred := hZp
         Z_vanish := fun k => (hY' k).Z_vanish
         Z_sq := fun k => (hY' k).Z_sq
         U_pred := hUp
         U_vanish := fun k => (hY' k).U_vanish
         U_sq := fun k => (hY' k).U_sq }, hX'l, hY'l, hXsup, hYsup⟩⟩
  -- uniqueness
  · rintro X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨hf₁, hb₁, -⟩ ⟨hf₂, hb₂, -⟩
    have hX := fun i => FrozenForward.ae_forall_Icc_eq hf₁ hf₂ hT.le i
    have hXT : ∀ᵐ ω ∂P, ∀ i, X₁ i T ω = X₂ i T ω := by
      filter_upwards [ae_all_iff.mpr hX] with ω hω i
      exact hω i T ⟨hT.le, le_rfl⟩
    have hlaw : lawP2 P (fun ω => (WithLp.toLp 2 fun i => X₁ i T ω : EuclideanSpace ℝ (Fin n)))
        = lawP2 P (fun ω => (WithLp.toLp 2 fun i => X₂ i T ω : EuclideanSpace ℝ (Fin n))) :=
      lawP2_congr (hXT.mono fun ω hω => by simp only [hω])
    have hterm : ∀ k, (fun ω => lam * terminalVal P T C X₁ k ω + qg k ω)
        =ᵐ[P] fun ω => lam * terminalVal P T C X₂ k ω + qg k ω := fun k => by
      filter_upwards [hXT] with ω hω
      simp only [terminalVal, hω, hlaw]
    have key := fun k => (hb₁ k).eq_of_ae_eq_terminal (hb₂ k) (hterm k) 𝒲 hℱ0 hnull hT
    exact ⟨hX, fun k => (key k).1, fun k j => (key k).2.1 j, fun k => (key k).2.2⟩

end MVFBSDEJ.Acceptance
