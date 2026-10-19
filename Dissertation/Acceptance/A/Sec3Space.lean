/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3Space
import Dissertation.Acceptance.A.WitnessNonzero

/-!
# The solution space and the solution definition of §3 of the well-posedness paper: proofs

## Main statements

* `Dissertation.Acceptance.A.ae_forall_Icc_eq_of_rightCont` — processes with right-continuous
  paths that agree almost surely at every time are indistinguishable.
* `Dissertation.Acceptance.A.sec3_one_null_set`, `sec3_HH_inclusion`, `sec3_HH_definite`.
* `Dissertation.Acceptance.A.sec3_space_hypotheses` — a tuple of `ℍ_weak` along which the
  integrals of (1.1) exist, with `X_0 = 1` almost surely.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Spec LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

/-- Two processes whose almost every path is right-continuous on `[0, T)` and which agree almost
surely at every time of `[0, T]` agree off one null set at every time of `[0, T]`. -/
theorem ae_forall_Icc_eq_of_rightCont {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℝ}
    {A B : ℝ → Ω → ℝ}
    (hA : ∀ᵐ ω ∂P, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => A s ω) (𝓝[>] t) (𝓝 (A t ω)))
    (hB : ∀ᵐ ω ∂P, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => B s ω) (𝓝[>] t) (𝓝 (B t ω)))
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, A t =ᵐ[P] B t) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, A t ω = B t ω := by
  have hQ : ∀ᵐ ω ∂P, ∀ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) T → A q ω = B q ω := by
    refine ae_all_iff.mpr fun q => ?_
    by_cases hq : (q : ℝ) ∈ Set.Icc (0 : ℝ) T
    · filter_upwards [h q hq] with ω hω _ using hω
    · exact Eventually.of_forall fun _ h' => absurd h' hq
  have hT : ∀ᵐ ω ∂P, 0 ≤ T → A T ω = B T ω := by
    by_cases h0 : 0 ≤ T
    · filter_upwards [h T ⟨h0, le_rfl⟩] with ω hω _ using hω
    · exact Eventually.of_forall fun _ h' => absurd h' h0
  filter_upwards [hA, hB, hQ, hT] with ω hAω hBω hQω hTω t ht
  rcases eq_or_lt_of_le ht.2 with htT | htT
  · rw [htT]
    exact hTω (ht.1.trans ht.2)
  -- rationals decreasing to `t` inside `(t, T)`
  have hq : ∀ k : ℕ, ∃ q : ℚ, t < q ∧ (q : ℝ) < min T (t + 1 / (k + 1)) := fun k =>
    exists_rat_btwn (lt_min htT (lt_add_of_pos_right t (by positivity)))
  choose q hq1 hq2 using hq
  have hlim : Tendsto (fun k => (q k : ℝ)) atTop (𝓝[>] t) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => hq1 k⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun k => (hq1 k).le) fun k => (hq2 k).le.trans (min_le_right _ _)
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add t
  have heq : ∀ k, A (q k) ω = B (q k) ω := fun k =>
    hQω (q k) ⟨ht.1.trans (hq1 k).le, (hq2 k).le.trans (min_le_left _ _)⟩
  have h1 := (hAω t ⟨ht.1, htT⟩).comp hlim
  have h2 := (hBω t ⟨ht.1, htT⟩).comp hlim
  refine tendsto_nhds_unique h1 ?_
  exact h2.congr fun k => (heq k).symm

/-- The primitive `t ↦ ∫_{[0, t]} f` of a function integrable on `[0, T]` is right-continuous on
`[0, T)`. -/
theorem tendsto_setIntegral_Icc_zero {f : ℝ → ℝ} {T t : ℝ}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T)) (ht : t ∈ Set.Ico (0 : ℝ) T) :
    Tendsto (fun s => ∫ x in Set.Icc (0 : ℝ) s, f x) (𝓝[>] t)
      (𝓝 (∫ x in Set.Icc (0 : ℝ) t, f x)) := by
  have hT : (0 : ℝ) ≤ T := ht.1.trans ht.2.le
  have hc := intervalIntegral.continuousOn_primitive_interval
    (μ := volume) (a := 0) (b := T) (f := f) (by rwa [Set.uIcc_of_le hT])
  rw [Set.uIcc_of_le hT] at hc
  have hct : Tendsto (fun s => ∫ x in (0 : ℝ)..s, f x) (𝓝[Set.Ioo t T] t)
      (𝓝 (∫ x in (0 : ℝ)..t, f x)) :=
    (hc t ⟨ht.1, ht.2.le⟩).tendsto.mono_left
      (nhdsWithin_mono _ fun s hs => ⟨ht.1.trans hs.1.le, hs.2.le⟩)
  rw [nhdsWithin_Ioo_eq_nhdsGT ht.2] at hct
  have e : ∀ s, 0 ≤ s → ∫ x in Set.Icc (0 : ℝ) s, f x = ∫ x in (0 : ℝ)..s, f x := fun s hs => by
    rw [intervalIntegral.integral_of_le hs, integral_Icc_eq_integral_Ioc]
  rw [e t ht.1]
  exact hct.congr' (eventually_nhdsWithin_of_forall fun s hs => (e s
    (ht.1.trans (le_of_lt hs))).symm)

/-- The integral `t ↦ ∫_{[t, T]} f` of a function integrable on `[0, T]` is right-continuous on
`[0, T)`. -/
theorem tendsto_setIntegral_Icc_right {f : ℝ → ℝ} {T t : ℝ}
    (hf : IntegrableOn f (Set.Icc (0 : ℝ) T)) (ht : t ∈ Set.Ico (0 : ℝ) T) :
    Tendsto (fun s => ∫ x in Set.Icc s T, f x) (𝓝[>] t) (𝓝 (∫ x in Set.Icc t T, f x)) := by
  have e : ∀ s ∈ Set.Icc (0 : ℝ) T, ∫ x in Set.Icc s T, f x
      = (∫ x in Set.Icc (0 : ℝ) T, f x) - ∫ x in Set.Icc (0 : ℝ) s, f x := by
    intro s hs
    have hfi : IntervalIntegrable f volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (hs.1.trans hs.2)).mpr hf
    have hsub : Set.uIcc 0 s ⊆ Set.uIcc 0 T := by
      rw [Set.uIcc_of_le hs.1, Set.uIcc_of_le (hs.1.trans hs.2)]
      exact Set.Icc_subset_Icc_right hs.2
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hs.2, ← intervalIntegral.integral_of_le hs.1,
      ← intervalIntegral.integral_of_le (hs.1.trans hs.2),
      intervalIntegral.integral_interval_sub_left hfi (hfi.mono_set hsub)]
  rw [e t ⟨ht.1, ht.2.le⟩]
  refine ((tendsto_setIntegral_Icc_zero hf ht).const_sub _).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT ht.2] with s hs
  exact (e s ⟨ht.1.trans hs.1.le, hs.2.le⟩).symm

/-- §3, one null set for all times. -/
theorem sec3_one_null_set : PaperSpec.A.sec3_one_null_set.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ T C ξ₀ X Y Z U γ hΘ hA
  set ℱ := enlJoint 𝒢₀ D h𝒢₀
  have hN := isPoissonFiltration_enlJoint D h𝒢₀ hind₀
  refine ⟨fun i M hM => ⟨fun h => ?_, fun h t ht => ?_⟩,
    fun k M hM => ⟨fun h => ?_, fun h t ht => ?_⟩⟩
  · refine ae_forall_Icc_eq_of_rightCont (Eventually.of_forall fun ω t ht =>
      hΘ.X_rightCont i ω t ht) ?_ h
    filter_upwards [hM, hA.b_int i, Poisson.Compensated.stochasticIntegral_cadlag
      (φ := fun ω' s e => jumpProc T γ i s ω' e) D.N ℱ hN (hA.γ_meas i) (hA.γ_prog i)
      (marked_sq_int_global_of_vanishing (fun ω _ e hs => jumpProc_of_notMem hs i ω e)
        (hA.γ_sq i))] with ω hMω hb hPω t ht
    exact ((tendsto_const_nhds.add (tendsto_setIntegral_Icc_zero hb ht)).add (hMω t ht)).add
      (hPω t).1
  · filter_upwards [h] with ω hω using hω t ht
  · refine ae_forall_Icc_eq_of_rightCont (Eventually.of_forall fun ω t ht =>
      hΘ.Y_rightCont k ω t ht) ?_ h
    filter_upwards [hM, hA.f_int k, Poisson.Compensated.stochasticIntegral_cadlag
      (φ := fun ω' s e => U k s ω' e) D.N ℱ hN
      ((hΘ.U_pred k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
      (hΘ.U_pred k).markedProgressivelyMeasurable
      (marked_sq_int_global_of_vanishing (hΘ.U_vanish k) (hΘ.U_sq k))] with ω hMω hf hPω t ht
    exact ((tendsto_const_nhds.add (tendsto_setIntegral_Icc_right hf ht)).sub
      (tendsto_const_nhds.sub (hMω t ht))).sub (tendsto_const_nhds.sub (hPω t).1)
  · filter_upwards [h] with ω hω using hω t ht

/-- §3, `𝔼 ∫_0^T |V|² ≤ T 𝔼 sup |V|²`. -/
theorem sec3_HH_inclusion : PaperSpec.A.sec3_HH_inclusion.{u} := by
  intro Ω _ P n T hT V
  have key : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, esq (fun i => V i s ω) ∂volume ∂P
      ≤ ENNReal.ofReal T * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => V i t ω)) ∂P := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ω => ?_
    calc ∫⁻ s in Set.Icc (0 : ℝ) T, esq (fun i => V i s ω)
        ≤ ∫⁻ _ in Set.Icc (0 : ℝ) T, ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => V i t ω) :=
          setLIntegral_mono' measurableSet_Icc fun s hs => le_iSup₂_of_le s hs le_rfl
      _ = ENNReal.ofReal T * ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => V i t ω) := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]
  refine ⟨key, fun hfin i => ?_⟩
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := T)) hfin.ne) ?_
  refine le_trans (lintegral_mono fun ω => lintegral_mono fun s => ?_) key
  exact Finset.single_le_sum (f := fun i => (‖V i s ω‖₊ : ℝ≥0∞) ^ 2)
    (fun _ _ => zero_le) (Finset.mem_univ i)

/-- `esq x = 0` exactly when every coordinate of `x` vanishes. -/
theorem esq_eq_zero_iff {ι : Type*} [Fintype ι] (x : ι → ℝ) : esq x = 0 ↔ ∀ i, x i = 0 := by
  simp [esq, Finset.sum_eq_zero_iff]

/-- For a process with measurable coordinates and right-continuous paths on `[0, T)`,
`𝔼 sup_{t ≤ T} |X_t|² = 0` exactly when `X` is indistinguishable from `0` on `[0, T]`. -/
theorem lintegral_iSup_esq_eq_zero_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {T : ℝ} {X : Fin n → ℝ → Ω → ℝ} (hm : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (X i t))
    (hrc : ∀ i ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => X i s ω) (𝓝[>] t) (𝓝 (X i t ω))) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P = 0
      ↔ ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, X i t ω = 0 := by
  constructor
  · intro h0
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i, X i t =ᵐ[P] fun _ => (0 : ℝ) := by
      intro t ht i
      have hle : ∫⁻ ω, esq (fun i => X i t ω) ∂P = 0 :=
        le_antisymm (h0 ▸ lintegral_mono fun ω => le_iSup₂_of_le t ht le_rfl) zero_le
      have hmeas : Measurable fun ω => esq (fun i => X i t ω) := by
        unfold esq
        exact Finset.measurable_sum _ fun i _ =>
          ((hm i t ht).nnnorm.coe_nnreal_ennreal).pow_const 2
      filter_upwards [(lintegral_eq_zero_iff hmeas).mp hle] with ω hω
      exact (esq_eq_zero_iff _).mp hω i
    have hall : ∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X i t ω = 0 := fun i =>
      ae_forall_Icc_eq_of_rightCont (A := X i) (B := fun _ _ => 0)
        (Eventually.of_forall fun ω t ht => hrc i ω t ht)
        (Eventually.of_forall fun _ _ _ => tendsto_const_nhds) fun t ht => hpt t ht i
    filter_upwards [ae_all_iff.mpr hall] with ω hω t ht i using hω i t ht
  · intro h
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [h] with ω hω
    exact le_antisymm (iSup₂_le fun t ht => ((esq_eq_zero_iff _).mpr (hω t ht)).le) zero_le

/-- §3, `‖·‖_ℍ` is a norm on the identified tuples. -/
theorem sec3_HH_definite : PaperSpec.A.sec3_HH_definite.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ T X Y Z U hΘ
  set ℱ := enlJoint 𝒢₀ D h𝒢₀
  have hX := lintegral_iSup_esq_eq_zero_iff (P := P)
    (fun i t ht => (hΘ.X_adapted i t ht).mono (ℱ.le t) le_rfl) hΘ.X_rightCont
  have hY := lintegral_iSup_esq_eq_zero_iff (P := P)
    (fun k t ht => (hΘ.Y_adapted k t ht).mono (ℱ.le t) le_rfl) hΘ.Y_rightCont
  have hZ : ∀ k j, Brownian.Ito.energy P T (fun ω s => Z k s ω j) = 0
      ↔ ∀ᵐ p ∂(Brownian.Ito.energyMeasure P T), Z k p.2 p.1 j = 0 := by
    intro k j
    have hm := Brownian.Ito.measurable_uncurry_of_predictable (hΘ.Z_pred k j)
    have hm' : Measurable fun p : Ω × ℝ => Z k p.2 p.1 j := hm
    rw [Brownian.Ito.energy_eq_eLpNorm_sq hm T, pow_eq_zero_iff two_ne_zero,
      eLpNorm_eq_zero_iff hm'.aestronglyMeasurable two_ne_zero]
    rfl
  have hU : ∀ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) = 0
      ↔ ∀ᵐ p ∂(Poisson.Compensated.markedEnergyMeasure P ν T), U k p.2.1 p.1 p.2.2 = 0 := by
    intro k
    have hm : Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2 :=
      (hΘ.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
    rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq hm T, pow_eq_zero_iff two_ne_zero,
      eLpNorm_eq_zero_iff hm.aestronglyMeasurable two_ne_zero]
    rfl
  simp only [supSize, add_eq_zero, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies, hX,
    hY, hZ, hU]
  tauto

/-- **The hypotheses of the §3 statements can be met by a nonzero tuple.** Over a probability
space carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`, `n = m = 1` and
`T = 1`, the solution of Example 5.1(i) (`β₁ = β₂ = 1`, `σ_c = h_c = 0`) from `ξ₀ ≡ e₁` is a
tuple of `ℍ_weak` along which the integrals of (1.1) exist, with `X_0 = 1` almost surely. -/
theorem sec3_space_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (_ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)
      (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U : Fin 1 → ℝ → Ω → ℝ → ℝ) (γ : Fin 1 → ℝ → Ω → ℝ → ℝ),
      PaperWeakTuple (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 X Y Z U
      ∧ PaperAdmissibleInt (enlJoint ⊥ D bot_le) P 1
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 1 1 0 0) X Y Z U γ
      ∧ ∀ᵐ ω ∂P, X 0 0 ω = 1 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨hJ, h22, h23, hG, h25⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := enlJoint ⊥ D bot_le) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  have e₁ : max (max (1 : ℝ) 1) 1 = 1 := by norm_num
  rw [e₁] at h23
  obtain ⟨X, Y, Z, U, hS⟩ := (thm_cwp ⊥ _ 1 1 1 P D bot_le hind₀ one_pos one_pos one_pos 1
    one_pos 1 1 1 1 1 _ _ hJ h22 h23 hG h25).1
  obtain ⟨⟨⟨γ, hw⟩, -, -⟩, -, -⟩ := id hS
  refine ⟨Ω, inferInstance, P, inferInstance, D, hind₀, X, Y, Z, U, γ, hw.toPaperWeakTuple,
    hw.toPaperAdmissibleInt, ?_⟩
  filter_upwards [Solution.X_zero_ae zero_le_one hS 0] with ω hω
  rw [hω]
  simp

end Dissertation.Acceptance.A
