/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.CadlagLegs
import LevyStochCalc.Ito.CompensatedLocalityStopping
import LevyStochCalc.Martingale.BDGTwo
import MVFBSDEJ.WellPosedness.Martingale.Lenglart
import MVFBSDEJ.WellPosedness.Martingale.EnergyHitting
import MVFBSDEJ.WellPosedness.Martingale.PathSup

/-!
# The Burkholder–Davis–Gundy inequality at `p = 1` for the stochastic integrals

For the multidimensional Brownian integral `M = ∫ Z dW` and the compensated Poisson integral
`M = ∫∫ φ dÑ` of integrands of finite energy, and any version of `M` with paths
right-continuous on `[0, T)`,

`𝔼 sup_{t ≤ T} |M_t| ≤ 9 𝔼 (∫_0^T |Z_s|² ds)^{1/2}`, resp.
`𝔼 sup_{t ≤ T} |M_t| ≤ 9 𝔼 (∫_0^T ∫_E φ_s(e)² ν(de) ds)^{1/2}`.

The integral of the integrand stopped when its energy reaches `δ` agrees with `M` up to that
time, and Doob's `L²` inequality bounds its squared supremum by `4 𝔼 (A_T ∧ δ)`, `A` the energy;
Lenglart's argument (`lintegral_le_of_good_lambda`) integrates these bounds over `δ`.

## Main statements

* `MVFBSDEJ.WellPosedness.Martingale.multidim_congr_of_le` — integrands agreeing up to a
  stopping time have the same multidimensional integral where it has not been reached.
* `MVFBSDEJ.WellPosedness.Martingale.lintegral_sq_multidim` — the isometry of the
  multidimensional integral.
* `MVFBSDEJ.WellPosedness.Martingale.lintegral_biSup_le_brownian` — BDG at `p = 1` for the
  Brownian integral.
* `MVFBSDEJ.WellPosedness.Martingale.lintegral_biSup_le_compensated` — BDG at `p = 1` for the
  compensated Poisson integral.
-/

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace MVFBSDEJ.WellPosedness.Martingale

open LevyStochCalc LevyStochCalc.Brownian.Multidim

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- `(‖x‖₊)² = (x²)⁺` in `[0, ∞]`. -/
theorem nnnorm_sq_eq_ofReal (x : ℝ) : ((‖x‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [← enorm_eq_nnnorm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs,
    sq_abs]

section Brownian

variable (W : MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : ∀ i, Brownian.IsBrownianFiltration (W.W i) ℱ)

/-- **Locality of the multidimensional Itô integral.** Integrands agreeing at the positive times
up to a stopping time have almost surely the same integral at a time it has not reached. -/
theorem multidim_congr_of_le {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ)
    {Z₁ Z₂ : ℝ → Ω → Fin d → ℝ}
    (hm₁ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z₁ s ω j))
    (hp₁ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₁ s ω j)
    (hq₁ : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖Z₁ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z₂ s ω j))
    (hp₂ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₂ s ω j)
    (hq₂ : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hagree : ∀ ω s, 0 < s → ((s : ℝ) : WithTop ℝ) ≤ τ ω → Z₁ s ω = Z₂ s ω) {t : ℝ}
    (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z₁ hm₁ hp₁ hq₁ t ω
        = MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z₂ hm₂ hp₂ hq₂ t ω := by
  have h : ∀ j : Fin d, ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hℱ j) (fun ω s => Z₁ s ω j)
          (hm₁ j) (hp₁ j) (hq₁ j) t ω
        = Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hℱ j) (fun ω s => Z₂ s ω j)
          (hm₂ j) (hp₂ j) (hq₂ j) t ω := fun j =>
    Brownian.Ito.stochasticIntegralBrownian_congr_of_le τ (W.W j) ℱ (hℱ j) hτ (hm₁ j) (hp₁ j)
      (hq₁ j) (hm₂ j) (hp₂ j) (hq₂ j) (fun ω s hs hsτ => by rw [hagree ω s hs hsτ]) ht
  filter_upwards [ae_all_iff.2 h] with ω hω hle
  simp only [MultidimBrownianMotion.stochasticIntegral, Brownian.Ito.stochasticIntegral]
  exact Finset.sum_congr rfl fun j _ => hω j hle

/-- **The isometry of the multidimensional Itô integral.**
`𝔼 |∫_0^T Z dW|² = ∑_j 𝔼 ∫_0^T Z_j(s)² ds`. -/
theorem lintegral_sq_multidim {Z : ℝ → Ω → Fin d → ℝ}
    (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω j)
    (hq : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) {T : ℝ}
    (hT : 0 < T) :
    ∫⁻ ω, (‖MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z hm hp hq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∑ j, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set I : Fin d → Ω → ℝ := fun j => Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hℱ j)
    (fun ω s => Z s ω j) (hm j) (hp j) (hq j) T with hIdef
  have hI : ∀ j, MemLp (I j) 2 P := fun j =>
    (Lp.memLp _).ae_eq (Brownian.Ito.stochasticIntegralBrownian_ae_eq (W.W j) ℱ (hℱ j)
      (fun ω s => Z s ω j) (hm j) (hp j) (hq j) T).symm
  have hsum : MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z hm hp hq T
      = fun ω => ∑ j, I j ω := rfl
  rw [hsum]
  have hmem : MemLp (fun ω => ∑ j, I j ω) 2 P := by
    have := memLp_finsetSum' (μ := P) (p := 2) Finset.univ (fun j _ => hI j)
    refine this.congr_norm ?_ (Eventually.of_forall fun ω => ?_)
    · exact (this.aestronglyMeasurable).congr (Eventually.of_forall fun ω => by simp)
    · simp
  have hprod : ∀ i j, Integrable (fun ω => I i ω * I j ω) P := fun i j =>
    (hI i).integrable_mul (hI j)
  have hcross : ∀ i j, i ≠ j → ∫ ω, I i ω * I j ω ∂P = 0 := fun i j hij =>
    MultidimBrownianMotion.integral_stochasticIntegral_mul_eq_zero W hij hℱ (hm i) (hp i) (hq i)
      (hm j) (hp j) (hq j) hT.le
  have hreal : ∫ ω, (∑ j, I j ω) ^ 2 ∂P = ∑ j, ∫ ω, I j ω ^ 2 ∂P := by
    have hexp : ∀ ω, (∑ j, I j ω) ^ 2 = ∑ i, ∑ j, I i ω * I j ω := fun ω => by
      rw [sq, Finset.sum_mul_sum]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hprod i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hprod i j, Finset.sum_eq_single i]
    · simp only [sq]
    · exact fun j _ hji => hcross i j (Ne.symm hji)
    · exact fun h => absurd (Finset.mem_univ i) h
  have hsq : ∀ f : Ω → ℝ, MemLp f 2 P →
      ∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P) := by
    intro f hf
    rw [ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
      (Eventually.of_forall fun ω => sq_nonneg _)]
    exact lintegral_congr fun ω => nnnorm_sq_eq_ofReal _
  rw [hsq _ hmem, hreal, ENNReal.ofReal_sum_of_nonneg fun j _ => integral_nonneg fun ω =>
    sq_nonneg _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hsq _ (hI j)]
  exact Brownian.Ito.isometry_stochasticIntegralBrownian (W.W j) ℱ (hℱ j) (fun ω s => Z s ω j)
    (hm j) (hp j) (hq j) hT

/-- **The Burkholder–Davis–Gundy inequality at `p = 1` for the multidimensional Itô integral.**
Over a right-continuous filtration whose null sets lie in its time-`0` field, every version `M`
of `∫ Z dW` with paths right-continuous on `[0, T)` almost surely satisfies
`𝔼 sup_{t ≤ T} |M_t| ≤ 9 𝔼 (∑_j ∫_0^T Z_j(s)² ds)^{1/2}`. -/
theorem lintegral_biSup_le_brownian [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {Z : ℝ → Ω → Fin d → ℝ}
    (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω j)
    (hq : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) {T : ℝ}
    (hT : 0 < T) {M : ℝ → Ω → ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T,
      M t =ᵐ[P] MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z hm hp hq t)
    (hMr : ∀ᵐ ω ∂P, ∀ t ∈ Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) :
    ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 9 * ∫⁻ ω, (∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) ∂P := by
  classical
  set a : Ω → ℝ → ℝ≥0∞ := fun ω s => ∑ j, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 with ha
  have hslice : ∀ ω j, Measurable fun s => (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 := fun ω j =>
    ((hm j).comp measurable_prodMk_left).nnnorm.coe_nnreal_ennreal.pow_const 2
  have hA_eq : ∀ ω t, ∫⁻ s in Icc (0 : ℝ) t, a ω s
      = ∑ j, ∫⁻ s in Icc (0 : ℝ) t, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 := fun ω t =>
    lintegral_finsetSum _ fun j _ => hslice ω j
  have hjoint : Measurable fun p : Ω × ℝ => a p.1 p.2 :=
    Finset.measurable_sum _ fun j _ => (hm j).nnnorm.coe_nnreal_ennreal.pow_const 2
  have hAm : Measurable fun ω => ∫⁻ s in Icc (0 : ℝ) T, a ω s := hjoint.lintegral_prod_right'
  have hadapt : ∀ t, Measurable[ℱ t] fun ω => ∫⁻ s in Icc (0 : ℝ) t, a ω s := by
    intro t
    have h : Measurable[ℱ t] fun ω => ∑ j, ∫⁻ s in Icc (0 : ℝ) t, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 :=
      Finset.measurable_sum _ fun j _ => measurable_energy_of_progressive (hp j) t
    have hfun : (fun ω => ∫⁻ s in Icc (0 : ℝ) t, a ω s)
        = fun ω => ∑ j, ∫⁻ s in Icc (0 : ℝ) t, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 :=
      funext fun ω => hA_eq ω t
    rw [hfun]
    exact h
  have hIm : ∀ t, Measurable (MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z hm hp hq t) :=
    fun t => Finset.measurable_sum _ fun j _ =>
      ((Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted (W.W j) ℱ (hℱ j) _ (hm j)
        (hp j) (hq j) t).mono (ℱ.le t)).measurable
  have hMa : ∀ t ∈ Icc (0 : ℝ) T, AEMeasurable (M t) P := fun t ht =>
    (hIm t).aemeasurable.congr (hM t ht).symm
  have hS := aemeasurable_biSup_Icc hT.le hMa hMr
  have key := lintegral_le_of_good_lambda (P := P)
    (S := fun ω => ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞))
    (A := fun ω => ∫⁻ s in Icc (0 : ℝ) T, a ω s) hS hAm (c := 4) ?_
  · calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
        ≤ (1 + 2 * 4) * ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, a ω s) ^ (1 / 2 : ℝ) ∂P := key
      _ = 9 * ∫⁻ ω, (∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) ∂P := by
        rw [show (1 + 2 * 4 : ℝ≥0∞) = 9 by norm_num]
        simp_rw [hA_eq]
  intro δ hδ
  set σ : Ω → WithTop ℝ := energyHit a (ENNReal.ofReal δ) with hσdef
  have hσ : IsStoppingTime ℱ σ := isStoppingTime_energyHit hadapt _
  set Zσ : ℝ → Ω → Fin d → ℝ :=
    fun s ω j => Probability.stopped σ (fun ω s => Z s ω j) ω s with hZσ
  have hmσ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Zσ s ω j) := fun j =>
    Probability.measurable_uncurry_stopped hσ (hm j)
  have hpσ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Zσ s ω j := fun j =>
    (hp j).stopped hσ
  have hqσ : ∀ (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T', (‖Zσ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun j =>
    Brownian.Ito.energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le σ _ ω s) (hq j)
  obtain ⟨M', -, hM'meas, hM'ae, hM'cad, hM'mart, hM'zero, -⟩ :=
    BSDEJ.Solves.exists_cadlag_vectorIntegral_supBound W ℱ hℱ Zσ hmσ hpσ hqσ hℱ0 hnull T hT.le
  have hM't : ∀ t, Measurable (M' t) := fun t =>
    hM'meas.comp (measurable_const.prodMk measurable_id)
  refine ⟨fun ω => ⨆ t ∈ Icc (0 : ℝ) T, (‖M' t ω‖₊ : ℝ≥0∞), ?_, ?_, ?_⟩
  · exact aemeasurable_biSup_Icc hT.le (fun t _ => (hM't t).aemeasurable)
      (ae_of_all _ fun ω t _ => (hM'cad ω t).1)
  · -- up to the passage time the stopped integral is the integral
    have hagree : ∀ ω s, 0 < s → ((s : ℝ) : WithTop ℝ) ≤ σ ω → Zσ s ω = Z s ω := by
      intro ω s _ hle
      funext j
      simp only [hZσ, Probability.stopped, if_pos hle]
    have hloc : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ σ ω → M t ω = M' t ω := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · subst h0
        filter_upwards [hM 0 ht, hM'zero 0 le_rfl,
          MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos W ℱ hℱ Z hm hp hq
            (le_refl (0 : ℝ))] with ω h1 h2 h3 _
        rw [h1, h3, h2]
      · filter_upwards [hM t ht, hM'ae t,
          multidim_congr_of_le W ℱ hℱ hσ hmσ hpσ hqσ hm hp hq hagree h0] with ω h1 h2 h3 hle
        rw [h1, h2, h3 hle]
    have hD : ∀ᵐ ω ∂P, (∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
        (((q : ℝ) : ℝ) : WithTop ℝ) ≤ σ ω → M q ω = M' q ω)
        ∧ (((T : ℝ) : WithTop ℝ) ≤ σ ω → M T ω = M' T ω) := by
      refine (ae_all_iff.2 fun q => ?_).and (hloc T ⟨hT.le, le_rfl⟩)
      by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
      · filter_upwards [hloc q hq] with ω hω _ hle
        exact hω hle
      · exact ae_of_all _ fun ω h => absurd h hq
    filter_upwards [hD, hMr] with ω hω hr hA
    have hTσ : ((T : ℝ) : WithTop ℝ) ≤ σ ω := le_energyHit_of_lt hA
    have heq : ∀ t ∈ Icc (0 : ℝ) T, M t ω = M' t ω := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with htT | htT
      · rw [htT]
        exact hω.2 hTσ
      · refine eq_of_rightCont_of_eq_rat (f := fun s => M s ω) (g := fun s => M' s ω) htT
          (hr t ⟨ht.1, htT⟩) (hM'cad ω t).1 fun q hq1 hq2 => ?_
        exact hω.1 q ⟨ht.1.trans hq1.le, hq2.le⟩
          (le_trans (WithTop.coe_le_coe.mpr hq2.le) hTσ)
    exact le_of_eq (iSup_congr fun t => iSup_congr fun ht => by rw [heq t ht])
  · -- Doob's inequality for the stopped integral
    have hsliceσ : ∀ ω j, Measurable fun s => (‖Zσ s ω j‖₊ : ℝ≥0∞) ^ 2 := fun ω j =>
      ((hmσ j).comp measurable_prodMk_left).nnnorm.coe_nnreal_ennreal.pow_const 2
    have hsplit : ∀ ω, ∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖Zσ s ω j‖₊ : ℝ≥0∞) ^ 2
        = ∫⁻ s in Icc (0 : ℝ) T, (if ((s : ℝ) : WithTop ℝ) ≤ σ ω then a ω s else 0) := by
      intro ω
      rw [← lintegral_finsetSum _ fun j _ => hsliceσ ω j]
      refine lintegral_congr fun s => ?_
      by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ σ ω
      · simp only [hZσ, Probability.stopped, if_pos hle, ha]
      · simp only [hZσ, Probability.stopped, if_neg hle]
        simp
    calc ∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ) T, (‖M' t ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
        = ∫⁻ ω, (⨆ t : Icc (0 : ℝ) T, (‖M' (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P := by
          simp_rw [iSup_subtype']
      _ ≤ 4 * ∫⁻ ω, (‖M' T ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
          Probability.lintegral_iSup_sq_le_of_martingale hM'mart hT.le
            (ae_of_all _ fun ω t => (hM'cad ω t).1)
      _ = 4 * ∫⁻ ω, (‖MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Zσ hmσ hpσ hqσ T ω‖₊
            : ℝ≥0∞) ^ 2 ∂P := by
          congr 1
          exact lintegral_congr_ae (by filter_upwards [hM'ae T] with ω hω; rw [hω])
      _ = 4 * ∑ j, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖Zσ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
          rw [lintegral_sq_multidim W ℱ hℱ hmσ hpσ hqσ hT]
      _ = 4 * ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T,
            (if ((s : ℝ) : WithTop ℝ) ≤ σ ω then a ω s else 0) ∂volume ∂P := by
          have hmj : ∀ j, Measurable fun ω => ∫⁻ s in Icc (0 : ℝ) T,
              (‖Zσ s ω j‖₊ : ℝ≥0∞) ^ 2 := fun j =>
            ((hmσ j).nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
          rw [← lintegral_finsetSum _ fun j _ => hmj j]
          simp_rw [hsplit]
      _ ≤ 4 * ∫⁻ ω, min (∫⁻ s in Icc (0 : ℝ) T, a ω s) (ENNReal.ofReal δ) ∂P := by
          gcongr with ω
          exact setLIntegral_ite_energyHit_le ω T

end Brownian

section Compensated

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)

/-- **The Burkholder–Davis–Gundy inequality at `p = 1` for the compensated Poisson integral.**
Over a right-continuous filtration, every version `M` of `∫∫ φ dÑ` with paths right-continuous on
`[0, T)` almost surely satisfies
`𝔼 sup_{t ≤ T} |M_t| ≤ 9 𝔼 (∫_0^T ∫_E φ_s(e)² ν(de) ds)^{1/2}`. -/
theorem lintegral_biSup_le_compensated [ℱ.IsRightContinuous] {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) {T : ℝ} (hT : 0 < T) {M : ℝ → Ω → ℝ}
    (hM : ∀ t ∈ Icc (0 : ℝ) T,
      M t =ᵐ[P] Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t)
    (hMr : ∀ᵐ ω ∂P, ∀ t ∈ Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) :
    ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 9 * ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
        ∂P := by
  classical
  set a : Ω → ℝ → ℝ≥0∞ := fun ω s => ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν with ha
  have hjoint : Measurable fun p : Ω × ℝ => a p.1 p.2 := by
    have h3 : Measurable fun q : (Ω × ℝ) × E => (‖φ q.1.1 q.1.2 q.2‖₊ : ℝ≥0∞) ^ 2 :=
      (hm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).nnnorm
        |>.coe_nnreal_ennreal.pow_const 2
    exact h3.lintegral_prod_right'
  have hAm : Measurable fun ω => ∫⁻ s in Icc (0 : ℝ) T, a ω s := hjoint.lintegral_prod_right'
  have hadapt : ∀ t, Measurable[ℱ t] fun ω => ∫⁻ s in Icc (0 : ℝ) t, a ω s := fun t =>
    measurable_markedEnergy_of_progressive hp t
  have hIm : ∀ (ψ : Ω → ℝ → E → ℝ) (hmψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
      (hpψ : Probability.MarkedProgressivelyMeasurable ℱ ψ)
      (hqψ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
        (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) (t : ℝ),
      Measurable (Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hmψ hpψ hqψ t) :=
    fun ψ hmψ hpψ hqψ t =>
      (Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱ ψ hmψ hpψ hqψ t).mono
        (ℱ.rightCont.le t) le_rfl
  have hMa : ∀ t ∈ Icc (0 : ℝ) T, AEMeasurable (M t) P := fun t ht =>
    (hIm φ hm hp hq t).aemeasurable.congr (hM t ht).symm
  have hS := aemeasurable_biSup_Icc hT.le hMa hMr
  have key := lintegral_le_of_good_lambda (P := P)
    (S := fun ω => ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞))
    (A := fun ω => ∫⁻ s in Icc (0 : ℝ) T, a ω s) hS hAm (c := 4) ?_
  · calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
        ≤ (1 + 2 * 4) * ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, a ω s) ^ (1 / 2 : ℝ) ∂P := key
      _ = _ := by rw [show (1 + 2 * 4 : ℝ≥0∞) = 9 by norm_num]
  intro δ hδ
  set σ : Ω → WithTop ℝ := energyHit a (ENNReal.ofReal δ) with hσdef
  have hσ : IsStoppingTime ℱ σ := isStoppingTime_energyHit hadapt _
  have hmσ := Poisson.Compensated.measurable_markedStopped hσ hm
  have hpσ := Poisson.Compensated.markedProgressivelyMeasurable_markedStopped hσ hp
  have hqσ := Poisson.Compensated.sq_int_global_markedStopped (τ := σ) hq
  set M' : ℝ → Ω → ℝ := Poisson.Compensated.stochasticIntegral N ℱ hℱ
    (Poisson.Compensated.markedStopped σ φ) hmσ hpσ hqσ with hM'def
  have hM'cad := Poisson.Compensated.stochasticIntegral_cadlag N ℱ hℱ
    (Poisson.Compensated.markedStopped σ φ) hmσ hpσ hqσ
  refine ⟨fun ω => ⨆ t ∈ Icc (0 : ℝ) T, (‖M' t ω‖₊ : ℝ≥0∞), ?_, ?_, ?_⟩
  · exact aemeasurable_biSup_Icc hT.le (fun t _ => (hIm _ hmσ hpσ hqσ t).aemeasurable)
      (by filter_upwards [hM'cad] with ω hω t _; exact (hω t).1)
  · have hloc : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ σ ω → M t ω = M' t ω := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · subst h0
        filter_upwards [hM 0 ht,
          Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ hm hp hq
            (le_refl (0 : ℝ)),
          Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ hmσ hpσ hqσ
            (le_refl (0 : ℝ))] with ω h1 h2 h3 _
        rw [h1, h2, hM'def, h3]
      · filter_upwards [hM t ht,
          Poisson.Compensated.stochasticIntegral_markedStopped_eq_of_le N hℱ hm hp hq hσ h0]
          with ω h1 h2 hle
        rw [h1, hM'def, h2 hle]
    have hD : ∀ᵐ ω ∂P, (∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
        (((q : ℝ) : ℝ) : WithTop ℝ) ≤ σ ω → M q ω = M' q ω)
        ∧ (((T : ℝ) : WithTop ℝ) ≤ σ ω → M T ω = M' T ω) := by
      refine (ae_all_iff.2 fun q => ?_).and (hloc T ⟨hT.le, le_rfl⟩)
      by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
      · filter_upwards [hloc q hq] with ω hω _ hle
        exact hω hle
      · exact ae_of_all _ fun ω h => absurd h hq
    filter_upwards [hD, hMr, hM'cad] with ω hω hr hc hA
    have hTσ : ((T : ℝ) : WithTop ℝ) ≤ σ ω := le_energyHit_of_lt hA
    have heq : ∀ t ∈ Icc (0 : ℝ) T, M t ω = M' t ω := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with htT | htT
      · rw [htT]
        exact hω.2 hTσ
      · refine eq_of_rightCont_of_eq_rat (f := fun s => M s ω) (g := fun s => M' s ω) htT
          (hr t ⟨ht.1, htT⟩) (hc t).1 fun q hq1 hq2 => ?_
        exact hω.1 q ⟨ht.1.trans hq1.le, hq2.le⟩
          (le_trans (WithTop.coe_le_coe.mpr hq2.le) hTσ)
    exact le_of_eq (iSup_congr fun t => iSup_congr fun ht => by rw [heq t ht])
  · have hsplit : ∀ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
        (‖Poisson.Compensated.markedStopped σ φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν
        = ∫⁻ s in Icc (0 : ℝ) T, (if ((s : ℝ) : WithTop ℝ) ≤ σ ω then a ω s else 0) := by
      intro ω
      refine lintegral_congr fun s => ?_
      by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ σ ω
      · simp only [Poisson.Compensated.markedStopped, if_pos hle, ha]
      · simp only [Poisson.Compensated.markedStopped, if_neg hle]
        simp
    calc ∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ) T, (‖M' t ω‖₊ : ℝ≥0∞)) ^ 2 ∂P
        = ∫⁻ ω, (⨆ t : Icc (0 : ℝ) T, (‖M' (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂P := by
          simp_rw [iSup_subtype']
      _ ≤ 4 * ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
            (‖Poisson.Compensated.markedStopped σ φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
          LevyStochCalc.Martingale.lintegral_iSup_sq_le_energy_compensated N ℱ hℱ _ hmσ hpσ hqσ
            hT
      _ = 4 * ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T,
            (if ((s : ℝ) : WithTop ℝ) ≤ σ ω then a ω s else 0) ∂volume ∂P := by
          simp_rw [hsplit]
      _ ≤ 4 * ∫⁻ ω, min (∫⁻ s in Icc (0 : ℝ) T, a ω s) (ENNReal.ofReal δ) ∂P := by
          gcongr with ω
          exact setLIntegral_ite_energyHit_le ω T

end Compensated

end MVFBSDEJ.WellPosedness.Martingale
