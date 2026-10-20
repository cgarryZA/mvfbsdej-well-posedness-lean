/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoPullOut
import LevyStochCalc.Brownian.ItoFinsetSum
import LevyStochCalc.Brownian.MultidimIto
import LevyStochCalc.Brownian.ItoIntegrandComplete
import Mathlib
import LevyStochCalc.Driver.VectorIncrement
import LevyStochCalc.Poisson.CompensatedIsometry
import LevyStochCalc.Driver.CellProfileStep
import LevyStochCalc.Poisson.CompensatedProfileLinear
import LevyStochCalc.Brownian.AugmentedFiltration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.SetToL1
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# The Brownian integral of a coefficient frozen over a cell

Let `W` be a Brownian motion for a filtration `ℱ` and `(s, t]` a cell with `0 ≤ s < t`. For a
square-integrable `ℱ_s`-measurable coefficient `V`, the integrand `r ↦ 1_{(s,t]}(r) V` is
admissible for the `L²` Itô integral, and

`∫_0^r 1_{(s,t]} V dW = V (W_{t ∧ r} − W_{s ∧ r})`

almost surely at every time `r ≥ 0`. For a bounded `V` this is the elementary integral of a
simple integrand. A square-integrable `V` is the pointwise limit of its truncations
`V 1_{|V| ≤ n}`; their integrals converge in `L²` by the isometry of differences, hence almost
surely along a subsequence, while the elementary integrals converge pointwise.

For a coefficient row `z = (z₁, …, z_d)` the multidimensional integral of `r ↦ 1_{(s,t]}(r) z` is
therefore `∑ⱼ zⱼ (Wʲ_{t ∧ r} − Wʲ_{s ∧ r})`.

## Main definitions

* `frozenCell` — the scalar integrand `r ↦ 1_{(s,t]}(r) V`.
* `frozenCellVec` — the integrand `r ↦ 1_{(s,t]}(r) z` of a coefficient row.

## Main statements

* `stochasticIntegralBrownian_frozenCell` — `∫_0^r 1_{(s,t]} V dW = V (W_{t ∧ r} − W_{s ∧ r})`.
* `multidimStochasticIntegral_frozenCell` — the multidimensional integral of `1_{(s,t]} z`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MVFBSDEJ.WellPosedness

open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v w

section Frozen

variable {Ω : Type u}

/-- The integrand `r ↦ 1_{(s,t]}(r) V` of a coefficient `V` frozen over the cell `(s, t]`. -/
noncomputable def frozenCell (s t : ℝ) (V : Ω → ℝ) (ω : Ω) (r : ℝ) : ℝ :=
  (Set.Ioc s t).indicator (fun _ => V ω) r

theorem nnnorm_frozenCell_le (s t : ℝ) (V : Ω → ℝ) (ω : Ω) (r : ℝ) :
    ‖frozenCell s t V ω r‖₊ ≤ ‖V ω‖₊ := by
  simp only [frozenCell, Set.indicator_apply]
  split_ifs <;> simp

theorem frozenCell_sub (s t : ℝ) (V V' : Ω → ℝ) (ω : Ω) (r : ℝ) :
    frozenCell s t V ω r - frozenCell s t V' ω r = frozenCell s t (fun ω => V ω - V' ω) ω r := by
  simp only [frozenCell, Set.indicator_apply]
  split_ifs <;> simp

variable [mΩ : MeasurableSpace Ω]

theorem frozenCell_eq_mul_indIoc (s t : ℝ) (V : Ω → ℝ) (ω : Ω) (r : ℝ) :
    frozenCell s t V ω r = V ω * indIoc Ω s t ω r := by
  simp only [frozenCell, indIoc, Set.indicator_apply]
  split_ifs <;> simp

/-- The frozen integrand of a measurable coefficient is jointly measurable. -/
theorem measurable_uncurry_frozenCell (s t : ℝ) {V : Ω → ℝ} (hV : Measurable V) :
    Measurable (Function.uncurry (frozenCell s t V)) := by
  have : Function.uncurry (frozenCell s t V)
      = fun p : Ω × ℝ => (Set.Ioc s t).indicator (fun _ => (1 : ℝ)) p.2 * V p.1 := by
    funext p
    change (Set.Ioc s t).indicator (fun _ => V p.1) p.2 = _
    simp only [Set.indicator_apply]
    split_ifs <;> simp
  rw [this]
  exact ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd).mul
    (hV.comp measurable_fst)

/-- **The frozen integrand of a coefficient measurable at the start of the cell is progressively
measurable.** -/
theorem progressivelyMeasurable_frozenCell {ℱ : MeasureTheory.Filtration ℝ mΩ} {s t : ℝ}
    {V : Ω → ℝ} (hVm : Measurable[ℱ s] V) :
    Probability.ProgressivelyMeasurable ℱ (frozenCell s t V) := by
  intro T
  have e : (fun p : Ω × ℝ => (Set.Iic T).indicator (frozenCell s t V p.1) p.2)
      = fun p : Ω × ℝ => (Set.Iic T ∩ Set.Ioc s t).indicator (fun _ => (1 : ℝ)) p.2 * V p.1 := by
    funext p
    simp only [frozenCell, Set.indicator_apply, Set.mem_inter_iff]
    split_ifs <;> simp_all
  rw [e]
  rcases le_or_gt T s with hTs | hsT
  · have hz : (fun p : Ω × ℝ => (Set.Iic T ∩ Set.Ioc s t).indicator (fun _ => (1 : ℝ)) p.2
        * V p.1) = fun _ => 0 := by
      funext p
      have : p.2 ∉ Set.Iic T ∩ Set.Ioc s t := fun h =>
        absurd (h.1.trans hTs) (not_le.mpr h.2.1)
      simp [this]
    rw [hz]
    exact stronglyMeasurable_const
  · letI : MeasurableSpace Ω := ℱ T
    have hV' : Measurable V := hVm.mono (ℱ.mono hsT.le) le_rfl
    exact (((measurable_const.indicator (measurableSet_Iic.inter measurableSet_Ioc)).comp
      measurable_snd).mul (hV'.comp measurable_fst)).stronglyMeasurable

variable {P : Measure Ω}

theorem lintegral_nnnorm_sq_lt_top {V : Ω → ℝ} (hV : MemLp V 2 P) :
    ∫⁻ ω, (‖V ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
  rw [← eLpNorm_sq_eq_lintegral]
  exact ENNReal.pow_lt_top hV.eLpNorm_lt_top

/-- The frozen integrand of a square-integrable coefficient has finite energy on every horizon. -/
theorem frozenCell_sq_int (s t : ℝ) {V : Ω → ℝ} (hV : MemLp V 2 P) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T,
      (‖frozenCell s t V ω r‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T _
  calc ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T, (‖frozenCell s t V ω r‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ _ in Set.Icc (0 : ℝ) T, (‖V ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun r => by
          gcongr
          exact_mod_cast nnnorm_frozenCell_le s t V ω r
    _ = (∫⁻ ω, (‖V ω‖₊ : ℝ≥0∞) ^ 2 ∂P) * ENNReal.ofReal T := by
        simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.mul_lt_top (lintegral_nnnorm_sq_lt_top hV) ENNReal.ofReal_lt_top

end Frozen

/-! ### The scalar identity -/

section Scalar

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : BrownianMotion P) (ℱ : MeasureTheory.Filtration ℝ mΩ) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **The Itô integral of a bounded coefficient frozen over a cell.** For a bounded
`ℱ_s`-measurable `V` and `r ≥ 0`, `∫_0^r 1_{(s,t]} V dW = V (W_{t ∧ r} − W_{s ∧ r})`. -/
theorem stochasticIntegralBrownian_frozenCell_of_bdd {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVa : StronglyMeasurable[ℱ s] V)
    (hm : Measurable (Function.uncurry (frozenCell s t V)))
    (hp : Probability.ProgressivelyMeasurable ℱ (frozenCell s t V))
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T,
      (‖frozenCell s t V ω r‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {r : ℝ} (hr : 0 ≤ r) :
    stochasticIntegralBrownian W ℱ hℱ (frozenCell s t V) hm hp hq r
      =ᵐ[P] fun ω => V ω * (W.W (min t r) ω - W.W (min s r) ω) := by
  have hVm : Measurable V := hVa.measurable.mono (ℱ.le s) le_rfl
  rcases eq_or_lt_of_le hs with rfl | hs'
  · set G := stepIocMul₀ Ω hst V hVb hVm
    have hfun : frozenCell 0 t V = fun ω x => G.eval x ω := by
      funext ω x
      rw [stepIocMul₀_eval, frozenCell_eq_mul_indIoc]
    have hm' : Measurable (Function.uncurry fun ω x => G.eval x ω) := hfun ▸ hm
    have hp' : Probability.ProgressivelyMeasurable ℱ fun ω x => G.eval x ω := hfun ▸ hp
    have hq' := energy_lt_top_congr hfun hq
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun hm hp hq hm' hp' hq' r]
    refine (stochasticIntegralBrownian_eval_simple W ℱ hℱ G
      (stepIocMul₀_adapt ℱ hst hVb hVm hVa) hm' hp' hq' hr).trans ?_
    exact Filter.Eventually.of_forall fun ω => stepIocMul₀_integralAgainst hst hVb hVm W.W r ω
  · set G := stepIocMul Ω hs' hst V hVb hVm
    have hfun : frozenCell s t V = fun ω x => G.eval x ω := by
      funext ω x
      rw [stepIocMul_eval, frozenCell_eq_mul_indIoc]
    have hm' : Measurable (Function.uncurry fun ω x => G.eval x ω) := hfun ▸ hm
    have hp' : Probability.ProgressivelyMeasurable ℱ fun ω x => G.eval x ω := hfun ▸ hp
    have hq' := energy_lt_top_congr hfun hq
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun hm hp hq hm' hp' hq' r]
    refine (stochasticIntegralBrownian_eval_simple W ℱ hℱ G
      (stepIocMul_adapt ℱ hs' hst hVb hVm hVa) hm' hp' hq' hr).trans ?_
    exact Filter.Eventually.of_forall fun ω => stepIocMul_integralAgainst hs' hst hVb hVm W.W r ω

omit [IsProbabilityMeasure P] in
/-- An extended sequence whose squares tend to `0` tends to `0`. -/
theorem tendsto_zero_of_tendsto_sq {f : ℕ → ℝ≥0∞}
    (h : Tendsto (fun n => f n ^ 2) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  have h' := ((ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).tendsto 0).comp h
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h'
  refine h'.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

omit [IsProbabilityMeasure P] in
/-- The truncations `V 1_{|V| ≤ n}` of a square-integrable `V` converge to `V` in energy. -/
theorem tendsto_lintegral_truncate_sub_sq {V : Ω → ℝ} (hV : MemLp V 2 P) (hVm : Measurable V) :
    Tendsto (fun n : ℕ => ∫⁻ ω, (‖{ω | |V ω| ≤ n}.indicator V ω - V ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hpt : ∀ (n : ℕ) ω, {ω | |V ω| ≤ n}.indicator V ω - V ω
      = if |V ω| ≤ n then 0 else -V ω := by
    intro n ω
    by_cases h : |V ω| ≤ n
    · simp [h]
    · simp [h]
  have hlim : ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P = 0 := lintegral_zero
  rw [← hlim]
  refine tendsto_lintegral_of_dominated_convergence' (fun ω => (‖V ω‖₊ : ℝ≥0∞) ^ 2)
    (fun n => ?_) (fun n => ae_of_all _ fun ω => ?_) (lintegral_nnnorm_sq_lt_top hV).ne
    (ae_of_all _ fun ω => ?_)
  · have hS : MeasurableSet {ω | |V ω| ≤ (n : ℝ)} := measurableSet_le hVm.abs measurable_const
    exact (((hVm.indicator hS).sub hVm).nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable
  · dsimp only
    rw [hpt]
    split_ifs <;> simp
  · refine tendsto_atTop_of_eventually_const (i₀ := ⌈|V ω|⌉₊) fun n hn => ?_
    have h : |V ω| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    rw [hpt, if_pos h]
    simp

include hℱ in
/-- **The Itô integral of a coefficient frozen over a cell.** For a square-integrable
`ℱ_s`-measurable `V` and `r ≥ 0`, `∫_0^r 1_{(s,t]} V dW = V (W_{t ∧ r} − W_{s ∧ r})` almost
surely. -/
theorem stochasticIntegralBrownian_frozenCell {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    {V : Ω → ℝ} (hV : MemLp V 2 P) (hVa : StronglyMeasurable[ℱ s] V)
    (hm : Measurable (Function.uncurry (frozenCell s t V)))
    (hp : Probability.ProgressivelyMeasurable ℱ (frozenCell s t V))
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T,
      (‖frozenCell s t V ω r‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {r : ℝ} (hr : 0 ≤ r) :
    stochasticIntegralBrownian W ℱ hℱ (frozenCell s t V) hm hp hq r
      =ᵐ[P] fun ω => V ω * (W.W (min t r) ω - W.W (min s r) ω) := by
  have hVm : Measurable V := hVa.measurable.mono (ℱ.le s) le_rfl
  rcases eq_or_lt_of_le hr with rfl | hr'
  · filter_upwards [stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ (frozenCell s t V) hm
      hp hq (le_refl (0 : ℝ))] with ω hω
    rw [hω, min_eq_right hs, min_eq_right (hs.trans hst.le)]
    simp
  set V' : ℕ → Ω → ℝ := fun n => {ω | |V ω| ≤ n}.indicator V with hV'
  have hS : ∀ n : ℕ, MeasurableSet[ℱ s] {ω | |V ω| ≤ (n : ℝ)} := fun n => by
    letI : MeasurableSpace Ω := ℱ s
    exact measurableSet_le hVa.measurable.abs measurable_const
  have hV'a : ∀ n, StronglyMeasurable[ℱ s] (V' n) := fun n => hVa.indicator (hS n)
  have hV'b : ∀ n : ℕ, ∃ M : ℝ, ∀ ω, |V' n ω| ≤ M := fun n => ⟨n, fun ω => by
    change |{ω | |V ω| ≤ (n : ℝ)}.indicator V ω| ≤ n
    by_cases h : |V ω| ≤ n
    · rw [Set.indicator_of_mem (show ω ∈ {ω | |V ω| ≤ (n : ℝ)} from h)]
      exact h
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | |V ω| ≤ (n : ℝ)} from h)]
      simp⟩
  have hV'm : ∀ n, Measurable (V' n) := fun n => (hV'a n).measurable.mono (ℱ.le s) le_rfl
  have hV'L : ∀ n, MemLp (V' n) 2 P := fun n => hV.indicator (ℱ.le s _ (hS n))
  have hm' := fun n => measurable_uncurry_frozenCell s t (hV'm n)
  have hp' := fun n => progressivelyMeasurable_frozenCell (ℱ := ℱ) (t := t) (hV'a n).measurable
  have hq' := fun n => frozenCell_sq_int (P := P) s t (hV'L n)
  set X : ℕ → Ω → ℝ := fun n =>
    stochasticIntegralBrownian W ℱ hℱ (frozenCell s t (V' n)) (hm' n) (hp' n) (hq' n) r with hX
  set Y := stochasticIntegralBrownian W ℱ hℱ (frozenCell s t V) hm hp hq r with hY
  have hXeq : ∀ n, X n =ᵐ[P] fun ω => V' n ω * (W.W (min t r) ω - W.W (min s r) ω) := fun n =>
    stochasticIntegralBrownian_frozenCell_of_bdd W ℱ hℱ hs hst (hV'b n) (hV'a n) _ _ _ hr
  have hiso : ∀ n, ∫⁻ ω, (‖X n ω - Y ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ (∫⁻ ω, (‖V' n ω - V ω‖₊ : ℝ≥0∞) ^ 2 ∂P) * ENNReal.ofReal r := by
    intro n
    rw [hX, hY, isometry_diff_stochasticIntegralBrownian W ℱ hℱ _ _ (hm' n) hm (hp' n) hp
      (hq' n) hq hr']
    calc ∫⁻ ω, ∫⁻ x in Set.Icc (0 : ℝ) r,
          (‖frozenCell s t (V' n) ω x - frozenCell s t V ω x‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ _ in Set.Icc (0 : ℝ) r, (‖V' n ω - V ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
          lintegral_mono fun ω => lintegral_mono fun x => by
            rw [frozenCell_sub]
            gcongr
            exact_mod_cast nnnorm_frozenCell_le s t _ ω x
      _ = (∫⁻ ω, (‖V' n ω - V ω‖₊ : ℝ≥0∞) ^ 2 ∂P) * ENNReal.ofReal r := by
          simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have hsq : Tendsto (fun n => ∫⁻ ω, (‖X n ω - Y ω‖₊ : ℝ≥0∞) ^ 2 ∂P) atTop (𝓝 0) := by
    have h0 := (ENNReal.Tendsto.mul_const (tendsto_lintegral_truncate_sub_sq hV hVm)
      (Or.inr ENNReal.ofReal_ne_top) : Tendsto _ atTop (𝓝 (0 * ENNReal.ofReal r)))
    rw [zero_mul] at h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le)
      hiso
  have hXL : ∀ n, MemLp (X n) 2 P := fun n => stochasticIntegralBrownian_memLp W ℱ hℱ _ _ _ _ r
  have hYL : MemLp Y 2 P := stochasticIntegralBrownian_memLp W ℱ hℱ _ _ _ _ r
  have hL2 : Tendsto (fun n => eLpNorm (X n - Y) 2 P) atTop (𝓝 0) := by
    refine tendsto_zero_of_tendsto_sq ?_
    simp_rw [eLpNorm_sq_eq_lintegral, Pi.sub_apply]
    exact hsq
  have htim : TendstoInMeasure P X atTop Y :=
    tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (fun n => (hXL n).aestronglyMeasurable)
      hYL.aestronglyMeasurable hL2
  obtain ⟨ns, hns, hae⟩ := htim.exists_seq_tendsto_ae
  filter_upwards [hae, ae_all_iff.2 fun n => hXeq (ns n)] with ω hω hωe
  refine tendsto_nhds_unique hω ?_
  simp_rw [hωe]
  refine tendsto_atTop_of_eventually_const (i₀ := ⌈|V ω|⌉₊) fun k hk => ?_
  have h : |V ω| ≤ (ns k : ℕ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hk.trans (hns.id_le k))
  change {ω | |V ω| ≤ ((ns k : ℕ) : ℝ)}.indicator V ω * _ = _
  rw [Set.indicator_of_mem (show ω ∈ {ω | |V ω| ≤ ((ns k : ℕ) : ℝ)} from h)]

end Scalar

/-! ### Coefficient rows -/

section Vector

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The integrand `r ↦ 1_{(s,t]}(r) z` of a coefficient row `z` frozen over the cell `(s, t]`. -/
noncomputable def frozenCellVec (s t : ℝ) (z : Ω → Fin d → ℝ) (r : ℝ) (ω : Ω) : Fin d → ℝ :=
  fun j => frozenCell s t (fun ω => z ω j) ω r

omit [IsProbabilityMeasure P] in
/-- Each coordinate of the frozen integrand of a measurable row is jointly measurable. -/
theorem measurable_frozenCellVec (s t : ℝ) {z : Ω → Fin d → ℝ}
    (hz : ∀ j, Measurable fun ω => z ω j) (j : Fin d) :
    Measurable (Function.uncurry fun ω r => frozenCellVec s t z r ω j) :=
  measurable_uncurry_frozenCell s t (hz j)

omit [IsProbabilityMeasure P] in
/-- Each coordinate of the frozen integrand of a row measurable at the start of the cell is
progressively measurable. -/
theorem progressivelyMeasurable_frozenCellVec {ℱ : MeasureTheory.Filtration ℝ mΩ} {s t : ℝ}
    {z : Ω → Fin d → ℝ} (hza : ∀ j, Measurable[ℱ s] fun ω => z ω j) (j : Fin d) :
    Probability.ProgressivelyMeasurable ℱ fun ω r => frozenCellVec s t z r ω j :=
  progressivelyMeasurable_frozenCell (hza j)

omit [IsProbabilityMeasure P] in
/-- Each coordinate of the frozen integrand of a square-integrable row has finite energy on
every horizon. -/
theorem frozenCellVec_sq_int (s t : ℝ) {z : Ω → Fin d → ℝ}
    (hz : ∀ j, MemLp (fun ω => z ω j) 2 P) (j : Fin d) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T,
      (‖frozenCellVec s t z r ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  frozenCell_sq_int s t (hz j)

variable (W : Multidim.MultidimBrownianMotion P d) (ℱ : MeasureTheory.Filtration ℝ mΩ)
  (hℱ : ∀ j, IsBrownianFiltration (W.W j) ℱ)

include hℱ in
/-- **The multidimensional integral of a row frozen over a cell.** For a square-integrable
`ℱ_s`-measurable row `z` and `r ≥ 0`, `∫_0^r 1_{(s,t]} z · dW = ∑ⱼ zⱼ (Wʲ_{t ∧ r} − Wʲ_{s ∧ r})`
almost surely. -/
theorem multidimStochasticIntegral_frozenCell {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    {z : Ω → Fin d → ℝ} (hz : ∀ j, MemLp (fun ω => z ω j) 2 P)
    (hza : ∀ j, StronglyMeasurable[ℱ s] fun ω => z ω j)
    (hm : ∀ j, Measurable (Function.uncurry fun ω r => frozenCellVec s t z r ω j))
    (hp : ∀ j, Probability.ProgressivelyMeasurable ℱ fun ω r => frozenCellVec s t z r ω j)
    (hq : ∀ j, ∀ T, 0 < T → ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T,
      (‖frozenCellVec s t z r ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {r : ℝ} (hr : 0 ≤ r) :
    Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ (frozenCellVec s t z) hm hp hq r
      =ᵐ[P] fun ω => ∑ j, z ω j * ((W.W j).W (min t r) ω - (W.W j).W (min s r) ω) := by
  have h := fun j => stochasticIntegralBrownian_frozenCell (W.W j) ℱ (hℱ j) hs hst (hz j)
    (hza j) (hm j) (hp j) (hq j) hr
  filter_upwards [ae_all_iff.2 h] with ω hω
  exact Finset.sum_congr rfl fun j _ => hω j

end Vector

end MVFBSDEJ.WellPosedness
