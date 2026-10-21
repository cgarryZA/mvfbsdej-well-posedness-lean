/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Dissertation.Law.LawP2
import Dissertation.Law.P2Metric

/-!
# The 2-Wasserstein distance separates laws

Two laws at squared 2-Wasserstein distance zero are equal. For every `r > 0` there is a coupling
`γ` of `(μ, ν)` of quadratic cost below `r³`; by Markov's inequality `γ` gives mass at most `r` to
`{‖x − y‖ ≥ r}`, so `μ(B) ≤ ν(B^r) + r` for every measurable `B` and its open `r`-thickening
`B^r`. The Lévy–Prokhorov distance of `μ` and `ν` therefore vanishes, and two laws at
Lévy–Prokhorov distance zero agree on the closed sets, hence everywhere. So the 2-Wasserstein
pseudometric on the laws of finite second moment is a metric.

## Main statements

* `Dissertation.Law.exists_isCoupling_transportCostSq_lt` — a coupling of quadratic cost below any
  bound above the squared distance.
* `Dissertation.Law.levyProkhorovEDist_eq_zero_of_w2sq_eq_zero` — squared 2-Wasserstein
  distance zero gives Lévy–Prokhorov distance zero.
* `Dissertation.Law.eq_of_w2sq_eq_zero` — laws at squared 2-Wasserstein distance zero are equal.
* `Dissertation.Law.P2.eq_of_w2P_eq_zero` — the same for laws of finite second moment.
* `Dissertation.Law.P2W.instT0Space` — the 2-Wasserstein space is a T₀ space.
-/

namespace Dissertation.Law

open MeasureTheory Filter Topology Metric
open scoped ENNReal

section Coupling

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

/-- A squared 2-Wasserstein distance below `c` is witnessed by a coupling of quadratic cost
below `c`. -/
theorem exists_isCoupling_transportCostSq_lt {μ ν : Measure E} {c : ℝ≥0∞} (h : w2sq μ ν < c) :
    ∃ γ, IsCoupling μ ν γ ∧ transportCostSq γ < c := by
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp h
  obtain ⟨hc, hlt⟩ := iInf_lt_iff.mp hγ
  exact ⟨γ, hc, hlt⟩

end Coupling

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- **Squared 2-Wasserstein distance zero gives Lévy–Prokhorov distance zero.** -/
theorem levyProkhorovEDist_eq_zero_of_w2sq_eq_zero {μ ν : Measure E} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : w2sq μ ν = 0) : levyProkhorovEDist μ ν = 0 := by
  refine le_antisymm (levyProkhorovEDist_le_of_forall_le μ ν 0 fun ε B hε hεt hB => ?_)
    bot_le
  set r := ε.toReal with hr
  have hr0 : 0 < r := ENNReal.toReal_pos hε.ne' hεt.ne
  obtain ⟨γ, hγ, hcost⟩ := exists_isCoupling_transportCostSq_lt
    (h.trans_lt (ENNReal.ofReal_pos.mpr (by positivity : 0 < r ^ 3)))
  have hsub : Prod.fst ⁻¹' B ⊆ Prod.snd ⁻¹' thickening r B
      ∪ {p : E × E | ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (‖p.1 - p.2‖ ^ 2)} := by
    intro p hp
    by_cases hlt : ‖p.1 - p.2‖ < r
    · refine Or.inl (mem_thickening_iff.mpr ⟨p.1, hp, ?_⟩)
      rwa [dist_eq_norm, norm_sub_rev]
    · refine Or.inr (ENNReal.ofReal_le_ofReal ?_)
      have := not_lt.mp hlt
      nlinarith
  have hmarkov : ENNReal.ofReal (r ^ 2)
      * γ {p : E × E | ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (‖p.1 - p.2‖ ^ 2)}
      < ENNReal.ofReal (r ^ 2) * ε := by
    refine (mul_meas_ge_le_lintegral₀ measurable_normSq_sub.aemeasurable _).trans_lt ?_
    refine hcost.trans_le (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal hεt.ne, ← hr, ← ENNReal.ofReal_mul (by positivity)]
    ring_nf
  have hsmall : γ {p : E × E | ENNReal.ofReal (r ^ 2) ≤ ENNReal.ofReal (‖p.1 - p.2‖ ^ 2)} < ε :=
    (ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      ENNReal.ofReal_ne_top).mp hmarkov
  calc μ B = γ (Prod.fst ⁻¹' B) := by
        rw [← hγ.1, Measure.fst_apply hB]
    _ ≤ γ (Prod.snd ⁻¹' thickening r B) + γ {p : E × E | ENNReal.ofReal (r ^ 2)
          ≤ ENNReal.ofReal (‖p.1 - p.2‖ ^ 2)} := (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ν (thickening r B) + ε := by
        rw [← hγ.2, Measure.snd_apply isOpen_thickening.measurableSet]
        exact add_le_add le_rfl hsmall.le

/-- **Laws at squared 2-Wasserstein distance zero are equal.** -/
theorem eq_of_w2sq_eq_zero {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : w2sq μ ν = 0) : μ = ν := by
  have hLP := levyProkhorovEDist_eq_zero_of_w2sq_eq_zero h
  refine ext_of_generate_finite _ ?_ isPiSystem_isClosed (fun A hA => ?_) (by simp)
  · rw [BorelSpace.measurable_eq (α := E), borel_eq_generateFrom_isClosed]
  · exact measure_eq_measure_of_levyProkhorovEDist_eq_zero_of_isClosed hLP hA
      ⟨1, one_pos, measure_ne_top _ _⟩ ⟨1, one_pos, measure_ne_top _ _⟩

/-- **Laws of finite second moment at 2-Wasserstein distance zero are equal.** -/
theorem P2.eq_of_w2P_eq_zero {μ ν : P2 E} (h : w2P μ ν = 0) : μ = ν := by
  refine P2.ext_law (eq_of_w2sq_eq_zero ?_)
  rw [w2P, w2, Real.sqrt_eq_zero ENNReal.toReal_nonneg,
    ENNReal.toReal_eq_zero_iff] at h
  exact h.resolve_right (w2sq_ne_top μ ν)

variable [CompleteSpace E]

/-- **The 2-Wasserstein space is T₀**: the 2-Wasserstein pseudometric on the laws of finite
second moment is a metric. -/
instance P2W.instT0Space : T0Space (P2W E) :=
  ⟨fun _ _ h => P2.eq_of_w2P_eq_zero (Metric.inseparable_iff.mp h)⟩

end Dissertation.Law
