/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Martingale.LocalIntegral
import LevyStochCalc.Probability.OpenExitTime
import LevyStochCalc.Ito.JumpCoefficientPredictableCriteria

/-!
# Local integrals of integrands weighted by left limits

Let `Y` be an `ℝᵐ`-valued process, adapted on `[0, T]` with càdlàg paths there and
`𝔼 sup_{t ≤ T} |Y_t|² < ∞`, and let `w_s` be a progressively measurable weight controlled by the
left limits of `Y` (as `e^s Y_{s−}` or `G Y_{s−}` are). For an integrand `Z` of finite energy the
product `∑_k w_k Z_k` need not have finite energy, but it does up to the exit times of `Y` from
balls, which localise it: it has a local stochastic integral `M`, and

`𝔼 sup_{t ≤ T} |M_t| ≤ 9 C (𝔼 sup_{t ≤ T} |Y_t|²)^{1/2} (𝔼 ∫_0^T |Z_s|² ds)^{1/2}`

when `|w_s|² ≤ C² sup_{t ≤ T} |Y_t|²`, by the Burkholder–Davis–Gundy inequality at `p = 1` and the
Cauchy–Schwarz inequality; the increments of `M` then have mean zero.

## Main statements

* `Dissertation.WellPosedness.Martingale.predictable_leftLim_Ioc` — the left limits of an adapted
  path on `(0, T]` are predictable.
* `Dissertation.WellPosedness.Martingale.localBrownian_weight` — the Brownian case.
* `Dissertation.WellPosedness.Martingale.localCompensated_weight` — the compensated Poisson case.
-/

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace Dissertation.WellPosedness.Martingale

open LevyStochCalc LevyStochCalc.Brownian.Multidim LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

section LeftLimit

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

/-- **The left limits of an adapted path on `(0, T]` are predictable.** For `Y` adapted on
`[0, T]` with left limits on `(0, T]`, the process equal to `Y_{s−}` for `s ∈ (0, T]` and to `0`
elsewhere is predictable. -/
theorem predictable_leftLim_Ioc {Y : ℝ → Ω → ℝ}
    (hYad : ∀ t ∈ Icc (0 : ℝ) T, Measurable[ℱ t] (Y t))
    (hYl : ∀ ω, ∀ t ∈ Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 l)) :
    Predictable ℱ fun ω s =>
      if s ∈ Ioc (0 : ℝ) T then Function.leftLim (fun r => Y r ω) s else 0 := by
  classical
  have hm : Measurable[predictableSigma ℱ] fun p : ℝ × Ω =>
      if p.1 ∈ Ioc (0 : ℝ) T then Function.leftLim (fun r => Y r p.2) p.1 else 0 := by
    refine measurable_predictableSigma_of_tendsto_leftGridPoint
      (Z := fun t ω => if t ∈ Ioc (0 : ℝ) T then Y t ω else 0)
      (Y := fun s ω => if s ∈ Ioc (0 : ℝ) T then Function.leftLim (fun r => Y r ω) s else 0)
      (fun t => ?_) (fun s ω => ?_)
    · by_cases ht : t ∈ Ioc (0 : ℝ) T
      · simp only [ht, if_true]
        exact hYad t ⟨ht.1.le, ht.2⟩
      · simp only [ht, if_false]
        exact measurable_const
    · have hgrid := tendsto_leftGridPoint s
      by_cases hs : s ∈ Ioc (0 : ℝ) T
      · obtain ⟨l, hl⟩ := hYl ω s hs
        have hll : Function.leftLim (fun r => Y r ω) s = l :=
          leftLim_eq_of_tendsto hl
        simp only [hs, if_true, hll]
        have hev : ∀ᶠ k : ℕ in atTop, leftGridPoint k s ∈ Ioc (0 : ℝ) T := by
          have h0 : ∀ᶠ k : ℕ in atTop, 0 < leftGridPoint k s :=
            (hgrid.mono_right nhdsWithin_le_nhds).eventually (lt_mem_nhds hs.1)
          filter_upwards [h0] with k hk
          exact ⟨hk, (leftGridPoint_lt k s).le.trans hs.2⟩
        refine (hl.comp hgrid).congr' ?_
        filter_upwards [hev] with k hk
        simp only [Function.comp_apply, hk, if_true]
      · simp only [hs, if_false]
        rcases le_or_gt s 0 with hs0 | hs0
        · refine tendsto_const_nhds.congr fun k => ?_
          have : leftGridPoint k s ∉ Ioc (0 : ℝ) T := fun h =>
            absurd (h.1.trans (leftGridPoint_lt k s)) (not_lt.mpr hs0)
          simp only [this, if_false]
        · have hsT : T < s := by
            by_contra h
            exact hs ⟨hs0, not_lt.mp h⟩
          have hev : ∀ᶠ k : ℕ in atTop, T < leftGridPoint k s :=
            (hgrid.mono_right nhdsWithin_le_nhds).eventually (lt_mem_nhds hsT)
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [hev] with k hk
          have : leftGridPoint k s ∉ Ioc (0 : ℝ) T := fun h => absurd h.2 (not_le.mpr hk)
          simp only [this, if_false]
  letI : MeasurableSpace (ℝ × Ω) := predictableSigma ℱ
  exact hm.stronglyMeasurable

end LeftLimit

section LeftLimitBounds

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ} {m : ℕ}

/-- **The left limits on `(0, T]` of an adapted process with left limits there** are jointly and
progressively measurable. -/
theorem progressive_leftLim_Ioc (hℱneg : ∀ r : ℝ, r ≤ 0 → ℱ 0 ≤ ℱ r) {Y : ℝ → Ω → ℝ}
    (hYad : ∀ t ∈ Icc (0 : ℝ) T, Measurable[ℱ t] (Y t))
    (hYl : ∀ ω, ∀ t ∈ Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 l)) :
    Measurable (Function.uncurry fun ω s =>
        if s ∈ Ioc (0 : ℝ) T then Function.leftLim (fun r => Y r ω) s else 0)
      ∧ ProgressivelyMeasurable ℱ fun ω s =>
        if s ∈ Ioc (0 : ℝ) T then Function.leftLim (fun r => Y r ω) s else 0 := by
  have hp := (predictable_leftLim_Ioc hYad hYl).progressivelyMeasurable hℱneg
  exact ⟨hp.measurable_uncurry, hp⟩

/-- A left limit at `s > 0` of a path bounded by `R` on `[0, s)` is bounded by `R`. -/
theorem abs_leftLim_le {f : ℝ → ℝ} {s R : ℝ} (hs : 0 < s) {l : ℝ}
    (hl : Tendsto f (𝓝[<] s) (𝓝 l)) (hb : ∀ u, 0 ≤ u → u < s → |f u| ≤ R) :
    |Function.leftLim f s| ≤ R := by
  rw [leftLim_eq_of_tendsto hl]
  have hev : ∀ᶠ u in 𝓝[<] s, |f u| ≤ R := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hs)] with u hu hu0
    exact hb u (le_of_lt hu0) hu
  exact le_of_tendsto (continuous_abs.continuousAt.tendsto.comp hl) hev

/-- The squared length of the left limit at `s ∈ (0, T]` of a path is at most the supremum of
its squared length over `[0, T]`. -/
theorem ofReal_sum_leftLim_sq_le {Y : Fin m → ℝ → Ω → ℝ} {ω : Ω} {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) T)
    (hYl : ∀ k, ∃ l : ℝ, Tendsto (fun r => Y k r ω) (𝓝[<] s) (𝓝 l)) :
    ENNReal.ofReal (∑ k, Function.leftLim (fun r => Y k r ω) s ^ 2)
      ≤ ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2 := by
  choose l hl using hYl
  have hll : ∀ k, Function.leftLim (fun r => Y k r ω) s = l k := fun k =>
    leftLim_eq_of_tendsto (hl k)
  simp only [hll]
  have htend : Tendsto (fun r => ENNReal.ofReal (∑ k, Y k r ω ^ 2)) (𝓝[<] s)
      (𝓝 (ENNReal.ofReal (∑ k, l k ^ 2))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_finsetSum _ fun k _ => (hl k).pow 2)
  have hev : ∀ᶠ r in 𝓝[<] s, ENNReal.ofReal (∑ k, Y k r ω ^ 2)
      ≤ ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hs.1)] with r hr hr0
    refine le_iSup₂_of_le r ⟨le_of_lt hr0, (le_of_lt hr).trans hs.2⟩ (le_of_eq ?_)
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
    simp_rw [nnnorm_sq_eq_ofReal]
  exact le_of_tendsto htend hev

end LeftLimitBounds

section Exit

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ} {m : ℕ}

/-- The path of `Y`, frozen at `Y_0` before `0` and at `Y_T` after `T`. -/
noncomputable def frozenPath (Y : Fin m → ℝ → Ω → ℝ) (T : ℝ) : Ω → ℝ → (Fin m → ℝ) :=
  fun ω r i => Y i (max 0 (min r T)) ω

/-- The exit times of the frozen path from the closed balls of radius `N`. -/
noncomputable def exitSeq (Y : Fin m → ℝ → Ω → ℝ) (T : ℝ) : ℕ → Ω → WithTop ℝ :=
  fun N => openExitTime (frozenPath Y T) (N : ℝ)

theorem frozenPath_of_mem {Y : Fin m → ℝ → Ω → ℝ} {ω : Ω} {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T)
    (i : Fin m) : frozenPath Y T ω r i = Y i r ω := by
  simp only [frozenPath, min_eq_left hr.2, max_eq_right hr.1]

theorem adapted_frozenPath (hT : 0 ≤ T) (hℱneg : ∀ r : ℝ, r ≤ 0 → ℱ 0 ≤ ℱ r)
    {Y : Fin m → ℝ → Ω → ℝ} (hYad : ∀ i, ∀ t ∈ Icc (0 : ℝ) T, Measurable[ℱ t] (Y i t)) :
    Adapted ℱ fun r ω => frozenPath Y T ω r := by
  intro r
  refine @measurable_pi_lambda Ω (Fin m) (fun _ => ℝ) (ℱ r) _
    (fun ω => frozenPath Y T ω r) fun i => ?_
  rcases lt_or_ge r 0 with hr | hr
  · have hc : max 0 (min r T) = 0 := max_eq_left ((min_le_left _ _).trans hr.le)
    simp only [frozenPath, hc]
    exact (hYad i 0 ⟨le_rfl, hT⟩).mono (hℱneg r hr.le) le_rfl
  · have hc : max 0 (min r T) ∈ Icc (0 : ℝ) T :=
      ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
    have hcr : max 0 (min r T) ≤ r := max_le hr (min_le_left _ _)
    exact (hYad i _ hc).mono (ℱ.mono hcr) le_rfl

theorem rightCont_frozenPath (hT : 0 ≤ T) {Y : Fin m → ℝ → Ω → ℝ}
    (hYr : ∀ i ω, ∀ t ∈ Ico (0 : ℝ) T, Tendsto (fun s => Y i s ω) (𝓝[>] t) (𝓝 (Y i t ω)))
    (ω : Ω) (s : ℝ) : Tendsto (frozenPath Y T ω) (𝓝[>] s) (𝓝 (frozenPath Y T ω s)) := by
  refine tendsto_pi_nhds.2 fun i => ?_
  rcases lt_or_ge s 0 with hs | hs
  · have hev : ∀ᶠ r in 𝓝[>] s, frozenPath Y T ω r i = frozenPath Y T ω s i := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hs)] with r hr
      have h1 : max 0 (min r T) = 0 := max_eq_left ((min_le_left _ _).trans (le_of_lt hr))
      have h2 : max 0 (min s T) = 0 := max_eq_left ((min_le_left _ _).trans hs.le)
      simp only [frozenPath, h1, h2]
    exact tendsto_const_nhds.congr' (hev.mono fun r hr => hr.symm)
  rcases lt_or_ge s T with hsT | hsT
  · have hev : ∀ᶠ r in 𝓝[>] s, Y i r ω = frozenPath Y T ω r i := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hsT), self_mem_nhdsWithin] with r hr hr'
      exact (frozenPath_of_mem ⟨hs.trans (le_of_lt hr'), le_of_lt hr⟩ i).symm
    rw [frozenPath_of_mem ⟨hs, hsT.le⟩ i]
    exact (hYr i ω s ⟨hs, hsT⟩).congr' hev
  · have hev : ∀ᶠ r in 𝓝[>] s, frozenPath Y T ω r i = frozenPath Y T ω s i := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : T ≤ r := hsT.trans (le_of_lt hr)
      simp only [frozenPath, min_eq_right hr', min_eq_right hsT]
    exact tendsto_const_nhds.congr' (hev.mono fun r hr => hr.symm)

/-- The exit times are stopping times of a right-continuous filtration. -/
theorem isStoppingTime_exitSeq [ℱ.IsRightContinuous] (hT : 0 ≤ T)
    (hℱneg : ∀ r : ℝ, r ≤ 0 → ℱ 0 ≤ ℱ r) {Y : Fin m → ℝ → Ω → ℝ}
    (hYad : ∀ i, ∀ t ∈ Icc (0 : ℝ) T, Measurable[ℱ t] (Y i t))
    (hYr : ∀ i ω, ∀ t ∈ Ico (0 : ℝ) T, Tendsto (fun s => Y i s ω) (𝓝[>] t) (𝓝 (Y i t ω)))
    (N : ℕ) : IsStoppingTime ℱ (exitSeq Y T N) := by
  have h := isStoppingTime_openExitTime (adapted_frozenPath hT hℱneg hYad)
    (rightCont_frozenPath hT hYr) (N : ℝ)
  rw [Filtration.IsRightContinuous.eq] at h
  exact h

theorem monotone_exitSeq (Y : Fin m → ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) :
    Monotone fun N => exitSeq Y T N ω := fun _ _ h =>
  openExitTime_mono _ ω (by exact_mod_cast h)

/-- Strictly before a time `s ≤ T` that the exit time has not passed, the path stays in the
ball. -/
theorem abs_le_of_le_exitSeq {Y : Fin m → ℝ → Ω → ℝ} {N : ℕ} {ω : Ω} {s u : ℝ} (hsT : s ≤ T)
    (hu : 0 ≤ u) (hus : u < s) (hs : ((s : ℝ) : WithTop ℝ) ≤ exitSeq Y T N ω) (i : Fin m) :
    |Y i u ω| ≤ N := by
  have hlt : ((u : ℝ) : WithTop ℝ) < exitSeq Y T N ω :=
    lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hus) hs
  have h := norm_le_of_lt_openExitTime hu hlt
  have hi := (norm_le_pi_norm (frozenPath Y T ω u) i).trans h
  rwa [frozenPath_of_mem ⟨hu, hus.le.trans hsT⟩, Real.norm_eq_abs] at hi

/-- A path with finite supremum of `|Y_t|²` on `[0, T]` has not exited a large ball by `T`. -/
theorem exists_le_exitSeq {Y : Fin m → ℝ → Ω → ℝ} {ω : Ω}
    (h : ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2 < ⊤) :
    ∃ N : ℕ, ((T : ℝ) : WithTop ℝ) ≤ exitSeq Y T N ω := by
  set B : ℝ := (⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2).toReal with hB
  refine ⟨⌈1 + B⌉₊, le_openExitTime_of_forall_norm_le fun s hs0 hsT => ?_⟩
  have hN : 1 + B ≤ (⌈1 + B⌉₊ : ℝ) := Nat.le_ceil _
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [frozenPath_of_mem ⟨hs0, hsT⟩, Real.norm_eq_abs]
  have hsq : (‖Y i s ω‖₊ : ℝ≥0∞) ^ 2 ≤ ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2 :=
    le_iSup₂_of_le s ⟨hs0, hsT⟩ (Finset.single_le_sum (f := fun i =>
      (‖Y i s ω‖₊ : ℝ≥0∞) ^ 2) (fun _ _ => bot_le) (Finset.mem_univ i))
  have hsqr : Y i s ω ^ 2 ≤ B := by
    rw [nnnorm_sq_eq_ofReal] at hsq
    have := ENNReal.toReal_mono h.ne hsq
    rwa [ENNReal.toReal_ofReal (sq_nonneg _)] at this
  have habs : |Y i s ω| ≤ 1 + Y i s ω ^ 2 := by
    rcases le_or_gt |Y i s ω| 1 with h1 | h1
    · nlinarith [sq_nonneg (Y i s ω)]
    · nlinarith [sq_abs (Y i s ω)]
  linarith

end Exit

section Helpers

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- A finite sum of progressively measurable processes is progressively measurable. -/
theorem progressivelyMeasurable_finset_sum {ι : Type*} (s : Finset ι) {A : ι → Ω → ℝ → ℝ}
    (h : ∀ i ∈ s, ProgressivelyMeasurable ℱ (A i)) :
    ProgressivelyMeasurable ℱ fun ω t => ∑ i ∈ s, A i ω t := by
  intro t
  have key : (fun p : Ω × ℝ => (Iic t).indicator (fun r => ∑ i ∈ s, A i p.1 r) p.2)
      = ∑ i ∈ s, fun p : Ω × ℝ => (Iic t).indicator (A i p.1) p.2 := by
    funext p
    rw [Finset.sum_apply]
    by_cases hp : p.2 ∈ Iic t
    · simp only [indicator_of_mem hp]
    · simp only [indicator_of_notMem hp, Finset.sum_const_zero]
  rw [key]
  exact Finset.stronglyMeasurable_sum s fun i hi => h i hi t

/-- `(∑_k |a_k|)² ≤ n ∑_k a_k²`, in `[0, ∞]`. -/
theorem nnnorm_sum_abs_sq_le {n : ℕ} (c : ℝ) (a : Fin n → ℝ) :
    (‖c * ∑ k, |a k|‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (c ^ 2 * n) * ∑ k, (‖a k‖₊ : ℝ≥0∞) ^ 2 := by
  rw [nnnorm_sq_eq_ofReal]
  simp_rw [nnnorm_sq_eq_ofReal]
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _,
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) fun k => |a k|
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sq_abs] at h
  calc (c * ∑ k, |a k|) ^ 2 = c ^ 2 * (∑ k, |a k|) ^ 2 := by ring
    _ ≤ c ^ 2 * (n * ∑ k, a k ^ 2) := by gcongr
    _ = c ^ 2 * n * ∑ k, a k ^ 2 := by ring

end Helpers

section Bounds

variable {P : Measure Ω}

/-- `(c²)^{1/2} = c` in `[0, ∞]` for `c ≥ 0`. -/
theorem ofReal_sq_rpow_half {C : ℝ} (hC : 0 ≤ C) :
    ENNReal.ofReal (C ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal C := by
  rw [ENNReal.ofReal_pow hC, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- **Cauchy–Schwarz for the expectation of a product of square roots.**
`𝔼 [C S^{1/2} B^{1/2}] ≤ C (𝔼 S)^{1/2} (𝔼 B)^{1/2}`. -/
theorem lintegral_mul_sqrt_le {S B : Ω → ℝ≥0∞} (hS : AEMeasurable S P) (hB : AEMeasurable B P)
    (c : ℝ≥0∞) :
    ∫⁻ ω, c * S ω ^ (1 / 2 : ℝ) * B ω ^ (1 / 2 : ℝ) ∂P
      ≤ c * (∫⁻ ω, S ω ∂P) ^ (1 / 2 : ℝ) * (∫⁻ ω, B ω ∂P) ^ (1 / 2 : ℝ) := by
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_mul]
    norm_num
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    (hS.pow_const (1 / 2 : ℝ)) (hB.pow_const (1 / 2 : ℝ))
  simp only [Pi.mul_apply, hsq] at h
  calc ∫⁻ ω, c * S ω ^ (1 / 2 : ℝ) * B ω ^ (1 / 2 : ℝ) ∂P
      = c * ∫⁻ ω, S ω ^ (1 / 2 : ℝ) * B ω ^ (1 / 2 : ℝ) ∂P := by
        simp_rw [mul_assoc]
        exact lintegral_const_mul'' c ((hS.pow_const _).mul (hB.pow_const _))
    _ ≤ c * ((∫⁻ ω, S ω ∂P) ^ (1 / 2 : ℝ) * (∫⁻ ω, B ω ∂P) ^ (1 / 2 : ℝ)) := by gcongr
    _ = _ := by ring

end Bounds

section BrownianWeight

variable {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
  (W : MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : ∀ i, Brownian.IsBrownianFiltration (W.W i) ℱ)

/-- **Local Itô integrals of integrands weighted by left limits.** Let `Y` be adapted on `[0, T]`
with paths right-continuous on `[0, T)` and `𝔼 sup_{t ≤ T} |Y_t|² < ∞`; let the weight `w` be
progressively measurable, bounded by `C₁ R` at a time `s ≤ T` before which `|Y| ≤ R`, with
`|w_s|² ≤ C² sup_{t ≤ T} |Y_t|²` on `[0, T]`; and let `Z` be of finite energy, vanishing off
`[0, T]`. Then `H = ∑_k w_k Z_k` has a local Itô integral `M` on `[0, T]`; every such `M` has
`𝔼 sup_{t ≤ T} |M_t| ≤ 9 C (𝔼 sup_{t ≤ T} |Y_t|²)^{1/2} (𝔼 ∫_0^T |Z_s|² ds)^{1/2}`, and its
increments `M_T − M_t` are integrable with mean zero. -/
theorem localBrownian_weight [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hℱneg : ∀ r : ℝ, r ≤ 0 → ℱ 0 ≤ ℱ r)
    {T : ℝ} (hT : 0 < T) {m n : ℕ} {Y : Fin m → ℝ → Ω → ℝ}
    (hYad : ∀ i, ∀ t ∈ Icc (0 : ℝ) T, Measurable[ℱ t] (Y i t))
    (hYr : ∀ i ω, ∀ t ∈ Ico (0 : ℝ) T, Tendsto (fun s => Y i s ω) (𝓝[>] t) (𝓝 (Y i t ω)))
    (hYS : ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤)
    {w : Fin n → ℝ → Ω → ℝ}
    (hwm : ∀ k, Measurable (Function.uncurry fun ω s => w k s ω))
    (hwp : ∀ k, ProgressivelyMeasurable ℱ fun ω s => w k s ω)
    {C₁ : ℝ} (hwb : ∀ (R : ℝ), 0 ≤ R → ∀ k ω s, 0 ≤ s → s ≤ T →
      (∀ u, 0 ≤ u → u < s → ∀ i, |Y i u ω| ≤ R) → |w k s ω| ≤ C₁ * R)
    {C : ℝ} (hC : 0 ≤ C)
    (hwsq : ∀ ω, ∀ s ∈ Icc (0 : ℝ) T, ENNReal.ofReal (∑ k, w k s ω ^ 2)
      ≤ ENNReal.ofReal (C ^ 2) * ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2)
    {Z : Fin n → ℝ → Ω → Fin d → ℝ}
    (hZm : ∀ k j, Measurable (Function.uncurry fun ω s => Z k s ω j))
    (hZp : ∀ k j, ProgressivelyMeasurable ℱ fun ω s => Z k s ω j)
    (hZq : ∀ k j (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T', (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hZv : ∀ k ω s, s ∉ Icc (0 : ℝ) T → Z k s ω = 0) :
    (∃ M, IsLocalBrownianIntegral W ℱ hℱ T (fun s ω j => ∑ k, w k s ω * Z k s ω j) M)
    ∧ ∀ M, IsLocalBrownianIntegral W ℱ hℱ T (fun s ω j => ∑ k, w k s ω * Z k s ω j) M →
      ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
          ≤ 9 * ENNReal.ofReal C
            * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)
            * (∑ k, ∑ j, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
              ^ (1 / 2 : ℝ)
        ∧ ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun ω => M T ω - M t ω) P
          ∧ ∫ ω, (M T ω - M t ω) ∂P = 0 := by
  classical
  set H : ℝ → Ω → Fin d → ℝ := fun s ω j => ∑ k, w k s ω * Z k s ω j with hHdef
  have hHm : ∀ j, Measurable (Function.uncurry fun ω s => H s ω j) := fun j =>
    Finset.measurable_sum _ fun k _ => (hwm k).mul (hZm k j)
  have hHp : ∀ j, ProgressivelyMeasurable ℱ fun ω s => H s ω j := fun j =>
    progressivelyMeasurable_finset_sum _ fun k _ => (hwp k).mul (hZp k j)
  set S : Ω → ℝ≥0∞ := fun ω => ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2 with hSdef
  have hSm : Measurable S := by
    refine measurable_biSup_Icc_ennreal hT.le (fun t ht => Finset.measurable_sum _ fun i _ =>
      ((hYad i t ht).mono (ℱ.le t) le_rfl).nnnorm.coe_nnreal_ennreal.pow_const 2)
      fun ω t ht => ?_
    refine tendsto_finsetSum _ fun i _ => ?_
    exact ((ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp
      continuous_nnnorm)).continuousAt.tendsto.comp (hYr i ω t ht)
  have hSfin : ∀ᵐ ω ∂P, S ω < ⊤ := ae_lt_top hSm hYS.ne
  set τ : ℕ → Ω → WithTop ℝ := exitSeq Y T with hτdef
  have hτ : ∀ N, IsStoppingTime ℱ (τ N) := isStoppingTime_exitSeq hT.le hℱneg hYad hYr
  have hmono : ∀ ω, Monotone fun N => τ N ω := monotone_exitSeq Y T
  have hex : ∀ᵐ ω ∂P, ∃ N, ((T : ℝ) : WithTop ℝ) ≤ τ N ω := by
    filter_upwards [hSfin] with ω h
    exact exists_le_exitSeq h
  -- the cut-off integrands are dominated by integrands of finite energy
  have hcutle : ∀ (N : ℕ) (j : Fin d) ω s,
      |Probability.stopped (τ N) (fun ω s => H s ω j) ω s|
        ≤ abs ((|C₁| * N) * ∑ k, |Z k s ω j|) := by
    intro N j ω s
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (|C₁| * N) * ∑ k, |Z k s ω j|)]
    simp only [Probability.stopped]
    split_ifs with hle
    · by_cases hs : s ∈ Icc (0 : ℝ) T
      · calc |H s ω j| ≤ ∑ k, |w k s ω * Z k s ω j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k, |w k s ω| * |Z k s ω j| := by simp only [abs_mul]
          _ ≤ ∑ k, (|C₁| * N) * |Z k s ω j| := by
              refine Finset.sum_le_sum fun k _ => ?_
              gcongr
              refine (hwb N (Nat.cast_nonneg N) k ω s hs.1 hs.2 fun u hu hus i =>
                abs_le_of_le_exitSeq hs.2 hu hus hle i).trans ?_
              gcongr
              exact le_abs_self C₁
          _ = (|C₁| * N) * ∑ k, |Z k s ω j| := by rw [Finset.mul_sum]
      · have : H s ω j = 0 := by
          simp only [hHdef, hZv _ ω s hs, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
        rw [this, abs_zero]
        positivity
    · rw [abs_zero]
      positivity
  have hGq : ∀ (N : ℕ) (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T',
      (‖(|C₁| * N) * ∑ k, |Z k s ω j|‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro N j T' hT'
    have hslice : ∀ k ω, Measurable fun s => (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 := fun k ω =>
      ((hZm k j).comp measurable_prodMk_left).nnnorm.coe_nnreal_ennreal.pow_const 2
    have hfun : ∀ k, Measurable fun ω => ∫⁻ s in Icc (0 : ℝ) T', (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 :=
      fun k => ((hZm k j).nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
    calc ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T', (‖(|C₁| * N) * ∑ k, |Z k s ω j|‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T', ENNReal.ofReal ((|C₁| * N) ^ 2 * n)
            * ∑ k, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
          lintegral_mono fun ω => lintegral_mono fun s =>
            nnnorm_sum_abs_sq_le _ fun k => Z k s ω j
      _ = ENNReal.ofReal ((|C₁| * N) ^ 2 * n)
            * ∑ k, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T', (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
          simp_rw [lintegral_const_mul _ (Finset.measurable_sum _ fun k _ => hslice k _)]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          simp_rw [lintegral_finsetSum _ fun k _ => hslice k _]
          exact lintegral_finsetSum _ fun k _ => hfun k
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.sum_lt_top.2 fun k _ => hZq k j T' hT')
  refine ⟨exists_isLocalBrownianIntegral W ℱ hℱ hℱ0 hnull hT H τ hτ hmono hex
    (fun N j => Probability.measurable_uncurry_stopped (hτ N) (hHm j))
    (fun N j => (hHp j).stopped (hτ N))
    (fun N j => Brownian.Ito.energy_lt_top_of_abs_le (hcutle N j) (hGq N j)), ?_⟩
  intro M hM
  -- the pathwise bound on the quadratic variation
  set B : Ω → ℝ≥0∞ := fun ω => ∑ k, ∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2
    with hBdef
  have hBm : Measurable B := Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun j _ => ((hZm k j).nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  have hpt : ∀ ω, (∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal C * S ω ^ (1 / 2 : ℝ) * B ω ^ (1 / 2 : ℝ) := by
    intro ω
    have hZs : ∀ k j, Measurable fun s => (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 := fun k j =>
      ((hZm k j).comp measurable_prodMk_left).nnnorm.coe_nnreal_ennreal.pow_const 2
    have h1 : ∀ s ∈ Icc (0 : ℝ) T, ∑ j, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal (C ^ 2) * S ω * ∑ k, ∑ j, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 := by
      intro s hs
      calc ∑ j, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2
          ≤ ∑ j, ENNReal.ofReal (∑ k, w k s ω ^ 2) * ENNReal.ofReal (∑ k, Z k s ω j ^ 2) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [nnnorm_sq_eq_ofReal, ← ENNReal.ofReal_mul (Finset.sum_nonneg fun k _ =>
              sq_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
        _ = ENNReal.ofReal (∑ k, w k s ω ^ 2) * ∑ j, ∑ k, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            congr 1
            rw [ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _]
            simp_rw [nnnorm_sq_eq_ofReal]
        _ ≤ ENNReal.ofReal (C ^ 2) * S ω * ∑ j, ∑ k, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 := by
            gcongr
            exact hwsq ω s hs
        _ = ENNReal.ofReal (C ^ 2) * S ω * ∑ k, ∑ j, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 := by
            rw [Finset.sum_comm]
    have h2 : ∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal (C ^ 2) * S ω * B ω := by
      have hHs : ∀ j, Measurable fun s => (‖H s ω j‖₊ : ℝ≥0∞) ^ 2 := fun j =>
        ((hHm j).comp measurable_prodMk_left).nnnorm.coe_nnreal_ennreal.pow_const 2
      rw [← lintegral_finsetSum _ fun j _ => hHs j]
      calc ∫⁻ s in Icc (0 : ℝ) T, ∑ j, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2
          ≤ ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (C ^ 2) * S ω
              * ∑ k, ∑ j, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 :=
            setLIntegral_mono' measurableSet_Icc h1
        _ = ENNReal.ofReal (C ^ 2) * S ω * B ω := by
            rw [lintegral_const_mul _ (Finset.measurable_sum _ fun k _ =>
              Finset.measurable_sum _ fun j _ => hZs k j)]
            congr 1
            rw [lintegral_finsetSum _ fun k _ => Finset.measurable_sum _ fun j _ => hZs k j]
            refine Finset.sum_congr rfl fun k _ => ?_
            exact lintegral_finsetSum _ fun j _ => hZs k j
    calc (∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (C ^ 2) * S ω * B ω) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow h2 (by norm_num)
      _ = ENNReal.ofReal C * S ω ^ (1 / 2 : ℝ) * B ω ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ofReal_sq_rpow_half hC]
  have hBint : ∫⁻ ω, B ω ∂P
      = ∑ k, ∑ j, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    have hZω : ∀ k j, Measurable fun ω => ∫⁻ s in Icc (0 : ℝ) T, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 :=
      fun k j => ((hZm k j).nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
    rw [hBdef, lintegral_finsetSum _ fun k _ => Finset.measurable_sum _ fun j _ => hZω k j]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact lintegral_finsetSum _ fun j _ => hZω k j
  have hroot : ∫⁻ ω, (∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) ∂P
      ≤ ENNReal.ofReal C * (∫⁻ ω, S ω ∂P) ^ (1 / 2 : ℝ)
        * (∑ k, ∑ j, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          ^ (1 / 2 : ℝ) := by
    rw [← hBint]
    exact (lintegral_mono hpt).trans
      (lintegral_mul_sqrt_le hSm.aemeasurable hBm.aemeasurable _)
  refine ⟨?_, fun t ht => ?_⟩
  · calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
        ≤ 9 * ∫⁻ ω, (∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) ∂P :=
          hM.lintegral_biSup_le W ℱ hℱ hℱ0 hnull hT
      _ ≤ 9 * (ENNReal.ofReal C * (∫⁻ ω, S ω ∂P) ^ (1 / 2 : ℝ)
          * (∑ k, ∑ j, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖Z k s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            ^ (1 / 2 : ℝ)) := by gcongr
      _ = _ := by simp only [hSdef]; ring
  · have hfin : ∫⁻ ω, (∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) ∂P
        < ⊤ := by
      refine hroot.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hYS.ne))
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_))
      exact (ENNReal.sum_lt_top.2 fun k _ => ENNReal.sum_lt_top.2 fun j _ =>
        hZq k j T hT).ne
    exact hM.integral_sub_eq_zero W ℱ hℱ hℱ0 hnull hT hHm hfin ht

end BrownianWeight

section CompensatedWeight

variable {P : Measure Ω} [IsProbabilityMeasure P] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν]

/-- The product of a progressively measurable process and a marked progressively measurable
process is marked progressively measurable. -/
theorem markedProgressivelyMeasurable_mul_left {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {A : Ω → ℝ → ℝ} {φ : Ω → ℝ → E → ℝ} (hA : ProgressivelyMeasurable ℱ A)
    (hφ : MarkedProgressivelyMeasurable ℱ φ) :
    MarkedProgressivelyMeasurable ℱ fun ω s e => A ω s * φ ω s e := by
  intro t
  have key : (fun p : Ω × ℝ × E => (Iic t).indicator (fun s => A p.1 s * φ p.1 s p.2.2) p.2.1)
      = fun p : Ω × ℝ × E => (Iic t).indicator (A p.1) p.2.1
        * (Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1 := by
    funext p
    by_cases hp : p.2.1 ∈ Iic t
    · simp only [indicator_of_mem hp]
    · simp only [indicator_of_notMem hp, zero_mul]
  rw [key]
  letI : MeasurableSpace Ω := ℱ t
  have h1 : StronglyMeasurable fun p : Ω × ℝ × E => (Iic t).indicator (A p.1) p.2.1 :=
    (hA t).comp_measurable (measurable_fst.prodMk measurable_snd.fst)
  exact h1.mul (hφ t)

/-- A finite sum of marked progressively measurable processes is marked progressively
measurable. -/
theorem markedProgressivelyMeasurable_finset_sum {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {ι : Type*} (s : Finset ι) {φ : ι → Ω → ℝ → E → ℝ}
    (h : ∀ i ∈ s, MarkedProgressivelyMeasurable ℱ (φ i)) :
    MarkedProgressivelyMeasurable ℱ fun ω r e => ∑ i ∈ s, φ i ω r e := by
  intro t
  have key : (fun p : Ω × ℝ × E => (Iic t).indicator (fun r => ∑ i ∈ s, φ i p.1 r p.2.2) p.2.1)
      = ∑ i ∈ s, fun p : Ω × ℝ × E => (Iic t).indicator (fun r => φ i p.1 r p.2.2) p.2.1 := by
    funext p
    rw [Finset.sum_apply]
    by_cases hp : p.2.1 ∈ Iic t
    · simp only [indicator_of_mem hp]
    · simp only [indicator_of_notMem hp, Finset.sum_const_zero]
  rw [key]
  exact Finset.stronglyMeasurable_sum s fun i hi => h i hi t

variable (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)

/-- **Local compensated integrals of marked integrands weighted by left limits.** With `Y` and the
weight `w` as in `localBrownian_weight`, and a marked integrand `U` of finite energy vanishing off
`[0, T]`, `φ = ∑_k w_k U_k` has a local compensated integral `M` on `[0, T]`; every such `M` has
`𝔼 sup_{t ≤ T} |M_t| ≤ 9 C (𝔼 sup_{t ≤ T} |Y_t|²)^{1/2} (𝔼 ∫_0^T ‖U_s‖²_{L²(ν)} ds)^{1/2}`, and
its increments `M_T − M_t` are integrable with mean zero. -/
theorem localCompensated_weight [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hℱneg : ∀ r : ℝ, r ≤ 0 → ℱ 0 ≤ ℱ r)
    {T : ℝ} (hT : 0 < T) {m n : ℕ} {Y : Fin m → ℝ → Ω → ℝ}
    (hYad : ∀ i, ∀ t ∈ Icc (0 : ℝ) T, Measurable[ℱ t] (Y i t))
    (hYr : ∀ i ω, ∀ t ∈ Ico (0 : ℝ) T, Tendsto (fun s => Y i s ω) (𝓝[>] t) (𝓝 (Y i t ω)))
    (hYS : ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤)
    {w : Fin n → ℝ → Ω → ℝ}
    (hwm : ∀ k, Measurable (Function.uncurry fun ω s => w k s ω))
    (hwp : ∀ k, ProgressivelyMeasurable ℱ fun ω s => w k s ω)
    {C₁ : ℝ} (hwb : ∀ (R : ℝ), 0 ≤ R → ∀ k ω s, 0 ≤ s → s ≤ T →
      (∀ u, 0 ≤ u → u < s → ∀ i, |Y i u ω| ≤ R) → |w k s ω| ≤ C₁ * R)
    {C : ℝ} (hC : 0 ≤ C)
    (hwsq : ∀ ω, ∀ s ∈ Icc (0 : ℝ) T, ENNReal.ofReal (∑ k, w k s ω ^ 2)
      ≤ ENNReal.ofReal (C ^ 2) * ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2)
    {U : Fin n → ℝ → Ω → E → ℝ}
    (hUm : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2)
    (hUp : ∀ k, MarkedProgressivelyMeasurable ℱ fun ω s e => U k s ω e)
    (hUq : ∀ k (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T', ∫⁻ e,
      (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hUv : ∀ k ω s e, s ∉ Icc (0 : ℝ) T → U k s ω e = 0) :
    (∃ M, IsLocalCompensatedIntegral N ℱ hℱ T
      (fun ω s e => ∑ k, w k s ω * U k s ω e) M)
    ∧ ∀ M, IsLocalCompensatedIntegral N ℱ hℱ T (fun ω s e => ∑ k, w k s ω * U k s ω e) M →
      ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
          ≤ 9 * ENNReal.ofReal C
            * (∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ (1 / 2 : ℝ)
            * (∑ k, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2
                ∂ν ∂volume ∂P) ^ (1 / 2 : ℝ)
        ∧ ∀ t ∈ Icc (0 : ℝ) T, Integrable (fun ω => M T ω - M t ω) P
          ∧ ∫ ω, (M T ω - M t ω) ∂P = 0 := by
  classical
  set φ : Ω → ℝ → E → ℝ := fun ω s e => ∑ k, w k s ω * U k s ω e with hφdef
  have hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 :=
    Finset.measurable_sum _ fun k _ =>
      ((hwm k).comp (measurable_fst.prodMk measurable_snd.fst)).mul (hUm k)
  have hφp : MarkedProgressivelyMeasurable ℱ φ :=
    markedProgressivelyMeasurable_finset_sum _ fun k _ =>
      markedProgressivelyMeasurable_mul_left (hwp k) (hUp k)
  set S : Ω → ℝ≥0∞ := fun ω => ⨆ t ∈ Icc (0 : ℝ) T, ∑ i, (‖Y i t ω‖₊ : ℝ≥0∞) ^ 2 with hSdef
  have hSm : Measurable S := by
    refine measurable_biSup_Icc_ennreal hT.le (fun t ht => Finset.measurable_sum _ fun i _ =>
      ((hYad i t ht).mono (ℱ.le t) le_rfl).nnnorm.coe_nnreal_ennreal.pow_const 2)
      fun ω t ht => ?_
    refine tendsto_finsetSum _ fun i _ => ?_
    exact ((ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp
      continuous_nnnorm)).continuousAt.tendsto.comp (hYr i ω t ht)
  have hSfin : ∀ᵐ ω ∂P, S ω < ⊤ := ae_lt_top hSm hYS.ne
  set τ : ℕ → Ω → WithTop ℝ := exitSeq Y T with hτdef
  have hτ : ∀ k, IsStoppingTime ℱ (τ k) := isStoppingTime_exitSeq hT.le hℱneg hYad hYr
  have hmono : ∀ ω, Monotone fun k => τ k ω := monotone_exitSeq Y T
  have hex : ∀ᵐ ω ∂P, ∃ k, ((T : ℝ) : WithTop ℝ) ≤ τ k ω := by
    filter_upwards [hSfin] with ω h
    exact exists_le_exitSeq h
  have hcutle : ∀ (R : ℕ) ω s e,
      |Poisson.Compensated.markedStopped (τ R) φ ω s e|
        ≤ abs ((|C₁| * R) * ∑ k, |U k s ω e|) := by
    intro R ω s e
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (|C₁| * R) * ∑ k, |U k s ω e|)]
    simp only [Poisson.Compensated.markedStopped]
    split_ifs with hle
    · by_cases hs : s ∈ Icc (0 : ℝ) T
      · calc |φ ω s e| ≤ ∑ k, |w k s ω * U k s ω e| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k, |w k s ω| * |U k s ω e| := by simp only [abs_mul]
          _ ≤ ∑ k, (|C₁| * R) * |U k s ω e| := by
              refine Finset.sum_le_sum fun k _ => ?_
              gcongr
              refine (hwb R (Nat.cast_nonneg R) k ω s hs.1 hs.2 fun u hu hus i =>
                abs_le_of_le_exitSeq hs.2 hu hus hle i).trans ?_
              gcongr
              exact le_abs_self C₁
          _ = (|C₁| * R) * ∑ k, |U k s ω e| := by rw [Finset.mul_sum]
      · have : φ ω s e = 0 := by
          simp only [hφdef, hUv _ ω s e hs, mul_zero, Finset.sum_const_zero]
        rw [this, abs_zero]
        positivity
    · rw [abs_zero]
      positivity
  have hGq : ∀ (R : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T', ∫⁻ e,
      (‖(|C₁| * R) * ∑ k, |U k s ω e|‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
    intro R T' hT'
    have he : ∀ k ω s, Measurable fun e => (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 := fun k ω s =>
      ((hUm k).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).nnnorm
        |>.coe_nnreal_ennreal.pow_const 2
    have hs : ∀ k ω, Measurable fun s => ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := fun k ω => by
      have h3 : Measurable fun q : ℝ × E => (‖U k q.1 ω q.2‖₊ : ℝ≥0∞) ^ 2 :=
        ((hUm k).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).nnnorm
          |>.coe_nnreal_ennreal.pow_const 2
      exact h3.lintegral_prod_right'
    have hω : ∀ k, Measurable fun ω => ∫⁻ s in Icc (0 : ℝ) T', ∫⁻ e,
        (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := fun k => by
      have h3 : Measurable fun q : (Ω × ℝ) × E => (‖U k q.1.2 q.1.1 q.2‖₊ : ℝ≥0∞) ^ 2 :=
        ((hUm k).comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk
          measurable_snd))).nnnorm.coe_nnreal_ennreal.pow_const 2
      exact h3.lintegral_prod_right'.lintegral_prod_right'
    calc ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T', ∫⁻ e,
          (‖(|C₁| * R) * ∑ k, |U k s ω e|‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T', ∫⁻ e, ENNReal.ofReal ((|C₁| * R) ^ 2 * n)
            * ∑ k, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
          lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e =>
            nnnorm_sum_abs_sq_le _ fun k => U k s ω e
      _ = ENNReal.ofReal ((|C₁| * R) ^ 2 * n) * ∑ k, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T', ∫⁻ e,
            (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
          have hin : ∀ ω, ∫⁻ s in Icc (0 : ℝ) T', ∫⁻ e, ENNReal.ofReal ((|C₁| * R) ^ 2 * n)
              * ∑ k, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
              = ENNReal.ofReal ((|C₁| * R) ^ 2 * n) * ∑ k, ∫⁻ s in Icc (0 : ℝ) T', ∫⁻ e,
                (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
            intro ω
            simp_rw [lintegral_const_mul _ (Finset.measurable_sum _ fun k _ => he k _ _),
              lintegral_finsetSum _ fun k _ => he k _ _]
            rw [lintegral_const_mul _ (Finset.measurable_sum _ fun k _ => hs k _),
              lintegral_finsetSum _ fun k _ => hs k _]
          simp_rw [hin]
          rw [lintegral_const_mul _ (Finset.measurable_sum _ fun k _ => hω k),
            lintegral_finsetSum _ fun k _ => hω k]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.sum_lt_top.2 fun k _ => hUq k T' hT')
  refine ⟨exists_isLocalCompensatedIntegral N ℱ hℱ hℱ0 hnull hT φ τ hτ hmono hex
    (fun R => Poisson.Compensated.measurable_markedStopped (hτ R) hφm)
    (fun R => Poisson.Compensated.markedProgressivelyMeasurable_markedStopped (hτ R) hφp)
    (fun R => markedEnergy_lt_top_of_abs_le (hcutle R) (hGq R)), ?_⟩
  intro M hM
  set B : Ω → ℝ≥0∞ := fun ω => ∑ k, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν
    with hBdef
  have hUω : ∀ k, Measurable fun ω => ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
      (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := fun k => by
    have h3 : Measurable fun q : (Ω × ℝ) × E => (‖U k q.1.2 q.1.1 q.2‖₊ : ℝ≥0∞) ^ 2 :=
      ((hUm k).comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk
        measurable_snd))).nnnorm.coe_nnreal_ennreal.pow_const 2
    exact h3.lintegral_prod_right'.lintegral_prod_right'
  have hBm : Measurable B := Finset.measurable_sum _ fun k _ => hUω k
  have hpt : ∀ ω, (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal C * S ω ^ (1 / 2 : ℝ) * B ω ^ (1 / 2 : ℝ) := by
    intro ω
    have he : ∀ k s, Measurable fun e => (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 := fun k s =>
      ((hUm k).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).nnnorm
        |>.coe_nnreal_ennreal.pow_const 2
    have hs : ∀ k, Measurable fun s => ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := fun k => by
      have h3 : Measurable fun q : ℝ × E => (‖U k q.1 ω q.2‖₊ : ℝ≥0∞) ^ 2 :=
        ((hUm k).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).nnnorm
          |>.coe_nnreal_ennreal.pow_const 2
      exact h3.lintegral_prod_right'
    have h1 : ∀ s ∈ Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν
        ≤ ENNReal.ofReal (C ^ 2) * S ω * ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
      intro s hs'
      calc ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν
          ≤ ∫⁻ e, ENNReal.ofReal (∑ k, w k s ω ^ 2) * ∑ k, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
            refine lintegral_mono fun e => ?_
            rw [nnnorm_sq_eq_ofReal]
            simp_rw [nnnorm_sq_eq_ofReal]
            rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _,
              ← ENNReal.ofReal_mul (Finset.sum_nonneg fun k _ => sq_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
        _ = ENNReal.ofReal (∑ k, w k s ω ^ 2) * ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
            rw [lintegral_const_mul _ (Finset.measurable_sum _ fun k _ => he k s),
              lintegral_finsetSum _ fun k _ => he k s]
        _ ≤ ENNReal.ofReal (C ^ 2) * S ω * ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
            gcongr
            exact hwsq ω s hs'
    have h2 : ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν
        ≤ ENNReal.ofReal (C ^ 2) * S ω * B ω := by
      calc ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν
          ≤ ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal (C ^ 2) * S ω
              * ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
            setLIntegral_mono' measurableSet_Icc h1
        _ = ENNReal.ofReal (C ^ 2) * S ω * B ω := by
            rw [lintegral_const_mul _ (Finset.measurable_sum _ fun k _ => hs k),
              lintegral_finsetSum _ fun k _ => hs k]
    calc (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (C ^ 2) * S ω * B ω) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow h2 (by norm_num)
      _ = ENNReal.ofReal C * S ω ^ (1 / 2 : ℝ) * B ω ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ofReal_sq_rpow_half hC]
  have hBint : ∫⁻ ω, B ω ∂P = ∑ k, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
      (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
    rw [hBdef, lintegral_finsetSum _ fun k _ => hUω k]
  have hroot : ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
      ∂P ≤ ENNReal.ofReal C * (∫⁻ ω, S ω ∂P) ^ (1 / 2 : ℝ)
        * (∑ k, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P) ^ (1 / 2 : ℝ) := by
    rw [← hBint]
    exact (lintegral_mono hpt).trans
      (lintegral_mul_sqrt_le hSm.aemeasurable hBm.aemeasurable _)
  refine ⟨?_, fun t ht => ?_⟩
  · calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
        ≤ 9 * ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
            ^ (1 / 2 : ℝ) ∂P := hM.lintegral_biSup_le N ℱ hℱ hℱ0 hnull hT
      _ ≤ 9 * (ENNReal.ofReal C * (∫⁻ ω, S ω ∂P) ^ (1 / 2 : ℝ)
          * (∑ k, ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2
            ∂ν ∂volume ∂P) ^ (1 / 2 : ℝ)) := by gcongr
      _ = _ := by simp only [hSdef]; ring
  · have hfin : ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        ^ (1 / 2 : ℝ) ∂P < ⊤ := by
      refine hroot.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hYS.ne))
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_))
      exact (ENNReal.sum_lt_top.2 fun k _ => hUq k T hT).ne
    exact hM.integral_sub_eq_zero N ℱ hℱ hT hφm hfin ht

end CompensatedWeight

end Dissertation.WellPosedness.Martingale
