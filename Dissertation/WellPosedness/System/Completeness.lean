/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.PaperWeakSolution
import Dissertation.WellPosedness.System.ChannelCoords
import Dissertation.WellPosedness.BrownianPoisson.MeasurableDrift
import Dissertation.WellPosedness.Stability.SupUpgrade
import LevyStochCalc.Brownian.PredictableIntegrand
import LevyStochCalc.Probability.MarkedPredictableModification

/-!
# Completeness of the solution space `𝕊`

The solution space of the well-posedness paper is `𝕊 = S²(ℝⁿ) × S²(ℝᵐ) × H²_W × H²_N` with
`‖Θ‖²_𝕊 = 𝔼 sup_{t ≤ T} |X_t|² + 𝔼 sup_{t ≤ T} |Y_t|² + 𝔼 ∫_0^T (|Z_t|² + ‖U_t‖²_{L²(ν)}) dt`
(`supSize`). Over a filtration whose time-`0` field contains the null sets, every sequence of
tuples of `ℍ²` of finite norm that is Cauchy for `‖·‖_𝕊` has a limit in `ℍ²`, of finite
norm, whose forward and backward components have càdlàg paths.

For the `S²` components, a subsequence with `𝔼 sup |x_{n_{l+1}} − x_{n_l}|² < 2^{-3l}` has, by
the Markov inequality and the Borel–Cantelli lemma, `sup |x_{n_{l+1}} − x_{n_l}| < 2^{-l}`
eventually, almost surely; off a null set of the time-`0` field it converges uniformly on
`[0, T]`, and the limit is set to `0` on that null set. Uniform limits keep right-continuity and
left limits, and Fatou's lemma gives the convergence of the whole sequence. For the integrands,
the energy is the square of an `L²`-norm on the product space, and the pointwise upper limit of
an almost everywhere convergent subsequence is a predictable representative of the `L²`-limit.

## Main statements

* `measurable_biSup_esq_of_Ico` — the running supremum of `|x_t|²` over `[0, T]` is measurable
  for paths right-continuous on `[0, T)`.
* `exists_tendsto_of_tendstoUniformlyOn` — a uniform limit of functions with limits along a
  filter has a limit along it.
* `exists_lintegral_biSup_esq_limit` — completeness of the càdlàg adapted processes of finite
  `S²`-norm.
* `exists_predictable_energy_limit`, `exists_markedPredictable_energy_limit` — completeness of
  the predictable integrands of finite energy.
* `PaperWeakTuple.exists_supSize_limit` — completeness of `(𝕊, ‖·‖_𝕊)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.Stability LevyStochCalc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} [Fintype ι]
  {E : Type*} [MeasurableSpace E] {ν : Measure E}

/-! ### Squared Euclidean norms -/

/-- The squared Euclidean norm `x ↦ ∑ᵢ xᵢ²`, in `ℝ≥0∞`, is continuous. -/
theorem continuous_esq : Continuous (esq : (ι → ℝ) → ℝ≥0∞) := by
  unfold esq
  exact continuous_finsetSum _ fun i _ => (ENNReal.continuous_pow 2).comp
    (ENNReal.continuous_coe.comp (continuous_nnnorm.comp (continuous_apply i)))

/-- The squared triangle inequality `|x − y|² ≤ 2 |x|² + 2 |y|²`. -/
theorem esq_sub_le (x y : ι → ℝ) :
    esq (fun i => x i - y i) ≤ 2 * esq x + 2 * esq y := by
  simp only [esq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  calc (‖x i - y i‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖x i‖₊ : ℝ≥0∞) ^ 2 + (‖-y i‖₊ : ℝ≥0∞) ^ 2) := by
        rw [sub_eq_add_neg]
        exact Brownian.Ito.sq_nnnorm_add_le_two_mul _ _
    _ = 2 * (‖x i‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖y i‖₊ : ℝ≥0∞) ^ 2 := by
        rw [nnnorm_neg, mul_add]

/-- A squared coordinate is at most the squared Euclidean norm. -/
theorem sq_nnnorm_le_esq (x : ι → ℝ) (i : ι) : (‖x i‖₊ : ℝ≥0∞) ^ 2 ≤ esq x :=
  Finset.single_le_sum (f := fun i => (‖x i‖₊ : ℝ≥0∞) ^ 2) (fun _ _ => zero_le)
    (Finset.mem_univ i)

/-- The running supremum over `[0, T]` of `|x_t|²`, for a process with measurable slices on
`[0, T]` and paths right-continuous on `[0, T)`, is measurable. -/
theorem measurable_biSup_esq_of_Ico {x : ι → ℝ → Ω → ℝ} {T : ℝ}
    (hm : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (x i t))
    (hrc : ∀ i ω, ∀ t ∈ Set.Ico (0 : ℝ) T,
      Tendsto (fun s => x i s ω) (𝓝[>] t) (𝓝 (x i t ω))) :
    Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω) := by
  rcases lt_or_ge T 0 with hT | hT
  · have he : Set.Icc (0 : ℝ) T = ∅ := Set.Icc_eq_empty (not_le.mpr hT)
    simp only [he, Set.mem_empty_iff_false, iSup_false, ciSup_const]
    exact measurable_const
  have h := BrownianPoisson.measurable_biSup_sq_of_Ico hT
    (Y := fun t ω => ‖(WithLp.toLp 2 fun i => x i t ω : EuclideanSpace ℝ ι)‖)
    (fun t ht => (measurable_toLp_of_forall fun i => hm i t ht).norm)
    (fun ω t ht => ((PiLp.continuous_toLp 2 _).tendsto _).norm.comp
      (tendsto_pi_nhds.mpr fun i => hrc i ω t ht))
  have heq : (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω))
      = fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T,
          (‖‖(WithLp.toLp 2 fun i => x i t ω : EuclideanSpace ℝ ι)‖‖₊ : ℝ≥0∞) ^ 2 := by
    funext ω
    refine iSup_congr fun t => iSup_congr fun _ => ?_
    rw [esq_eq_enorm_sq, nnnorm_norm]
    rfl
  rw [heq]
  exact h

/-! ### Uniform limits and geometric sequences -/

/-- A function that is a uniform limit on `S` of functions with limits along a filter `l`, with
`S ∈ l`, has a limit along `l`. -/
theorem exists_tendsto_of_tendstoUniformlyOn {α : Type*} {F : ℕ → α → ℝ} {f : α → ℝ}
    {S : Set α} {l : Filter α} (hu : TendstoUniformlyOn F f atTop S) (hS : S ∈ l)
    (hF : ∀ n, ∃ L, Tendsto (F n) l (𝓝 L)) : ∃ L, Tendsto f l (𝓝 L) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact ⟨0, tendsto_bot⟩
  rw [← cauchy_map_iff_exists_tendsto, cauchy_map_iff',
    Metric.uniformity_basis_dist.tendsto_right_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hu (ε / 3) (by positivity)).exists
  obtain ⟨L, hL⟩ := hF n
  have h2 := Metric.uniformity_basis_dist.tendsto_right_iff.mp
    (cauchy_map_iff'.mp hL.cauchy_map) (ε / 3) (by positivity)
  filter_upwards [h2, prod_mem_prod hS hS] with p hp hpS
  have h1 := hn p.1 hpS.1
  have h3 := hn p.2 hpS.2
  calc dist (f p.1) (f p.2)
      ≤ dist (f p.1) (F n p.1) + dist (F n p.1) (F n p.2) + dist (F n p.2) (f p.2) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [dist_comm (F n p.2)]
        gcongr
    _ = ε := by ring

/-- A real sequence with `|a_{l+1} − a_l| < 2^{-l}` for `l ≥ l₀` converges, to a limit `α` with
`|a_l − α| ≤ 2 · 2^{-l}` for `l ≥ l₀`. -/
theorem exists_tendsto_of_abs_sub_lt_half_pow {a : ℕ → ℝ} {l₀ : ℕ}
    (h : ∀ l ≥ l₀, |a (l + 1) - a l| < (1 / 2) ^ l) :
    ∃ α, Tendsto a atTop (𝓝 α) ∧ ∀ l ≥ l₀, |a l - α| ≤ 2 * (1 / 2) ^ l := by
  have hb : ∀ k, dist (a (k + l₀)) (a (k + 1 + l₀)) ≤ (1 / 2) ^ l₀ * (1 / 2) ^ k := by
    intro k
    have := h (k + l₀) (Nat.le_add_left _ _)
    rw [Real.dist_eq, abs_sub_comm, show k + 1 + l₀ = k + l₀ + 1 by omega]
    rw [pow_add] at this
    linarith
  obtain ⟨α, hα⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1 / 2) ((1 / 2) ^ l₀) (by norm_num) hb)
  refine ⟨α, (tendsto_add_atTop_iff_nat l₀).mp hα, fun l hl => ?_⟩
  have hd := dist_le_of_le_geometric_of_tendsto (1 / 2) ((1 / 2) ^ l₀) (by norm_num) hb hα
    (l - l₀)
  rw [Real.dist_eq, Nat.sub_add_cancel hl] at hd
  have e : (1 / 2 : ℝ) ^ l₀ * (1 / 2) ^ (l - l₀) = (1 / 2) ^ l := by
    rw [← pow_add, Nat.add_sub_cancel' hl]
  rw [e] at hd
  have e2 : (1 / 2 : ℝ) ^ l / (1 - 1 / 2) = 2 * (1 / 2) ^ l := by ring
  linarith

/-! ### The `S²` components -/

/-- **Completeness of the càdlàg adapted processes of finite `S²`-norm.** Over a filtration whose
time-`0` field contains the null sets, let `x_j` be processes adapted on `[0, T]`, with paths
right-continuous on `[0, T)` and almost surely with left limits on `(0, T]`, with
`𝔼 sup_{t ≤ T} |x_{j,t}|² < ∞`, and Cauchy for `𝔼 sup_{t ≤ T} |x_{j,t} − x_{k,t}|²`. Then there is
a process `y` adapted on `[0, T]`, every path of which is right-continuous on `[0, T)` and has
left limits on `(0, T]`, with `𝔼 sup_{t ≤ T} |y_t|² < ∞` and
`𝔼 sup_{t ≤ T} |x_{j,t} − y_t|² → 0`. -/
theorem exists_lintegral_biSup_esq_limit (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ}
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {x : ℕ → ι → ℝ → Ω → ℝ}
    (hm : ∀ j i, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (x j i t))
    (hrc : ∀ j i ω, ∀ t ∈ Set.Ico (0 : ℝ) T,
      Tendsto (fun s => x j i s ω) (𝓝[>] t) (𝓝 (x j i t ω)))
    (hll : ∀ j i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioc (0 : ℝ) T,
      ∃ L : ℝ, Tendsto (fun s => x j i s ω) (𝓝[<] t) (𝓝 L))
    (hfin : ∀ j, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x j i t ω)) ∂P ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x j i t ω - x k i t ω)) ∂P < ε) :
    ∃ y : ι → ℝ → Ω → ℝ,
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable[ℱ t] (y i t))
      ∧ (∀ i ω, ∀ t ∈ Set.Ico (0 : ℝ) T,
          Tendsto (fun s => y i s ω) (𝓝[>] t) (𝓝 (y i t ω)))
      ∧ (∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T,
          ∃ L : ℝ, Tendsto (fun s => y i s ω) (𝓝[<] t) (𝓝 L))
      ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => y i t ω)) ∂P ≠ ⊤
      ∧ Tendsto (fun j => ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
          esq (fun i => x j i t ω - y i t ω)) ∂P) atTop (𝓝 0) := by
  classical
  -- the running suprema of the differences
  set Dm : ℕ → ℕ → Ω → ℝ≥0∞ := fun j k ω =>
    ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x j i t ω - x k i t ω) with hDm
  have hDmeas : ∀ j k, Measurable (Dm j k) := fun j k =>
    measurable_biSup_esq_of_Ico (x := fun i t ω => x j i t ω - x k i t ω)
      (fun i t ht => ((hm j i t ht).mono (ℱ.le t) le_rfl).sub
        ((hm k i t ht).mono (ℱ.le t) le_rfl))
      (fun i ω t ht => (hrc j i ω t ht).sub (hrc k i ω t ht))
  -- a fast subsequence
  have hr0 : ∀ l : ℕ, (0 : ℝ) < (1 / 2) ^ l := fun l => by positivity
  have hc0 : ∀ l : ℕ, ENNReal.ofReal (((1 / 2 : ℝ) ^ l) ^ 2) ≠ 0 := fun l =>
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hε : ∀ l : ℕ,
      0 < ENNReal.ofReal (((1 / 2 : ℝ) ^ l) ^ 2) * ENNReal.ofReal ((1 / 2 : ℝ) ^ l) := fun l =>
    ENNReal.mul_pos (hc0 l) (ENNReal.ofReal_pos.mpr (hr0 l)).ne'
  choose N hN using fun l => hcau _ (hε l)
  set ns : ℕ → ℕ := fun l => l + ∑ i ∈ Finset.range (l + 1), N i with hns
  have hns_ge : ∀ l, N l ≤ ns l := fun l => by
    have := Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _)
      (Finset.self_mem_range_succ l)
    simp only [hns]
    omega
  have hns_mono : ∀ l, ns l ≤ ns (l + 1) := fun l => by
    simp only [hns, Finset.sum_range_succ _ (l + 1)]
    omega
  have hns_le : ∀ l, l ≤ ns l := fun l => Nat.le_add_right _ _
  -- the Markov inequality and the Borel–Cantelli lemma
  set A : ℕ → Set Ω := fun l =>
    {ω | ENNReal.ofReal (((1 / 2 : ℝ) ^ l) ^ 2) ≤ Dm (ns (l + 1)) (ns l) ω} with hAdef
  have hA : ∀ l, P (A l) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ l) := by
    intro l
    have h1 := mul_meas_ge_le_lintegral₀ (μ := P) (hDmeas (ns (l + 1)) (ns l)).aemeasurable
      (ENNReal.ofReal (((1 / 2 : ℝ) ^ l) ^ 2))
    have h2 := hN l (ns (l + 1)) ((hns_ge l).trans (hns_mono l)) (ns l) (hns_ge l)
    exact ((ENNReal.mul_lt_mul_iff_right (hc0 l) ENNReal.ofReal_ne_top).mp
      (h1.trans_lt h2)).le
  have hsum : ∑' l, P (A l) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hA)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun l => (hr0 l).le)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  -- the good sample points and a null set of the time-`0` field containing the others
  set G : Set Ω := {ω | (∀ᶠ l in atTop, ω ∉ A l) ∧ ∀ l i, ∀ t ∈ Set.Ioc (0 : ℝ) T,
      ∃ L : ℝ, Tendsto (fun s => x (ns l) i s ω) (𝓝[<] t) (𝓝 L)} with hGdef
  have hG : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [ae_eventually_notMem hsum,
      ae_all_iff.mpr fun l => ae_all_iff.mpr fun i => hll (ns l) i] with ω h1 h2
    exact ⟨h1, h2⟩
  set Nset := toMeasurable P Gᶜ with hNdef
  have hN0 : P Nset = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact mem_ae_iff.mp hG
  have hNsub : ∀ ω ∉ Nset, ω ∈ G := fun ω hω =>
    by_contra fun h => hω (subset_toMeasurable P _ h)
  have hNℱ : MeasurableSet[ℱ 0] Nset := hnull _ (measurableSet_toMeasurable P _) hN0
  -- the limit
  set y : ι → ℝ → Ω → ℝ := fun i t ω =>
    Nsetᶜ.indicator (fun ω => limsup (fun l => x (ns l) i t ω) atTop) ω with hydef
  have hy0 : ∀ ω ∈ Nset, ∀ i s, y i s ω = 0 := fun ω hω i s =>
    Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hω) _
  have key : ∀ ω ∉ Nset, ∃ l₀ : ℕ, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Tendsto (fun l => x (ns l) i t ω) atTop (𝓝 (y i t ω))
      ∧ ∀ l ≥ l₀, |x (ns l) i t ω - y i t ω| ≤ 2 * (1 / 2) ^ l := by
    intro ω hω
    obtain ⟨l₀, hl₀⟩ := eventually_atTop.mp (hNsub ω hω).1
    refine ⟨l₀, fun i t ht => ?_⟩
    have hinc : ∀ l ≥ l₀, |x (ns (l + 1)) i t ω - x (ns l) i t ω| < (1 / 2) ^ l := by
      intro l hl
      have h1 : Dm (ns (l + 1)) (ns l) ω < ENNReal.ofReal (((1 / 2 : ℝ) ^ l) ^ 2) :=
        not_le.mp (hl₀ l hl)
      have h2 : (‖x (ns (l + 1)) i t ω - x (ns l) i t ω‖₊ : ℝ≥0∞) ^ 2
          < ENNReal.ofReal (((1 / 2 : ℝ) ^ l) ^ 2) :=
        lt_of_le_of_lt ((sq_nnnorm_le_esq
          (fun i => x (ns (l + 1)) i t ω - x (ns l) i t ω) i).trans
          (le_iSup₂_of_le t ht le_rfl)) h1
      rw [Brownian.Ito.sq_nnnorm_eq_ofReal_sq] at h2
      exact abs_lt_of_sq_lt_sq ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp h2)
        (hr0 l).le
    obtain ⟨α, hα, hαb⟩ :=
      exists_tendsto_of_abs_sub_lt_half_pow (a := fun l => x (ns l) i t ω) hinc
    have hy : y i t ω = α := by
      rw [hydef]
      simp only [Set.indicator_of_mem (Set.mem_compl hω)]
      exact hα.limsup_eq
    rw [hy]
    exact ⟨hα, hαb⟩
  have hunif : ∀ ω ∉ Nset, ∀ i, TendstoUniformlyOn (fun l s => x (ns l) i s ω)
      (fun s => y i s ω) atTop (Set.Icc (0 : ℝ) T) := by
    intro ω hω i
    obtain ⟨l₀, hl₀⟩ := key ω hω
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h2 : Tendsto (fun l : ℕ => 2 * (1 / 2 : ℝ) ^ l) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 2
    filter_upwards [eventually_ge_atTop l₀, h2.eventually (gt_mem_nhds hε)] with l hl hlε s hs
    rw [Real.dist_eq, abs_sub_comm]
    exact ((hl₀ i s hs).2 l hl).trans_lt hlε
  -- convergence of the whole sequence, by Fatou's lemma
  have hconv : ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℕ, ∀ j ≥ M, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
      esq (fun i => x j i t ω - y i t ω)) ∂P ≤ ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := hcau ε hε
    refine ⟨M, fun j hj => ?_⟩
    have hpt : ∀ᵐ ω ∂P, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x j i t ω - y i t ω))
        ≤ liminf (fun l => Dm j (ns l) ω) atTop := by
      filter_upwards [compl_mem_ae_iff.mpr hN0] with ω hω
      obtain ⟨l₀, hl₀⟩ := key ω hω
      refine iSup₂_le fun t ht => ?_
      have hlim : Tendsto (fun l => esq (fun i => x j i t ω - x (ns l) i t ω)) atTop
          (𝓝 (esq (fun i => x j i t ω - y i t ω))) :=
        (continuous_esq.tendsto _).comp
          (tendsto_pi_nhds.mpr fun i => tendsto_const_nhds.sub (hl₀ i t ht).1)
      rw [← hlim.liminf_eq]
      exact liminf_le_liminf (Eventually.of_forall fun l => le_iSup₂_of_le t ht le_rfl)
    calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x j i t ω - y i t ω)) ∂P
        ≤ ∫⁻ ω, liminf (fun l => Dm j (ns l) ω) atTop ∂P := lintegral_mono_ae hpt
      _ ≤ liminf (fun l => ∫⁻ ω, Dm j (ns l) ω ∂P) atTop :=
          lintegral_liminf_le fun l => hDmeas j (ns l)
      _ ≤ ε := liminf_le_of_frequently_le' (Eventually.frequently (eventually_atTop.mpr
          ⟨M, fun l hl => (hM j hj (ns l) (hl.trans (hns_le l))).le⟩))
  refine ⟨y, ?_, ?_, ?_, ?_, ?_⟩
  · intro i t ht
    exact (Measurable.limsup fun l => hm (ns l) i t ht).indicator (ℱ.mono ht.1 _ hNℱ).compl
  · intro i ω t ht
    by_cases hω : ω ∈ Nset
    · simp only [hy0 ω hω]
      exact tendsto_const_nhds
    · obtain ⟨l₀, hl₀⟩ := key ω hω
      have hS : Set.Icc (0 : ℝ) T ∈ 𝓝[>] t := mem_of_superset (Ioo_mem_nhdsGT ht.2)
        fun s hs => ⟨ht.1.trans hs.1.le, hs.2.le⟩
      exact ((hunif ω hω i).tendstoUniformlyOnFilter.mono_right
        (le_principal_iff.mpr hS)).tendsto_of_eventually_tendsto
        (Eventually.of_forall fun l => hrc (ns l) i ω t ht) (hl₀ i t ⟨ht.1, ht.2.le⟩).1
  · intro i ω t ht
    by_cases hω : ω ∈ Nset
    · exact ⟨0, by simp only [hy0 ω hω]; exact tendsto_const_nhds⟩
    · exact exists_tendsto_of_tendstoUniformlyOn (hunif ω hω i)
        (mem_of_superset (Ioo_mem_nhdsLT ht.1) fun s hs => ⟨hs.1.le, hs.2.le.trans ht.2⟩)
        fun l => (hNsub ω hω).2 l i t ht
  · obtain ⟨M, hM⟩ := hconv 1 one_pos
    have hle : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => y i t ω))
        ≤ 2 * (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x M i t ω))
          + 2 * (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x M i t ω - y i t ω)) := by
      intro ω
      refine iSup₂_le fun t ht => ?_
      calc esq (fun i => y i t ω)
          = esq (fun i => x M i t ω - (x M i t ω - y i t ω)) := by simp only [sub_sub_cancel]
        _ ≤ 2 * esq (fun i => x M i t ω) + 2 * esq (fun i => x M i t ω - y i t ω) :=
            esq_sub_le _ _
        _ ≤ _ := by
            gcongr
            · exact le_iSup₂_of_le (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) =>
                esq (fun i => x M i t ω)) t ht le_rfl
            · exact le_iSup₂_of_le (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) =>
                esq (fun i => x M i t ω - y i t ω)) t ht le_rfl
    have hmeasM := measurable_biSup_esq_of_Ico (x := x M)
      (fun i t ht => (hm M i t ht).mono (ℱ.le t) le_rfl) (hrc M)
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    rw [lintegral_add_left (hmeasM.const_mul 2), lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top (hfin M),
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top
        (hM M le_rfl))⟩
  · exact ENNReal.tendsto_nhds_zero.mpr fun ε hε => eventually_atTop.mpr (hconv ε hε)

/-! ### The integrands -/

/-- **Completeness of the predictable integrands.** A sequence of predictable integrands
vanishing off `[0, T]`, of finite energy on `[0, T]` and Cauchy for that energy has a predictable
limit vanishing off `[0, T]`, of finite energy, with `energy(H_n − K) → 0`. -/
theorem exists_predictable_energy_limit (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ}
    {H : ℕ → Ω → ℝ → ℝ} (hp : ∀ n, Probability.Predictable ℱ (H n))
    (hz : ∀ n ω s, s ∉ Set.Icc (0 : ℝ) T → H n ω s = 0)
    (hfin : ∀ n, Brownian.Ito.energy P T (H n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Brownian.Ito.energy P T (fun ω s => H m ω s - H n ω s) < ε) :
    ∃ K : Ω → ℝ → ℝ, Probability.Predictable ℱ K
      ∧ (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → K ω s = 0)
      ∧ Brownian.Ito.energy P T K ≠ ⊤
      ∧ Tendsto (fun n => Brownian.Ito.energy P T (fun ω s => H n ω s - K ω s)) atTop
          (𝓝 0) := by
  have hm : ∀ n, Measurable (Function.uncurry (H n)) := fun n =>
    Brownian.Ito.measurable_uncurry_of_predictable (hp n)
  obtain ⟨g, hgMem, hgt⟩ := Brownian.Ito.exists_energy_limit hm hfin hcau
  have hMem : ∀ n, MemLp (fun p : Ω × ℝ => H n p.1 p.2) 2 (Brownian.Ito.energyMeasure P T) :=
    fun n => Brownian.Ito.memLp_of_energy_ne_top (hm n) (hfin n)
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (μ := Brownian.Ito.energyMeasure P T) (p := 2) (by norm_num)
    (fun n => (hMem n).aestronglyMeasurable) hgMem.aestronglyMeasurable
    hgt).exists_seq_tendsto_ae
  set K : Ω → ℝ → ℝ := fun ω s => limsup (fun i => H (ns i) ω s) atTop with hKdef
  have hKp : Probability.Predictable ℱ K := Probability.Predictable.limsup fun i => hp (ns i)
  have hKm : Measurable (Function.uncurry K) :=
    Brownian.Ito.measurable_uncurry_of_predictable hKp
  have hKz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → K ω s = 0 := by
    intro ω s hs
    have h0 : (fun i => H (ns i) ω s) = fun _ => (0 : ℝ) := funext fun i => hz (ns i) ω s hs
    rw [hKdef]
    simp only [h0, limsup_const]
  have hKg : (fun p : Ω × ℝ => K p.1 p.2) =ᵐ[Brownian.Ito.energyMeasure P T] g := by
    filter_upwards [hae] with p hp'
    exact hp'.limsup_eq
  have hKfin : Brownian.Ito.energy P T K ≠ ⊤ := by
    rw [Brownian.Ito.energy_eq_eLpNorm_sq hKm T, eLpNorm_congr_ae hKg]
    exact ENNReal.pow_ne_top hgMem.eLpNorm_lt_top.ne
  have hEq : ∀ n, Brownian.Ito.energy P T (fun ω s => H n ω s - K ω s)
      = eLpNorm ((fun p : Ω × ℝ => H n p.1 p.2) - g) 2 (Brownian.Ito.energyMeasure P T) ^ 2 := by
    intro n
    rw [Brownian.Ito.energy_eq_eLpNorm_sq ((hm n).sub hKm) T]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [hKg] with p h1
    simp only [Pi.sub_apply]
    rw [h1]
  refine ⟨K, hKp, hKz, hKfin, ?_⟩
  simp only [hEq]
  simpa [Function.comp_def] using ((ENNReal.continuous_pow 2).tendsto 0).comp hgt

/-- **Completeness of the marked predictable integrands.** A sequence of marked predictable
integrands vanishing off `[0, T]`, of finite marked energy on `[0, T]` and Cauchy for that
energy has a marked predictable limit vanishing off `[0, T]`, of finite marked energy, with
`markedEnergy(φ_n − ψ) → 0`. -/
theorem exists_markedPredictable_energy_limit [SigmaFinite ν]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ}
    {φ : ℕ → Ω → ℝ → E → ℝ} (hp : ∀ n, Probability.MarkedPredictable ℱ ν (φ n))
    (hz : ∀ n ω s e, s ∉ Set.Icc (0 : ℝ) T → φ n ω s e = 0)
    (hfin : ∀ n, Poisson.Compensated.markedEnergy P ν T (φ n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Poisson.Compensated.markedEnergy P ν T (fun ω s e => φ m ω s e - φ n ω s e) < ε) :
    ∃ ψ : Ω → ℝ → E → ℝ, Probability.MarkedPredictable ℱ ν ψ
      ∧ (∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → ψ ω s e = 0)
      ∧ Poisson.Compensated.markedEnergy P ν T ψ ≠ ⊤
      ∧ Tendsto (fun n => Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => φ n ω s e - ψ ω s e)) atTop (𝓝 0) := by
  have hm : ∀ n, Measurable fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2 := fun n =>
    (hp n).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  obtain ⟨g, hgMem, hgt⟩ := Poisson.Compensated.exists_markedEnergy_limit hm hfin hcau
  have hMem : ∀ n, MemLp (fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2) 2
      (Poisson.Compensated.markedEnergyMeasure P ν T) := fun n =>
    Poisson.Compensated.memLp_of_markedEnergy_ne_top (hm n) (hfin n)
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (μ := Poisson.Compensated.markedEnergyMeasure P ν T) (p := 2) (by norm_num)
    (fun n => (hMem n).aestronglyMeasurable) hgMem.aestronglyMeasurable
    hgt).exists_seq_tendsto_ae
  set ψ : Ω → ℝ → E → ℝ := fun ω s e => limsup (fun i => φ (ns i) ω s e) atTop with hψdef
  have hψp : Probability.MarkedPredictable ℱ ν ψ :=
    Probability.MarkedPredictable.limsup fun i => hp (ns i)
  have hψm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2 :=
    hψp.mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hψz : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → ψ ω s e = 0 := by
    intro ω s e hs
    have h0 : (fun i => φ (ns i) ω s e) = fun _ => (0 : ℝ) :=
      funext fun i => hz (ns i) ω s e hs
    rw [hψdef]
    simp only [h0, limsup_const]
  have hψg : (fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
      =ᵐ[Poisson.Compensated.markedEnergyMeasure P ν T] g := by
    filter_upwards [hae] with p hp'
    exact hp'.limsup_eq
  have hψfin : Poisson.Compensated.markedEnergy P ν T ψ ≠ ⊤ := by
    rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq hψm T, eLpNorm_congr_ae hψg]
    exact ENNReal.pow_ne_top hgMem.eLpNorm_lt_top.ne
  have hEq : ∀ n, Poisson.Compensated.markedEnergy P ν T (fun ω s e => φ n ω s e - ψ ω s e)
      = eLpNorm ((fun p : Ω × ℝ × E => φ n p.1 p.2.1 p.2.2) - g) 2
        (Poisson.Compensated.markedEnergyMeasure P ν T) ^ 2 := by
    intro n
    rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq ((hm n).sub hψm) T]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [hψg] with p h1
    simp only [Pi.sub_apply]
    rw [h1]
  refine ⟨ψ, hψp, hψz, hψfin, ?_⟩
  simp only [hEq]
  simpa [Function.comp_def] using ((ENNReal.continuous_pow 2).tendsto 0).comp hgt

/-! ### The solution space -/

section Tuple

variable [SigmaFinite ν] {n m d : ℕ}

/-- **Completeness of `(𝕊, ‖·‖_𝕊)`.** Over a filtration whose time-`0` field contains the null
sets, let `Θ_j = (X_j, Y_j, Z_j, U_j)` be tuples of `ℍ²` with `‖Θ_j‖²_𝕊 = supSize < ∞`, Cauchy
for `‖·‖_𝕊`. Then there is a tuple `Θ = (X, Y, Z, U)` of `ℍ²`, every path of `X` and of `Y`
having left limits on `(0, T]`, with `‖Θ‖_𝕊 < ∞` and `‖Θ_j − Θ‖_𝕊 → 0`. -/
theorem PaperWeakTuple.exists_supSize_limit (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) {T : ℝ}
    {X : ℕ → Fin n → ℝ → Ω → ℝ} {Y : ℕ → Fin m → ℝ → Ω → ℝ}
    {Z : ℕ → Fin m → ℝ → Ω → Fin d → ℝ} {U : ℕ → Fin m → ℝ → Ω → E → ℝ}
    (hΘ : ∀ j, PaperWeakTuple ℱ P ν T (X j) (Y j) (Z j) (U j))
    (hfin : ∀ j, supSize P ν T (X j) (Y j) (Z j) (U j) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
      supSize P ν T (fun i t ω => X j i t ω - X k i t ω) (fun l t ω => Y j l t ω - Y k l t ω)
        (fun l t ω a => Z j l t ω a - Z k l t ω a) (fun l t ω e => U j l t ω e - U k l t ω e)
        < ε) :
    ∃ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ) (Z' : Fin m → ℝ → Ω → Fin d → ℝ)
      (U' : Fin m → ℝ → Ω → E → ℝ),
      PaperWeakTuple ℱ P ν T X' Y' Z' U'
      ∧ (∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X' i s ω) (𝓝[<] t) (𝓝 l))
      ∧ (∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y' k s ω) (𝓝[<] t) (𝓝 l))
      ∧ supSize P ν T X' Y' Z' U' ≠ ⊤
      ∧ Tendsto (fun j => supSize P ν T (fun i t ω => X j i t ω - X' i t ω)
          (fun l t ω => Y j l t ω - Y' l t ω) (fun l t ω a => Z j l t ω a - Z' l t ω a)
          (fun l t ω e => U j l t ω e - U' l t ω e)) atTop (𝓝 0) := by
  -- the four parts of `supSize` are bounded by it
  have hXle : ∀ {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
      {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ},
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P ≤ supSize P ν T X Y Z U :=
    fun {_ _ _ _} => (le_self_add.trans le_self_add).trans le_self_add
  have hYle : ∀ {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
      {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ},
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y k t ω)) ∂P ≤ supSize P ν T X Y Z U :=
    fun {_ _ _ _} => (le_add_self.trans le_self_add).trans le_self_add
  have hZle : ∀ {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
      {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} (k : Fin m) (a : Fin d),
      Brownian.Ito.energy P T (fun ω s => Z k s ω a) ≤ supSize P ν T X Y Z U := by
    intro X Y Z U k a
    refine le_trans ?_ (le_add_self.trans le_self_add)
    exact (Finset.single_le_sum (f := fun a => Brownian.Ito.energy P T (fun ω s => Z k s ω a))
      (fun _ _ => zero_le) (Finset.mem_univ a)).trans
      (Finset.single_le_sum (f := fun k => ∑ a, Brownian.Ito.energy P T (fun ω s => Z k s ω a))
        (fun _ _ => zero_le) (Finset.mem_univ k))
  have hUle : ∀ {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
      {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} (k : Fin m),
      Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)
        ≤ supSize P ν T X Y Z U := by
    intro X Y Z U k
    refine le_trans ?_ le_add_self
    exact Finset.single_le_sum
      (f := fun k => Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e))
      (fun _ _ => zero_le) (Finset.mem_univ k)
  -- the forward and backward components
  obtain ⟨X', hXa, hXr, hXl, hXf, hXt⟩ := exists_lintegral_biSup_esq_limit (P := P) ℱ hnull
    (x := X) (fun j => (hΘ j).X_adapted) (fun j => (hΘ j).X_rightCont)
    (fun j => (hΘ j).X_leftLim) (fun j => ne_top_of_le_ne_top (hfin j) hXle)
    fun ε hε => (hcau ε hε).imp fun N hN j hj k hk => hXle.trans_lt (hN j hj k hk)
  obtain ⟨Y', hYa, hYr, hYl, hYf, hYt⟩ := exists_lintegral_biSup_esq_limit (P := P) ℱ hnull
    (x := Y) (fun j => (hΘ j).Y_adapted) (fun j => (hΘ j).Y_rightCont)
    (fun j => (hΘ j).Y_leftLim) (fun j => ne_top_of_le_ne_top (hfin j) hYle)
    fun ε hε => (hcau ε hε).imp fun N hN j hj k hk => hYle.trans_lt (hN j hj k hk)
  -- the Brownian integrands
  have hZex : ∀ k a, ∃ K : Ω → ℝ → ℝ, Probability.Predictable ℱ K
      ∧ (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → K ω s = 0)
      ∧ Brownian.Ito.energy P T K ≠ ⊤
      ∧ Tendsto (fun j => Brownian.Ito.energy P T (fun ω s => Z j k s ω a - K ω s)) atTop
          (𝓝 0) := fun k a =>
    exists_predictable_energy_limit (P := P) ℱ (H := fun j ω s => Z j k s ω a)
      (fun j => (hΘ j).Z_pred k a)
      (fun j ω s hs => by simp only [(hΘ j).Z_vanish k ω s hs, Pi.zero_apply])
      (fun j => (hΘ j).Z_sq k a)
      fun ε hε => (hcau ε hε).imp fun N hN j hj l hl => (hZle k a).trans_lt (hN j hj l hl)
  choose K hKp hKz hKf hKt using hZex
  -- the Poisson integrands
  have hUex : ∀ k, ∃ ψ : Ω → ℝ → E → ℝ, Probability.MarkedPredictable ℱ ν ψ
      ∧ (∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → ψ ω s e = 0)
      ∧ Poisson.Compensated.markedEnergy P ν T ψ ≠ ⊤
      ∧ Tendsto (fun j => Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => U j k s ω e - ψ ω s e)) atTop (𝓝 0) := fun k =>
    exists_markedPredictable_energy_limit (P := P) ℱ (φ := fun j ω s e => U j k s ω e)
      (fun j => (hΘ j).U_pred k) (fun j ω s e hs => (hΘ j).U_vanish k ω s e hs)
      (fun j => (hΘ j).U_sq k)
      fun ε hε => (hcau ε hε).imp fun N hN j hj l hl => (hUle k).trans_lt (hN j hj l hl)
  choose ψ hψp hψz hψf hψt using hUex
  refine ⟨X', Y', fun k s ω a => K k a ω s, fun k s ω e => ψ k ω s e, ?_, hXl, hYl, ?_, ?_⟩
  · exact
    { X_adapted := hXa
      X_rightCont := hXr
      X_leftLim := fun i => Eventually.of_forall fun ω t ht => hXl i ω t ht
      X_sq := energy_ne_top_of_lintegral_biSup_esq_lt_top (lt_top_iff_ne_top.mpr hXf)
      Y_adapted := hYa
      Y_rightCont := hYr
      Y_leftLim := fun k => Eventually.of_forall fun ω t ht => hYl k ω t ht
      Y_sq := energy_ne_top_of_lintegral_biSup_esq_lt_top (lt_top_iff_ne_top.mpr hYf)
      Z_pred := fun k a => hKp k a
      Z_vanish := fun k ω s hs => funext fun a => hKz k a ω s hs
      Z_sq := fun k a => hKf k a
      U_pred := fun k => hψp k
      U_vanish := fun k ω s e hs => hψz k ω s e hs
      U_sq := fun k => hψf k }
  · refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hXf, hYf⟩,
      ENNReal.sum_ne_top.mpr fun k _ => ENNReal.sum_ne_top.mpr fun a _ => hKf k a⟩,
      ENNReal.sum_ne_top.mpr fun k _ => hψf k⟩
  · have hZs : Tendsto (fun j => ∑ k, ∑ a,
        Brownian.Ito.energy P T (fun ω s => Z j k s ω a - K k a ω s)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun k _ =>
        tendsto_finsetSum Finset.univ fun a _ => hKt k a
    have hUs : Tendsto (fun j => ∑ k, Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => U j k s ω e - ψ k ω s e)) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ fun k _ => hψt k
    have h := ((hXt.add hYt).add hZs).add hUs
    rw [add_zero, add_zero, add_zero] at h
    exact h

end Tuple

end Dissertation.WellPosedness.System
