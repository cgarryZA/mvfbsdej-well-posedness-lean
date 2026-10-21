/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Martingale.BDGOne

/-!
# Local stochastic integrals

An integrand `H` that is square integrable only locally — along stopping times `τ_k` increasing
to `T` whose cut-offs `H 1_{[0, τ_k]}` have finite energy — has a local stochastic integral: a
càdlàg adapted process `M` that agrees, up to each `τ_k`, with the `L²` integral of the cut-off
integrand. This is the integral of the paper's local martingales `∫ e^s ⟨δY_{s−}, δZ_s dW_s⟩`
and their analogues, whose integrands carry a factor `δY_{s−}` with no moment beyond the second.

For a local integral, the Burkholder–Davis–Gundy inequality at `p = 1` of the `L²` integrals
passes to the limit (monotone convergence), and the increments `M_T − M_t` have mean zero as soon
as `𝔼 (∫_0^T |H|²)^{1/2} < ∞`: the increments of the integrals of the cut-off integrands have mean
zero, converge almost surely to `M_T − M_t`, and form a Cauchy sequence in `L¹` by the same
inequality.

## Main definitions

* `Dissertation.WellPosedness.Martingale.IsLocalBrownianIntegral` — `M` is a local Itô integral
  of `H` against a multidimensional Brownian motion.
* `Dissertation.WellPosedness.Martingale.IsLocalCompensatedIntegral` — `M` is a local integral of
  `φ` against a compensated Poisson random measure.

## Main statements

* `exists_isLocalBrownianIntegral`, `exists_isLocalCompensatedIntegral` — existence along a
  localising sequence.
* `IsLocalBrownianIntegral.lintegral_biSup_le`, `IsLocalCompensatedIntegral.lintegral_biSup_le` —
  `𝔼 sup_{t ≤ T} |M_t| ≤ 9 𝔼 (∫_0^T |H|²)^{1/2}`.
* `IsLocalBrownianIntegral.integral_sub_eq_zero`,
  `IsLocalCompensatedIntegral.integral_sub_eq_zero` — `𝔼[M_T − M_t] = 0`.
-/

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace Dissertation.WellPosedness.Martingale

open LevyStochCalc LevyStochCalc.Brownian.Multidim

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The pairs `(ω, s)` with `τ(ω) < s` form a measurable set. -/
theorem measurableSet_lt_coe {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {τ : Ω → WithTop ℝ}
    (hτ : IsStoppingTime ℱ τ) :
    MeasurableSet {p : Ω × ℝ | τ p.1 < ((p.2 : ℝ) : WithTop ℝ)} := by
  have hset : {p : Ω × ℝ | τ p.1 < ((p.2 : ℝ) : WithTop ℝ)}
      = ⋃ q : ℚ, {ω | τ ω < (((q : ℝ) : ℝ) : WithTop ℝ)} ×ˢ Ioi (q : ℝ) := by
    ext ⟨ω, s⟩
    simp only [mem_setOf_eq, mem_iUnion, mem_prod, mem_Ioi]
    constructor
    · intro h
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt h)
      rw [← hr] at h
      obtain ⟨q, hrq, hqs⟩ := exists_rat_btwn (WithTop.coe_lt_coe.mp h)
      exact ⟨q, by rw [← hr]; exact WithTop.coe_lt_coe.mpr hrq, hqs⟩
    · rintro ⟨q, h1, h2⟩
      exact h1.trans (WithTop.coe_lt_coe.mpr h2)
  rw [hset]
  exact MeasurableSet.iUnion fun q =>
    (ℱ.le _ _ (hτ.measurableSet_lt (q : ℝ))).prod measurableSet_Ioi

section Brownian

variable (W : MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : ∀ i, Brownian.IsBrownianFiltration (W.W i) ℱ)

/-- **A local Itô integral.** `M` is a local Itô integral on `[0, T]` of the integrand
`H : ℝ → Ω → ℝ^d` against the multidimensional Brownian motion `W`: `M` is adapted on `[0, T]`
with càdlàg paths there (right-continuous on `[0, T)`, left limits on `(0, T]`), and there are
stopping times `τ_k`, nondecreasing in `k` and almost surely eventually at least `T`, such that
each cut-off integrand `H_s 1_{s ≤ τ_k}` meets the conditions of the Itô integral (jointly
measurable, progressively measurable, of finite energy on every horizon) and `M` agrees with its
integral up to `τ_k`: for every `t ∈ [0, T]`, almost surely on `{t ≤ τ_k}`,
`M_t = ∫_0^t H_s 1_{s ≤ τ_k} dW_s`. -/
def IsLocalBrownianIntegral (T : ℝ) (H : ℝ → Ω → Fin d → ℝ) (M : ℝ → Ω → ℝ) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) T, Measurable[ℱ t] (M t))
    ∧ (∀ ω, ∀ t ∈ Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)))
    ∧ (∀ ω, ∀ t ∈ Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 l))
    ∧ ∃ τ : ℕ → Ω → WithTop ℝ, (∀ k, IsStoppingTime ℱ (τ k))
      ∧ (∀ ω, Monotone fun k => τ k ω)
      ∧ (∀ᵐ ω ∂P, ∃ k, ((T : ℝ) : WithTop ℝ) ≤ τ k ω)
      ∧ ∀ k, ∃ (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s =>
            if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then H s ω j else 0))
          (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s =>
            if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then H s ω j else 0)
          (hq : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T',
            (‖if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then H s ω j else 0‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P < ⊤),
          ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ k ω →
            M t ω = MultidimBrownianMotion.stochasticIntegral W ℱ hℱ
              (fun s ω j => if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then H s ω j else 0) hm hp hq t ω

/-- **Existence of the local Itô integral.** Along stopping times `τ_k`, nondecreasing in `k` and
almost surely eventually at least `T`, whose cut-off integrands meet the conditions of the Itô
integral, the integrand `H` has a local Itô integral on `[0, T]`. -/
theorem exists_isLocalBrownianIntegral [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {T : ℝ} (hT : 0 < T) (H : ℝ → Ω → Fin d → ℝ) (τ : ℕ → Ω → WithTop ℝ)
    (hτ : ∀ k, IsStoppingTime ℱ (τ k)) (hmono : ∀ ω, Monotone fun k => τ k ω)
    (hex : ∀ᵐ ω ∂P, ∃ k, ((T : ℝ) : WithTop ℝ) ≤ τ k ω)
    (hm : ∀ k (j : Fin d), Measurable (Function.uncurry fun ω s =>
      if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then H s ω j else 0))
    (hp : ∀ k (j : Fin d), Probability.ProgressivelyMeasurable ℱ fun ω s =>
      if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then H s ω j else 0)
    (hq : ∀ k (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T',
      (‖if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then H s ω j else 0‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ M, IsLocalBrownianIntegral W ℱ hℱ T H M := by
  classical
  set cut : ℕ → ℝ → Ω → Fin d → ℝ :=
    fun k s ω j => if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then H s ω j else 0 with hcut
  have hrc : ℱ.rightCont = ℱ := Filtration.IsRightContinuous.eq
  have hv : ∀ k, ∃ N : ℝ → Ω → ℝ, (∀ t, Measurable[ℱ t] (N t))
      ∧ (∀ t, N t =ᵐ[P] MultidimBrownianMotion.stochasticIntegral W ℱ hℱ (cut k) (hm k) (hp k)
          (hq k) t)
      ∧ (∀ ω t, Tendsto (fun s => N s ω) (𝓝[>] t) (𝓝 (N t ω))
          ∧ ∃ L : ℝ, Tendsto (fun s => N s ω) (𝓝[<] t) (𝓝 L))
      ∧ (∀ t : ℝ, t ≤ 0 → N t =ᵐ[P] 0) := fun k => by
    obtain ⟨N, h1, -, h3, h4, -, h6, -⟩ := BSDEJ.Solves.exists_cadlag_vectorIntegral_supBound W ℱ
      hℱ (cut k) (hm k) (hp k) (hq k) hℱ0 hnull T hT.le
    refine ⟨N, fun t => ?_, h3, h4, h6⟩
    have h := h1 t
    rw [hrc] at h
    exact h
  choose N hNad hNae hNcad hNzero using hv
  -- agreement of the cut-off integrals at a fixed time
  have hcons : ∀ j k, j ≤ k → ∀ t ∈ Icc (0 : ℝ) T,
      ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ j ω → N j t ω = N k t ω := by
    intro j k hjk t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · subst h0
      filter_upwards [hNzero j 0 le_rfl, hNzero k 0 le_rfl] with ω h1 h2 _
      rw [h1, h2]
    · have hagree : ∀ ω s, 0 < s → ((s : ℝ) : WithTop ℝ) ≤ τ j ω → cut j s ω = cut k s ω := by
        intro ω s _ hle
        funext i
        simp only [hcut, if_pos hle, if_pos (hle.trans (hmono ω hjk))]
      filter_upwards [hNae j t, hNae k t, multidim_congr_of_le W ℱ hℱ (hτ j) (hm j) (hp j)
        (hq j) (hm k) (hp k) (hq k) hagree h0] with ω h1 h2 h3 hle
      rw [h1, h2, h3 hle]
  -- the event on which the cut-off integrals are consistent
  set G0 : Set Ω := {ω | (∃ k, ((T : ℝ) : WithTop ℝ) ≤ τ k ω)
      ∧ (∀ j k, j ≤ k → ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
          (((q : ℝ) : ℝ) : WithTop ℝ) ≤ τ j ω → N j q ω = N k q ω)
      ∧ (∀ j k, j ≤ k → ((T : ℝ) : WithTop ℝ) ≤ τ j ω → N j T ω = N k T ω)} with hG0def
  have hG0 : ∀ᵐ ω ∂P, ω ∈ G0 := by
    have h1 : ∀ᵐ ω ∂P, ∀ j k, j ≤ k → ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
        (((q : ℝ) : ℝ) : WithTop ℝ) ≤ τ j ω → N j q ω = N k q ω := by
      refine ae_all_iff.2 fun j => ae_all_iff.2 fun k => ?_
      by_cases hjk : j ≤ k
      · refine (ae_all_iff.2 fun q => ?_).mono fun ω hω _ => hω
        by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
        · filter_upwards [hcons j k hjk q hq] with ω hω _ hle
          exact hω hle
        · exact ae_of_all _ fun ω h => absurd h hq
      · exact ae_of_all _ fun ω h => absurd h hjk
    have h2 : ∀ᵐ ω ∂P, ∀ j k, j ≤ k → ((T : ℝ) : WithTop ℝ) ≤ τ j ω → N j T ω = N k T ω := by
      refine ae_all_iff.2 fun j => ae_all_iff.2 fun k => ?_
      by_cases hjk : j ≤ k
      · filter_upwards [hcons j k hjk T ⟨hT.le, le_rfl⟩] with ω hω _ hle
        exact hω hle
      · exact ae_of_all _ fun ω h => absurd h hjk
    filter_upwards [hex, h1, h2] with ω h0 h1 h2
    exact ⟨h0, h1, h2⟩
  set G : Set Ω := (toMeasurable P G0ᶜ)ᶜ with hGdef
  have hGsub : G ⊆ G0 := by
    intro ω hω
    by_contra hcon
    exact hω (subset_toMeasurable P G0ᶜ hcon)
  have hGnull : P Gᶜ = 0 := by
    rw [hGdef, compl_compl, measure_toMeasurable]
    exact ae_iff.mp hG0
  have hG0m : MeasurableSet[ℱ 0] G := by
    have := hnull Gᶜ (by rw [hGdef, compl_compl]; exact measurableSet_toMeasurable _ _) hGnull
    simpa using this.compl
  -- the index from which the cut-off integrals have stabilised
  set K : Ω → ℕ := fun ω =>
    if h : ∃ k, ((T : ℝ) : WithTop ℝ) ≤ τ k ω then Nat.find h else 0 with hKdef
  have hKspec : ∀ ω ∈ G, ((T : ℝ) : WithTop ℝ) ≤ τ (K ω) ω := by
    intro ω hω
    have h := (hGsub hω).1
    simp only [hKdef, dif_pos h]
    exact Nat.find_spec h
  have hstab : ∀ ω ∈ G, ∀ k, K ω ≤ k → ∀ t ∈ Icc (0 : ℝ) T, N k t ω = N (K ω) t ω := by
    intro ω hω k hk t ht
    obtain ⟨-, hq, hT'⟩ := hGsub hω
    rcases eq_or_lt_of_le ht.2 with htT | htT
    · rw [htT]
      exact (hT' (K ω) k hk (hKspec ω hω)).symm
    · refine (eq_of_rightCont_of_eq_rat (f := fun s => N k s ω) (g := fun s => N (K ω) s ω) htT
        (hNcad k ω t).1 (hNcad (K ω) ω t).1 fun q hq1 hq2 => ?_)
      exact (hq (K ω) k hk q ⟨ht.1.trans hq1.le, hq2.le⟩
        ((WithTop.coe_le_coe.mpr hq2.le).trans (hKspec ω hω))).symm
  set M : ℝ → Ω → ℝ := fun t ω => if ω ∈ G then N (K ω) t ω else N 0 t ω with hMdef
  refine ⟨M, ?_, ?_, ?_, τ, hτ, hmono, hex, fun k => ⟨hm k, hp k, hq k, fun t ht => ?_⟩⟩
  · -- adaptedness, as a pointwise limit
    intro t ht
    set F : ℕ → Ω → ℝ := fun n ω => if ω ∈ G then N n t ω else N 0 t ω with hFdef
    have hF : ∀ n, Measurable[ℱ t] (F n) := fun n =>
      Measurable.ite (ℱ.mono ht.1 _ hG0m) (hNad n t) (hNad 0 t)
    have hlim : Tendsto F atTop (𝓝 (M t)) := by
      refine tendsto_pi_nhds.2 fun ω => ?_
      by_cases hω : ω ∈ G
      · refine tendsto_atTop_of_eventually_const (i₀ := K ω) fun n hn => ?_
        simp only [hFdef, hMdef, if_pos hω]
        exact hstab ω hω n hn t ht
      · simp only [hFdef, hMdef, if_neg hω]
        exact tendsto_const_nhds
    exact @measurable_of_tendsto_metrizable Ω ℝ (ℱ t) _ _ _ _ F (M t) hF hlim
  · intro ω t _
    by_cases hω : ω ∈ G
    · simp only [hMdef, if_pos hω]
      exact (hNcad (K ω) ω t).1
    · simp only [hMdef, if_neg hω]
      exact (hNcad 0 ω t).1
  · intro ω t _
    by_cases hω : ω ∈ G
    · simp only [hMdef, if_pos hω]
      exact (hNcad (K ω) ω t).2
    · simp only [hMdef, if_neg hω]
      exact (hNcad 0 ω t).2
  · -- agreement with the cut-off integral up to the stopping time
    have hpair : ∀ᵐ ω ∂P, ∀ j, (j ≤ k → ((t : ℝ) : WithTop ℝ) ≤ τ j ω → N j t ω = N k t ω)
        ∧ (k ≤ j → ((t : ℝ) : WithTop ℝ) ≤ τ k ω → N k t ω = N j t ω) := by
      refine ae_all_iff.2 fun j => ?_
      have h1 : ∀ᵐ ω ∂P, j ≤ k → ((t : ℝ) : WithTop ℝ) ≤ τ j ω → N j t ω = N k t ω := by
        by_cases hjk : j ≤ k
        · filter_upwards [hcons j k hjk t ht] with ω hω _ hle
          exact hω hle
        · exact ae_of_all _ fun ω h => absurd h hjk
      have h2 : ∀ᵐ ω ∂P, k ≤ j → ((t : ℝ) : WithTop ℝ) ≤ τ k ω → N k t ω = N j t ω := by
        by_cases hkj : k ≤ j
        · filter_upwards [hcons k j hkj t ht] with ω hω _ hle
          exact hω hle
        · exact ae_of_all _ fun ω h => absurd h hkj
      exact h1.and h2
    have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
      have h : Gᶜᶜ ∈ ae P := compl_mem_ae_iff.mpr hGnull
      rw [compl_compl] at h
      exact h
    filter_upwards [hpair, hNae k t, hGae] with ω hω hN hωG hle
    have hMt : M t ω = N (K ω) t ω := by simp only [hMdef, if_pos hωG]
    rw [hMt, ← hN]
    rcases le_total (K ω) k with hKk | hkK
    · exact (hω (K ω)).1 hKk
        ((WithTop.coe_le_coe.mpr ht.2).trans (hKspec ω hωG))
    · exact ((hω (K ω)).2 hkK hle).symm

/-- **Linearity of the multidimensional Itô integral** at a positive time. -/
theorem multidim_sub {Z₁ Z₂ : ℝ → Ω → Fin d → ℝ}
    (hm₁ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z₁ s ω j))
    (hp₁ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₁ s ω j)
    (hq₁ : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖Z₁ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z₂ s ω j))
    (hp₂ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₂ s ω j)
    (hq₂ : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmS : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z₁ s ω j - Z₂ s ω j))
    (hpS : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₁ s ω j - Z₂ s ω j)
    (hqS : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, (‖Z₁ s ω j - Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    MultidimBrownianMotion.stochasticIntegral W ℱ hℱ (fun s ω j => Z₁ s ω j - Z₂ s ω j)
        hmS hpS hqS t
      =ᵐ[P] fun ω => MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z₁ hm₁ hp₁ hq₁ t ω
        - MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z₂ hm₂ hp₂ hq₂ t ω := by
  have h : ∀ j : Fin d, ∀ᵐ ω ∂P,
      Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hℱ j)
          (fun ω s => Z₁ s ω j - Z₂ s ω j) (hmS j) (hpS j) (hqS j) t ω
        = Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hℱ j) (fun ω s => Z₁ s ω j)
            (hm₁ j) (hp₁ j) (hq₁ j) t ω
          - Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hℱ j) (fun ω s => Z₂ s ω j)
            (hm₂ j) (hp₂ j) (hq₂ j) t ω := fun j =>
    Brownian.Ito.stochasticIntegralBrownian_sub (W.W j) ℱ (hℱ j) (hm₁ j) (hm₂ j) (hp₁ j)
      (hp₂ j) (hq₁ j) (hq₂ j) (hmS j) (hpS j) (hqS j) ht
  filter_upwards [ae_all_iff.2 h] with ω hω
  simp only [MultidimBrownianMotion.stochasticIntegral, Brownian.Ito.stochasticIntegral]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => hω j

/-- **The Burkholder–Davis–Gundy inequality at `p = 1` for a local Itô integral.** Over a
right-continuous filtration whose null sets lie in its time-`0` field,
`𝔼 sup_{t ≤ T} |M_t| ≤ 9 𝔼 (∑_j ∫_0^T H_j(s)² ds)^{1/2}`. -/
theorem IsLocalBrownianIntegral.lintegral_biSup_le [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {T : ℝ} (hT : 0 < T) {H : ℝ → Ω → Fin d → ℝ} {M : ℝ → Ω → ℝ}
    (hM : IsLocalBrownianIntegral W ℱ hℱ T H M) :
    ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 9 * ∫⁻ ω, (∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) ∂P := by
  obtain ⟨-, hMr, -, τ, hτ, hmono, hex, hk⟩ := hM
  set A : ℕ → Set Ω := fun k => {ω | ((T : ℝ) : WithTop ℝ) ≤ τ k ω} with hAdef
  have hAm : ∀ k, MeasurableSet (A k) := fun k => by
    have : A k = {ω | τ k ω < ((T : ℝ) : WithTop ℝ)}ᶜ := by
      ext ω
      simp [hAdef, not_lt]
    rw [this]
    exact (ℱ.le T _ ((hτ k).measurableSet_lt T)).compl
  have hAdir : Directed (· ⊆ ·) A :=
    Monotone.directed_le fun k k' hkk' ω hω => le_trans hω (hmono ω hkk')
  have hAunion : ∀ᵐ ω ∂P, ω ∈ ⋃ k, A k := by
    filter_upwards [hex] with ω hω
    obtain ⟨k, hk⟩ := hω
    exact mem_iUnion.2 ⟨k, hk⟩
  have hbound : ∀ k, ∫⁻ ω in A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 9 * ∫⁻ ω, (∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) ∂P := by
    intro k
    obtain ⟨hm, hp, hq, hagree⟩ := hk k
    obtain ⟨N, -, -, hNae, hNcad, -, -, -⟩ := BSDEJ.Solves.exists_cadlag_vectorIntegral_supBound W
      ℱ hℱ _ hm hp hq hℱ0 hnull T hT.le
    have hBDG := lintegral_biSup_le_brownian W ℱ hℱ hℱ0 hnull hm hp hq hT (M := N)
      (fun t _ => hNae t) (ae_of_all _ fun ω t _ => (hNcad ω t).1)
    have hD : ∀ᵐ ω ∂P, (∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
        (((q : ℝ) : ℝ) : WithTop ℝ) ≤ τ k ω → M q ω = N q ω)
        ∧ (((T : ℝ) : WithTop ℝ) ≤ τ k ω → M T ω = N T ω) := by
      have hloc : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
          ((t : ℝ) : WithTop ℝ) ≤ τ k ω → M t ω = N t ω := by
        intro t ht
        filter_upwards [hagree t ht, hNae t] with ω h1 h2 hle
        rw [h1 hle, h2]
      refine (ae_all_iff.2 fun q => ?_).and (hloc T ⟨hT.le, le_rfl⟩)
      by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
      · filter_upwards [hloc q hq] with ω hω _ hle
        exact hω hle
      · exact ae_of_all _ fun ω h => absurd h hq
    have hle : ∀ᵐ ω ∂P, ω ∈ A k →
        ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ≤ ⨆ t ∈ Icc (0 : ℝ) T, (‖N t ω‖₊ : ℝ≥0∞) := by
      filter_upwards [hD] with ω hω hωA
      have hωA' : ((T : ℝ) : WithTop ℝ) ≤ τ k ω := hωA
      have heq : ∀ t ∈ Icc (0 : ℝ) T, M t ω = N t ω := by
        intro t ht
        rcases eq_or_lt_of_le ht.2 with htT | htT
        · rw [htT]
          exact hω.2 hωA'
        · refine eq_of_rightCont_of_eq_rat (f := fun s => M s ω) (g := fun s => N s ω) htT
            (hMr ω t ⟨ht.1, htT⟩) (hNcad ω t).1 fun q hq1 hq2 => ?_
          exact hω.1 q ⟨ht.1.trans hq1.le, hq2.le⟩
            ((WithTop.coe_le_coe.mpr hq2.le).trans hωA')
      exact le_of_eq (iSup_congr fun t => iSup_congr fun ht => by rw [heq t ht])
    calc ∫⁻ ω in A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
        ≤ ∫⁻ ω in A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖N t ω‖₊ : ℝ≥0∞) ∂P :=
          lintegral_mono_ae ((ae_restrict_iff' (hAm k)).2 hle)
      _ ≤ ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖N t ω‖₊ : ℝ≥0∞) ∂P := setLIntegral_le_lintegral _ _
      _ ≤ _ := hBDG
      _ ≤ 9 * ∫⁻ ω, (∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) ∂P := by
          gcongr with ω j s
          split_ifs <;> simp
  calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      = ∫⁻ ω in ⋃ k, A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P := by
        rw [Measure.restrict_eq_self_of_ae_mem hAunion]
    _ = ⨆ k, ∫⁻ ω in A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P :=
        setLIntegral_iUnion_of_directed _ hAdir
    _ ≤ _ := iSup_le hbound

/-- **The increments of a local Itô integral have mean zero** when
`𝔼 (∑_j ∫_0^T H_j(s)² ds)^{1/2} < ∞`: for `t ∈ [0, T]`, `M_T − M_t` is integrable with mean
zero. -/
theorem IsLocalBrownianIntegral.integral_sub_eq_zero [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {T : ℝ} (hT : 0 < T) {H : ℝ → Ω → Fin d → ℝ} {M : ℝ → Ω → ℝ}
    (hM : IsLocalBrownianIntegral W ℱ hℱ T H M)
    (hHm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => H s ω j))
    (hfin : ∫⁻ ω, (∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) ∂P < ⊤)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Integrable (fun ω => M T ω - M t ω) P ∧ ∫ ω, (M T ω - M t ω) ∂P = 0 := by
  classical
  obtain ⟨hMad, -, -, τ, hτ, hmono, hex, hk⟩ := hM
  choose hm hp hq hagree using hk
  set cut : ℕ → ℝ → Ω → Fin d → ℝ :=
    fun k s ω j => if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then H s ω j else 0 with hcut
  -- martingale versions of the cut-off integrals
  have hv : ∀ k, ∃ N : ℝ → Ω → ℝ, (∀ t, N t =ᵐ[P]
      MultidimBrownianMotion.stochasticIntegral W ℱ hℱ (cut k) (hm k) (hp k) (hq k) t)
      ∧ Martingale N ℱ.rightCont P := fun k => by
    obtain ⟨N, -, -, h3, -, h5, -, -⟩ := BSDEJ.Solves.exists_cadlag_vectorIntegral_supBound W ℱ
      hℱ (cut k) (hm k) (hp k) (hq k) hℱ0 hnull T hT.le
    exact ⟨N, h3, h5⟩
  choose N hNae hNmart using hv
  set X : ℕ → Ω → ℝ := fun k ω => N k T ω - N k t ω with hXdef
  set Y : Ω → ℝ := fun ω => M T ω - M t ω with hYdef
  have hXi : ∀ k, Integrable (X k) P := fun k =>
    ((hNmart k).integrable T).sub ((hNmart k).integrable t)
  have hX0 : ∀ k, ∫ ω, X k ω ∂P = 0 := fun k => by
    rw [hXdef, integral_sub ((hNmart k).integrable T) ((hNmart k).integrable t)]
    have h := (hNmart k).setIntegral_eq ht.2 (s := univ) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [h, sub_self]
  have hY : AEStronglyMeasurable Y P :=
    (((hMad T ⟨hT.le, le_rfl⟩).mono (ℱ.le T) le_rfl).sub
      ((hMad t ht).mono (ℱ.le t) le_rfl)).aestronglyMeasurable
  -- almost surely the increments stabilise
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => X k ω) atTop (𝓝 (Y ω)) := by
    have hall : ∀ᵐ ω ∂P, ∀ k, (((T : ℝ) : WithTop ℝ) ≤ τ k ω →
        M T ω = MultidimBrownianMotion.stochasticIntegral W ℱ hℱ (cut k) (hm k) (hp k) (hq k) T ω)
        ∧ (((t : ℝ) : WithTop ℝ) ≤ τ k ω →
        M t ω = MultidimBrownianMotion.stochasticIntegral W ℱ hℱ (cut k) (hm k) (hp k) (hq k) t ω)
        ∧ N k T ω = MultidimBrownianMotion.stochasticIntegral W ℱ hℱ (cut k) (hm k) (hp k) (hq k)
          T ω
        ∧ N k t ω = MultidimBrownianMotion.stochasticIntegral W ℱ hℱ (cut k) (hm k) (hp k) (hq k)
          t ω :=
      ae_all_iff.2 fun k => (hagree k T ⟨hT.le, le_rfl⟩).and
        ((hagree k t ht).and ((hNae k T).and (hNae k t)))
    filter_upwards [hex, hall] with ω hω hall
    obtain ⟨k₀, hk₀⟩ := hω
    refine tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => ?_
    have hTk : ((T : ℝ) : WithTop ℝ) ≤ τ k ω := hk₀.trans (hmono ω hk)
    have htk : ((t : ℝ) : WithTop ℝ) ≤ τ k ω := (WithTop.coe_le_coe.mpr ht.2).trans hTk
    obtain ⟨h1, h2, h3, h4⟩ := hall k
    simp only [hXdef, hYdef]
    rw [h3, h4, h1 hTk, h2 htk]
  -- the tails of the integrand
  set g : ℕ → Ω → ℝ≥0∞ := fun k ω => (∑ j, ∫⁻ s in Icc (0 : ℝ) T,
    (if τ k ω < ((s : ℝ) : WithTop ℝ) then (‖H s ω j‖₊ : ℝ≥0∞) ^ 2 else 0)) ^ (1 / 2 : ℝ)
    with hgdef
  have hgm : ∀ k, Measurable (g k) := by
    intro k
    refine Measurable.pow_const ?_ _
    refine Finset.measurable_sum _ fun j _ => ?_
    refine Measurable.lintegral_prod_right' (f := fun p : Ω × ℝ =>
      if τ k p.1 < ((p.2 : ℝ) : WithTop ℝ) then (‖H p.2 p.1 j‖₊ : ℝ≥0∞) ^ 2 else 0) ?_
    exact Measurable.ite (measurableSet_lt_coe (hτ k))
      ((hHm j).nnnorm.coe_nnreal_ennreal.pow_const 2) measurable_const
  have hgle : ∀ k ω, g k ω
      ≤ (∑ j, ∫⁻ s in Icc (0 : ℝ) T, (‖H s ω j‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) := by
    intro k ω
    simp only [hgdef]
    gcongr with j s
    split_ifs
    · exact le_rfl
    · exact bot_le
  have hg0 : Tendsto (fun k => ∫⁻ ω, g k ω ∂P) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence (μ := P) (F := g) (f := fun _ => 0)
      _ hgm (fun k => ae_of_all _ (hgle k)) hfin.ne (by
        filter_upwards [hex] with ω hω
        obtain ⟨k₀, hk₀⟩ := hω
        refine tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => ?_
        have hTk : ((T : ℝ) : WithTop ℝ) ≤ τ k ω := hk₀.trans (hmono ω hk)
        have hzero : ∀ j, ∫⁻ s in Icc (0 : ℝ) T, (if τ k ω < ((s : ℝ) : WithTop ℝ) then
            (‖H s ω j‖₊ : ℝ≥0∞) ^ 2 else 0) = 0 := by
          intro j
          refine (setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_).trans
            (lintegral_zero)
          rw [if_neg]
          exact not_lt.mpr ((WithTop.coe_le_coe.mpr hs.2).trans hTk)
        simp only [hgdef, hzero, Finset.sum_const_zero]
        exact ENNReal.zero_rpow_of_pos (by norm_num))
    simpa using h
  -- the increments form a Cauchy sequence in `L¹`
  have hC : ∀ k k', k ≤ k' → ∫⁻ ω, ‖X k ω - X k' ω‖ₑ ∂P ≤ 18 * ∫⁻ ω, g k ω ∂P := by
    intro k k' hkk'
    set D : ℝ → Ω → Fin d → ℝ := fun s ω j => cut k s ω j - cut k' s ω j with hDdef
    have hmD : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => D s ω j) := fun j =>
      (hm k j).sub (hm k' j)
    have hpD : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => D s ω j := fun j =>
      (hp k j).sub (hp k' j)
    have hDle : ∀ ω s j, |D s ω j| ≤ |cut k' s ω j| := by
      intro ω s j
      simp only [hDdef, hcut]
      by_cases h1 : ((s : ℝ) : WithTop ℝ) ≤ τ k ω
      · rw [if_pos h1, if_pos (h1.trans (hmono ω hkk')), sub_self, abs_zero]
        exact abs_nonneg _
      · rw [if_neg h1, zero_sub, abs_neg]
    have hqD : ∀ (j : Fin d) (T' : ℝ), 0 < T' →
        ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T', (‖D s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun j =>
      Brownian.Ito.energy_lt_top_of_abs_le (fun ω s => hDle ω s j) (hq k' j)
    obtain ⟨V, -, -, hVae, hVcad, -, hVzero, -⟩ :=
      BSDEJ.Solves.exists_cadlag_vectorIntegral_supBound W ℱ hℱ D hmD hpD hqD hℱ0 hnull T hT.le
    have hBDG := lintegral_biSup_le_brownian W ℱ hℱ hℱ0 hnull hmD hpD hqD hT (M := V)
      (fun t _ => hVae t) (ae_of_all _ fun ω t _ => (hVcad ω t).1)
    -- the increment of the difference is that of `V`
    have hlin : ∀ r ∈ Icc (0 : ℝ) T, ∀ᵐ ω ∂P, N k r ω - N k' r ω = V r ω := by
      intro r hr
      rcases eq_or_lt_of_le hr.1 with h0 | h0
      · subst h0
        have hz : ∀ k'', N k'' 0 =ᵐ[P] 0 := fun k'' =>
          (hNae k'' 0).trans (MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos W ℱ hℱ
            _ (hm k'') (hp k'') (hq k'') le_rfl)
        filter_upwards [hz k, hz k', hVzero 0 le_rfl] with ω h1 h2 h3
        simp only [Pi.zero_apply] at h1 h2 h3
        rw [h1, h2, h3, sub_zero]
      · filter_upwards [hNae k r, hNae k' r, hVae r,
          multidim_sub W ℱ hℱ (hm k) (hp k) (hq k) (hm k') (hp k') (hq k') hmD hpD hqD h0]
          with ω h1 h2 h3 h4
        rw [h1, h2, h3, h4]
    have hsupV : ∀ ω, ∀ r ∈ Icc (0 : ℝ) T,
        (‖V r ω‖₊ : ℝ≥0∞) ≤ ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞) := fun ω r hr =>
      le_iSup₂_of_le r hr le_rfl
    calc ∫⁻ ω, ‖X k ω - X k' ω‖ₑ ∂P
        = ∫⁻ ω, ‖V T ω - V t ω‖ₑ ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlin T ⟨hT.le, le_rfl⟩, hlin t ht] with ω h1 h2
          simp only [hXdef]
          rw [show N k T ω - N k t ω - (N k' T ω - N k' t ω)
            = (N k T ω - N k' T ω) - (N k t ω - N k' t ω) by ring, h1, h2]
      _ ≤ ∫⁻ ω, 2 * ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞) ∂P := by
          refine lintegral_mono fun ω => ?_
          calc ‖V T ω - V t ω‖ₑ ≤ ‖V T ω‖ₑ + ‖V t ω‖ₑ := enorm_sub_le
            _ = (‖V T ω‖₊ : ℝ≥0∞) + ‖V t ω‖₊ := by simp only [enorm_eq_nnnorm]
            _ ≤ _ := by
                rw [two_mul]
                exact add_le_add (hsupV ω T ⟨hT.le, le_rfl⟩) (hsupV ω t ht)
      _ = 2 * ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞) ∂P :=
          lintegral_const_mul' _ _ (by norm_num)
      _ ≤ 2 * (9 * ∫⁻ ω, (∑ j, ∫⁻ s in Icc (0 : ℝ) T,
            (‖D s ω j‖₊ : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) ∂P) := by gcongr
      _ ≤ 2 * (9 * ∫⁻ ω, g k ω ∂P) := by
          gcongr with ω
          simp only [hgdef]
          gcongr with j s
          by_cases h1 : ((s : ℝ) : WithTop ℝ) ≤ τ k ω
          · have : D s ω j = 0 := by
              simp only [hDdef, hcut, if_pos h1, if_pos (h1.trans (hmono ω hkk')), sub_self]
            rw [this, if_neg (not_lt.mpr h1)]
            simp
          · rw [if_pos (not_le.mp h1)]
            have := hDle ω s j
            have h2 : |cut k' s ω j| ≤ |H s ω j| := by
              simp only [hcut]
              split_ifs
              · exact le_rfl
              · simp
            gcongr
            exact_mod_cast (this.trans h2 : |D s ω j| ≤ |H s ω j|)
      _ = 18 * ∫⁻ ω, g k ω ∂P := by rw [← mul_assoc]; norm_num
  have hε : Tendsto (fun k => 18 * ∫⁻ ω, g k ω ∂P) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hg0 (Or.inr (by norm_num : (18 : ℝ≥0∞) ≠ ⊤))
  exact integrable_and_integral_eq_zero_of_cauchy hXi hX0 hY hlim hε hC

end Brownian

section Compensated

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)

/-- **A local compensated Poisson integral.** `M` is a local integral on `[0, T]` of the marked
integrand `φ : Ω → ℝ → E → ℝ` against the compensated Poisson random measure `Ñ` of `N`: `M` is
adapted on `[0, T]` with càdlàg paths there (right-continuous on `[0, T)`, left limits on
`(0, T]`), and there are stopping times `τ_k`, nondecreasing in `k` and almost surely eventually
at least `T`, such that each cut-off integrand `φ_s(e) 1_{s ≤ τ_k}` meets the conditions of the
compensated integral (jointly measurable, marked progressively measurable, of finite energy on
every horizon) and `M` agrees with its integral up to `τ_k`: for every `t ∈ [0, T]`, almost surely
on `{t ≤ τ_k}`, `M_t = ∫_0^t ∫_E φ_s(e) 1_{s ≤ τ_k} Ñ(ds, de)`. -/
def IsLocalCompensatedIntegral (T : ℝ) (φ : Ω → ℝ → E → ℝ) (M : ℝ → Ω → ℝ) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) T, Measurable[ℱ t] (M t))
    ∧ (∀ ω, ∀ t ∈ Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)))
    ∧ (∀ ω, ∀ t ∈ Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 l))
    ∧ ∃ τ : ℕ → Ω → WithTop ℝ, (∀ k, IsStoppingTime ℱ (τ k))
      ∧ (∀ ω, Monotone fun k => τ k ω)
      ∧ (∀ᵐ ω ∂P, ∃ k, ((T : ℝ) : WithTop ℝ) ≤ τ k ω)
      ∧ ∀ k, ∃ (hm : Measurable fun p : Ω × ℝ × E =>
            if ((p.2.1 : ℝ) : WithTop ℝ) ≤ τ k p.1 then φ p.1 p.2.1 p.2.2 else 0)
          (hp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e =>
            if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then φ ω s e else 0)
          (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T', ∫⁻ e,
            (‖if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then φ ω s e else 0‖₊ : ℝ≥0∞) ^ 2
              ∂ν ∂volume ∂P < ⊤),
          ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ k ω →
            M t ω = Poisson.Compensated.stochasticIntegral N ℱ hℱ
              (fun ω s e => if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then φ ω s e else 0) hm hp hq t ω

/-- Finite energy passes to a pointwise smaller marked integrand. -/
theorem markedEnergy_lt_top_of_abs_le {ψ φ : Ω → ℝ → E → ℝ}
    (h : ∀ ω s e, |ψ ω s e| ≤ |φ ω s e|)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  intro T hT
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s =>
    lintegral_mono fun e => ?_) (hq T hT)
  gcongr
  have := h ω s e
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs] at this
  exact_mod_cast this

/-- **Existence of the local compensated integral.** Along stopping times `τ_k`, nondecreasing in
`k` and almost surely eventually at least `T`, whose cut-off integrands meet the conditions of the
compensated integral, the marked integrand `φ` has a local compensated integral on `[0, T]`. -/
theorem exists_isLocalCompensatedIntegral [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ) (τ : ℕ → Ω → WithTop ℝ)
    (hτ : ∀ k, IsStoppingTime ℱ (τ k)) (hmono : ∀ ω, Monotone fun k => τ k ω)
    (hex : ∀ᵐ ω ∂P, ∃ k, ((T : ℝ) : WithTop ℝ) ≤ τ k ω)
    (hm : ∀ k, Measurable fun p : Ω × ℝ × E =>
      if ((p.2.1 : ℝ) : WithTop ℝ) ≤ τ k p.1 then φ p.1 p.2.1 p.2.2 else 0)
    (hp : ∀ k, Probability.MarkedProgressivelyMeasurable ℱ fun ω s e =>
      if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then φ ω s e else 0)
    (hq : ∀ k (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) T', ∫⁻ e,
      (‖if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then φ ω s e else 0‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∃ M, IsLocalCompensatedIntegral N ℱ hℱ T φ M := by
  classical
  set cut : ℕ → Ω → ℝ → E → ℝ :=
    fun k ω s e => if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then φ ω s e else 0 with hcut
  have hrc : ℱ.rightCont = ℱ := Filtration.IsRightContinuous.eq
  have hv : ∀ k, ∃ V : ℝ → Ω → ℝ, (∀ t, Measurable[ℱ t] (V t))
      ∧ (∀ t, V t =ᵐ[P] Poisson.Compensated.stochasticIntegral N ℱ hℱ (cut k) (hm k) (hp k)
          (hq k) t)
      ∧ (∀ ω t, Tendsto (fun s => V s ω) (𝓝[>] t) (𝓝 (V t ω))
          ∧ ∃ L : ℝ, Tendsto (fun s => V s ω) (𝓝[<] t) (𝓝 L)) := fun k => by
    obtain ⟨V, h1, h2, h3, h4⟩ := Poisson.Compensated.exists_everywhere_cadlag_stochasticIntegral
      N ℱ hℱ (cut k) (hm k) (hp k) (hq k) hℱ0 hnull
    refine ⟨V, fun t => ?_, h2, fun ω t => ⟨h3 ω t, h4 ω t⟩⟩
    have h := h1 t
    rw [hrc] at h
    exact h
  choose V hVad hVae hVcad using hv
  have hcons : ∀ j k, j ≤ k → ∀ t ∈ Icc (0 : ℝ) T,
      ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ j ω → V j t ω = V k t ω := by
    intro j k hjk t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · subst h0
      filter_upwards [hVae j 0, hVae k 0,
        Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ (hm j) (hp j) (hq j)
          (le_refl (0 : ℝ)),
        Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ (hm k) (hp k) (hq k)
          (le_refl (0 : ℝ))] with ω h1 h2 h3 h4 _
      rw [h1, h2, h3, h4]
    · have hagree : ∀ ω s, 0 < s → ((s : ℝ) : WithTop ℝ) ≤ τ j ω → ∀ e,
          cut j ω s e = cut k ω s e := by
        intro ω s _ hle e
        simp only [hcut, if_pos hle, if_pos (hle.trans (hmono ω hjk))]
      filter_upwards [hVae j t, hVae k t, Poisson.Compensated.stochasticIntegral_congr_of_le N hℱ
        (hm j) (hp j) (hq j) (hτ j) (hm k) (hp k) (hq k) hagree h0] with ω h1 h2 h3 hle
      rw [h1, h2, h3 hle]
  set G0 : Set Ω := {ω | (∃ k, ((T : ℝ) : WithTop ℝ) ≤ τ k ω)
      ∧ (∀ j k, j ≤ k → ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
          (((q : ℝ) : ℝ) : WithTop ℝ) ≤ τ j ω → V j q ω = V k q ω)
      ∧ (∀ j k, j ≤ k → ((T : ℝ) : WithTop ℝ) ≤ τ j ω → V j T ω = V k T ω)} with hG0def
  have hG0 : ∀ᵐ ω ∂P, ω ∈ G0 := by
    have h1 : ∀ᵐ ω ∂P, ∀ j k, j ≤ k → ∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
        (((q : ℝ) : ℝ) : WithTop ℝ) ≤ τ j ω → V j q ω = V k q ω := by
      refine ae_all_iff.2 fun j => ae_all_iff.2 fun k => ?_
      by_cases hjk : j ≤ k
      · refine (ae_all_iff.2 fun q => ?_).mono fun ω hω _ => hω
        by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
        · filter_upwards [hcons j k hjk q hq] with ω hω _ hle
          exact hω hle
        · exact ae_of_all _ fun ω h => absurd h hq
      · exact ae_of_all _ fun ω h => absurd h hjk
    have h2 : ∀ᵐ ω ∂P, ∀ j k, j ≤ k → ((T : ℝ) : WithTop ℝ) ≤ τ j ω → V j T ω = V k T ω := by
      refine ae_all_iff.2 fun j => ae_all_iff.2 fun k => ?_
      by_cases hjk : j ≤ k
      · filter_upwards [hcons j k hjk T ⟨hT.le, le_rfl⟩] with ω hω _ hle
        exact hω hle
      · exact ae_of_all _ fun ω h => absurd h hjk
    filter_upwards [hex, h1, h2] with ω h0 h1 h2
    exact ⟨h0, h1, h2⟩
  set G : Set Ω := (toMeasurable P G0ᶜ)ᶜ with hGdef
  have hGsub : G ⊆ G0 := by
    intro ω hω
    by_contra hcon
    exact hω (subset_toMeasurable P G0ᶜ hcon)
  have hGnull : P Gᶜ = 0 := by
    rw [hGdef, compl_compl, measure_toMeasurable]
    exact ae_iff.mp hG0
  have hG0m : MeasurableSet[ℱ 0] G := by
    have := hnull Gᶜ (by rw [hGdef, compl_compl]; exact measurableSet_toMeasurable _ _) hGnull
    simpa using this.compl
  set K : Ω → ℕ := fun ω =>
    if h : ∃ k, ((T : ℝ) : WithTop ℝ) ≤ τ k ω then Nat.find h else 0 with hKdef
  have hKspec : ∀ ω ∈ G, ((T : ℝ) : WithTop ℝ) ≤ τ (K ω) ω := by
    intro ω hω
    have h := (hGsub hω).1
    simp only [hKdef, dif_pos h]
    exact Nat.find_spec h
  have hstab : ∀ ω ∈ G, ∀ k, K ω ≤ k → ∀ t ∈ Icc (0 : ℝ) T, V k t ω = V (K ω) t ω := by
    intro ω hω k hk t ht
    obtain ⟨-, hq, hT'⟩ := hGsub hω
    rcases eq_or_lt_of_le ht.2 with htT | htT
    · rw [htT]
      exact (hT' (K ω) k hk (hKspec ω hω)).symm
    · refine (eq_of_rightCont_of_eq_rat (f := fun s => V k s ω) (g := fun s => V (K ω) s ω) htT
        (hVcad k ω t).1 (hVcad (K ω) ω t).1 fun q hq1 hq2 => ?_)
      exact (hq (K ω) k hk q ⟨ht.1.trans hq1.le, hq2.le⟩
        ((WithTop.coe_le_coe.mpr hq2.le).trans (hKspec ω hω))).symm
  set M : ℝ → Ω → ℝ := fun t ω => if ω ∈ G then V (K ω) t ω else V 0 t ω with hMdef
  refine ⟨M, ?_, ?_, ?_, τ, hτ, hmono, hex, fun k => ⟨hm k, hp k, hq k, fun t ht => ?_⟩⟩
  · intro t ht
    set F : ℕ → Ω → ℝ := fun n ω => if ω ∈ G then V n t ω else V 0 t ω with hFdef
    have hF : ∀ n, Measurable[ℱ t] (F n) := fun n =>
      Measurable.ite (ℱ.mono ht.1 _ hG0m) (hVad n t) (hVad 0 t)
    have hlim : Tendsto F atTop (𝓝 (M t)) := by
      refine tendsto_pi_nhds.2 fun ω => ?_
      by_cases hω : ω ∈ G
      · refine tendsto_atTop_of_eventually_const (i₀ := K ω) fun n hn => ?_
        simp only [hFdef, hMdef, if_pos hω]
        exact hstab ω hω n hn t ht
      · simp only [hFdef, hMdef, if_neg hω]
        exact tendsto_const_nhds
    exact @measurable_of_tendsto_metrizable Ω ℝ (ℱ t) _ _ _ _ F (M t) hF hlim
  · intro ω t _
    by_cases hω : ω ∈ G
    · simp only [hMdef, if_pos hω]
      exact (hVcad (K ω) ω t).1
    · simp only [hMdef, if_neg hω]
      exact (hVcad 0 ω t).1
  · intro ω t _
    by_cases hω : ω ∈ G
    · simp only [hMdef, if_pos hω]
      exact (hVcad (K ω) ω t).2
    · simp only [hMdef, if_neg hω]
      exact (hVcad 0 ω t).2
  · have hpair : ∀ᵐ ω ∂P, ∀ j, (j ≤ k → ((t : ℝ) : WithTop ℝ) ≤ τ j ω → V j t ω = V k t ω)
        ∧ (k ≤ j → ((t : ℝ) : WithTop ℝ) ≤ τ k ω → V k t ω = V j t ω) := by
      refine ae_all_iff.2 fun j => ?_
      have h1 : ∀ᵐ ω ∂P, j ≤ k → ((t : ℝ) : WithTop ℝ) ≤ τ j ω → V j t ω = V k t ω := by
        by_cases hjk : j ≤ k
        · filter_upwards [hcons j k hjk t ht] with ω hω _ hle
          exact hω hle
        · exact ae_of_all _ fun ω h => absurd h hjk
      have h2 : ∀ᵐ ω ∂P, k ≤ j → ((t : ℝ) : WithTop ℝ) ≤ τ k ω → V k t ω = V j t ω := by
        by_cases hkj : k ≤ j
        · filter_upwards [hcons k j hkj t ht] with ω hω _ hle
          exact hω hle
        · exact ae_of_all _ fun ω h => absurd h hkj
      exact h1.and h2
    have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
      have h : Gᶜᶜ ∈ ae P := compl_mem_ae_iff.mpr hGnull
      rw [compl_compl] at h
      exact h
    filter_upwards [hpair, hVae k t, hGae] with ω hω hV hωG hle
    have hMt : M t ω = V (K ω) t ω := by simp only [hMdef, if_pos hωG]
    rw [hMt, ← hV]
    rcases le_total (K ω) k with hKk | hkK
    · exact (hω (K ω)).1 hKk
        ((WithTop.coe_le_coe.mpr ht.2).trans (hKspec ω hωG))
    · exact ((hω (K ω)).2 hkK hle).symm

/-- **The Burkholder–Davis–Gundy inequality at `p = 1` for a local compensated integral.** Over a
right-continuous filtration whose null sets lie in its time-`0` field,
`𝔼 sup_{t ≤ T} |M_t| ≤ 9 𝔼 (∫_0^T ∫_E φ_s(e)² ν(de) ds)^{1/2}`. -/
theorem IsLocalCompensatedIntegral.lintegral_biSup_le [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {T : ℝ} (hT : 0 < T) {φ : Ω → ℝ → E → ℝ} {M : ℝ → Ω → ℝ}
    (hM : IsLocalCompensatedIntegral N ℱ hℱ T φ M) :
    ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 9 * ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
        ∂P := by
  obtain ⟨-, hMr, -, τ, hτ, hmono, hex, hk⟩ := hM
  set A : ℕ → Set Ω := fun k => {ω | ((T : ℝ) : WithTop ℝ) ≤ τ k ω} with hAdef
  have hAm : ∀ k, MeasurableSet (A k) := fun k => by
    have : A k = {ω | τ k ω < ((T : ℝ) : WithTop ℝ)}ᶜ := by
      ext ω
      simp [hAdef, not_lt]
    rw [this]
    exact (ℱ.le T _ ((hτ k).measurableSet_lt T)).compl
  have hAdir : Directed (· ⊆ ·) A :=
    Monotone.directed_le fun k k' hkk' ω hω => le_trans hω (hmono ω hkk')
  have hAunion : ∀ᵐ ω ∂P, ω ∈ ⋃ k, A k := by
    filter_upwards [hex] with ω hω
    obtain ⟨k, hk⟩ := hω
    exact mem_iUnion.2 ⟨k, hk⟩
  have hbound : ∀ k, ∫⁻ ω in A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      ≤ 9 * ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
        ∂P := by
    intro k
    obtain ⟨hm, hp, hq, hagree⟩ := hk k
    obtain ⟨V, -, hVae, hVr, -⟩ := Poisson.Compensated.exists_everywhere_cadlag_stochasticIntegral
      N ℱ hℱ _ hm hp hq hℱ0 hnull
    have hBDG := lintegral_biSup_le_compensated N ℱ hℱ hm hp hq hT (M := V)
      (fun t _ => hVae t) (ae_of_all _ fun ω t _ => hVr ω t)
    have hD : ∀ᵐ ω ∂P, (∀ q : ℚ, (q : ℝ) ∈ Icc (0 : ℝ) T →
        (((q : ℝ) : ℝ) : WithTop ℝ) ≤ τ k ω → M q ω = V q ω)
        ∧ (((T : ℝ) : WithTop ℝ) ≤ τ k ω → M T ω = V T ω) := by
      have hloc : ∀ t ∈ Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
          ((t : ℝ) : WithTop ℝ) ≤ τ k ω → M t ω = V t ω := by
        intro t ht
        filter_upwards [hagree t ht, hVae t] with ω h1 h2 hle
        rw [h1 hle, h2]
      refine (ae_all_iff.2 fun q => ?_).and (hloc T ⟨hT.le, le_rfl⟩)
      by_cases hq : (q : ℝ) ∈ Icc (0 : ℝ) T
      · filter_upwards [hloc q hq] with ω hω _ hle
        exact hω hle
      · exact ae_of_all _ fun ω h => absurd h hq
    have hle : ∀ᵐ ω ∂P, ω ∈ A k →
        ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ≤ ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞) := by
      filter_upwards [hD] with ω hω hωA
      have hωA' : ((T : ℝ) : WithTop ℝ) ≤ τ k ω := hωA
      have heq : ∀ t ∈ Icc (0 : ℝ) T, M t ω = V t ω := by
        intro t ht
        rcases eq_or_lt_of_le ht.2 with htT | htT
        · rw [htT]
          exact hω.2 hωA'
        · refine eq_of_rightCont_of_eq_rat (f := fun s => M s ω) (g := fun s => V s ω) htT
            (hMr ω t ⟨ht.1, htT⟩) (hVr ω t) fun q hq1 hq2 => ?_
          exact hω.1 q ⟨ht.1.trans hq1.le, hq2.le⟩
            ((WithTop.coe_le_coe.mpr hq2.le).trans hωA')
      exact le_of_eq (iSup_congr fun t => iSup_congr fun ht => by rw [heq t ht])
    calc ∫⁻ ω in A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
        ≤ ∫⁻ ω in A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞) ∂P :=
          lintegral_mono_ae ((ae_restrict_iff' (hAm k)).2 hle)
      _ ≤ ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞) ∂P := setLIntegral_le_lintegral _ _
      _ ≤ _ := hBDG
      _ ≤ 9 * ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
            ∂P := by
          gcongr with ω s e
          split_ifs <;> simp
  calc ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P
      = ∫⁻ ω in ⋃ k, A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P := by
        rw [Measure.restrict_eq_self_of_ae_mem hAunion]
    _ = ⨆ k, ∫⁻ ω in A k, ⨆ t ∈ Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ∂P :=
        setLIntegral_iUnion_of_directed _ hAdir
    _ ≤ _ := iSup_le hbound

/-- **The increments of a local compensated integral have mean zero** when
`𝔼 (∫_0^T ∫_E φ_s(e)² ν(de) ds)^{1/2} < ∞`: for `t ∈ [0, T]`, `M_T − M_t` is integrable with mean
zero. -/
theorem IsLocalCompensatedIntegral.integral_sub_eq_zero [ℱ.IsRightContinuous]
    {T : ℝ} (hT : 0 < T) {φ : Ω → ℝ → E → ℝ} {M : ℝ → Ω → ℝ}
    (hM : IsLocalCompensatedIntegral N ℱ hℱ T φ M)
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hfin : ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
      ∂P < ⊤)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    Integrable (fun ω => M T ω - M t ω) P ∧ ∫ ω, (M T ω - M t ω) ∂P = 0 := by
  classical
  obtain ⟨hMad, -, -, τ, hτ, hmono, hex, hk⟩ := hM
  choose hm hp hq hagree using hk
  set cut : ℕ → Ω → ℝ → E → ℝ :=
    fun k ω s e => if ((s : ℝ) : WithTop ℝ) ≤ τ k ω then φ ω s e else 0 with hcut
  set I : ℕ → ℝ → Ω → ℝ := fun k =>
    Poisson.Compensated.stochasticIntegral N ℱ hℱ (cut k) (hm k) (hp k) (hq k) with hIdef
  have hImart : ∀ k, Martingale (I k) ℱ.rightCont P := fun k =>
    Poisson.Compensated.martingale_stochasticIntegral_rightCont N ℱ hℱ _ (hm k) (hp k) (hq k)
  set X : ℕ → Ω → ℝ := fun k ω => I k T ω - I k t ω with hXdef
  set Y : Ω → ℝ := fun ω => M T ω - M t ω with hYdef
  have hXi : ∀ k, Integrable (X k) P := fun k =>
    ((hImart k).integrable T).sub ((hImart k).integrable t)
  have hX0 : ∀ k, ∫ ω, X k ω ∂P = 0 := fun k => by
    rw [hXdef, integral_sub ((hImart k).integrable T) ((hImart k).integrable t)]
    have h := (hImart k).setIntegral_eq ht.2 (s := univ) MeasurableSet.univ
    simp only [Measure.restrict_univ] at h
    rw [h, sub_self]
  have hY : AEStronglyMeasurable Y P :=
    (((hMad T ⟨hT.le, le_rfl⟩).mono (ℱ.le T) le_rfl).sub
      ((hMad t ht).mono (ℱ.le t) le_rfl)).aestronglyMeasurable
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => X k ω) atTop (𝓝 (Y ω)) := by
    have hall : ∀ᵐ ω ∂P, ∀ k, (((T : ℝ) : WithTop ℝ) ≤ τ k ω → M T ω = I k T ω)
        ∧ (((t : ℝ) : WithTop ℝ) ≤ τ k ω → M t ω = I k t ω) :=
      ae_all_iff.2 fun k => (hagree k T ⟨hT.le, le_rfl⟩).and (hagree k t ht)
    filter_upwards [hex, hall] with ω hω hall
    obtain ⟨k₀, hk₀⟩ := hω
    refine tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => ?_
    have hTk : ((T : ℝ) : WithTop ℝ) ≤ τ k ω := hk₀.trans (hmono ω hk)
    have htk : ((t : ℝ) : WithTop ℝ) ≤ τ k ω := (WithTop.coe_le_coe.mpr ht.2).trans hTk
    simp only [hXdef, hYdef]
    rw [(hall k).1 hTk, (hall k).2 htk]
  set a : Ω → ℝ → ℝ≥0∞ := fun ω s => ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν with ha
  have hjoint : Measurable fun p : Ω × ℝ => a p.1 p.2 := by
    have h3 : Measurable fun q : (Ω × ℝ) × E => (‖φ q.1.1 q.1.2 q.2‖₊ : ℝ≥0∞) ^ 2 :=
      (hφm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).nnnorm
        |>.coe_nnreal_ennreal.pow_const 2
    exact h3.lintegral_prod_right'
  set g : ℕ → Ω → ℝ≥0∞ := fun k ω => (∫⁻ s in Icc (0 : ℝ) T,
    (if τ k ω < ((s : ℝ) : WithTop ℝ) then a ω s else 0)) ^ (1 / 2 : ℝ) with hgdef
  have hgm : ∀ k, Measurable (g k) := by
    intro k
    refine Measurable.pow_const ?_ _
    refine Measurable.lintegral_prod_right' (f := fun p : Ω × ℝ =>
      if τ k p.1 < ((p.2 : ℝ) : WithTop ℝ) then a p.1 p.2 else 0) ?_
    exact Measurable.ite (measurableSet_lt_coe (hτ k)) hjoint measurable_const
  have hgle : ∀ k ω, g k ω
      ≤ (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
    intro k ω
    simp only [hgdef]
    gcongr with s
    split_ifs
    · exact le_rfl
    · exact bot_le
  have hg0 : Tendsto (fun k => ∫⁻ ω, g k ω ∂P) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence (μ := P) (F := g) (f := fun _ => 0)
      _ hgm (fun k => ae_of_all _ (hgle k)) hfin.ne (by
        filter_upwards [hex] with ω hω
        obtain ⟨k₀, hk₀⟩ := hω
        refine tendsto_atTop_of_eventually_const (i₀ := k₀) fun k hk => ?_
        have hTk : ((T : ℝ) : WithTop ℝ) ≤ τ k ω := hk₀.trans (hmono ω hk)
        have hzero : ∫⁻ s in Icc (0 : ℝ) T,
            (if τ k ω < ((s : ℝ) : WithTop ℝ) then a ω s else 0) = 0 := by
          refine (setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_).trans
            (lintegral_zero)
          rw [if_neg]
          exact not_lt.mpr ((WithTop.coe_le_coe.mpr hs.2).trans hTk)
        simp only [hgdef, hzero]
        exact ENNReal.zero_rpow_of_pos (by norm_num))
    simpa using h
  have hC : ∀ k k', k ≤ k' → ∫⁻ ω, ‖X k ω - X k' ω‖ₑ ∂P ≤ 18 * ∫⁻ ω, g k ω ∂P := by
    intro k k' hkk'
    set D : Ω → ℝ → E → ℝ := fun ω s e => cut k ω s e - cut k' ω s e with hDdef
    have hmD : Measurable fun p : Ω × ℝ × E => D p.1 p.2.1 p.2.2 := (hm k).sub (hm k')
    have hpD : Probability.MarkedProgressivelyMeasurable ℱ D :=
      Poisson.Compensated.markedProgressivelyMeasurable_sub (hp k) (hp k')
    have hDle : ∀ ω s e, |D ω s e| ≤ |cut k' ω s e| := by
      intro ω s e
      simp only [hDdef, hcut]
      by_cases h1 : ((s : ℝ) : WithTop ℝ) ≤ τ k ω
      · rw [if_pos h1, if_pos (h1.trans (hmono ω hkk')), sub_self, abs_zero]
        exact abs_nonneg _
      · rw [if_neg h1, zero_sub, abs_neg]
    have hqD := markedEnergy_lt_top_of_abs_le hDle (hq k')
    set V : ℝ → Ω → ℝ := Poisson.Compensated.stochasticIntegral N ℱ hℱ D hmD hpD hqD with hVdef
    have hBDG := lintegral_biSup_le_compensated N ℱ hℱ hmD hpD hqD hT (M := V)
      (fun t _ => ae_eq_refl _)
      (by
        filter_upwards [Poisson.Compensated.stochasticIntegral_cadlag N ℱ hℱ D hmD hpD hqD]
          with ω hω t _
        exact (hω t).1)
    have hlin : ∀ r ∈ Icc (0 : ℝ) T, ∀ᵐ ω ∂P, I k r ω - I k' r ω = V r ω := by
      intro r hr
      rcases eq_or_lt_of_le hr.1 with h0 | h0
      · subst h0
        filter_upwards [Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ (hm k)
            (hp k) (hq k) (le_refl (0 : ℝ)),
          Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ (hm k') (hp k') (hq k')
            (le_refl (0 : ℝ)),
          Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos N hℱ hmD hpD hqD
            (le_refl (0 : ℝ))] with ω h1 h2 h3
        simp only [Pi.zero_apply] at h1 h2 h3
        simp only [hIdef, hVdef]
        rw [h1, h2, h3, sub_zero]
      · filter_upwards [Poisson.Compensated.stochasticIntegral_sub N hℱ (hm k) (hm k') (hp k)
          (hp k') (hq k) (hq k') hmD hpD hqD h0] with ω h1
        simp only [hIdef, hVdef]
        rw [h1]
    have hsupV : ∀ ω, ∀ r ∈ Icc (0 : ℝ) T,
        (‖V r ω‖₊ : ℝ≥0∞) ≤ ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞) := fun ω r hr =>
      le_iSup₂_of_le r hr le_rfl
    calc ∫⁻ ω, ‖X k ω - X k' ω‖ₑ ∂P
        = ∫⁻ ω, ‖V T ω - V t ω‖ₑ ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlin T ⟨hT.le, le_rfl⟩, hlin t ht] with ω h1 h2
          simp only [hXdef]
          rw [show I k T ω - I k t ω - (I k' T ω - I k' t ω)
            = (I k T ω - I k' T ω) - (I k t ω - I k' t ω) by ring, h1, h2]
      _ ≤ ∫⁻ ω, 2 * ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞) ∂P := by
          refine lintegral_mono fun ω => ?_
          calc ‖V T ω - V t ω‖ₑ ≤ ‖V T ω‖ₑ + ‖V t ω‖ₑ := enorm_sub_le
            _ = (‖V T ω‖₊ : ℝ≥0∞) + ‖V t ω‖₊ := by simp only [enorm_eq_nnnorm]
            _ ≤ _ := by
                rw [two_mul]
                exact add_le_add (hsupV ω T ⟨hT.le, le_rfl⟩) (hsupV ω t ht)
      _ = 2 * ∫⁻ ω, ⨆ t ∈ Icc (0 : ℝ) T, (‖V t ω‖₊ : ℝ≥0∞) ∂P :=
          lintegral_const_mul' _ _ (by norm_num)
      _ ≤ 2 * (9 * ∫⁻ ω, (∫⁻ s in Icc (0 : ℝ) T, ∫⁻ e,
            (‖D ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ) ∂P) := by gcongr
      _ ≤ 2 * (9 * ∫⁻ ω, g k ω ∂P) := by
          gcongr with ω
          simp only [hgdef]
          gcongr with s
          by_cases h1 : ((s : ℝ) : WithTop ℝ) ≤ τ k ω
          · have : ∀ e, D ω s e = 0 := fun e => by
              simp only [hDdef, hcut, if_pos h1, if_pos (h1.trans (hmono ω hkk')), sub_self]
            simp only [this, if_neg (not_lt.mpr h1)]
            simp
          · rw [if_pos (not_le.mp h1)]
            refine lintegral_mono fun e => ?_
            have := hDle ω s e
            have h2 : |cut k' ω s e| ≤ |φ ω s e| := by
              simp only [hcut]
              split_ifs
              · exact le_rfl
              · simp
            gcongr
            exact_mod_cast (this.trans h2 : |D ω s e| ≤ |φ ω s e|)
      _ = 18 * ∫⁻ ω, g k ω ∂P := by rw [← mul_assoc]; norm_num
  have hε : Tendsto (fun k => 18 * ∫⁻ ω, g k ω ∂P) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hg0 (Or.inr (by norm_num : (18 : ℝ≥0∞) ≠ ⊤))
  exact integrable_and_integral_eq_zero_of_cauchy hXi hX0 hY hlim hε hC

end Compensated

end Dissertation.WellPosedness.Martingale
