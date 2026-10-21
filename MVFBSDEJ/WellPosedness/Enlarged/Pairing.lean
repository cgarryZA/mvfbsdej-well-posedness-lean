/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.MarkCoding.Representation

/-!
# Product characters against a weight with a time-zero factor

Let `ℱ` be a filtration carrying a multidimensional Brownian motion `W` and a Poisson random
measure `N`, and let `Z` be a square-integrable weight orthogonal to every coordinate's Itô
integrals and to the compensated integral of every admissible integrand. The grid induction of
the joint predictable representation property shows that `Z` integrates to zero against every
product of a Brownian cylinder character and a window character, starting from `E[Z] = 0`.

The induction starts equally well from a bounded complex weight `g` measurable for `ℱ₀` with
`E[Z g] = 0`: at every cell the factor carried along is `g` times the joint character of the
earlier cells, which is bounded and measurable at the left end of the cell, so the one-cell lemma
applies unchanged. Hence

`E[e^{i ∑ w_p W_{t_p}} · e^{i ∑ v_B N(B)} · g · Z] = 0`.

For `g = 1` this is the vanishing of the pairing of `Z` with every product character.

The induction places the windows in a set of marks of finite intensity containing a given mark.
On an empty mark space every window is empty and every window character is `1`. The image of `N`
under the constant map to a one-point mark space is then a Poisson random measure for `ℱ` of
intensity zero, the compensated integral of each of its admissible integrands is almost surely
that of the integrand read through the constant map against `N`, and the statement for the image
without windows is the statement for `N`.

## Main statements

* `pairing_jointGridCharacterMultidim_mul_eq_zero` — the grid induction from a time-zero weight.
* `pairing_joint_value_characterMultidim_mul_eq_zero` — value characters along a grid.
* `pairing_char_joint_mul_eq_zero` — product characters times a time-zero weight.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MVFBSDEJ.WellPosedness.Enlarged

open LevyStochCalc LevyStochCalc.Driver
open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Grid

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)
  (ℱ : MeasureTheory.Filtration ℝ mΩ)

/-- **The multidimensional joint grid induction from a time-zero weight.** For a weight `Z`
orthogonal to every coordinate's Itô integrals and to every compensated integral, and a bounded
complex weight `g` measurable at time `0` with `E[Z g] = 0`, the pairing of `Z` with `g` times
the joint character of the first `n` cells of a grid vanishes. -/
theorem pairing_jointGridCharacterMultidim_mul_eq_zero (hd : 0 < d)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱN : IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {T : ℝ} (hT : 0 < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {g : Ω → ℂ} (hgm : StronglyMeasurable[ℱ 0] g) {Mg : ℝ} (hgb : ∀ ω, ‖g ω‖ ≤ Mg)
    (hZg : ∫ ω, ((Z ω : ℝ) : ℂ) * g ω ∂P = 0) (lam : ℕ → Fin d → ℝ) :
    ∀ n : ℕ, (∀ k, k < n → τ k < τ (k + 1)) → τ n < T →
      ∫ ω, ((Z ω : ℝ) : ℂ) * (g ω * jointGridCharacterMultidim W N τ lam w Bfam n ω) ∂P
        = 0 := by
  intro n
  induction n with
  | zero =>
      intro _ _
      have h1 : ∀ ω : Ω, ((Z ω : ℝ) : ℂ)
          * (g ω * jointGridCharacterMultidim W N τ lam w Bfam 0 ω)
          = ((Z ω : ℝ) : ℂ) * g ω := by
        intro ω; rw [jointGridCharacterMultidim]; simp
      simp_rw [h1]
      exact hZg
  | succ n ih =>
      intro hlt hTn
      have hlt' : ∀ k, k < n → τ k < τ (k + 1) := fun k hk => hlt k (Nat.lt_succ_of_lt hk)
      have hle' : ∀ k, k < n → τ k ≤ τ (k + 1) := fun k hk => (hlt' k hk).le
      have hcell : τ n < τ (n + 1) := hlt n (Nat.lt_succ_self n)
      have hτn0 : 0 ≤ τ n := grid_nonneg hτ0 hle' (le_refl n)
      have hmeas := measurable_jointGridCharacterMultidim W N hℱi hℱN hle' lam w hBm
      have hVm : StronglyMeasurable[ℱ (τ n)]
          fun ω => g ω * jointGridCharacterMultidim W N τ lam w Bfam n ω :=
        (hgm.mono (ℱ.mono hτn0)).mul hmeas.stronglyMeasurable
      have hVb : ∀ ω, ‖g ω * jointGridCharacterMultidim W N τ lam w Bfam n ω‖ ≤ max Mg 0 := by
        intro ω
        rw [norm_mul, norm_jointGridCharacterMultidim, mul_one]
        exact (hgb ω).trans (le_max_left _ _)
      have hstep := pairing_cell_multidim_joint_eq_zero W N ℱ hd hℱi hℱB hℱN hℱ0 hnull
        hτn0 hcell hT hTn hA hAν w (measurableSet_cellFam hBm τ n)
        (cellFam_subset hBsub τ n) he₀ hZ2 hperp hZcomp
        (V := fun ω => g ω * jointGridCharacterMultidim W N τ lam w Bfam n ω) hVm
        (Mv := max Mg 0) (le_max_right _ _) hVb (ih hlt' (lt_trans hcell hTn)) (lam n)
      have hrw : ∀ ω : Ω, ((Z ω : ℝ) : ℂ)
          * (g ω * jointGridCharacterMultidim W N τ lam w Bfam (n + 1) ω)
          = ((Z ω : ℝ) : ℂ) * (g ω * jointGridCharacterMultidim W N τ lam w Bfam n ω)
            * (Complex.exp (Complex.I * ((∑ i, lam n i
                * ((W.W i).W (τ (n + 1)) ω - (W.W i).W (τ n) ω) : ℝ) : ℂ))
              * charAt N w (cellFam Bfam τ n) (τ (n + 1)) ω) := by
        intro ω
        rw [jointGridCharacterMultidim, jointGridCharacterMultidim, Finset.prod_range_succ]
        ring
      simpa only [hrw] using hstep

/-- **Value characters along a joint grid, from a time-zero weight.** For a weight `Z`
orthogonal to every coordinate's Itô integrals and to every compensated integral, and a bounded
complex weight `g` measurable at time `0` with `E[Z g] = 0`, the pairing of `Z` with `g` times a
character of the Brownian values at the grid points and the Poisson counts before the last grid
point vanishes. -/
theorem pairing_joint_value_characterMultidim_mul_eq_zero (hd : 0 < d)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱN : IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {T : ℝ} (hT : 0 < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {g : Ω → ℂ} (hgm : StronglyMeasurable[ℱ 0] g) {Mg : ℝ} (hgb : ∀ ω, ‖g ω‖ ≤ Mg)
    (hZg : ∫ ω, ((Z ω : ℝ) : ℂ) * g ω ∂P = 0) (c : ℕ → Fin d → ℝ) (n : ℕ)
    (hlt : ∀ k, k < n → τ k < τ (k + 1)) (hTn : τ n < T) :
    ∫ ω, ((Z ω : ℝ) : ℂ)
        * (g ω * (Complex.exp (Complex.I * ((∑ i, ∑ k ∈ Finset.Ico 1 (n + 1),
            c k i * (W.W i).W (τ k) ω : ℝ) : ℂ))
          * charAt N w Bfam (τ n) ω)) ∂P = 0 := by
  have hle' : ∀ k, k < n → τ k ≤ τ (k + 1) := fun k hk => (hlt k hk).le
  have hkey := pairing_jointGridCharacterMultidim_mul_eq_zero W N ℱ hd hℱi hℱB hℱN hℱ0 hnull
    hτ0 hT hA hAν w hBm hBsub he₀ hZ2 hperp hZcomp hgm hgb hZg
    (fun k i => ∑ j ∈ Finset.Ico (k + 1) (n + 1), c j i) n hlt hTn
  refine Eq.trans (integral_congr_ae ?_) hkey
  have hinit : ∀ᵐ ω ∂P, ∀ i : Fin d, (W.W i).W 0 ω = 0 :=
    ae_all_iff.mpr fun i => (W.W i).initial_zero
  filter_upwards [hinit, ae_charAt_eq_prod_cellFam N w hBm hA hAν hBsub hτ0 hle'] with ω hω hprod
  have heq : (∑ k ∈ Finset.range n, ∑ i, (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j i)
        * ((W.W i).W (τ (k + 1)) ω - (W.W i).W (τ k) ω))
      = ∑ i, ∑ k ∈ Finset.Ico 1 (n + 1), c k i * (W.W i).W (τ k) ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      sum_tail_mul_sub (fun k => c k i) (Wv := fun k => (W.W i).W (τ k) ω)
        (by rw [hτ0]; exact hω i) n
  rw [← heq, hprod, jointGridCharacterMultidim, Finset.prod_mul_distrib, ← Complex.exp_sum,
    Complex.ofReal_sum, Finset.mul_sum]

end Grid

section Characters

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)
  (ℱ : MeasureTheory.Filtration ℝ mΩ) {T : ℝ}

/-- Product characters times a time-zero weight, on a nonempty mark space. -/
private theorem pairing_char_joint_mul_eq_zero_of_nonempty [Nonempty E] (hd : 0 < d)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱN : IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {g : Ω → ℂ} (hgm : StronglyMeasurable[ℱ 0] g) {Mg : ℝ} (hgb : ∀ ω, ‖g ω‖ ≤ Mg)
    (hZg : ∫ ω, ((Z ω : ℝ) : ℂ) * g ω ∂P = 0) (F : Finset (Fin d × Set.Iic T))
    (G : Finset (Poisson.WindowSet E ν T)) (w : F → ℝ) (v : G → ℝ) :
    ∫ ω, Complex.exp (((∑ p : F, (W.W p.1.1).W (p.1.2 : ℝ) ω * w p : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((∑ B : G,
          (N.N ω ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))).toReal * v B : ℝ) : ℂ)
        * Complex.I) * g ω * ((Z ω : ℝ) : ℂ) ∂P = 0 := by
  classical
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, (Classical.arbitrary E) ∈ spanningSets ν n := by
    have : (Classical.arbitrary E) ∈ ⋃ n, spanningSets ν n := by
      rw [iUnion_spanningSets ν]; trivial
    exact Set.mem_iUnion.mp this
  set S : Finset ℝ := insert T (Analysis.posTimes F) with hSdef
  set τ : ℕ → ℝ := Analysis.sortedGrid S with hτdef
  have hSpos : ∀ x ∈ S, 0 < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hT
    · exact Analysis.pos_of_mem_posTimes hx
  have hSle : ∀ x ∈ S, x ≤ T := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact Analysis.le_of_mem_posTimes hx
  have hlt : ∀ k, k < S.card → τ k < τ (k + 1) := fun k hk =>
    Analysis.sortedGrid_lt_succ S hSpos hk
  have hTle : T ≤ τ S.card := Analysis.le_sortedGrid_card (Finset.mem_insert_self T _)
  have hleT : τ S.card ≤ T :=
    hSle _ (Analysis.sortedGrid_card_mem ⟨T, Finset.mem_insert_self T _⟩)
  have hTn : τ S.card < T + 1 := lt_of_le_of_lt hleT (by linarith)
  have hR : (0 : ℝ) < T + 1 := by linarith
  have hTR : T ≤ T + 1 := by linarith
  have hBm : ∀ B : G, MeasurableSet ((B : Poisson.WindowSet E ν T) : Set (ℝ × E)) :=
    fun B => (B : Poisson.WindowSet E ν T).measurableSet
  have hBsub : ∀ B : G, ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))
      ⊆ Set.Ioc (0 : ℝ) (T + 1) ×ˢ markUnion G n₀ := by
    intro B
    refine (subset_markSet (B : Poisson.WindowSet E ν T)).trans ?_
    exact Set.prod_mono (Set.Ioc_subset_Ioc le_rfl hTR)
      (markSet_subset_markUnion B.2 n₀)
  have hZcompR : ∀ G' : MarkedHorizonIntegrand P ν ℱ (T + 1),
      ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0 := fun G' =>
    Compensated.integral_mul_integral_eq_zero N hℱN hT hZ2 hZm hZcomp hTR G'
  have hkey := pairing_joint_value_characterMultidim_mul_eq_zero W N ℱ hd hℱi hℱB hℱN hℱ0
    hnull (τ := τ) (Analysis.sortedGrid_zero S) hR (measurableSet_markUnion G n₀)
    (markUnion_ne_top G n₀) v hBm hBsub (mem_markUnion G hn₀) hZ2 hperp hZcompR hgm hgb hZg
    (fun k i => Analysis.weightAt F w (τ k) i) S.card hlt hTn
  refine Eq.trans (integral_congr_ae ?_) hkey
  filter_upwards [ae_forall_eq_zero_of_nonpos W F] with ω hω
  have hBrown : (∑ p : F, (W.W p.1.1).W (p.1.2 : ℝ) ω * w p)
      = ∑ i, ∑ k ∈ Finset.Ico 1 (S.card + 1),
          Analysis.weightAt F w (τ k) i * (W.W i).W (τ k) ω :=
    Analysis.sum_weight_eq_sum_grid F w (fun i t => (W.W i).W t ω)
      (fun p hp => hω p.1 p.2 hp) (Finset.subset_insert _ _) hSpos
  have hwin : (∑ B : G,
        (N.N ω ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))).toReal * v B)
      = ∑ B : G, v B * (N.N ω (((B : Poisson.WindowSet E ν T) : Set (ℝ × E))
          ∩ Set.Ioc (0 : ℝ) (τ S.card) ×ˢ Set.univ)).toReal := by
    refine Finset.sum_congr rfl fun B _ => ?_
    have hsub : ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))
        ⊆ Set.Ioc (0 : ℝ) (τ S.card) ×ˢ Set.univ := by
      refine (subset_markSet (B : Poisson.WindowSet E ν T)).trans ?_
      exact Set.prod_mono (Set.Ioc_subset_Ioc le_rfl hTle) (Set.subset_univ _)
    rw [Set.inter_eq_self_of_subset_left hsub, mul_comm]
  have hE : ∀ x : ℝ, Complex.exp ((x : ℂ) * Complex.I)
      = Complex.exp (Complex.I * (x : ℂ)) := fun x => by rw [mul_comm]
  rw [hE, hE, hBrown, hwin, charAt]
  ring

/-- **Product characters times a time-zero weight.** A square-integrable weight `Z`, measurable
before the horizon, orthogonal to every coordinate's Itô integrals and to the compensated
integral of every admissible integrand, and a bounded complex weight `g` measurable at time `0`
with `E[Z g] = 0` satisfy `E[e^{i ∑ w_p W_{t_p}} · e^{i ∑ v_B N(B)} · g · Z] = 0` for every
product of a Brownian cylinder character and a window character. -/
theorem pairing_char_joint_mul_eq_zero (hd : 0 < d)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱN : IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {g : Ω → ℂ} (hgm : StronglyMeasurable[ℱ 0] g) {Mg : ℝ} (hgb : ∀ ω, ‖g ω‖ ≤ Mg)
    (hZg : ∫ ω, ((Z ω : ℝ) : ℂ) * g ω ∂P = 0) (F : Finset (Fin d × Set.Iic T))
    (G : Finset (Poisson.WindowSet E ν T)) (w : F → ℝ) (v : G → ℝ) :
    ∫ ω, Complex.exp (((∑ p : F, (W.W p.1.1).W (p.1.2 : ℝ) ω * w p : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((∑ B : G,
          (N.N ω ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))).toReal * v B : ℝ) : ℂ)
        * Complex.I) * g ω * ((Z ω : ℝ) : ℂ) ∂P = 0 := by
  rcases isEmpty_or_nonempty E with hE | hE
  · have hφ : Measurable fun _ : E => () := measurable_const
    haveI : SigmaFinite (ν.map fun _ : E => ()) := by
      rw [Measure.eq_zero_of_isEmpty ν, Measure.map_zero]
      infer_instance
    have hN' := MarkCoding.isPoissonFiltration_mapMarks hℱN hφ
    have hZcomp' : ∀ K : MarkedHorizonIntegrand P (ν.map fun _ : E => ()) ℱ T,
        ∫ ω, Z ω * K.integral (MarkCoding.PoissonRandomMeasure.mapMarks N hφ) hN' ω ∂P = 0 := by
      intro K
      rw [← hZcomp (MarkCoding.pullMarkedHorizonIntegrand hφ rfl K)]
      refine integral_congr_ae ?_
      filter_upwards [MarkCoding.integral_pullMarkedHorizonIntegrand hφ rfl N hℱN hN' K]
        with ω hK
      rw [hK]
    have h := pairing_char_joint_mul_eq_zero_of_nonempty W
      (MarkCoding.PoissonRandomMeasure.mapMarks N hφ) ℱ hd hℱi hℱB hN' hℱ0 hnull hT hZ2 hZm
      hperp hZcomp' hgm hgb hZg F ∅ w fun _ => 0
    refine Eq.trans (integral_congr_ae (Eventually.of_forall fun ω => ?_)) h
    have hB : ∀ B : G, N.N ω ((B : Poisson.WindowSet E ν T) : Set (ℝ × E)) = 0 := fun B => by
      rw [Set.eq_empty_of_isEmpty ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))]
      exact measure_empty
    simp [hB]
  · exact pairing_char_joint_mul_eq_zero_of_nonempty W N ℱ hd hℱi hℱB hℱN hℱ0 hnull hT hZ2 hZm
      hperp hZcomp hgm hgb hZg F G w v

end Characters

end MVFBSDEJ.WellPosedness.Enlarged
