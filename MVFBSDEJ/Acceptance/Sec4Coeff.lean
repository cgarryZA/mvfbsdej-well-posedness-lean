/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec4Coeff
import MVFBSDEJ.WellPosedness.Robustness.JumpMargin

/-!
# The coefficient bounds (4.2) and (4.3) of the well-posedness paper: proofs

## Main statements

* `MVFBSDEJ.Acceptance.lintegral_sq_le_of_lip` — the second moment of a map Lipschitz in
  the tuple and its law, against the origin and `δ₀`.
* `MVFBSDEJ.Acceptance.eq_coeffint` — (4.2), with `K(L) = 2 + 20 L²`.
* `MVFBSDEJ.Acceptance.eq_termg` — (4.3), with `K(L) = 2 + 8 L²`.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Spec MVFBSDEJ.Law

universe u v

/-- `x ≤ f + |L| (a + b + c + e + W)` with all terms nonnegative gives
`x² ≤ 2 f² + 10 L² W² + 10 L² (a² + b² + c² + e²)`. -/
theorem sq_le_of_le_add_abs_mul {x f L a b c e W : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e) (hW : 0 ≤ W)
    (hn : x ≤ f + |L| * (a + b + c + e + W)) :
    x ^ 2 ≤ 2 * f ^ 2 + 10 * L ^ 2 * W ^ 2 + 10 * L ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2) := by
  have hs : (a + b + c + e + W) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + e ^ 2 + W ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (a - W),
      sq_nonneg (b - c), sq_nonneg (b - e), sq_nonneg (b - W), sq_nonneg (c - e),
      sq_nonneg (c - W), sq_nonneg (e - W)]
  set S := a + b + c + e + W with hS
  have hS0 : 0 ≤ S := by positivity
  have hL2 : |L| ^ 2 = L ^ 2 := sq_abs L
  have h1 : x ^ 2 ≤ (f + |L| * S) ^ 2 := pow_le_pow_left₀ hx hn 2
  have h2 : (f + |L| * S) ^ 2 ≤ 2 * f ^ 2 + 2 * L ^ 2 * S ^ 2 := by
    nlinarith [sq_nonneg (f - |L| * S)]
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * L ^ 2)]

/-- A map that is `L`-Lipschitz in the tuple and its law against the zero tuple, along a
square-integrable random tuple `Θ`, has
`𝔼 ‖F(Θ, Law Θ)‖² ≤ (2 + 20 L²) (𝔼 (|X|² + |Y|² + |Z|²_F + ‖U‖²) + ‖F(0, δ₀)‖²)`. -/
theorem lintegral_sq_le_of_lip {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
    [MeasurableSpace.CountablyGenerated E] {n m d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {V : Type*} [NormedAddCommGroup V] (L : ℝ)
    {Θ : Ω → TupleH ν n m d} (hΘ : MemLp Θ 2 P)
    (F : TupleH ν n m d → P2 (TupleH ν n m d) → V)
    (hF : ∀ᵐ ω ∂P, ‖F (Θ ω) (lawP2 P Θ) - F 0 (P2.dirac 0)‖
      ≤ L * (‖(Θ ω).1‖ + ‖(Θ ω).2.1‖ + ‖(Θ ω).2.2.1‖ + ‖(Θ ω).2.2.2‖
        + w2H (lawP2 P Θ) (P2.dirac 0))) :
    ∫⁻ ω, ‖F (Θ ω) (lawP2 P Θ)‖ₑ ^ 2 ∂P
      ≤ ENNReal.ofReal (2 + 20 * L ^ 2) * ∫⁻ ω, (‖(Θ ω).1‖ₑ ^ 2 + ‖(Θ ω).2.1‖ₑ ^ 2
        + ‖(Θ ω).2.2.1‖ₑ ^ 2 + ‖(Θ ω).2.2.2‖ₑ ^ 2 + ‖F 0 (P2.dirac 0)‖ₑ ^ 2) ∂P := by
  have h0 : MemLp (fun _ : Ω => (0 : TupleH ν n m d)) 2 P := memLp_const 0
  have hlaw : lawP2 P (fun _ : Ω => (0 : TupleH ν n m d)) = P2.dirac 0 := lawP2_const 0
  set W := w2H (lawP2 P Θ) (P2.dirac 0) with hW
  have hint : Integrable (fun ω => channelSq (Θ ω)) P := by
    simpa using integrable_channelSq_sub hΘ h0
  have hW2 : W ^ 2 ≤ ∫ ω, channelSq (Θ ω) ∂P := by
    have := w2H_lawP2_sq_le hΘ h0
    simpa [hlaw] using this
  have hW0 : 0 ≤ W := w2H_nonneg _ _
  set F₀ := F 0 (P2.dirac 0)
  have key : ∀ᵐ ω ∂P, ‖F (Θ ω) (lawP2 P Θ)‖ₑ ^ 2
      ≤ ENNReal.ofReal (2 * ‖F₀‖ ^ 2 + 10 * L ^ 2 * W ^ 2)
        + ENNReal.ofReal (10 * L ^ 2) * ENNReal.ofReal (channelSq (Θ ω)) := by
    filter_upwards [hF] with ω hω
    have hn : ‖F (Θ ω) (lawP2 P Θ)‖ ≤ ‖F₀‖ + |L| * (‖(Θ ω).1‖ + ‖(Θ ω).2.1‖ + ‖(Θ ω).2.2.1‖
        + ‖(Θ ω).2.2.2‖ + W) := by
      have h1 := norm_le_insert' (F (Θ ω) (lawP2 P Θ)) F₀
      have h2 := mul_le_mul_of_nonneg_right (le_abs_self L) (by positivity :
        (0 : ℝ) ≤ ‖(Θ ω).1‖ + ‖(Θ ω).2.1‖ + ‖(Θ ω).2.2.1‖ + ‖(Θ ω).2.2.2‖ + W)
      linarith
    have hsq := sq_le_of_le_add_abs_mul (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _) hW0 hn
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (mul_nonneg (by positivity) (channelSq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (by simp only [channelSq]; linarith)
  have hI : ∫⁻ ω, ENNReal.ofReal (channelSq (Θ ω)) ∂P
      = ENNReal.ofReal (∫ ω, channelSq (Θ ω) ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => channelSq_nonneg _)).symm
  have hJ : 0 ≤ ∫ ω, channelSq (Θ ω) ∂P := integral_nonneg fun ω => channelSq_nonneg _
  have hR : ∫⁻ ω, (‖(Θ ω).1‖ₑ ^ 2 + ‖(Θ ω).2.1‖ₑ ^ 2 + ‖(Θ ω).2.2.1‖ₑ ^ 2 + ‖(Θ ω).2.2.2‖ₑ ^ 2
      + ‖F₀‖ₑ ^ 2) ∂P = ENNReal.ofReal (∫ ω, channelSq (Θ ω) ∂P + ‖F₀‖ ^ 2) := by
    rw [ENNReal.ofReal_add hJ (by positivity), ← hI, lintegral_add_right _ measurable_const,
      lintegral_const, measure_univ, mul_one, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    congr 1
    refine lintegral_congr fun ω => ?_
    simp only [channelSq]
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  calc ∫⁻ ω, ‖F (Θ ω) (lawP2 P Θ)‖ₑ ^ 2 ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * ‖F₀‖ ^ 2 + 10 * L ^ 2 * W ^ 2)
          + ENNReal.ofReal (10 * L ^ 2) * ENNReal.ofReal (channelSq (Θ ω))) ∂P :=
        lintegral_mono_ae key
    _ = ENNReal.ofReal (2 * ‖F₀‖ ^ 2 + 10 * L ^ 2 * W ^ 2)
          + ENNReal.ofReal (10 * L ^ 2) * ENNReal.ofReal (∫ ω, channelSq (Θ ω) ∂P) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hI]
    _ ≤ _ := by
        rw [hR, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [sq_nonneg L, sq_nonneg ‖F₀‖]

/-- The time integral of the bound of `lintegral_sq_le_of_lip`. -/
theorem lintegral_time_sq_le_of_lip {E : Type*} [MeasurableSpace E] {ν : Measure E}
    [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {V : Type*}
    [NormedAddCommGroup V] (L T : ℝ) {Θ : ℝ → Ω → TupleH ν n m d}
    (hΘ : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (Θ t) 2 P)
    (F : ℝ → TupleH ν n m d → P2 (TupleH ν n m d) → V)
    (hF : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      ‖F t (Θ t ω) (lawP2 P (Θ t)) - F t 0 (P2.dirac 0)‖
        ≤ L * (‖(Θ t ω).1‖ + ‖(Θ t ω).2.1‖ + ‖(Θ t ω).2.2.1‖ + ‖(Θ t ω).2.2.2‖
          + w2H (lawP2 P (Θ t)) (P2.dirac 0))) :
    ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ω, ‖F t (Θ t ω) (lawP2 P (Θ t))‖ₑ ^ 2 ∂P
      ≤ ENNReal.ofReal (2 + 20 * L ^ 2) * ∫⁻ t in Set.Icc (0 : ℝ) T, ∫⁻ ω, (‖(Θ t ω).1‖ₑ ^ 2
        + ‖(Θ t ω).2.1‖ₑ ^ 2 + ‖(Θ t ω).2.2.1‖ₑ ^ 2 + ‖(Θ t ω).2.2.2‖ₑ ^ 2
        + ‖F t 0 (P2.dirac 0)‖ₑ ^ 2) ∂P := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hΘ, hF] with t h1 h2
  exact lintegral_sq_le_of_lip L h1 (F t) h2

/-- (4.2), with `K(L) = 2 + 20 L²`. -/
theorem eq_coeffint : PaperSpec.eq_coeffint.{u, v} := by
  refine ⟨fun L => 2 + 20 * L ^ 2, ?_⟩
  intro Ω mΩ ℱ P _ E _ ν _ _ n m d T L C hL Θ hΘ
  have hlaw : lawP2 P (fun _ : Ω => (0 : TupleH ν n m d)) = P2.dirac 0 := lawP2_const 0
  have hsum : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      ‖C.b t (Θ t ω) (lawP2 P (Θ t)) - C.b t 0 (P2.dirac 0)‖
        + ‖C.σ t (Θ t ω) (lawP2 P (Θ t)) - C.σ t 0 (P2.dirac 0)‖
        + ‖C.h t (Θ t ω) (lawP2 P (Θ t)) - C.h t 0 (P2.dirac 0)‖
        + ‖C.f t (Θ t ω) (lawP2 P (Θ t)) - C.f t 0 (P2.dirac 0)‖
      ≤ L * (‖(Θ t ω).1‖ + ‖(Θ t ω).2.1‖ + ‖(Θ t ω).2.2.1‖ + ‖(Θ t ω).2.2.2‖
        + w2H (lawP2 P (Θ t)) (P2.dirac 0)) := by
    filter_upwards [hL, hΘ] with t ht hΘt
    have h := ht (Θ t, lawP2 P (Θ t)) ⟨hΘt.1, hΘt.2, rfl⟩
      ((fun _ => 0), lawP2 P (fun _ : Ω => (0 : TupleH ν n m d)))
      ⟨stronglyMeasurable_const, memLp_const 0, rfl⟩
    simpa only [hlaw, Prod.fst_zero, Prod.snd_zero, sub_zero] using h
  have hΘ2 : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (Θ t) 2 P :=
    hΘ.mono fun t h => h.2
  refine ⟨lintegral_time_sq_le_of_lip L T hΘ2 (fun t => C.b t) ?_,
    lintegral_time_sq_le_of_lip L T hΘ2 (fun t => C.σ t) ?_,
    lintegral_time_sq_le_of_lip L T hΘ2 (fun t => C.h t) ?_,
    lintegral_time_sq_le_of_lip L T hΘ2 (fun t => C.f t) ?_⟩ <;>
  · filter_upwards [hsum] with t ht
    filter_upwards [ht] with ω hω
    refine le_trans ?_ hω
    linarith [norm_nonneg (C.b t (Θ t ω) (lawP2 P (Θ t)) - C.b t 0 (P2.dirac 0)),
      norm_nonneg (C.σ t (Θ t ω) (lawP2 P (Θ t)) - C.σ t 0 (P2.dirac 0)),
      norm_nonneg (C.h t (Θ t ω) (lawP2 P (Θ t)) - C.h t 0 (P2.dirac 0)),
      norm_nonneg (C.f t (Θ t ω) (lawP2 P (Θ t)) - C.f t 0 (P2.dirac 0))]

/-- (4.3), with `K(L) = 2 + 8 L²`. -/
theorem eq_termg : PaperSpec.eq_termg.{u} := by
  refine ⟨fun L => 2 + 8 * L ^ 2, ?_⟩
  intro Ω mΩ ℱ P _ n m T L g hg XT hXs hX
  have h0 : MemLp (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin n))) 2 P := memLp_const 0
  have hlaw : lawP2 P (fun _ : Ω => (0 : EuclideanSpace ℝ (Fin n))) = P2.dirac 0 := lawP2_const 0
  set W := w2P (lawP2 P XT) (P2.dirac 0) with hW
  have hW2 : W ^ 2 ≤ ∫ ω, ‖XT ω‖ ^ 2 ∂P := by
    have := w2P_lawP2_sq_le hX h0
    simpa [hlaw] using this
  have hW0 : 0 ≤ W := w2P_nonneg _ _
  set g₀ := g 0 (P2.dirac 0)
  have hpt := hg XT (fun _ => 0) hXs stronglyMeasurable_const hX h0
  rw [hlaw] at hpt
  have key : ∀ᵐ ω ∂P, ‖g (XT ω) (lawP2 P XT)‖ₑ ^ 2
      ≤ ENNReal.ofReal (2 * ‖g₀‖ ^ 2 + 4 * L ^ 2 * W ^ 2)
        + ENNReal.ofReal (4 * L ^ 2) * ‖XT ω‖ₑ ^ 2 := by
    filter_upwards [hpt] with ω hω
    simp only [sub_zero] at hω
    have hn : ‖g (XT ω) (lawP2 P XT)‖ ≤ ‖g₀‖ + |L| * (‖XT ω‖ + W) := by
      have h1 := norm_le_insert' (g (XT ω) (lawP2 P XT)) g₀
      have h2 : L * (‖XT ω‖ + W) ≤ |L| * (‖XT ω‖ + W) :=
        mul_le_mul_of_nonneg_right (le_abs_self L) (by positivity)
      linarith
    have hsq : ‖g (XT ω) (lawP2 P XT)‖ ^ 2
        ≤ 2 * ‖g₀‖ ^ 2 + 4 * L ^ 2 * W ^ 2 + 4 * L ^ 2 * ‖XT ω‖ ^ 2 := by
      have ha : 0 ≤ ‖g (XT ω) (lawP2 P XT)‖ := norm_nonneg _
      have hL2 : |L| ^ 2 = L ^ 2 := sq_abs L
      nlinarith [sq_nonneg (‖g₀‖ - |L| * (‖XT ω‖ + W)), sq_nonneg (‖XT ω‖ - W), abs_nonneg L,
        norm_nonneg (XT ω), norm_nonneg g₀, mul_le_mul hn hn ha (by positivity)]
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc ∫⁻ ω, ‖g (XT ω) (lawP2 P XT)‖ₑ ^ 2 ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * ‖g₀‖ ^ 2 + 4 * L ^ 2 * W ^ 2)
          + ENNReal.ofReal (4 * L ^ 2) * ‖XT ω‖ₑ ^ 2) ∂P := lintegral_mono_ae key
    _ = ENNReal.ofReal (2 * ‖g₀‖ ^ 2 + 4 * L ^ 2 * W ^ 2)
          + ENNReal.ofReal (4 * L ^ 2) * ∫⁻ ω, ‖XT ω‖ₑ ^ 2 ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 + 8 * L ^ 2) * (∫⁻ ω, ‖XT ω‖ₑ ^ 2 ∂P + ‖g₀‖ₑ ^ 2) := by
        have hint : Integrable (fun ω => ‖XT ω‖ ^ 2) P := hX.integrable_norm_pow two_ne_zero
        have hI : ∫⁻ ω, ‖XT ω‖ₑ ^ 2 ∂P = ENNReal.ofReal (∫ ω, ‖XT ω‖ ^ 2 ∂P) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => by positivity)]
          refine lintegral_congr fun ω => ?_
          rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
        have hJ : 0 ≤ ∫ ω, ‖XT ω‖ ^ 2 ∂P := integral_nonneg fun ω => by positivity
        have hg₀ : ‖g₀‖ₑ ^ 2 = ENNReal.ofReal (‖g₀‖ ^ 2) := by
          rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
        rw [hI, hg₀, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity), ← ENNReal.ofReal_add hJ (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [sq_nonneg L, sq_nonneg ‖g₀‖]

end MVFBSDEJ.Acceptance
