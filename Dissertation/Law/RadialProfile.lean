/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.Mixture

/-!
# Radial law functionals with an arbitrary reference law

For a law `μ₀` of finite second moment on a real normed space, a vector `v` and `t ∈ [0, 1]`, the
mixtures `(1 − t) μ₀ + t δ_{R v}`, `R ∈ ℝ`, form a path of laws, `√t |v|`-Lipschitz in `R` for
`W₂`, starting within `√t (∫ |x|² dμ₀)^{1/2}` of `μ₀` and leaving every bounded set. A law
functional `μ ↦ q(D(μ))`, for a bounded profile `q` not constant on `[0, ∞)` and a distance-like
`D` vanishing at `μ₀` with these three properties along the path, is therefore not affine along
mixtures: the intermediate value theorem places the mixtures at every prescribed distance `r`,
while affinity forces `q(r)` within `2 t sup |q|` of `q(0)`.

## Main statements

* `Dissertation.Law.w2P_mix_dirac_mix_dirac_le` — `W₂((1 − t) μ + t δ_a, (1 − t) μ + t δ_b)
  ≤ √t |a − b|`.
* `Dissertation.Law.w2P_mix_dirac_self_le` — `W₂((1 − t) μ + t δ_0, μ) ≤ √t (∫ |x|² dμ)^{1/2}`.
* `Dissertation.Law.sqrt_mul_norm_le_w2P_mix_dirac` — `√t |c| ≤ W₂((1 − t) μ + t δ_c, δ_0)`.
* `Dissertation.Law.not_affineAlongMixtures_of_radialProfile` — a bounded profile of a distance
  with these properties along the path is not affine along mixtures.
-/

namespace Dissertation.Law

open MeasureTheory
open scoped ENNReal

section Couplings

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
/-- Mixing the diagonal coupling of `μ` with the Dirac mass at `(a, b)` couples
`(1 − t) μ + t δ_a` with `(1 − t) μ + t δ_b`. -/
theorem isCoupling_mix_dirac (t : ℝ) (μ : Measure E) (a b : E) :
    IsCoupling (ENNReal.ofReal (1 - t) • μ + ENNReal.ofReal t • Measure.dirac a)
      (ENNReal.ofReal (1 - t) • μ + ENNReal.ofReal t • Measure.dirac b)
      (ENNReal.ofReal (1 - t) • μ.map (fun x => (x, x))
        + ENNReal.ofReal t • Measure.dirac (a, b)) := by
  obtain ⟨h1, h2⟩ := isCoupling_diagonal μ
  refine ⟨?_, ?_⟩
  · rw [Measure.fst, Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
      ← Measure.fst, h1, Measure.map_dirac' measurable_fst]
  · rw [Measure.snd, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
      ← Measure.snd, h2, Measure.map_dirac' measurable_snd]

/-- **Two mixtures of one law with Dirac masses**: the distance of `(1 − t) μ + t δ_a` to
`(1 − t) μ + t δ_b` is at most `√t |a − b|`. -/
theorem w2P_mix_dirac_mix_dirac_le (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (μ : P2 E) (a b : E) :
    w2P (P2.mix t ht μ (P2.dirac a)) (P2.mix t ht μ (P2.dirac b)) ≤ Real.sqrt t * ‖a - b‖ := by
  have hc := w2sq_le_transportCostSq (isCoupling_mix_dirac t μ.law a b)
  have hcost : transportCostSq (ENNReal.ofReal (1 - t) • μ.law.map (fun x => (x, x))
      + ENNReal.ofReal t • Measure.dirac (a, b)) = ENNReal.ofReal (t * ‖a - b‖ ^ 2) := by
    rw [transportCostSq, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      ← transportCostSq, transportCostSq_diagonal, lintegral_dirac' _ measurable_normSq_sub]
    simp [ENNReal.ofReal_mul ht.1]
  rw [hcost] at hc
  have hle : (w2sq (P2.mix t ht μ (P2.dirac a)).law (P2.mix t ht μ (P2.dirac b)).law).toReal
      ≤ t * ‖a - b‖ ^ 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
    rwa [ENNReal.toReal_ofReal (mul_nonneg ht.1 (sq_nonneg _))] at this
  calc w2P (P2.mix t ht μ (P2.dirac a)) (P2.mix t ht μ (P2.dirac b))
      ≤ Real.sqrt (t * ‖a - b‖ ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt t * ‖a - b‖ := by
      rw [Real.sqrt_mul ht.1, Real.sqrt_sq (norm_nonneg _)]

omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
/-- Mixing the diagonal coupling of `μ` with the coupling of `δ_c` and `μ` couples
`(1 − t) μ + t δ_c` with `μ`. -/
theorem isCoupling_mix_dirac_self (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (μ : Measure E)
    [IsProbabilityMeasure μ] (c : E) :
    IsCoupling (ENNReal.ofReal (1 - t) • μ + ENNReal.ofReal t • Measure.dirac c) μ
      (ENNReal.ofReal (1 - t) • μ.map (fun x => (x, x))
        + ENNReal.ofReal t • μ.map (fun x => (c, x))) := by
  obtain ⟨h1, h2⟩ := isCoupling_diagonal μ
  obtain ⟨h3, h4⟩ := isCoupling_swap (isCoupling_dirac μ c)
  have e1 : (μ.map fun x => (x, c)).map Prod.swap = μ.map fun x => (c, x) := by
    rw [Measure.map_map measurable_swap (by fun_prop)]
    rfl
  rw [e1] at h3 h4
  refine ⟨?_, ?_⟩
  · rw [Measure.fst, Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_smul,
      ← Measure.fst, ← Measure.fst, h1, h3]
  · rw [Measure.snd, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
      ← Measure.snd, ← Measure.snd, h2, h4, ← add_smul,
      ← ENNReal.ofReal_add (by linarith [ht.2]) ht.1, sub_add_cancel, ENNReal.ofReal_one,
      one_smul]

/-- **A mixture with the Dirac mass at the origin is close to the law**: the distance of
`(1 − t) μ + t δ_0` to `μ` is at most `√t` times the square root of the second moment of `μ`. -/
theorem w2P_mix_dirac_self_le (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (μ : P2 E) :
    w2P (P2.mix t ht μ (P2.dirac 0)) μ ≤ Real.sqrt t * Real.sqrt (secondMoment μ.law).toReal := by
  have hc := w2sq_le_transportCostSq (isCoupling_mix_dirac_self t ht μ.law 0)
  have hcost : transportCostSq (ENNReal.ofReal (1 - t) • μ.law.map (fun x => (x, x))
      + ENNReal.ofReal t • μ.law.map (fun x => ((0 : E), x)))
      = ENNReal.ofReal t * secondMoment μ.law := by
    rw [transportCostSq, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      ← transportCostSq, transportCostSq_diagonal,
      lintegral_map measurable_normSq_sub (by fun_prop), secondMoment]
    simp
  rw [hcost] at hc
  have hfin : ENNReal.ofReal t * secondMoment μ.law ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top μ.secondMoment_ne_top
  have hle := ENNReal.toReal_mono hfin hc
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.1] at hle
  calc w2P (P2.mix t ht μ (P2.dirac 0)) μ
      ≤ Real.sqrt (t * (secondMoment μ.law).toReal) := Real.sqrt_le_sqrt hle
    _ = _ := Real.sqrt_mul ht.1 _

/-- **A mixture with a distant Dirac mass is far from the origin**: the distance of
`(1 − t) μ + t δ_c` to `δ_0` is at least `√t |c|`. -/
theorem sqrt_mul_norm_le_w2P_mix_dirac (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (μ : P2 E) (c : E) :
    Real.sqrt t * ‖c‖ ≤ w2P (P2.mix t ht μ (P2.dirac c)) (P2.dirac 0) := by
  have hm : Measurable fun x : E => ENNReal.ofReal (‖x - 0‖ ^ 2) := by fun_prop
  have hge : ENNReal.ofReal (t * ‖c‖ ^ 2)
      ≤ w2sq (P2.mix t ht μ (P2.dirac c)).law (P2.dirac (0 : E)).law := by
    rw [show (P2.dirac (0 : E)).law = Measure.dirac 0 from rfl, w2sq_dirac, P2.mix_law,
      lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      show (P2.dirac c).law = Measure.dirac c from rfl, lintegral_dirac' _ hm, sub_zero,
      ENNReal.ofReal_mul ht.1, smul_eq_mul, smul_eq_mul]
    exact le_add_self
  have h := ENNReal.toReal_mono (w2sq_ne_top _ _) hge
  rw [ENNReal.toReal_ofReal (mul_nonneg ht.1 (sq_nonneg _))] at h
  calc Real.sqrt t * ‖c‖ = Real.sqrt (t * ‖c‖ ^ 2) := by
        rw [Real.sqrt_mul ht.1, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ _ := Real.sqrt_le_sqrt h

end Couplings

section Profile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [MeasurableSingletonClass E]

/-- **A bounded profile of a distance growing along mixtures is not affine along mixtures.**
Let `F = q ∘ D` for a law functional `D` with `D(μ₀) = 0` and a bounded `q` with `q(a) ≠ q(b)` for
some `a, b ≥ 0`. Suppose that along the mixtures `(1 − t) μ₀ + t δ_{R v}`, `t ∈ [0, 1]`, `R ∈ ℝ`,
`D` is `K √t`-Lipschitz in `R`, at most `√t M` at `R = 0`, and at least `c √t R − C` for `R ≥ 0`,
with `c > 0`. Then `F` is not affine along mixtures. For `r > 0` and small `t`, the intermediate
value theorem gives `R` with `D = r` at the mixture, where affinity gives
`q(r) − q(0) = t (q(D(δ_{R v})) − q(0))`, of size at most `2 t sup |q|`; so `q` is constant on
`[0, ∞)`. -/
theorem not_affineAlongMixtures_of_radialProfile {F D : P2 E → ℝ} (μ₀ : P2 E) (v : E)
    {q : ℝ → ℝ} {B K M c C : ℝ} (hB : ∀ r, |q r| ≤ B)
    (hne : ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ q a ≠ q b) (hF : ∀ μ, F μ = q (D μ)) (hD0 : D μ₀ = 0)
    (hlip : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (a b : ℝ),
      |D (P2.mix t ht μ₀ (P2.dirac (a • v))) - D (P2.mix t ht μ₀ (P2.dirac (b • v)))|
        ≤ K * Real.sqrt t * |a - b|)
    (hsmall : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1),
      D (P2.mix t ht μ₀ (P2.dirac ((0 : ℝ) • v))) ≤ Real.sqrt t * M)
    (hc : 0 < c)
    (hlarge : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (R : ℝ), 0 ≤ R →
      c * Real.sqrt t * R - C ≤ D (P2.mix t ht μ₀ (P2.dirac (R • v)))) :
    ¬ AffineAlongMixtures F := by
  intro hAff
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have key : ∀ r, 0 < r → q r = q 0 := by
    intro r hr
    by_contra hne'
    have hδ : 0 < |q r - q 0| := abs_pos.mpr (sub_ne_zero.mpr hne')
    set δ := |q r - q 0| with hδdef
    set t : ℝ := min (1 / 2) (min (δ / (4 * (B + 1))) (r ^ 2 / (4 * (M ^ 2 + 1)))) with htdef
    have ht0 : 0 < t := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
    have ht1 : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0.le, ht1⟩
    have htδ : t ≤ δ / (4 * (B + 1)) := (min_le_right _ _).trans (min_le_left _ _)
    have htr : t ≤ r ^ 2 / (4 * (M ^ 2 + 1)) := (min_le_right _ _).trans (min_le_right _ _)
    have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have hsm : Real.sqrt t * M < r := by
      have h1 : Real.sqrt t * M ≤ Real.sqrt t * |M| :=
        mul_le_mul_of_nonneg_left (le_abs_self M) hsqt.le
      have h2 : (Real.sqrt t * |M|) ^ 2 < r ^ 2 := by
        rw [mul_pow, Real.sq_sqrt ht0.le, sq_abs]
        have h3 : t * M ^ 2 ≤ r ^ 2 / (4 * (M ^ 2 + 1)) * M ^ 2 :=
          mul_le_mul_of_nonneg_right htr (sq_nonneg M)
        have h4 : r ^ 2 / (4 * (M ^ 2 + 1)) * M ^ 2 < r ^ 2 := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [sq_nonneg M, pow_pos hr 2]
        linarith
      have h5 : Real.sqrt t * |M| < r :=
        lt_of_pow_lt_pow_left₀ 2 hr.le h2
      linarith
    set g : ℝ → ℝ := fun R => D (P2.mix t ht μ₀ (P2.dirac (R • v))) with hgdef
    have hgc : Continuous g := by
      have hL : LipschitzWith (Real.toNNReal (K * Real.sqrt t)) g :=
        LipschitzWith.of_dist_le_mul fun a b => by
          rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
          exact (hlip t ht a b).trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
      exact hL.continuous
    set R1 := max 0 ((r + C) / (c * Real.sqrt t)) with hR1def
    have hR1 : r ≤ g R1 := by
      have h1 := hlarge t ht R1 (le_max_left _ _)
      have h2 : r + C ≤ c * Real.sqrt t * R1 := by
        have h3 : (r + C) / (c * Real.sqrt t) ≤ R1 := le_max_right _ _
        rwa [div_le_iff₀ (by positivity), mul_comm] at h3
      simp only [hgdef]
      linarith
    have hg0 : g 0 ≤ r := (hsmall t ht).trans hsm.le
    obtain ⟨R, -, hR⟩ :=
      intermediate_value_Icc (le_max_left 0 _) hgc.continuousOn ⟨hg0, hR1⟩
    have haff := hAff t ht μ₀ (P2.dirac (R • v))
    rw [hF, hF, hF, hD0] at haff
    have hgR : D (P2.mix t ht μ₀ (P2.dirac (R • v))) = r := hR
    rw [hgR] at haff
    have he : q r - q 0 = t * (q (D (P2.dirac (R • v))) - q 0) := by rw [haff]; ring
    have hbound : δ ≤ t * (2 * B) := by
      rw [hδdef, he, abs_mul, abs_of_pos ht0]
      refine mul_le_mul_of_nonneg_left ?_ ht0.le
      have h1 := abs_le.mp (hB (D (P2.dirac (R • v))))
      have h2 := abs_le.mp (hB 0)
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hlt : t * (2 * B) < δ := by
      calc t * (2 * B) ≤ δ / (4 * (B + 1)) * (2 * B) :=
            mul_le_mul_of_nonneg_right htδ (by positivity)
        _ < δ := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
    linarith
  obtain ⟨a, b, ha, hb, hab⟩ := hne
  have hq : ∀ x, 0 ≤ x → q x = q 0 := fun x hx => by
    rcases hx.lt_or_eq with h | h
    · exact key x h
    · rw [← h]
  exact hab ((hq a ha).trans (hq b hb).symm)

end Profile

end Dissertation.Law
