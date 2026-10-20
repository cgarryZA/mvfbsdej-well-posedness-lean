/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.Law.LawP2
import MVFBSDEJ.Law.Projection
import MVFBSDEJ.WellPosedness.System.Tuple

/-!
# The 2-Wasserstein distance for the Hilbert norm of the tuple space

The tuple space `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)` of the well-posedness paper carries the
Hilbert norm `|θ|_H = (|x|² + |y|² + |z|²_F + ‖u‖²_{L²(ν)})^{1/2}`, and the paper's `W₂` on
`P₂(H)` is the 2-Wasserstein distance for that norm. The product `Tuple` carries instead the
maximum of its four channel norms, for which the 2-Wasserstein distance is `w2P`. This file
realises `H` with its Hilbert norm as the iterated `L²` product `TupleL2` of the four channels,
identified with `Tuple` by `toL2`, so that `|toL2 θ|² = channelSq θ`, and defines `w2H μ μ'` as
the 2-Wasserstein distance of the images of `μ` and `μ'` under `toL2`.

Since `‖θ‖ ≤ |toL2 θ| ≤ 2 ‖θ‖`, the two distances satisfy `w2P ≤ w2H ≤ 2 w2P`. For two
square-integrable random tuples `Θ, Θ'` on one probability space the synchronous coupling gives
the coupling bound (2.8) for the Hilbert norm,

`W₂(Law Θ, Law Θ')² ≤ 𝔼 (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)})`.

## Main definitions

* `TupleL2` — the tuple space with the Hilbert norm.
* `toL2`, `ofL2` — the identification of `Tuple` with `TupleL2` and its inverse.
* `w2H` — the 2-Wasserstein distance on the laws of finite second moment on the tuple space, for
  the Hilbert norm.

## Main statements

* `norm_toL2_sq` — `|toL2 θ|² = ‖x‖² + ‖y‖² + ‖z‖² + ‖u‖²`.
* `norm_le_norm_toL2`, `norm_toL2_le` — `‖θ‖ ≤ |toL2 θ| ≤ 2 ‖θ‖`.
* `w2sq_le_w2sq_map_toL2`, `w2sq_map_toL2_le` — the squared distances of two laws for the two
  norms are within a factor `4`.
* `w2P_le_w2H`, `w2H_le_two_mul_w2P` — `w2P ≤ w2H ≤ 2 w2P`.
* `w2H_lawP2_sq_le` — the coupling bound (2.8) for the Hilbert norm.
-/

open MeasureTheory MVFBSDEJ.Law
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.System

/-! ### The Hilbert norm on the tuple space -/

section Norm

/-- The tuple space `HX × HY × HZY × HUY` with the Hilbert norm
`(‖x‖² + ‖y‖² + ‖z‖² + ‖u‖²)^{1/2}`: the iterated `L²` product of its four channels. -/
abbrev TupleL2 (HX HY HZY HUY : Type*) [NormedAddCommGroup HX] [NormedAddCommGroup HY]
    [NormedAddCommGroup HZY] [NormedAddCommGroup HUY] : Type _ :=
  WithLp 2 (HX × WithLp 2 (HY × WithLp 2 (HZY × HUY)))

variable {HX HY HZY HUY : Type*} [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [NormedAddCommGroup HZY]
  [InnerProductSpace ℝ HZY] [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY]

/-- A tuple, as a point of the tuple space with the Hilbert norm. -/
def toL2 (θ : Tuple HX HY HZY HUY) : TupleL2 HX HY HZY HUY :=
  WithLp.toLp 2 (θ.1, WithLp.toLp 2 (θ.2.1, WithLp.toLp 2 (θ.2.2.1, θ.2.2.2)))

/-- A point of the tuple space with the Hilbert norm, as a tuple. -/
def ofL2 (w : TupleL2 HX HY HZY HUY) : Tuple HX HY HZY HUY :=
  ((WithLp.ofLp w).1, (WithLp.ofLp (WithLp.ofLp w).2).1,
    (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp w).2).2).1,
    (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp w).2).2).2)

/-- `ofL2` is a left inverse of `toL2`. -/
@[simp]
theorem ofL2_toL2 (θ : Tuple HX HY HZY HUY) : ofL2 (toL2 θ) = θ :=
  rfl

/-- `ofL2` is a right inverse of `toL2`. -/
@[simp]
theorem toL2_ofL2 (w : TupleL2 HX HY HZY HUY) : toL2 (ofL2 w) = w :=
  rfl

/-- `toL2` is additive on differences. -/
theorem toL2_sub (θ θ' : Tuple HX HY HZY HUY) : toL2 (θ - θ') = toL2 θ - toL2 θ' :=
  rfl

/-- **The Hilbert norm of a tuple**: `|toL2 θ|² = ‖x‖² + ‖y‖² + ‖z‖² + ‖u‖²`. -/
theorem norm_toL2_sq (θ : Tuple HX HY HZY HUY) : ‖toL2 θ‖ ^ 2 = channelSq θ := by
  simp only [toL2, channelSq, WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd]
  ring

/-- The maximum of the channel norms is at most the Hilbert norm. -/
theorem norm_le_norm_toL2 (θ : Tuple HX HY HZY HUY) : ‖θ‖ ≤ ‖toL2 θ‖ := by
  have h := norm_sq_le_channelSq θ
  rw [← norm_toL2_sq] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- The Hilbert norm is at most twice the maximum of the channel norms. -/
theorem norm_toL2_le (θ : Tuple HX HY HZY HUY) : ‖toL2 θ‖ ≤ 2 * ‖θ‖ := by
  have h1 : ‖θ.1‖ ≤ ‖θ‖ := norm_fst_le θ
  have h2 : ‖θ.2.1‖ ≤ ‖θ‖ := (norm_fst_le θ.2).trans (norm_snd_le θ)
  have h3 : ‖θ.2.2.1‖ ≤ ‖θ‖ :=
    ((norm_fst_le θ.2.2).trans (norm_snd_le θ.2)).trans (norm_snd_le θ)
  have h4 : ‖θ.2.2.2‖ ≤ ‖θ‖ :=
    ((norm_snd_le θ.2.2).trans (norm_snd_le θ.2)).trans (norm_snd_le θ)
  have h : ‖toL2 θ‖ ^ 2 ≤ (2 * ‖θ‖) ^ 2 := by
    rw [norm_toL2_sq, channelSq]
    have := norm_nonneg θ.1
    have := norm_nonneg θ.2.1
    have := norm_nonneg θ.2.2.1
    have := norm_nonneg θ.2.2.2
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- `toL2` is continuous. -/
theorem continuous_toL2 : Continuous (toL2 : Tuple HX HY HZY HUY → TupleL2 HX HY HZY HUY) := by
  unfold toL2
  fun_prop

end Norm

/-! ### The 2-Wasserstein distance for the Hilbert norm -/

section Wasserstein

variable {HX HY HZY HUY : Type*} [NormedAddCommGroup HX] [InnerProductSpace ℝ HX]
  [NormedAddCommGroup HY] [InnerProductSpace ℝ HY] [NormedAddCommGroup HZY]
  [InnerProductSpace ℝ HZY] [NormedAddCommGroup HUY] [InnerProductSpace ℝ HUY]
  [MeasurableSpace HX] [MeasurableSpace HY] [MeasurableSpace HZY] [MeasurableSpace HUY]

/-- `toL2` is measurable. -/
theorem measurable_toL2 : Measurable (toL2 : Tuple HX HY HZY HUY → TupleL2 HX HY HZY HUY) := by
  unfold toL2
  fun_prop

/-- `ofL2` is measurable. -/
theorem measurable_ofL2 : Measurable (ofL2 : TupleL2 HX HY HZY HUY → Tuple HX HY HZY HUY) := by
  unfold ofL2
  fun_prop

/-- The 2-Wasserstein distance between two laws of finite second moment on the tuple space, for
the Hilbert norm `(‖x‖² + ‖y‖² + ‖z‖² + ‖u‖²)^{1/2}`: the distance of their images under
`toL2`. -/
noncomputable def w2H (μ μ' : P2 (Tuple HX HY HZY HUY)) : ℝ :=
  w2 (μ.law.map toL2) (μ'.law.map toL2)

/-- The 2-Wasserstein distance for the Hilbert norm is nonnegative. -/
theorem w2H_nonneg (μ μ' : P2 (Tuple HX HY HZY HUY)) : 0 ≤ w2H μ μ' :=
  w2_nonneg _ _

variable [BorelSpace HX] [BorelSpace HY] [BorelSpace HZY] [BorelSpace HUY]
  [SecondCountableTopology HX] [SecondCountableTopology HY] [SecondCountableTopology HZY]
  [SecondCountableTopology HUY]

/-- The squared 2-Wasserstein distance of two laws on the tuple space is at most that of their
images under `toL2`. -/
theorem w2sq_le_w2sq_map_toL2 (μ μ' : Measure (Tuple HX HY HZY HUY)) :
    w2sq μ μ' ≤ w2sq (μ.map toL2) (μ'.map toL2) := by
  have hlip : ∀ w w' : TupleL2 HX HY HZY HUY, ‖ofL2 w - ofL2 w'‖ ≤ ‖w - w'‖ := fun w w' =>
    norm_le_norm_toL2 (ofL2 w - ofL2 w')
  have h := w2sq_map_le_of_norm_sub_le measurable_ofL2 hlip (μ.map toL2) (μ'.map toL2)
  have hid : (ofL2 ∘ toL2 : Tuple HX HY HZY HUY → Tuple HX HY HZY HUY) = id := rfl
  rwa [Measure.map_map measurable_ofL2 measurable_toL2,
    Measure.map_map measurable_ofL2 measurable_toL2, hid, Measure.map_id, Measure.map_id] at h

/-- The squared 2-Wasserstein distance of the images under `toL2` of two laws on the tuple space
is at most four times their squared 2-Wasserstein distance. -/
theorem w2sq_map_toL2_le (μ μ' : Measure (Tuple HX HY HZY HUY)) :
    w2sq (μ.map toL2) (μ'.map toL2) ≤ 4 * w2sq μ μ' := by
  have hm : Measurable fun p : Tuple HX HY HZY HUY × Tuple HX HY HZY HUY =>
      (toL2 p.1, toL2 p.2) :=
    (measurable_toL2.comp measurable_fst).prodMk (measurable_toL2.comp measurable_snd)
  calc w2sq (μ.map toL2) (μ'.map toL2)
      ≤ ⨅ γ, ⨅ _ : IsCoupling μ μ' γ, 4 * transportCostSq γ := by
        refine le_iInf₂ fun γ hγ => ?_
        refine (w2sq_le_transportCostSq (isCoupling_map_prodMap hγ measurable_toL2)).trans ?_
        rw [transportCostSq, transportCostSq, lintegral_map measurable_normSq_sub hm,
          ← lintegral_const_mul _ measurable_normSq_sub]
        refine lintegral_mono fun p => ?_
        have h := norm_toL2_le (p.1 - p.2)
        rw [toL2_sub] at h
        have h0 := norm_nonneg (toL2 p.1 - toL2 p.2)
        rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith)
    _ = 4 * w2sq μ μ' := by
        rw [w2sq, ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
        refine iInf_congr fun γ => ?_
        rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]

/-- The squared 2-Wasserstein distance for the Hilbert norm of two laws of finite second moment
is finite. -/
theorem w2sq_map_toL2_ne_top (μ μ' : P2 (Tuple HX HY HZY HUY)) :
    w2sq (μ.law.map toL2) (μ'.law.map toL2) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) (w2sq_ne_top μ μ'))
    (w2sq_map_toL2_le μ.law μ'.law)

/-- **`w2P ≤ w2H`**: the 2-Wasserstein distance for the maximum of the channel norms is at most
that for the Hilbert norm. -/
theorem w2P_le_w2H (μ μ' : P2 (Tuple HX HY HZY HUY)) : w2P μ μ' ≤ w2H μ μ' :=
  Real.sqrt_le_sqrt
    (ENNReal.toReal_mono (w2sq_map_toL2_ne_top μ μ') (w2sq_le_w2sq_map_toL2 μ.law μ'.law))

/-- **`w2H ≤ 2 w2P`**: the 2-Wasserstein distance for the Hilbert norm is at most twice that for
the maximum of the channel norms. -/
theorem w2H_le_two_mul_w2P (μ μ' : P2 (Tuple HX HY HZY HUY)) : w2H μ μ' ≤ 2 * w2P μ μ' := by
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) (w2sq_ne_top μ μ'))
    (w2sq_map_toL2_le μ.law μ'.law)
  rw [ENNReal.toReal_mul] at h
  have h4 : (4 : ℝ≥0∞).toReal = 2 ^ 2 := by norm_num
  rw [h4] at h
  calc w2H μ μ' = Real.sqrt (w2sq (μ.law.map toL2) (μ'.law.map toL2)).toReal := rfl
    _ ≤ Real.sqrt (2 ^ 2 * (w2sq μ.law μ'.law).toReal) := Real.sqrt_le_sqrt h
    _ = 2 * w2P μ μ' := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
        rfl

/-- **The coupling bound (2.8) for the Hilbert norm.** For square-integrable random tuples
`Θ, Θ'` on one probability space,
`W₂(Law Θ, Law Θ')² ≤ 𝔼 (‖δX‖² + ‖δY‖² + ‖δZ‖² + ‖δU‖²)`, with `W₂` for the Hilbert norm. -/
theorem w2H_lawP2_sq_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {Θ Θ' : Ω → Tuple HX HY HZY HUY} (hΘ : MemLp Θ 2 P)
    (hΘ' : MemLp Θ' 2 P) :
    w2H (lawP2 P Θ) (lawP2 P Θ') ^ 2 ≤ ∫ ω, channelSq (Θ ω - Θ' ω) ∂P := by
  have hL : ∀ {Ξ : Ω → Tuple HX HY HZY HUY}, MemLp Ξ 2 P → MemLp (fun ω => toL2 (Ξ ω)) 2 P :=
    fun hΞ => hΞ.of_le_mul (c := 2)
      (continuous_toL2.comp_aestronglyMeasurable hΞ.aestronglyMeasurable)
      (ae_of_all _ fun ω => norm_toL2_le _)
  have hmap : ∀ {Ξ : Ω → Tuple HX HY HZY HUY}, MemLp Ξ 2 P →
      (lawP2 P Ξ).law.map toL2 = (lawP2 P fun ω => toL2 (Ξ ω)).law := by
    intro Ξ hΞ
    rw [lawP2_law hΞ, lawP2_law (hL hΞ), AEMeasurable.map_map_of_aemeasurable
      measurable_toL2.aemeasurable hΞ.aestronglyMeasurable.aemeasurable]
    rfl
  have h := w2P_lawP2_sq_le (hL hΘ) (hL hΘ')
  rw [w2H, hmap hΘ, hmap hΘ']
  refine h.trans (le_of_eq (integral_congr_ae (ae_of_all _ fun ω => ?_)))
  dsimp only
  rw [← toL2_sub, norm_toL2_sq]

end Wasserstein

end MVFBSDEJ.WellPosedness.System
