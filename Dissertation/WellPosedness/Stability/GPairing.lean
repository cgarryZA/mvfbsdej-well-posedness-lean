/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.SampleEnergy

/-!
# `G`-pairings: Young's inequality and integrability on the window

Step 2 of the proof of Lemma 4.3 of the well-posedness paper inserts Assumption 2.5 into the
`G`-energy identity (4.19) and bounds the remaining forcing pairings by Young's inequality with
`|G v| ≤ ‖G‖ |v|`. This file collects the vector facts and the integrability facts it uses.

* For `η > 0`, `u ⬝ v ≤ η |v|² + |u|²/(4η)`; with `a ⬝ Gᵀ c = G a ⬝ c`, `c ⬝ G x = Gᵀ c ⬝ x` and
  a bound `|G x|² ≤ g² |x|²`, which also gives `|Gᵀ y|² ≤ g² |y|²`, each forcing pairing is at
  most `η` times the square of the solution coordinate plus `g²/(4η)` times the square of the
  forcing.
* On a measure space, a pairing `v ⬝ w` of square-integrable coordinates is integrable, and a
  matrix image `A v` of square-integrable coordinates has square-integrable coordinates. On the
  window `Ω × [0, T]` with `P ⊗ ds`, and on the marked window with `(P ⊗ ds) ⊗ ν`, integrands of
  finite energy are square integrable, and the integral of `|x|²` is the window energy.

## Main statements

* `dotProduct_le_add_div`, `mulVec_dotProduct_le`, `transpose_mulVec_dotProduct_le`,
  `neg_dotProduct_mulVec_le`, `abs_mulVec_dotProduct_le`, `abs_dotProduct_mulVec_le` — Young's
  inequality for `G`-pairings.
* `gPairing_le`, `abs_gPairing_le` — Young's inequality for the forcing pairing of (4.19).
* `integrable_dotProduct_of_memLp`, `memLp_mulVec` — pairings of square-integrable coordinates.
* `neg_sub_dotProduct`, `integral_dotProduct_congr_ae` — rewriting pairings.
* `memLp_markedWindow` — marked integrands of finite energy on the marked window.
* `integral_dotProduct_self_window`, `integral_integral_dotProduct_self_markedWindow`,
  `integral_dotProduct_self` — the integrals of `|x|²` are the energies.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc Dissertation.WellPosedness.BrownianPoisson

universe u v w

/-! ### Young's inequality for `G`-pairings -/

section Algebra

variable {n m : ℕ} {G : Matrix (Fin m) (Fin n) ℝ} {gG η : ℝ}

/-- `a ⬝ Gᵀ c = G a ⬝ c`. -/
theorem dotProduct_transpose_mulVec (G : Matrix (Fin m) (Fin n) ℝ) (a : Fin n → ℝ)
    (c : Fin m → ℝ) : a ⬝ᵥ (Gᵀ *ᵥ c) = (G *ᵥ a) ⬝ᵥ c := by
  rw [dotProduct_mulVec, vecMul_transpose]

/-- `c ⬝ G x = Gᵀ c ⬝ x`. -/
theorem dotProduct_mulVec_eq_transpose (G : Matrix (Fin m) (Fin n) ℝ) (c : Fin m → ℝ)
    (x : Fin n → ℝ) : c ⬝ᵥ (G *ᵥ x) = (Gᵀ *ᵥ c) ⬝ᵥ x := by
  rw [dotProduct_mulVec, mulVec_transpose]

/-- **Young's inequality**: `u ⬝ v ≤ η |v|² + |u|²/(4η)` for `η > 0`. -/
theorem dotProduct_le_add_div {ι : Type*} [Fintype ι] (hη : 0 < η) (u v : ι → ℝ) :
    u ⬝ᵥ v ≤ η * (v ⬝ᵥ v) + (u ⬝ᵥ u) / (4 * η) := by
  have key : ∀ a c : ℝ, a * c ≤ η * (c * c) + a * a / (4 * η) := fun a c => by
    rw [← sub_nonneg]
    have e : η * (c * c) + a * a / (4 * η) - a * c = (2 * η * c - a) ^ 2 / (4 * η) := by
      field_simp
      ring
    rw [e]
    positivity
  simp only [dotProduct, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => key _ _

/-- **Young's inequality, negative pairing**: `−(u ⬝ v) ≤ η |v|² + |u|²/(4η)` for `η > 0`. -/
theorem neg_dotProduct_le_add_div {ι : Type*} [Fintype ι] (hη : 0 < η) (u v : ι → ℝ) :
    -(u ⬝ᵥ v) ≤ η * (v ⬝ᵥ v) + (u ⬝ᵥ u) / (4 * η) := by
  simpa only [neg_dotProduct, dotProduct_neg, neg_neg] using dotProduct_le_add_div hη (-u) v

/-- **Young's inequality for a `G`-pairing**: with `|G x|² ≤ g² |x|²`,
`G a ⬝ c ≤ η |c|² + (g²/(4η)) |a|²`. -/
theorem mulVec_dotProduct_le (hGn : ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ gG ^ 2 * (x ⬝ᵥ x))
    (hη : 0 < η) (a : Fin n → ℝ) (c : Fin m → ℝ) :
    (G *ᵥ a) ⬝ᵥ c ≤ η * (c ⬝ᵥ c) + gG ^ 2 / (4 * η) * (a ⬝ᵥ a) := by
  refine (dotProduct_le_add_div hη _ _).trans ?_
  rw [div_mul_eq_mul_div]
  gcongr
  exact hGn a

/-- A bound `|G x|² ≤ g² |x|²` gives `|Gᵀ y|² ≤ g² |y|²`. -/
theorem transpose_mulVec_dotProduct_le
    (hGn : ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ gG ^ 2 * (x ⬝ᵥ x)) (y : Fin m → ℝ) :
    (Gᵀ *ᵥ y) ⬝ᵥ (Gᵀ *ᵥ y) ≤ gG ^ 2 * (y ⬝ᵥ y) := by
  set w := Gᵀ *ᵥ y with hwdef
  have hw : w ⬝ᵥ w = (G *ᵥ w) ⬝ᵥ y := by
    conv_lhs => rw [hwdef]
    rw [dotProduct_transpose_mulVec]
  rcases (sq_nonneg gG).eq_or_lt with h0 | hpos
  · have hle : (G *ᵥ w) ⬝ᵥ (G *ᵥ w) ≤ 0 := by simpa [← h0] using hGn w
    have hGw : G *ᵥ w = 0 :=
      dotProduct_self_eq_zero.mp (le_antisymm hle (dotProduct_self_star_nonneg _))
    rw [hw, hGw, zero_dotProduct, ← h0, zero_mul]
  · have h := dotProduct_le_add_div (η := gG ^ 2 / 2) (by positivity) (G *ᵥ w) y
    rw [← hw] at h
    have h2 : (G *ᵥ w) ⬝ᵥ (G *ᵥ w) / (4 * (gG ^ 2 / 2)) ≤ w ⬝ᵥ w / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hGn w]
    linarith

/-- **Young's inequality for a transposed `G`-pairing**: with `|G x|² ≤ g² |x|²`,
`−(c ⬝ G x) ≤ η |x|² + (g²/(4η)) |c|²`. -/
theorem neg_dotProduct_mulVec_le
    (hGn : ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ gG ^ 2 * (x ⬝ᵥ x)) (hη : 0 < η)
    (c : Fin m → ℝ) (x : Fin n → ℝ) :
    -(c ⬝ᵥ (G *ᵥ x)) ≤ η * (x ⬝ᵥ x) + gG ^ 2 / (4 * η) * (c ⬝ᵥ c) := by
  rw [dotProduct_mulVec_eq_transpose]
  refine (neg_dotProduct_le_add_div hη _ _).trans ?_
  rw [div_mul_eq_mul_div]
  gcongr
  exact transpose_mulVec_dotProduct_le hGn c

/-- `(−a − b) ⬝ w = −((a + b) ⬝ w)`. -/
theorem neg_sub_dotProduct {ι : Type*} [Fintype ι] (a b w : ι → ℝ) :
    (fun k => -a k - b k) ⬝ᵥ w = -((fun k => a k + b k) ⬝ᵥ w) := by
  simp only [dotProduct, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `(λ a + c) ⬝ v = λ (a ⬝ v) + c ⬝ v`. -/
theorem dotProduct_mul_add {ι : Type*} [Fintype ι] (l : ℝ) (a c v : ι → ℝ) :
    (fun i => l * a i + c i) ⬝ᵥ v = l * (a ⬝ᵥ v) + c ⬝ᵥ v := by
  simp only [dotProduct, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- The squared Frobenius norm of an `m × d` array, by columns and by rows. -/
theorem sum_col_dotProduct_self {d : ℕ} (z : Fin m → Fin d → ℝ) :
    ∑ j, (fun k => z k j) ⬝ᵥ (fun k => z k j) = ∑ k, z k ⬝ᵥ z k := by
  simp only [dotProduct]
  exact Finset.sum_comm

/-- **Young's inequality for the forcing pairing of (4.19).** With `|G x|² ≤ g² |x|²` and
`η > 0`, for a drift `b`, diffusion columns `s_{· j}`, driver `f`, solution `(x, y, z)` and a mark
term `J ≤ η J_W + (g²/(4η)) J_Q`,

`b ⬝ Gᵀy + ∑_j s_{·j} ⬝ Gᵀz_{·j} − f ⬝ Gx + J
  ≤ η (|x|² + |y|² + |z|²_F + J_W) + (g²/(4η)) (|b|² + |s|²_F + J_Q + |f|²)`. -/
theorem gPairing_le {d : ℕ}
    (hGn : ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ gG ^ 2 * (x ⬝ᵥ x)) (hη : 0 < η)
    (b : Fin n → ℝ) (s : Fin n → Fin d → ℝ) (f : Fin m → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (z : Fin m → Fin d → ℝ) {J JW JQ : ℝ} (hJ : J ≤ η * JW + gG ^ 2 / (4 * η) * JQ) :
    b ⬝ᵥ (Gᵀ *ᵥ y) + ∑ j, (fun i => s i j) ⬝ᵥ (Gᵀ *ᵥ fun k => z k j) - f ⬝ᵥ (G *ᵥ x) + J
      ≤ η * (x ⬝ᵥ x + y ⬝ᵥ y + ∑ k, z k ⬝ᵥ z k + JW)
        + gG ^ 2 / (4 * η) * (b ⬝ᵥ b + ∑ i, s i ⬝ᵥ s i + JQ + f ⬝ᵥ f) := by
  have h1 : b ⬝ᵥ (Gᵀ *ᵥ y) ≤ η * (y ⬝ᵥ y) + gG ^ 2 / (4 * η) * (b ⬝ᵥ b) := by
    rw [dotProduct_transpose_mulVec]
    exact mulVec_dotProduct_le hGn hη b y
  have h2 : ∑ j, (fun i => s i j) ⬝ᵥ (Gᵀ *ᵥ fun k => z k j)
      ≤ η * ∑ k, z k ⬝ᵥ z k + gG ^ 2 / (4 * η) * ∑ i, s i ⬝ᵥ s i := by
    rw [← sum_col_dotProduct_self z, ← sum_col_dotProduct_self (m := n) s, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [dotProduct_transpose_mulVec]
    exact mulVec_dotProduct_le hGn hη _ _
  have h3 := neg_dotProduct_mulVec_le hGn hη f x
  nlinarith

/-- **Young's inequality for a `G`-pairing, in absolute value**: with `|G x|² ≤ g² |x|²`,
`|G a ⬝ c| ≤ η |c|² + (g²/(4η)) |a|²`. -/
theorem abs_mulVec_dotProduct_le
    (hGn : ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ gG ^ 2 * (x ⬝ᵥ x)) (hη : 0 < η)
    (a : Fin n → ℝ) (c : Fin m → ℝ) :
    |(G *ᵥ a) ⬝ᵥ c| ≤ η * (c ⬝ᵥ c) + gG ^ 2 / (4 * η) * (a ⬝ᵥ a) := by
  refine abs_le.mpr ⟨?_, mulVec_dotProduct_le hGn hη a c⟩
  have h := mulVec_dotProduct_le hGn hη a (-c)
  simp only [dotProduct_neg, neg_dotProduct, neg_neg] at h
  linarith

/-- **Young's inequality for a transposed `G`-pairing, in absolute value**: with
`|G x|² ≤ g² |x|²`, `|c ⬝ G x| ≤ η |x|² + (g²/(4η)) |c|²`. -/
theorem abs_dotProduct_mulVec_le
    (hGn : ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ gG ^ 2 * (x ⬝ᵥ x)) (hη : 0 < η)
    (c : Fin m → ℝ) (x : Fin n → ℝ) :
    |c ⬝ᵥ (G *ᵥ x)| ≤ η * (x ⬝ᵥ x) + gG ^ 2 / (4 * η) * (c ⬝ᵥ c) := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h := neg_dotProduct_mulVec_le hGn hη c x
    linarith
  · have h := neg_dotProduct_mulVec_le hGn hη (-c) x
    simp only [neg_dotProduct, neg_neg, dotProduct_neg] at h
    linarith

/-- **Young's inequality for the forcing pairing of (4.19), in absolute value.** With
`|G x|² ≤ g² |x|²` and `η > 0`, for a drift `b`, diffusion columns `s_{· j}`, driver `f`,
solution `(x, y, z)` and a mark term `|J| ≤ η J_W + (g²/(4η)) J_Q`,

`|b ⬝ Gᵀy| + |∑_j s_{·j} ⬝ Gᵀz_{·j}| + |J| + |f ⬝ Gx|
  ≤ η (|x|² + |y|² + |z|²_F + J_W) + (g²/(4η)) (|b|² + |s|²_F + J_Q + |f|²)`. -/
theorem abs_gPairing_le {d : ℕ}
    (hGn : ∀ x : Fin n → ℝ, (G *ᵥ x) ⬝ᵥ (G *ᵥ x) ≤ gG ^ 2 * (x ⬝ᵥ x)) (hη : 0 < η)
    (b : Fin n → ℝ) (s : Fin n → Fin d → ℝ) (f : Fin m → ℝ) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (z : Fin m → Fin d → ℝ) {J JW JQ : ℝ} (hJ : |J| ≤ η * JW + gG ^ 2 / (4 * η) * JQ) :
    |b ⬝ᵥ (Gᵀ *ᵥ y)| + |∑ j, (fun i => s i j) ⬝ᵥ (Gᵀ *ᵥ fun k => z k j)| + |J|
        + |f ⬝ᵥ (G *ᵥ x)|
      ≤ η * (x ⬝ᵥ x + y ⬝ᵥ y + ∑ k, z k ⬝ᵥ z k + JW)
        + gG ^ 2 / (4 * η) * (b ⬝ᵥ b + ∑ i, s i ⬝ᵥ s i + JQ + f ⬝ᵥ f) := by
  have h1 : |b ⬝ᵥ (Gᵀ *ᵥ y)| ≤ η * (y ⬝ᵥ y) + gG ^ 2 / (4 * η) * (b ⬝ᵥ b) := by
    rw [dotProduct_transpose_mulVec]
    exact abs_mulVec_dotProduct_le hGn hη b y
  have h2 : |∑ j, (fun i => s i j) ⬝ᵥ (Gᵀ *ᵥ fun k => z k j)|
      ≤ η * ∑ k, z k ⬝ᵥ z k + gG ^ 2 / (4 * η) * ∑ i, s i ⬝ᵥ s i := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← sum_col_dotProduct_self z, ← sum_col_dotProduct_self (m := n) s, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [dotProduct_transpose_mulVec]
    exact abs_mulVec_dotProduct_le hGn hη _ _
  have h3 := abs_dotProduct_mulVec_le hGn hη f x
  nlinarith

end Algebra

/-! ### Pairings of square-integrable coordinates -/

section Pairing

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The pairing `v ⬝ w` of square-integrable coordinates is integrable. -/
theorem integrable_dotProduct_of_memLp {ι : Type*} [Fintype ι] {v w : ι → α → ℝ}
    (hv : ∀ i, MemLp (v i) 2 μ) (hw : ∀ i, MemLp (w i) 2 μ) :
    Integrable (fun p => (fun i => v i p) ⬝ᵥ (fun i => w i p)) μ := by
  simp only [dotProduct]
  exact integrable_finsetSum _ fun i _ => (hv i).integrable_mul (hw i)

/-- Pairings with integrands that agree coordinatewise almost everywhere have the same
integral. -/
theorem integral_dotProduct_congr_ae {ι : Type*} [Fintype ι] {u v w : α → ι → ℝ}
    (h : ∀ᵐ p ∂μ, ∀ i, u p i = v p i) : ∫ p, u p ⬝ᵥ w p ∂μ = ∫ p, v p ⬝ᵥ w p ∂μ :=
  integral_congr_ae (h.mono fun p hp => by simp only [funext hp])

/-- The matrix image `A v` of square-integrable coordinates has square-integrable
coordinates. -/
theorem memLp_mulVec {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℝ) {v : ι → α → ℝ}
    (hv : ∀ i, MemLp (v i) 2 μ) (k : κ) : MemLp (fun p => (A *ᵥ fun i => v i p) k) 2 μ := by
  simp only [mulVec, dotProduct]
  exact memLp_finsetSum _ fun i _ => (hv i).const_mul (A k i)

/-- **The `G`-pairing integrand is integrable** when all its coordinates are square
integrable, the mark coordinates for the product with the mark measure. -/
theorem integrable_gPairing {n m d : ℕ} {F : Type*} [MeasurableSpace F] {ν : Measure F}
    [SFinite μ] [SFinite ν] (G : Matrix (Fin m) (Fin n) ℝ) {b x : Fin n → α → ℝ}
    {s : Fin n → Fin d → α → ℝ} {f y : Fin m → α → ℝ} {z : Fin m → Fin d → α → ℝ}
    {h : Fin n → α × F → ℝ} {u : Fin m → α × F → ℝ} (hb : ∀ i, MemLp (b i) 2 μ)
    (hs : ∀ i j, MemLp (s i j) 2 μ) (hf : ∀ k, MemLp (f k) 2 μ)
    (hh : ∀ i, MemLp (h i) 2 (μ.prod ν)) (hx : ∀ i, MemLp (x i) 2 μ) (hy : ∀ k, MemLp (y k) 2 μ)
    (hz : ∀ k j, MemLp (z k j) 2 μ) (hu : ∀ k, MemLp (u k) 2 (μ.prod ν)) :
    Integrable (fun p => (fun i => b i p) ⬝ᵥ (Gᵀ *ᵥ fun k => y k p)
      + ∑ j, (fun i => s i j p) ⬝ᵥ (Gᵀ *ᵥ fun k => z k j p)
      - (fun k => f k p) ⬝ᵥ (G *ᵥ fun i => x i p)
      + ∫ e, (fun i => h i (p, e)) ⬝ᵥ (Gᵀ *ᵥ fun k => u k (p, e)) ∂ν) μ :=
  (((integrable_dotProduct_of_memLp hb (memLp_mulVec _ hy)).add
    (integrable_finsetSum _ fun j _ => integrable_dotProduct_of_memLp (fun i => hs i j)
      (memLp_mulVec _ fun k => hz k j))).sub
    (integrable_dotProduct_of_memLp hf (memLp_mulVec _ hx))).add
    (integrable_dotProduct_of_memLp hh (memLp_mulVec _ hu)).integral_prod_left

end Pairing

/-! ### The window and the marked window -/

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} [SigmaFinite ν] {T : ℝ}

/-- A marked integrand of finite energy on `[0, T]` is square integrable on the marked window
`(Ω × [0, T]) × E` with `(P ⊗ ds) ⊗ ν`. -/
theorem memLp_markedWindow [SFinite P] {φ : Ω → ℝ → E → ℝ}
    (hφ : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hq : Poisson.Compensated.markedEnergy P ν T φ < ⊤) :
    MemLp (fun q : (Ω × ℝ) × E => φ q.1.1 q.1.2 q.2) 2
      ((P.prod (volume.restrict (Set.Icc (0 : ℝ) T))).prod ν) :=
  (Ito.SecondMoment.memLp_two_prod_marked hφ hq).comp_measurePreserving
    (measurePreserving_prodAssoc P _ ν)

/-- The integral of `f²` on the window is the energy of `f`. -/
theorem integral_mul_self_window [SFinite P] {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) :
    ∫ p, f p.1 p.2 * f p.1 p.2 ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      = (Brownian.Ito.energy P T f).toReal := by
  have hm : Measurable fun p : Ω × ℝ => f p.1 p.2 * f p.1 p.2 := hf.mul hf
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => mul_self_nonneg _)
    hm.aestronglyMeasurable, lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
  simp only [Brownian.Ito.energy, sq_nnnorm_eq_ofReal]

/-- The integral of `φ²` on the marked window is the marked energy of `φ`. -/
theorem integral_mul_self_markedWindow [SFinite P] {φ : Ω → ℝ → E → ℝ}
    (hφ : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) :
    ∫ q, φ q.1.1 q.1.2 q.2 * φ q.1.1 q.1.2 q.2
        ∂((P.prod (volume.restrict (Set.Icc (0 : ℝ) T))).prod ν)
      = (Poisson.Compensated.markedEnergy P ν T φ).toReal := by
  have hm : Measurable fun q : (Ω × ℝ) × E => φ q.1.1 q.1.2 q.2 := hφ.comp (by fun_prop :
    Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))
  have hmm : Measurable fun q : (Ω × ℝ) × E => φ q.1.1 q.1.2 q.2 * φ q.1.1 q.1.2 q.2 :=
    hm.mul hm
  have hm2 : Measurable fun q : (Ω × ℝ) × E =>
      ENNReal.ofReal (φ q.1.1 q.1.2 q.2 * φ q.1.1 q.1.2 q.2) := hmm.ennreal_ofReal
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun q => mul_self_nonneg _)
    hmm.aestronglyMeasurable, lintegral_prod _ hm2.aemeasurable,
    lintegral_prod _ hm2.lintegral_prod_right'.aemeasurable]
  simp only [Poisson.Compensated.markedEnergy, sq_nnnorm_eq_ofReal]

/-- The integral of `|x|² = ∑_i x_i²` on the window is the sum of the energies of the
coordinates, for coordinates of finite energy. -/
theorem integral_dotProduct_self_window [SFinite P] {ι : Type*} [Fintype ι]
    {x : ι → Ω → ℝ → ℝ} (hx : ∀ i, Measurable (Function.uncurry (x i)))
    (hq : ∀ i, Brownian.Ito.energy P T (x i) < ⊤) :
    ∫ p, (fun i => x i p.1 p.2) ⬝ᵥ (fun i => x i p.1 p.2)
        ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      = (∑ i, Brownian.Ito.energy P T (x i)).toReal := by
  have hsum : ∫ p, ∑ i, x i p.1 p.2 * x i p.1 p.2 ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      = ∑ i, ∫ p, x i p.1 p.2 * x i p.1 p.2 ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    integral_finsetSum _ fun i _ => (Ito.SecondMoment.memLp_two_prod (hx i) (hq i)).integrable_mul
      (Ito.SecondMoment.memLp_two_prod (hx i) (hq i))
  simp only [dotProduct]
  rw [hsum, ENNReal.toReal_sum fun i _ => (hq i).ne]
  exact Finset.sum_congr rfl fun i _ => integral_mul_self_window (hx i)

/-- The integral of `‖u‖²_{L²(ν)} = ∑_i ∫_E u_i² dν` on the window is the sum of the marked
energies of the coordinates, for coordinates of finite marked energy. -/
theorem integral_integral_dotProduct_self_markedWindow [SFinite P] {ι : Type*} [Fintype ι]
    {x : ι → Ω → ℝ → E → ℝ} (hx : ∀ i, Measurable fun p : Ω × ℝ × E => x i p.1 p.2.1 p.2.2)
    (hq : ∀ i, Poisson.Compensated.markedEnergy P ν T (x i) < ⊤) :
    ∫ p, ∫ e, (fun i => x i p.1 p.2 e) ⬝ᵥ (fun i => x i p.1 p.2 e) ∂ν
        ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      = (∑ i, Poisson.Compensated.markedEnergy P ν T (x i)).toReal := by
  have hint := integrable_dotProduct_of_memLp (fun i => memLp_markedWindow (hx i) (hq i))
    (fun i => memLp_markedWindow (hx i) (hq i))
  rw [← integral_prod _ hint]
  have hsum : ∫ q, ∑ i, x i q.1.1 q.1.2 q.2 * x i q.1.1 q.1.2 q.2
        ∂((P.prod (volume.restrict (Set.Icc (0 : ℝ) T))).prod ν)
      = ∑ i, ∫ q, x i q.1.1 q.1.2 q.2 * x i q.1.1 q.1.2 q.2
        ∂((P.prod (volume.restrict (Set.Icc (0 : ℝ) T))).prod ν) :=
    integral_finsetSum _ fun i _ => (memLp_markedWindow (hx i) (hq i)).integrable_mul
      (memLp_markedWindow (hx i) (hq i))
  simp only [dotProduct]
  rw [hsum,
    ENNReal.toReal_sum fun i _ => (hq i).ne]
  exact Finset.sum_congr rfl fun i _ => integral_mul_self_markedWindow (hx i)

omit [MeasurableSpace E] [SigmaFinite ν] in
/-- `𝔼|x|² = 𝔼 ∑_i x_i²` for square-integrable coordinates. -/
theorem integral_dotProduct_self {ι : Type*} [Fintype ι] {x : ι → Ω → ℝ}
    (hx : ∀ i, MemLp (x i) 2 P) :
    ∫ ω, (fun i => x i ω) ⬝ᵥ (fun i => x i ω) ∂P = (∫⁻ ω, esq (fun i => x i ω) ∂P).toReal := by
  rw [toReal_lintegral_esq hx]
  simp only [dotProduct]
  exact integral_finsetSum (f := fun i ω => x i ω * x i ω) _ fun i _ =>
    (hx i).integrable_mul (hx i)

end Dissertation.WellPosedness.Stability
