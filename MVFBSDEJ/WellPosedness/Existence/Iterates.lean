/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Existence.ForcingLimit
import MVFBSDEJ.WellPosedness.System.CrossEval
import LevyStochCalc.BSDEJ.PicardLimit

/-!
# The iterates of a contraction for the data size

The continuation step of the existence proof of the well-posedness paper iterates a map `Φ` on
the forcings of the `λ`-system (4.1) that contracts the data size by a factor `1/4`:
`dataSize(Φ F − Φ F') ≤ ¼ dataSize(F − F')`. The data size is not a metric but a squared one:
it is symmetric, vanishes on the diagonal and satisfies
`dataSize(x − z) ≤ 2 dataSize(x − y) + 2 dataSize(y − z)`. For such a quasi-distance `δ` and a
map `Φ` with `δ(Φ x, Φ y) ≤ ¼ δ(x, y)` on a set of points it preserves, the iterates `xₐ = Φᵃ x₀`
satisfy

* `δ(xₐ₊₁, xₐ) ≤ 4⁻ᵃ δ(x₁, x₀)`;
* `δ(xₐ₊ₖ, xₐ) ≤ 4 · 4⁻ᵃ δ(x₁, x₀)`, hence they are Cauchy once `δ(x₁, x₀) < ∞`;
* if `δ(xₐ, x) → 0` for an admissible `x`, then `δ(Φ x, x) = 0`: indeed
  `δ(Φ x, x) ≤ 2 δ(Φ x, Φ xₐ) + 2 δ(xₐ₊₁, x) ≤ 2 (¼ δ(xₐ, x)) + 2 δ(xₐ₊₁, x) → 0`.

The data size with zero initial datum is such a quasi-distance on the forcings.

## Main statements

* `iterate_mem`, `dist_iterate_succ_le`, `dist_iterate_add_le` — the geometric decay.
* `exists_dist_iterate_lt` — the iterates are Cauchy.
* `dist_map_eq_zero_of_tendsto` — a limit of the iterates is a fixed point up to zero distance.
* `dataSize_sub_comm`, `dataSize_sub_self` — the data size of differences is symmetric and
  vanishes on the diagonal.
* `Forcing.dataSize_ne_top`, `Forcing.dataSize_sub_le` — the data size of a forcing is finite,
  and the triangle inequality for forcing differences.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.Stability MVFBSDEJ.WellPosedness.System LevyStochCalc

universe u v

/-! ### Iterating a contraction for a quasi-distance -/

section Iteration

variable {α : Type*} {δ : α → α → ℝ≥0∞} {S : Set α} {Φ : α → α} {x₀ : α}

/-- The iterates of a map preserving a set stay in it. -/
theorem iterate_mem (hΦ : ∀ x ∈ S, Φ x ∈ S) (h₀ : x₀ ∈ S) (a : ℕ) : Φ^[a] x₀ ∈ S := by
  induction a with
  | zero => exact h₀
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    exact hΦ _ ih

/-- **Geometric decay of consecutive iterates**: for a map contracting `δ` by `1/4` on a set it
preserves, `δ(Φᵃ⁺¹ x₀, Φᵃ x₀) ≤ 4⁻ᵃ δ(Φ x₀, x₀)`. -/
theorem dist_iterate_succ_le (hΦ : ∀ x ∈ S, Φ x ∈ S)
    (hc : ∀ x ∈ S, ∀ y ∈ S, δ (Φ x) (Φ y) ≤ 4⁻¹ * δ x y) (h₀ : x₀ ∈ S) (a : ℕ) :
    δ (Φ^[a + 1] x₀) (Φ^[a] x₀) ≤ 4⁻¹ ^ a * δ (Φ x₀) x₀ := by
  induction a with
  | zero => simp
  | succ a ih =>
    have key := hc _ (iterate_mem hΦ h₀ (a + 1)) _ (iterate_mem hΦ h₀ a)
    rw [← Function.iterate_succ_apply' Φ (a + 1), ← Function.iterate_succ_apply' Φ a] at key
    calc δ (Φ^[a + 1 + 1] x₀) (Φ^[a + 1] x₀) ≤ 4⁻¹ * δ (Φ^[a + 1] x₀) (Φ^[a] x₀) := key
      _ ≤ 4⁻¹ * (4⁻¹ ^ a * δ (Φ x₀) x₀) := by gcongr
      _ = 4⁻¹ ^ (a + 1) * δ (Φ x₀) x₀ := by rw [pow_succ]; ring

/-- **The Cauchy bound for the iterates**: for a map contracting `δ` by `1/4` on a set it
preserves, with `δ` vanishing on the diagonal and satisfying the triangle inequality up to the
factor `2` on that set, `δ(Φᵃ⁺ᵏ x₀, Φᵃ x₀) ≤ 4 · 4⁻ᵃ δ(Φ x₀, x₀)`. -/
theorem dist_iterate_add_le (hΦ : ∀ x ∈ S, Φ x ∈ S)
    (hc : ∀ x ∈ S, ∀ y ∈ S, δ (Φ x) (Φ y) ≤ 4⁻¹ * δ x y) (hself : ∀ x, δ x x = 0)
    (htri : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, δ x z ≤ 2 * δ x y + 2 * δ y z) (h₀ : x₀ ∈ S)
    (a k : ℕ) : δ (Φ^[a + k] x₀) (Φ^[a] x₀) ≤ 4 * 4⁻¹ ^ a * δ (Φ x₀) x₀ := by
  induction k generalizing a with
  | zero => simp [hself]
  | succ k ih =>
    rw [show a + (k + 1) = a + 1 + k by omega]
    refine (htri _ (iterate_mem hΦ h₀ _) _ (iterate_mem hΦ h₀ (a + 1)) _
      (iterate_mem hΦ h₀ a)).trans ?_
    refine (add_le_add (mul_le_mul' le_rfl (ih (a + 1)))
      (mul_le_mul' le_rfl (dist_iterate_succ_le hΦ hc h₀ a))).trans (le_of_eq ?_)
    have h84 : (8 : ℝ≥0∞) * 4⁻¹ = 2 := by
      rw [show (8 : ℝ≥0∞) = 2 * 4 by norm_num, mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    calc 2 * (4 * 4⁻¹ ^ (a + 1) * δ (Φ x₀) x₀) + 2 * (4⁻¹ ^ a * δ (Φ x₀) x₀)
        = 8 * 4⁻¹ * (4⁻¹ ^ a * δ (Φ x₀) x₀) + 2 * (4⁻¹ ^ a * δ (Φ x₀) x₀) := by ring
      _ = 4 * 4⁻¹ ^ a * δ (Φ x₀) x₀ := by rw [h84]; ring

/-- **The iterates are Cauchy**: under the hypotheses of `dist_iterate_add_le`, with `δ`
symmetric and `δ(Φ x₀, x₀)` finite, for every `ε > 0` there is `N` with `δ(Φᵃ x₀, Φᵇ x₀) < ε`
for all `a, b ≥ N`. -/
theorem exists_dist_iterate_lt (hΦ : ∀ x ∈ S, Φ x ∈ S)
    (hc : ∀ x ∈ S, ∀ y ∈ S, δ (Φ x) (Φ y) ≤ 4⁻¹ * δ x y) (hself : ∀ x, δ x x = 0)
    (htri : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, δ x z ≤ 2 * δ x y + 2 * δ y z)
    (hsymm : ∀ x y, δ x y = δ y x) (h₀ : x₀ ∈ S) (hW : δ (Φ x₀) x₀ ≠ ⊤) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ a, N ≤ a → ∀ b, N ≤ b → δ (Φ^[a] x₀) (Φ^[b] x₀) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := BSDEJ.Solves.exists_geom_lt _ hW ε hε
  refine ⟨N, fun a ha b hb => ?_⟩
  rcases le_total a b with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [hsymm]
    exact (dist_iterate_add_le hΦ hc hself htri h₀ a k).trans_lt (hN a ha)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact (dist_iterate_add_le hΦ hc hself htri h₀ b k).trans_lt (hN b hb)

/-- **A limit of the iterates is a fixed point up to zero distance**: for a map contracting `δ`
by `1/4` on a set it preserves, with `δ` symmetric and satisfying the triangle inequality up to
the factor `2` on that set, if `δ(Φᵃ x₀, x) → 0` for `x` in the set, then `δ(Φ x, x) = 0`. -/
theorem dist_map_eq_zero_of_tendsto (hΦ : ∀ x ∈ S, Φ x ∈ S)
    (hc : ∀ x ∈ S, ∀ y ∈ S, δ (Φ x) (Φ y) ≤ 4⁻¹ * δ x y)
    (htri : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, δ x z ≤ 2 * δ x y + 2 * δ y z)
    (hsymm : ∀ x y, δ x y = δ y x) (h₀ : x₀ ∈ S) {x : α} (hx : x ∈ S)
    (hlim : Tendsto (fun a => δ (Φ^[a] x₀) x) atTop (𝓝 0)) : δ (Φ x) x = 0 := by
  refine BSDEJ.Solves.eq_zero_of_le_two_mul_of_tendsto _ hlim fun a => ?_
  refine (htri _ (hΦ x hx) _ (iterate_mem hΦ h₀ (a + 1)) _ hx).trans ?_
  gcongr
  rw [Function.iterate_succ_apply', hsymm (Φ^[a] x₀)]
  exact hc _ hx _ (iterate_mem hΦ h₀ a)

end Iteration

/-! ### The data size on forcings -/

section DataSize

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  {ν : Measure E} {T : ℝ} {n m d : ℕ}

/-- **The data size of a difference is symmetric**: the data size of `q¹ − q²` is that of
`q² − q¹`, for any initial datum. -/
theorem dataSize_sub_comm (ξ₀ : Fin n → Ω → ℝ) (qb₁ qb₂ : Fin n → Ω → ℝ → ℝ)
    (qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ) (qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ)
    (qf₁ qf₂ : Fin m → Ω → ℝ → ℝ) (qg₁ qg₂ : Fin m → Ω → ℝ) :
    dataSize P ν T ξ₀ (fun i ω s => qb₁ i ω s - qb₂ i ω s)
        (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
        (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω)
      = dataSize P ν T ξ₀ (fun i ω s => qb₂ i ω s - qb₁ i ω s)
        (fun i s ω j => qσ₂ i s ω j - qσ₁ i s ω j) (fun i s ω e => qh₂ i s ω e - qh₁ i s ω e)
        (fun k ω s => qf₂ k ω s - qf₁ k ω s) (fun k ω => qg₂ k ω - qg₁ k ω) := by
  unfold dataSize
  have hg : ∫⁻ ω, esq (fun k => qg₁ k ω - qg₂ k ω) ∂P
      = ∫⁻ ω, esq (fun k => qg₂ k ω - qg₁ k ω) ∂P :=
    lintegral_congr fun ω => Finset.sum_congr rfl fun k _ => by rw [← nnnorm_neg, neg_sub]
  rw [hg]
  simp only [energy_sub_comm (qb₁ _) (qb₂ _), markedEnergy_sub_comm, energy_sub_comm (qf₁ _)]
  congr 3
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    energy_sub_comm (fun ω s => qσ₁ i s ω j) (fun ω s => qσ₂ i s ω j)

/-- **The data size vanishes on the diagonal**: the data size of `q − q` with zero initial datum
is `0`. -/
theorem dataSize_sub_self (qb : Fin n → Ω → ℝ → ℝ) (qσ : Fin n → ℝ → Ω → Fin d → ℝ)
    (qh : Fin n → ℝ → Ω → E → ℝ) (qf : Fin m → Ω → ℝ → ℝ) (qg : Fin m → Ω → ℝ) :
    dataSize P ν T 0 (fun i ω s => qb i ω s - qb i ω s) (fun i s ω j => qσ i s ω j - qσ i s ω j)
      (fun i s ω e => qh i s ω e - qh i s ω e) (fun k ω s => qf k ω s - qf k ω s)
      (fun k ω => qg k ω - qg k ω) = 0 := by
  simp [dataSize, esq, Brownian.Ito.energy, Poisson.Compensated.markedEnergy]

variable [SigmaFinite ν] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {qb qb₁ qb₂ qb₃ : Fin n → Ω → ℝ → ℝ} {qσ qσ₁ qσ₂ qσ₃ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh qh₁ qh₂ qh₃ : Fin n → ℝ → Ω → E → ℝ} {qf qf₁ qf₂ qf₃ : Fin m → Ω → ℝ → ℝ}
  {qg qg₁ qg₂ qg₃ : Fin m → Ω → ℝ}

omit [SigmaFinite ν] in
/-- **The data size of a forcing is finite**, with zero initial datum. -/
theorem _root_.MVFBSDEJ.WellPosedness.System.Forcing.dataSize_ne_top
    (h : Forcing ℱ P ν T qb qσ qh qf qg) : dataSize P ν T 0 qb qσ qh qf qg ≠ ⊤ := by
  have h0 : ∫⁻ ω, esq (fun i => (0 : Fin n → Ω → ℝ) i ω) ∂P = 0 := by simp [esq]
  unfold dataSize
  rw [h0, zero_add]
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨(lintegral_esq_lt_top h.qg_sq).ne,
      ENNReal.sum_ne_top.mpr fun i _ => h.qb_sq i⟩,
      ENNReal.sum_ne_top.mpr fun i _ => ENNReal.sum_ne_top.mpr fun j _ => h.qσ_sq i j⟩,
    ENNReal.sum_ne_top.mpr fun i _ => h.qh_sq i⟩, ENNReal.sum_ne_top.mpr fun k _ => h.qf_sq k⟩

/-- **The triangle inequality for forcing differences**: for forcings `q¹, q²` and any `q³`,
with zero initial datum,
`dataSize(q¹ − q³) ≤ 2 dataSize(q¹ − q²) + 2 dataSize(q² − q³)`. -/
theorem _root_.MVFBSDEJ.WellPosedness.System.Forcing.dataSize_sub_le
    (h₁ : Forcing ℱ P ν T qb₁ qσ₁ qh₁ qf₁ qg₁) (h₂ : Forcing ℱ P ν T qb₂ qσ₂ qh₂ qf₂ qg₂)
    (qb₃ : Fin n → Ω → ℝ → ℝ) (qσ₃ : Fin n → ℝ → Ω → Fin d → ℝ) (qh₃ : Fin n → ℝ → Ω → E → ℝ)
    (qf₃ : Fin m → Ω → ℝ → ℝ) (qg₃ : Fin m → Ω → ℝ) :
    dataSize P ν T 0 (fun i ω s => qb₁ i ω s - qb₃ i ω s)
        (fun i s ω j => qσ₁ i s ω j - qσ₃ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₃ i s ω e)
        (fun k ω s => qf₁ k ω s - qf₃ k ω s) (fun k ω => qg₁ k ω - qg₃ k ω)
      ≤ 2 * dataSize P ν T 0 (fun i ω s => qb₁ i ω s - qb₂ i ω s)
          (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
          (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω)
        + 2 * dataSize P ν T 0 (fun i ω s => qb₂ i ω s - qb₃ i ω s)
          (fun i s ω j => qσ₂ i s ω j - qσ₃ i s ω j) (fun i s ω e => qh₂ i s ω e - qh₃ i s ω e)
          (fun k ω s => qf₂ k ω s - qf₃ k ω s) (fun k ω => qg₂ k ω - qg₃ k ω) := by
  have hg : ∀ {q : Fin m → Ω → ℝ}, (∀ k, StronglyMeasurable[ℱ T] (q k)) →
      ∀ k, AEMeasurable (q k) P := fun hq k => ((hq k).mono (ℱ.le T)).measurable.aemeasurable
  have h := Stability.dataSize_sub_le (P := P) (ν := ν) (T := T) (ξ₁ := 0) (ξ₂ := 0) (ξ₃ := 0)
    (qb₃ := qb₃) (qσ₃ := qσ₃) (qh₃ := qh₃) (qf₃ := qf₃) (qg₃ := qg₃)
    (fun _ => aemeasurable_const) (fun _ => aemeasurable_const) h₁.qb_meas h₂.qb_meas
    h₁.qσ_meas h₂.qσ_meas h₁.qh_meas h₂.qh_meas h₁.qf_meas h₂.qf_meas (hg h₁.qg_meas)
    (hg h₂.qg_meas)
  simpa only [dataSize_initial_sub_self] using h

end DataSize

end MVFBSDEJ.WellPosedness.Existence
