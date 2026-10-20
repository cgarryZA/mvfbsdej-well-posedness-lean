/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Stability.SupUpgrade

/-!
# The energies of a difference against its size with running suprema

For a difference `(δX, δY, δZ, δU)` of two tuples, the expected Lipschitz bounds (3.2) and
(2.6) with (2.9) control the coefficient differences along the pair by the energies

`I = 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²_{L²(ν)})`

and by `A = 𝔼|δX_T|²`; the stability estimate (4.14) controls the size with running suprema

`N = 𝔼 sup_{t ≤ T} |δX_t|² + 𝔼 sup_{t ≤ T} |δY_t|² + 𝔼 ∫_0^T (|δZ|²_F + ‖δU‖²_{L²(ν)})`.

The two compare pathwise: a time integral over `[0, T]` is at most `T` times the running
supremum, and a value at a time of `[0, T]` is at most the running supremum. Hence
`I ≤ max(T, 1) N` and `A ≤ N`, and for `K, K_T ≥ 0`,

`K I + K_T A ≤ (K max(T, 1) + K_T) N`,

which turns (3.2) into a bound of the data size of the coefficient differences by `N`. No
measurability is needed: a finite sum of lower integrals is at most the lower integral of the
sum.

## Main statements

* `le_lintegral_finsetSum` — superadditivity of the lower integral over a finite sum.
* `sum_energy_le_mul_lintegral_biSup_esq` — the energies of a family by its running supremum.
* `lintegral_esq_le_lintegral_biSup_esq` — a value at a time of `[0, T]` by the running
  supremum.
* `energies_le_supSize` — `I ≤ max(T, 1) N`.
* `lintegral_esq_terminal_le_supSize` — `A ≤ N`.
* `energies_add_terminal_le_supSize` — `K I + K_T A ≤ (K max(T, 1) + K_T) N`.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.Stability LevyStochCalc

universe u v

/-- **A finite sum of lower integrals is at most the lower integral of the sum.** -/
theorem le_lintegral_finsetSum {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    ∑ i ∈ s, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑ i ∈ s, f i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  {ν : Measure E} {T : ℝ}

/-- **The energies of a family by its running supremum**:
`∑_i 𝔼 ∫_0^T x_i(s)² ds ≤ T 𝔼 sup_{t ≤ T} |x_t|²`. -/
theorem sum_energy_le_mul_lintegral_biSup_esq {ι : Type*} [Fintype ι] (x : ι → ℝ → Ω → ℝ) :
    ∑ i, Brownian.Ito.energy P T (fun ω s => x i s ω)
      ≤ ENNReal.ofReal T * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂P := by
  unfold Brownian.Ito.energy
  calc ∑ i, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖x i s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∑ i, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖x i s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        le_lintegral_finsetSum _ _
    _ ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, esq (fun i => x i s ω) ∂volume ∂P :=
        lintegral_mono fun ω => le_lintegral_finsetSum _ _
    _ ≤ ∫⁻ ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
          (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂volume ∂P := by
        refine lintegral_mono fun ω => lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => esq (fun i => x i t ω)) s hs
    _ = ENNReal.ofReal T * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂P := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun ω => ?_
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]

/-- **A value at a time of `[0, T]` by the running supremum**: `𝔼|x_t|² ≤ 𝔼 sup_{s ≤ T} |x_s|²`
for `t ∈ [0, T]`. -/
theorem lintegral_esq_le_lintegral_biSup_esq {ι : Type*} [Fintype ι] (x : ι → ℝ → Ω → ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, esq (fun i => x i t ω) ∂P
      ≤ ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i s ω)) ∂P :=
  lintegral_mono fun ω =>
    le_iSup₂ (f := fun s (_ : s ∈ Set.Icc (0 : ℝ) T) => esq (fun i => x i s ω)) t ht

variable {n m d : ℕ}

/-- **The energies of a difference by its size with running suprema**:
`𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²) ≤ max(T, 1) N`. -/
theorem energies_le_supSize (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ) :
    ∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
        + ∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
        + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)
      ≤ ENNReal.ofReal (max T 1) * supSize P ν T X Y Z U := by
  have hMT : ENNReal.ofReal T ≤ ENNReal.ofReal (max T 1) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hM1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max T 1) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  unfold supSize
  rw [mul_add, mul_add, mul_add]
  gcongr
  · exact (sum_energy_le_mul_lintegral_biSup_esq X).trans (mul_le_mul_left hMT _)
  · exact (sum_energy_le_mul_lintegral_biSup_esq Y).trans (mul_le_mul_left hMT _)
  · exact le_mul_of_one_le_left' hM1
  · exact le_mul_of_one_le_left' hM1

/-- **The terminal second moment of a difference by its size with running suprema**:
`𝔼|δX_T|² ≤ N` for `T ≥ 0`. -/
theorem lintegral_esq_terminal_le_supSize (hT : 0 ≤ T) (X : Fin n → ℝ → Ω → ℝ)
    (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ) :
    ∫⁻ ω, esq (fun i => X i T ω) ∂P ≤ supSize P ν T X Y Z U := by
  unfold supSize
  exact (lintegral_esq_le_lintegral_biSup_esq X ⟨hT, le_rfl⟩).trans
    (le_self_add.trans (le_self_add.trans le_self_add))

/-- **The weighted energies and terminal moment by the size with running suprema**: for
`K, K_T ≥ 0` and `T ≥ 0`,
`K 𝔼 ∫_0^T (|δX|² + |δY|² + |δZ|²_F + ‖δU‖²) + K_T 𝔼|δX_T|² ≤ (K max(T, 1) + K_T) N`. -/
theorem energies_add_terminal_le_supSize {K KT : ℝ} (hK : 0 ≤ K) (hKT : 0 ≤ KT) (hT : 0 ≤ T)
    (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
    (U : Fin m → ℝ → Ω → E → ℝ) :
    ENNReal.ofReal K * (∑ i, Brownian.Ito.energy P T (fun ω s => X i s ω)
          + ∑ k, Brownian.Ito.energy P T (fun ω s => Y k s ω)
          + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e))
        + ENNReal.ofReal KT * ∫⁻ ω, esq (fun i => X i T ω) ∂P
      ≤ ENNReal.ofReal (K * max T 1 + KT) * supSize P ν T X Y Z U := by
  rw [ENNReal.ofReal_add (mul_nonneg hK (le_max_of_le_right zero_le_one)) hKT,
    ENNReal.ofReal_mul hK, add_mul, mul_assoc]
  gcongr
  · exact energies_le_supSize X Y Z U
  · exact lintegral_esq_terminal_le_supSize hT X Y Z U

end MVFBSDEJ.WellPosedness.Existence
