/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Existence.PaperAdmissible

/-!
# A tuple of `ℍ²` as a progressive tuple

A tuple `Θ = (X, Y, Z, U)` of `ℍ²` (`PaperWeakTuple`) constrains `X` and `Y` on `[0, T]`
only. Extended by `0` before `0` and frozen after `T` (`exists_adapted_rightCont_extension`), it
is a progressive tuple with the same values on `[0, T]`, so its tuple `Θ_s` is strongly
`ℱ_s`-measurable at every `s ∈ [0, T]` and square integrable at almost every `s ∈ [0, T]`, and
its jump channel is almost surely square integrable in the mark at almost every time.

For jointly measurable coordinate processes the time integral of their expected squares is at
most `T` times the expected running suprema of `X` and `Y` plus the energies of `Z` and `U`:

`∫_0^T 𝔼(|X_s|² + |Y_s|² + |Z_s|²_F + ‖U_s‖²_{L²(ν)}) ds
  ≤ T 𝔼 sup_{t ≤ T} |X_t|² + T 𝔼 sup_{t ≤ T} |Y_t|² + 𝔼 ∫_0^T (|Z_s|²_F + ‖U_s‖²) ds`.

## Main statements

* `PaperWeakTuple.exists_progTuple` — the extension is a progressive tuple.
* `PaperWeakTuple.stronglyMeasurable_tupleAt` — `Θ_s` is strongly `ℱ_s`-measurable on `[0, T]`.
* `PaperWeakTuple.ae_memLp_tupleAt` — `Θ_s` is square integrable at almost every time.
* `PaperWeakTuple.ae_ae_memLp_jump` — the jump channel is square integrable in the mark.
* `setLIntegral_lintegral_coords_le` — the bound of the time integral by suprema and energies.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.Stability Dissertation.WellPosedness.Existence
  LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v

/-! ### Suprema and energies -/

section Coords

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SFinite ν] {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Tonelli for a finite sum**: for jointly measurable `F_k`,
`∫_S ∫_Ω ∑_k F_k(ω, s) dP ds = ∑_k ∫_Ω ∫_S F_k(ω, s) ds dP`. -/
theorem setLIntegral_lintegral_sum_eq {ι : Type*} [Fintype ι] {F : ι → Ω × ℝ → ℝ≥0∞}
    (hF : ∀ k, Measurable (F k)) (S : Set ℝ) :
    ∫⁻ s in S, ∫⁻ ω, ∑ k, F k (ω, s) ∂P = ∑ k, ∫⁻ ω, ∫⁻ s in S, F k (ω, s) ∂volume ∂P := by
  have hm : Measurable fun p : Ω × ℝ => ∑ k, F k p := Finset.measurable_sum _ fun k _ => hF k
  rw [lintegral_lintegral_swap (f := fun s ω => ∑ k, F k (ω, s))
    ((hm.comp measurable_swap).aemeasurable),
    ← lintegral_finsetSum _ fun k _ => (hF k).lintegral_prod_right']
  exact lintegral_congr fun ω =>
    lintegral_finsetSum _ fun k _ => (hF k).comp (measurable_const.prodMk measurable_id)

/-- **The time integral of the expected squares by suprema and energies.** For jointly measurable
coordinate processes,
`∫_0^T 𝔼(|X_s|² + |Y_s|² + |Z_s|²_F + ‖U_s‖²_{L²(ν)}) ds
  ≤ T 𝔼 sup_{t ≤ T} |X_t|² + T 𝔼 sup_{t ≤ T} |Y_t|² + 𝔼 ∫_0^T (|Z_s|²_F + ‖U_s‖²) ds`,
in `[0, ∞]`. -/
theorem setLIntegral_lintegral_coords_le {T : ℝ} {X : Fin n → ℝ → Ω → ℝ}
    {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
    (hX : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω))
    (hY : ∀ k, Measurable (Function.uncurry fun ω s => Y k s ω))
    (hZ : ∀ k j, Measurable (Function.uncurry fun ω s => Z k s ω j))
    (hU : ∀ k, Measurable fun p : Ω × ℝ × E => U k p.2.1 p.1 p.2.2) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, (esq (fun i => X i s ω) + esq (fun k => Y k s ω)
        + ∑ k, esq (Z k s ω) + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P
      ≤ ENNReal.ofReal T * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P
        + ENNReal.ofReal T * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun k => Y k t ω)) ∂P
        + ((∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j))
          + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)) := by
  -- the four integrands, jointly measurable
  have mX : Measurable fun p : Ω × ℝ => esq (fun i => X i p.2 p.1) :=
    Finset.measurable_sum _ fun i _ => (hX i).nnnorm.coe_nnreal_ennreal.pow_const 2
  have mY : Measurable fun p : Ω × ℝ => esq (fun k => Y k p.2 p.1) :=
    Finset.measurable_sum _ fun k _ => (hY k).nnnorm.coe_nnreal_ennreal.pow_const 2
  have mZ : ∀ k j, Measurable fun p : Ω × ℝ => (‖Z k p.2 p.1 j‖₊ : ℝ≥0∞) ^ 2 := fun k j =>
    (hZ k j).nnnorm.coe_nnreal_ennreal.pow_const 2
  have mZs : Measurable fun p : Ω × ℝ => ∑ k, esq (Z k p.2 p.1) :=
    Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun j _ => mZ k j
  have mU : ∀ k, Measurable fun p : Ω × ℝ => ∫⁻ e, (‖U k p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν := fun k =>
    (((hU k).nnnorm.coe_nnreal_ennreal.pow_const 2).comp (by fun_prop :
      Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))).lintegral_prod_right'
  have mUs : Measurable fun p : Ω × ℝ => ∑ k, ∫⁻ e, (‖U k p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
    Finset.measurable_sum _ fun k _ => mU k
  have sec : ∀ {f : Ω × ℝ → ℝ≥0∞}, Measurable f → ∀ s, Measurable fun ω => f (ω, s) :=
    fun hf s => hf.comp (measurable_id.prodMk measurable_const)
  -- split the inner and the outer integrals
  have hsplit : ∀ s, ∫⁻ ω, (esq (fun i => X i s ω) + esq (fun k => Y k s ω)
      + ∑ k, esq (Z k s ω) + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P
      = ∫⁻ ω, esq (fun i => X i s ω) ∂P + ∫⁻ ω, esq (fun k => Y k s ω) ∂P
        + ∫⁻ ω, ∑ k, esq (Z k s ω) ∂P
        + ∫⁻ ω, ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P := fun s => by
    rw [lintegral_add_right _ (sec mUs s), lintegral_add_right _ (sec mZs s),
      lintegral_add_right _ (sec mY s)]
  have pX : Measurable fun s => ∫⁻ ω, esq (fun i => X i s ω) ∂P := mX.lintegral_prod_left'
  have pY : Measurable fun s => ∫⁻ ω, esq (fun k => Y k s ω) ∂P := mY.lintegral_prod_left'
  have pZ : Measurable fun s => ∫⁻ ω, ∑ k, esq (Z k s ω) ∂P := mZs.lintegral_prod_left'
  have pU : Measurable fun s => ∫⁻ ω, ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P :=
    mUs.lintegral_prod_left'
  simp_rw [hsplit]
  rw [lintegral_add_right _ pU, lintegral_add_right _ pZ, lintegral_add_right _ pY]
  -- the suprema
  have hsup : ∀ {ι : Type} [Fintype ι] {x : ι → ℝ → Ω → ℝ},
      ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, esq (fun i => x i s ω) ∂P
        ≤ ENNReal.ofReal T * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂P := by
    intro ι _ x
    calc ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, esq (fun i => x i s ω) ∂P
        ≤ ∫⁻ _ in Set.Icc (0 : ℝ) T,
            ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂P :=
          setLIntegral_mono measurable_const fun s hs => lintegral_mono fun ω =>
            le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => esq (fun i => x i t ω)) s hs
      _ = _ := by
          rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]
  -- the energies, by Tonelli
  have hZe : ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, ∑ k, esq (Z k s ω) ∂P
      = ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j) := by
    have h := setLIntegral_lintegral_sum_eq (P := P)
      (F := fun (p : Fin m × Fin d) (q : Ω × ℝ) => (‖Z p.1 q.2 q.1 p.2‖₊ : ℝ≥0∞) ^ 2)
      (fun p => mZ p.1 p.2) (Set.Icc (0 : ℝ) T)
    simp only [esq, Brownian.Ito.energy, ← Fintype.sum_prod_type'] at h ⊢
    exact h
  have hUe : ∫⁻ s in Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P
      = ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e) :=
    setLIntegral_lintegral_sum_eq (P := P)
      (F := fun k (q : Ω × ℝ) => ∫⁻ e, (‖U k q.2 q.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν) mU _
  rw [hZe, hUe]
  exact (add_assoc _ _ _).trans_le (add_le_add (add_le_add hsup hsup) le_rfl)

end Coords

/-! ### The extension of a tuple of `ℍ²` -/

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ}

namespace PaperWeakTuple

variable (hΘ : PaperWeakTuple ℱ P ν T X Y Z U)
include hΘ

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] [IsProbabilityMeasure P] in
/-- **A tuple of `ℍ²` extends to a progressive tuple.** For `T ≥ 0` there are `X'`, `Y'`
equal to `X`, `Y` at every time of `[0, T]` such that `(X', Y', Z, U)` is a progressive tuple,
the coordinates of `X'` and `Y'` having finite energy on `[0, T]`. -/
theorem exists_progTuple (hT : 0 ≤ T) :
    ∃ (X' : Fin n → ℝ → Ω → ℝ) (Y' : Fin m → ℝ → Ω → ℝ),
      (∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, X' i t = X i t)
      ∧ (∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, Y' k t = Y k t)
      ∧ ProgTuple ℱ P ν T X' Y' Z U
      ∧ (∀ i, Brownian.Ito.energy P T (fun ω s => X' i s ω) ≠ ⊤)
      ∧ ∀ k, Brownian.Ito.energy P T (fun ω s => Y' k s ω) ≠ ⊤ := by
  obtain ⟨X', hXe, hXa, hXr⟩ := exists_adapted_rightCont_extension hT hΘ.X_adapted hΘ.X_rightCont
  obtain ⟨Y', hYe, hYa, hYr⟩ := exists_adapted_rightCont_extension hT hΘ.Y_adapted hΘ.Y_rightCont
  refine ⟨X', Y', hXe, hYe,
    { X_adapted := hXa
      X_rightCont := hXr
      Y_adapted := hYa
      Y_rightCont := hYr
      Z_meas := fun k j => Brownian.Ito.measurable_uncurry_of_predictable (hΘ.Z_pred k j)
      Z_prog := fun k =>
        progressivelyMeasurable_of_predictable_of_vanish (hΘ.Z_pred k) (hΘ.Z_vanish k)
      Z_sq := hΘ.Z_sq
      U_meas := fun k => (hΘ.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
      U_prog := fun k => (hΘ.U_pred k).markedProgressivelyMeasurable
      U_sq := hΘ.U_sq }, fun i => ?_, fun k => ?_⟩
  · rw [energy_eq_of_eqOn (hXe i)]
    exact hΘ.X_sq i
  · rw [energy_eq_of_eqOn (hYe k)]
    exact hΘ.Y_sq k

omit [IsProbabilityMeasure P] in
/-- The tuple `Θ_s` of a tuple of `ℍ²` is strongly `ℱ_s`-measurable at every time of
`[0, T]`. -/
theorem stronglyMeasurable_tupleAt {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    StronglyMeasurable[ℱ s] (tupleAt ν X Y Z U s) := by
  obtain ⟨X', Y', hXe, hYe, hP, -, -⟩ := hΘ.exists_progTuple (hs.1.trans hs.2)
  rw [← tupleAt_eq_of_eqOn hXe hYe hs]
  exact hP.stronglyMeasurable_tupleAt s

/-- The tuple `Θ_s` of a tuple of `ℍ²` is square integrable at almost every time of
`[0, T]`. -/
theorem ae_memLp_tupleAt (hT : 0 ≤ T) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (tupleAt ν X Y Z U s) 2 P := by
  obtain ⟨X', Y', hXe, hYe, hP, hXs, hYs⟩ := hΘ.exists_progTuple hT
  filter_upwards [hP.ae_memLp_tupleAt hXs hYs, ae_restrict_mem measurableSet_Icc] with s h hs
  rwa [tupleAt_eq_of_eqOn hXe hYe hs] at h

omit [MeasurableSpace.CountablyGenerated E] in
/-- The jump channel of a tuple of `ℍ²` is square integrable in the mark at almost every
time of `[0, T]`, almost surely. -/
theorem ae_ae_memLp_jump :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, ∀ k,
      MemLp (fun e => U k s ω e) 2 ν := by
  filter_upwards [ae_all_iff.mpr fun k => ae_ae_memLp_of_markedEnergy_ne_top
    ((hΘ.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl) (hΘ.U_sq k)]
    with s hs
  exact ae_all_iff.mpr hs

end PaperWeakTuple

end Dissertation.WellPosedness.System
