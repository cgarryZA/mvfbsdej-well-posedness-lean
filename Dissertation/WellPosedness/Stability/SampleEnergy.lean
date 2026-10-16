/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.PairDiff
import Dissertation.WellPosedness.Stability.WindowIntegrable

/-!
# Sample energies of the difference system

The forward and backward estimates of Lemma 4.3 of the well-posedness paper read the expected
Lipschitz bound (3.2) at almost every time `s`, where it compares the sample energies
`𝔼|δb_s|² + 𝔼|δσ_s|²_F + 𝔼‖δh_s‖²_{L²(ν)} + 𝔼|δf_s|²` and
`𝔼|δX_s|² + 𝔼|δY_s|² + 𝔼|δZ_s|²_F + 𝔼‖δU_s‖²_{L²(ν)}`, and integrate the result in time. This
file records the sample energy `∑_i 𝔼[x_i(s)²]` of a finite family of processes at a time `s`
and its marked analogue, whose time integrals over `[0, T]` are the window energies and whose
real values are sums of second moments; the bound `(λ x + q)² ≤ 2 x² + 2 q²` for `λ² ≤ 1` in
this form; and the six pieces of a finite data size.

## Main definitions

* `sampleEnergy` — `∑_i 𝔼[x_i(s)²]`.
* `markedSampleEnergy` — `∑_i 𝔼 ∫_E x_i(s, e)² ν(de)`.

## Main statements

* `lintegral_sampleEnergy`, `lintegral_markedSampleEnergy` — the time integrals over `[0, T]`
  are the window energies.
* `lintegral_sampleEnergy_add` — the same for a triple `(x, z, u)`.
* `toReal_sampleEnergy`, `toReal_lintegral_esq` — real values as sums of second moments.
* `sampleEnergy_mul_add_le`, `markedSampleEnergy_mul_add_le` — the sample energy of `λ x + q`.
* `lt_top_of_dataSize_ne_top`, `toReal_dataSize` — the pieces of a finite data size.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc Dissertation.WellPosedness.BrownianPoisson

universe u v w

/-- `‖x‖₊² = x · x` in `ℝ≥0∞`. -/
theorem sq_nnnorm_eq_ofReal (x : ℝ) : (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x * x) := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from rfl, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, sq]

/-- For `λ² ≤ 1`, `(λ x + q)² ≤ 2 x² + 2 q²`. -/
theorem sq_nnnorm_mul_add_le {l : ℝ} (hl : l ^ 2 ≤ 1) (x q : ℝ) :
    (‖l * x + q‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖q‖₊ : ℝ≥0∞) ^ 2 := by
  rw [sq_nnnorm_eq_ofReal, sq_nnnorm_eq_ofReal, sq_nnnorm_eq_ofReal]
  calc ENNReal.ofReal ((l * x + q) * (l * x + q)) ≤ ENNReal.ofReal (2 * (x * x) + 2 * (q * q)) :=
        ENNReal.ofReal_le_ofReal (by
          nlinarith [sq_nonneg (l * x - q), mul_le_mul_of_nonneg_right hl (mul_self_nonneg x)])
    _ = _ := by
        rw [ENNReal.ofReal_add (mul_nonneg zero_le_two (mul_self_nonneg x))
            (mul_nonneg zero_le_two (mul_self_nonneg q)),
          ENNReal.ofReal_mul (p := 2) (q := x * x) zero_le_two,
          ENNReal.ofReal_mul (p := 2) (q := q * q) zero_le_two, ENNReal.ofReal_ofNat]

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {ι : Type*} [Fintype ι]

/-- The sample energy `∑_i 𝔼[x_i(s)²]` at time `s` of a finite family of processes. -/
noncomputable def sampleEnergy (P : Measure Ω) (x : ι → Ω → ℝ → ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∑ i, ∫⁻ ω, (‖x i ω s‖₊ : ℝ≥0∞) ^ 2 ∂P

/-- The marked sample energy `∑_i 𝔼 ∫_E x_i(s, e)² ν(de)` at time `s` of a finite family of
marked processes. -/
noncomputable def markedSampleEnergy (P : Measure Ω) (ν : Measure E) (x : ι → Ω → ℝ → E → ℝ)
    (s : ℝ) : ℝ≥0∞ :=
  ∑ i, ∫⁻ ω, ∫⁻ e, (‖x i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P

/-! ### Time integrals -/

/-- The mark energy density `(ω, s) ↦ ∫_E φ(ω, s, e)² ν(de)` is jointly measurable. -/
theorem measurable_uncurry_lintegral_sq_mark [SFinite ν] {φ : Ω → ℝ → E → ℝ}
    (hφ : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) :
    Measurable (Function.uncurry fun ω s => ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) :=
  ((hφ.nnnorm.coe_nnreal_ennreal.pow_const 2).comp (by fun_prop :
    Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))).lintegral_prod_right'

/-- The sample energy is measurable in time. -/
theorem measurable_sampleEnergy [SFinite P] {x : ι → Ω → ℝ → ℝ}
    (hx : ∀ i, Measurable (Function.uncurry (x i))) : Measurable (sampleEnergy P x) :=
  Finset.measurable_sum _ fun i _ =>
    ((hx i).nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_left'

/-- The marked sample energy is measurable in time. -/
theorem measurable_markedSampleEnergy [SFinite P] [SFinite ν] {x : ι → Ω → ℝ → E → ℝ}
    (hx : ∀ i, Measurable fun p : Ω × ℝ × E => x i p.1 p.2.1 p.2.2) :
    Measurable (markedSampleEnergy P ν x) :=
  Finset.measurable_sum _ fun i _ =>
    (measurable_uncurry_lintegral_sq_mark (hx i)).lintegral_prod_left'

/-- **The time integral of the sample energy over `[0, T]` is the window energy.** -/
theorem lintegral_sampleEnergy [SFinite P] {x : ι → Ω → ℝ → ℝ}
    (hx : ∀ i, Measurable (Function.uncurry (x i))) (T : ℝ) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, sampleEnergy P x s = ∑ i, Brownian.Ito.energy P T (x i) := by
  have hm : ∀ i, Measurable fun s => ∫⁻ ω, (‖x i ω s‖₊ : ℝ≥0∞) ^ 2 ∂P := fun i =>
    ((hx i).nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_left'
  unfold sampleEnergy
  rw [lintegral_finsetSum' _ fun i _ => (hm i).aemeasurable]
  exact Finset.sum_congr rfl fun i _ =>
    (lintegral_lintegral_swap ((hx i).nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable).symm

/-- **The time integral of the marked sample energy over `[0, T]` is the marked window
energy.** -/
theorem lintegral_markedSampleEnergy [SFinite P] [SFinite ν] {x : ι → Ω → ℝ → E → ℝ}
    (hx : ∀ i, Measurable fun p : Ω × ℝ × E => x i p.1 p.2.1 p.2.2) (T : ℝ) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, markedSampleEnergy P ν x s
      = ∑ i, Poisson.Compensated.markedEnergy P ν T (x i) := by
  have hm : ∀ i, Measurable fun s => ∫⁻ ω, ∫⁻ e, (‖x i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P := fun i =>
    (measurable_uncurry_lintegral_sq_mark (hx i)).lintegral_prod_left'
  unfold markedSampleEnergy
  rw [lintegral_finsetSum' _ fun i _ => (hm i).aemeasurable]
  exact Finset.sum_congr rfl fun i _ =>
    (lintegral_lintegral_swap (measurable_uncurry_lintegral_sq_mark (hx i)).aemeasurable).symm

/-- The time integral over `[0, T]` of the sample energy of a triple `(x, z, u)` — a family, a
family of families and a marked family — is the sum of their window energies. -/
theorem lintegral_sampleEnergy_add [SFinite P] [SFinite ν] {κ ζ ι' : Type*} [Fintype κ]
    [Fintype ζ] [Fintype ι'] {x : ι → Ω → ℝ → ℝ} {z : κ → ζ → Ω → ℝ → ℝ}
    {u : ι' → Ω → ℝ → E → ℝ} (hx : ∀ i, Measurable (Function.uncurry (x i)))
    (hz : ∀ k j, Measurable (Function.uncurry (z k j)))
    (hu : ∀ i, Measurable fun p : Ω × ℝ × E => u i p.1 p.2.1 p.2.2) (T : ℝ) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, (sampleEnergy P x s + ∑ k, sampleEnergy P (z k) s
        + markedSampleEnergy P ν u s)
      = ∑ i, Brownian.Ito.energy P T (x i) + ∑ k, ∑ j, Brownian.Ito.energy P T (z k j)
        + ∑ i, Poisson.Compensated.markedEnergy P ν T (u i) := by
  have hxz : Measurable fun s => sampleEnergy P x s + ∑ k, sampleEnergy P (z k) s :=
    (measurable_sampleEnergy hx).add
      (Finset.measurable_sum _ fun k _ => measurable_sampleEnergy (hz k))
  rw [lintegral_add_left hxz, lintegral_add_left (measurable_sampleEnergy hx),
    lintegral_finsetSum' _ fun k _ => (measurable_sampleEnergy (hz k)).aemeasurable,
    lintegral_sampleEnergy hx, lintegral_markedSampleEnergy hu]
  simp only [lintegral_sampleEnergy (hz _)]

/-- The sample energy of a triple `(x, z, u)` is measurable in time. -/
theorem measurable_sampleEnergy_add [SFinite P] [SFinite ν] {κ ζ ι' : Type*} [Fintype κ]
    [Fintype ζ] [Fintype ι'] {x : ι → Ω → ℝ → ℝ} {z : κ → ζ → Ω → ℝ → ℝ}
    {u : ι' → Ω → ℝ → E → ℝ} (hx : ∀ i, Measurable (Function.uncurry (x i)))
    (hz : ∀ k j, Measurable (Function.uncurry (z k j)))
    (hu : ∀ i, Measurable fun p : Ω × ℝ × E => u i p.1 p.2.1 p.2.2) :
    Measurable fun s => sampleEnergy P x s + ∑ k, sampleEnergy P (z k) s
        + markedSampleEnergy P ν u s :=
  ((measurable_sampleEnergy hx).add (Finset.measurable_sum _ fun k _ =>
    measurable_sampleEnergy (hz k))).add (measurable_markedSampleEnergy hu)

/-! ### Real values -/

omit [MeasurableSpace E] in
/-- The real sample energy of square-integrable coordinates is the sum of their second
moments. -/
theorem toReal_sampleEnergy {x : ι → Ω → ℝ → ℝ} {s : ℝ}
    (hx : ∀ i, MemLp (fun ω => x i ω s) 2 P) :
    (sampleEnergy P x s).toReal = ∑ i, ∫ ω, x i ω s * x i ω s ∂P := by
  unfold sampleEnergy
  rw [ENNReal.toReal_sum fun i _ => (Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two (hx i)).ne]
  exact Finset.sum_congr rfl fun i _ => (Ito.SecondMoment.integral_mul_self_eq_toReal (hx i)).symm

omit [MeasurableSpace E] in
/-- `𝔼|x|²` for square-integrable coordinates is the sum of their second moments. -/
theorem toReal_lintegral_esq {x : ι → Ω → ℝ} (hx : ∀ i, MemLp (x i) 2 P) :
    (∫⁻ ω, esq (fun i => x i ω) ∂P).toReal = ∑ i, ∫ ω, x i ω * x i ω ∂P := by
  unfold esq
  rw [lintegral_finsetSum' _ fun i _ =>
      ((hx i).aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2,
    ENNReal.toReal_sum fun i _ => (Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two (hx i)).ne]
  exact Finset.sum_congr rfl fun i _ => (Ito.SecondMoment.integral_mul_self_eq_toReal (hx i)).symm

/-! ### The sample energy of `λ x + q` -/

omit [MeasurableSpace E] in
/-- For `λ² ≤ 1`, the sample energy of `λ x + q` is at most twice that of `x` plus twice that
of `q`. -/
theorem sampleEnergy_mul_add_le {l : ℝ} (hl : l ^ 2 ≤ 1) (x q : ι → Ω → ℝ → ℝ) (s : ℝ)
    (hq : ∀ i, AEMeasurable (fun ω => q i ω s) P) :
    sampleEnergy P (fun i ω s => l * x i ω s + q i ω s) s
      ≤ 2 * sampleEnergy P x s + 2 * sampleEnergy P q s := by
  unfold sampleEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∫⁻ ω, (‖l * x i ω s + q i ω s‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ ω, (2 * (‖x i ω s‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖q i ω s‖₊ : ℝ≥0∞) ^ 2) ∂P :=
        lintegral_mono fun ω => sq_nnnorm_mul_add_le hl _ _
    _ = _ := by
        rw [lintegral_add_right' _ (((hq i).nnnorm.coe_nnreal_ennreal.pow_const 2).const_mul 2),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]

/-- For `λ² ≤ 1`, the marked sample energy of `λ x + q` is at most twice that of `x` plus twice
that of `q`. -/
theorem markedSampleEnergy_mul_add_le [SFinite ν] {l : ℝ} (hl : l ^ 2 ≤ 1)
    (x q : ι → Ω → ℝ → E → ℝ) (s : ℝ) (hq : ∀ i, Measurable fun p : Ω × E => q i p.1 s p.2) :
    markedSampleEnergy P ν (fun i ω s e => l * x i ω s e + q i ω s e) s
      ≤ 2 * markedSampleEnergy P ν x s + 2 * markedSampleEnergy P ν q s := by
  unfold markedSampleEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hq2 : Measurable fun p : Ω × E => (‖q i p.1 s p.2‖₊ : ℝ≥0∞) ^ 2 :=
    (hq i).nnnorm.coe_nnreal_ennreal.pow_const 2
  have hqe : ∀ ω, Measurable fun e => (‖q i ω s e‖₊ : ℝ≥0∞) ^ 2 := fun ω =>
    hq2.comp (measurable_const.prodMk measurable_id)
  have hin : ∀ ω, ∫⁻ e, (‖l * x i ω s e + q i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ 2 * ∫⁻ e, (‖x i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν + 2 * ∫⁻ e, (‖q i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
    intro ω
    calc ∫⁻ e, (‖l * x i ω s e + q i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν
        ≤ ∫⁻ e, (2 * (‖x i ω s e‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖q i ω s e‖₊ : ℝ≥0∞) ^ 2) ∂ν :=
          lintegral_mono fun e => sq_nnnorm_mul_add_le hl _ _
      _ = _ := by
          rw [lintegral_add_right' _ ((hqe ω).const_mul 2).aemeasurable,
            lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
  calc ∫⁻ ω, ∫⁻ e, (‖l * x i ω s e + q i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P
      ≤ ∫⁻ ω, (2 * ∫⁻ e, (‖x i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν
          + 2 * ∫⁻ e, (‖q i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P := lintegral_mono hin
    _ = _ := by
        rw [lintegral_add_right' _ (hq2.lintegral_prod_right'.const_mul 2).aemeasurable,
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]

/-! ### The data size -/

variable {d n m : ℕ}

/-- The pieces of a finite data size are finite. -/
theorem lt_top_of_dataSize_ne_top {T : ℝ} {ξ₀ : Fin n → Ω → ℝ} {qb : Fin n → Ω → ℝ → ℝ}
    {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ} {qf : Fin m → Ω → ℝ → ℝ}
    {qg : Fin m → Ω → ℝ} (h : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) :
    ∫⁻ ω, esq (fun i => ξ₀ i ω) ∂P < ⊤ ∧ ∫⁻ ω, esq (fun k => qg k ω) ∂P < ⊤
      ∧ (∀ i, Brownian.Ito.energy P T (qb i) < ⊤)
      ∧ (∀ i j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j) < ⊤)
      ∧ (∀ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e) < ⊤)
      ∧ (∀ k, Brownian.Ito.energy P T (qf k) < ⊤) := by
  unfold dataSize at h
  simp only [ne_eq, ENNReal.add_eq_top, ENNReal.sum_eq_top, not_or, not_exists, not_and,
    Finset.mem_univ, true_implies] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨lt_top_iff_ne_top.mpr h1, lt_top_iff_ne_top.mpr h2, fun i => lt_top_iff_ne_top.mpr (h3 i),
    fun i j => lt_top_iff_ne_top.mpr (h4 i j), fun i => lt_top_iff_ne_top.mpr (h5 i),
    fun k => lt_top_iff_ne_top.mpr (h6 k)⟩

/-- The real data size is the sum of the real values of its six pieces. -/
theorem toReal_dataSize {T : ℝ} {ξ₀ : Fin n → Ω → ℝ} {qb : Fin n → Ω → ℝ → ℝ}
    {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ} {qf : Fin m → Ω → ℝ → ℝ}
    {qg : Fin m → Ω → ℝ} (h : dataSize P ν T ξ₀ qb qσ qh qf qg ≠ ⊤) :
    (dataSize P ν T ξ₀ qb qσ qh qf qg).toReal
      = (∫⁻ ω, esq (fun i => ξ₀ i ω) ∂P).toReal + (∫⁻ ω, esq (fun k => qg k ω) ∂P).toReal
        + (∑ i, Brownian.Ito.energy P T (qb i)).toReal
        + (∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j)).toReal
        + (∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e)).toReal
        + (∑ k, Brownian.Ito.energy P T (qf k)).toReal := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := lt_top_of_dataSize_ne_top h
  have s3 : ∑ i, Brownian.Ito.energy P T (qb i) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => (h3 i).ne
  have s4 : ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ i s ω j) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => ENNReal.sum_ne_top.mpr fun j _ => (h4 i j).ne
  have s5 : ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh i s ω e) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => (h5 i).ne
  have s6 : ∑ k, Brownian.Ito.energy P T (qf k) ≠ ⊤ := ENNReal.sum_ne_top.mpr fun k _ => (h6 k).ne
  unfold dataSize
  rw [ENNReal.toReal_add (by finiteness) s6, ENNReal.toReal_add (by finiteness) s5,
    ENNReal.toReal_add (by finiteness) s4, ENNReal.toReal_add (by finiteness) s3,
    ENNReal.toReal_add h1.ne h2.ne]

end Dissertation.WellPosedness.Stability
