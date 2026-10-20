/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.Coefficients
import MVFBSDEJ.WellPosedness.Stability.PairDiff

/-!
# The algebra of forcings and the data size

The forcings `q = (q^b, q^σ, q^h, q^f, q^g_T)` of the `λ`-system (4.1) form a vector space: a
linear combination `a q¹ + c q²` of forcings is a forcing. The continuation argument measures
forcings, and their differences, by the data size of (4.14),

`dataSize(ξ₀, q) = 𝔼|ξ₀|² + 𝔼|q^g_T|² + 𝔼 ∫_0^T (|q^b|² + |q^σ|²_F + ‖q^h‖²_{L²(ν)} + |q^f|²)`,

which is quadratic: `dataSize(a ξ₀, a q) = a² dataSize(ξ₀, q)`, and satisfies the triangle
inequality in the squared form
`dataSize(x + y) ≤ 2 dataSize(x) + 2 dataSize(y)`, hence
`dataSize(x − z) ≤ 2 dataSize(x − y) + 2 dataSize(y − z)`.
Only the first summand needs to be measurable in these bounds: a lower integral is additive as
soon as one of the two summands is measurable.

## Main statements

* `Forcing.linComb`, `Forcing.add`, `Forcing.smul` — linear combinations of forcings; the
  difference is `Forcing.sub`.
* `energy_const_mul`, `markedEnergy_const_mul`, `lintegral_esq_const_mul` — scaling of the
  pieces of the data size.
* `energy_add_le`, `markedEnergy_add_le`, `lintegral_esq_add_le` — the squared triangle
  inequality for the pieces.
* `dataSize_smul` — `dataSize` is quadratic.
* `dataSize_add_le`, `dataSize_sub_le` — the squared triangle inequality for `dataSize`.
-/

open MeasureTheory
open scoped NNReal ENNReal

/-! ### Linear combinations of forcings -/

namespace MVFBSDEJ.WellPosedness.System

open LevyStochCalc

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] {n m d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} {T : ℝ}
  {qb qb₁ qb₂ : Fin n → Ω → ℝ → ℝ} {qσ qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ}
  {qh qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ} {qf qf₁ qf₂ : Fin m → Ω → ℝ → ℝ}
  {qg qg₁ qg₂ : Fin m → Ω → ℝ}

/-- **Linear combinations of forcings are forcings**: for forcings `q¹, q²` and reals `a, c`,
`a q¹ + c q²` is a forcing. -/
theorem Forcing.linComb (h₁ : Forcing ℱ P ν T qb₁ qσ₁ qh₁ qf₁ qg₁)
    (h₂ : Forcing ℱ P ν T qb₂ qσ₂ qh₂ qf₂ qg₂) (a c : ℝ) :
    Forcing ℱ P ν T (fun i ω s => a * qb₁ i ω s + c * qb₂ i ω s)
      (fun i s ω j => a * qσ₁ i s ω j + c * qσ₂ i s ω j)
      (fun i s ω e => a * qh₁ i s ω e + c * qh₂ i s ω e)
      (fun k ω s => a * qf₁ k ω s + c * qf₂ k ω s) (fun k ω => a * qg₁ k ω + c * qg₂ k ω) where
  qb_meas i := ((h₁.qb_meas i).const_mul a).add ((h₂.qb_meas i).const_mul c)
  qb_prog i := ((continuous_const_mul a).comp_progressivelyMeasurable (mul_zero a)
    (h₁.qb_prog i)).add ((continuous_const_mul c).comp_progressivelyMeasurable (mul_zero c)
    (h₂.qb_prog i))
  qb_vanish i ω s hs := by simp [h₁.qb_vanish i ω s hs, h₂.qb_vanish i ω s hs]
  qb_sq i := Brownian.Ito.energy_add_ne_top ((h₁.qb_meas i).const_mul a)
    ((h₂.qb_meas i).const_mul c) (Brownian.Ito.energy_const_mul_ne_top (h₁.qb_meas i)
    (h₁.qb_sq i) a) (Brownian.Ito.energy_const_mul_ne_top (h₂.qb_meas i) (h₂.qb_sq i) c)
  qσ_meas i j := ((h₁.qσ_meas i j).const_mul a).add ((h₂.qσ_meas i j).const_mul c)
  qσ_prog i j := ((continuous_const_mul a).comp_progressivelyMeasurable (mul_zero a)
    (h₁.qσ_prog i j)).add ((continuous_const_mul c).comp_progressivelyMeasurable (mul_zero c)
    (h₂.qσ_prog i j))
  qσ_vanish i ω s hs := by
    funext j
    simp [h₁.qσ_vanish i ω s hs, h₂.qσ_vanish i ω s hs]
  qσ_sq i j := Brownian.Ito.energy_add_ne_top ((h₁.qσ_meas i j).const_mul a)
    ((h₂.qσ_meas i j).const_mul c) (Brownian.Ito.energy_const_mul_ne_top (h₁.qσ_meas i j)
    (h₁.qσ_sq i j) a) (Brownian.Ito.energy_const_mul_ne_top (h₂.qσ_meas i j) (h₂.qσ_sq i j) c)
  qh_meas i := ((h₁.qh_meas i).const_mul a).add ((h₂.qh_meas i).const_mul c)
  qh_prog i := Poisson.Compensated.markedProgressivelyMeasurable_add
    (Poisson.Compensated.markedProgressivelyMeasurable_const_mul (h₁.qh_prog i) a)
    (Poisson.Compensated.markedProgressivelyMeasurable_const_mul (h₂.qh_prog i) c)
  qh_vanish i ω s e hs := by simp [h₁.qh_vanish i ω s e hs, h₂.qh_vanish i ω s e hs]
  qh_sq i := Poisson.Compensated.markedEnergy_add_ne_top ((h₁.qh_meas i).const_mul a)
    ((h₂.qh_meas i).const_mul c)
    (Poisson.Compensated.markedEnergy_const_mul_ne_top (h₁.qh_meas i) (h₁.qh_sq i) a)
    (Poisson.Compensated.markedEnergy_const_mul_ne_top (h₂.qh_meas i) (h₂.qh_sq i) c)
  qf_meas k := ((h₁.qf_meas k).const_mul a).add ((h₂.qf_meas k).const_mul c)
  qf_prog k := ((continuous_const_mul a).comp_progressivelyMeasurable (mul_zero a)
    (h₁.qf_prog k)).add ((continuous_const_mul c).comp_progressivelyMeasurable (mul_zero c)
    (h₂.qf_prog k))
  qf_vanish k ω s hs := by simp [h₁.qf_vanish k ω s hs, h₂.qf_vanish k ω s hs]
  qf_sq k := Brownian.Ito.energy_add_ne_top ((h₁.qf_meas k).const_mul a)
    ((h₂.qf_meas k).const_mul c) (Brownian.Ito.energy_const_mul_ne_top (h₁.qf_meas k)
    (h₁.qf_sq k) a) (Brownian.Ito.energy_const_mul_ne_top (h₂.qf_meas k) (h₂.qf_sq k) c)
  qg_meas k := ((h₁.qg_meas k).const_mul a).add ((h₂.qg_meas k).const_mul c)
  qg_sq k := ((h₁.qg_sq k).const_mul a).add ((h₂.qg_sq k).const_mul c)

/-- The sum of two forcings is a forcing. -/
theorem Forcing.add (h₁ : Forcing ℱ P ν T qb₁ qσ₁ qh₁ qf₁ qg₁)
    (h₂ : Forcing ℱ P ν T qb₂ qσ₂ qh₂ qf₂ qg₂) :
    Forcing ℱ P ν T (fun i ω s => qb₁ i ω s + qb₂ i ω s)
      (fun i s ω j => qσ₁ i s ω j + qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e + qh₂ i s ω e)
      (fun k ω s => qf₁ k ω s + qf₂ k ω s) (fun k ω => qg₁ k ω + qg₂ k ω) := by
  simpa only [one_mul] using h₁.linComb h₂ 1 1

/-- A scalar multiple of a forcing is a forcing. -/
theorem Forcing.smul (h : Forcing ℱ P ν T qb qσ qh qf qg) (a : ℝ) :
    Forcing ℱ P ν T (fun i ω s => a * qb i ω s) (fun i s ω j => a * qσ i s ω j)
      (fun i s ω e => a * qh i s ω e) (fun k ω s => a * qf k ω s) (fun k ω => a * qg k ω) := by
  simpa only [zero_mul, add_zero] using h.linComb h a 0

end MVFBSDEJ.WellPosedness.System

/-! ### The data size -/

namespace MVFBSDEJ.WellPosedness.Stability

open LevyStochCalc

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {P : Measure Ω}
  {ν : Measure E} {T : ℝ}

section Scaling

/-- The squared extended norm of `a x` is `a²` times that of `x`. -/
theorem sq_nnnorm_const_mul (a x : ℝ) :
    (‖a * x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (a ^ 2) * (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  rw [Brownian.Ito.sq_nnnorm_eq_ofReal_sq, Brownian.Ito.sq_nnnorm_eq_ofReal_sq,
    ← ENNReal.ofReal_mul (sq_nonneg a), mul_pow]

/-- Scaling an integrand by `a` scales its energy by `a²`. -/
theorem energy_const_mul (a : ℝ) (H : Ω → ℝ → ℝ) :
    Brownian.Ito.energy P T (fun ω s => a * H ω s)
      = ENNReal.ofReal (a ^ 2) * Brownian.Ito.energy P T H := by
  simp only [Brownian.Ito.energy, sq_nnnorm_const_mul,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Scaling a marked integrand by `a` scales its marked energy by `a²`. -/
theorem markedEnergy_const_mul (a : ℝ) (φ : Ω → ℝ → E → ℝ) :
    Poisson.Compensated.markedEnergy P ν T (fun ω s e => a * φ ω s e)
      = ENNReal.ofReal (a ^ 2) * Poisson.Compensated.markedEnergy P ν T φ := by
  simp only [Poisson.Compensated.markedEnergy, sq_nnnorm_const_mul,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Scaling a family of random variables by `a` scales its second moment by `a²`. -/
theorem lintegral_esq_const_mul {ι : Type*} [Fintype ι] (a : ℝ) (x : ι → Ω → ℝ) :
    ∫⁻ ω, esq (fun i => a * x i ω) ∂P = ENNReal.ofReal (a ^ 2) * ∫⁻ ω, esq (fun i => x i ω) ∂P := by
  simp only [esq, sq_nnnorm_const_mul, ← Finset.mul_sum,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

variable {n m d : ℕ}

/-- **The data size is quadratic**: scaling the initial datum and the forcing by `a` scales the
data size by `a²`. -/
theorem dataSize_smul (a : ℝ) (ξ₀ : Fin n → Ω → ℝ) (qb : Fin n → Ω → ℝ → ℝ)
    (qσ : Fin n → ℝ → Ω → Fin d → ℝ) (qh : Fin n → ℝ → Ω → E → ℝ) (qf : Fin m → Ω → ℝ → ℝ)
    (qg : Fin m → Ω → ℝ) :
    dataSize P ν T (fun i ω => a * ξ₀ i ω) (fun i ω s => a * qb i ω s)
        (fun i s ω j => a * qσ i s ω j) (fun i s ω e => a * qh i s ω e)
        (fun k ω s => a * qf k ω s) (fun k ω => a * qg k ω)
      = ENNReal.ofReal (a ^ 2) * dataSize P ν T ξ₀ qb qσ qh qf qg := by
  simp only [dataSize, lintegral_esq_const_mul, energy_const_mul, markedEnergy_const_mul,
    mul_add, Finset.mul_sum]

end Scaling

section Triangle

/-- **The squared triangle inequality for the energy**:
`energy(H₁ + H₂) ≤ 2 energy(H₁) + 2 energy(H₂)`, for a jointly measurable `H₁`. -/
theorem energy_add_le {H₁ : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H₁))
    (H₂ : Ω → ℝ → ℝ) :
    Brownian.Ito.energy P T (fun ω s => H₁ ω s + H₂ ω s)
      ≤ 2 * Brownian.Ito.energy P T H₁ + 2 * Brownian.Ito.energy P T H₂ := by
  unfold Brownian.Ito.energy
  rw [← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
    ← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
    ← lintegral_add_left ((Brownian.Ito.measurable_energyDensity hm T).const_mul 2)]
  refine lintegral_mono fun ω => ?_
  have hs : Measurable fun s => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 :=
    (measurable_nnnorm.comp (hm.comp measurable_prodMk_left)).coe_nnreal_ennreal.pow_const 2
  rw [← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
    ← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top, ← lintegral_add_left (hs.const_mul 2)]
  refine lintegral_mono fun s => ?_
  calc (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2) :=
        Brownian.Ito.sq_nnnorm_add_le_two_mul _ _
    _ = 2 * (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 := mul_add _ _ _

/-- **The squared triangle inequality for the marked energy**:
`markedEnergy(φ₁ + φ₂) ≤ 2 markedEnergy(φ₁) + 2 markedEnergy(φ₂)`, for a jointly measurable
`φ₁`. -/
theorem markedEnergy_add_le [SigmaFinite ν] {φ₁ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2) (φ₂ : Ω → ℝ → E → ℝ) :
    Poisson.Compensated.markedEnergy P ν T (fun ω s e => φ₁ ω s e + φ₂ ω s e)
      ≤ 2 * Poisson.Compensated.markedEnergy P ν T φ₁
        + 2 * Poisson.Compensated.markedEnergy P ν T φ₂ := by
  have hd : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
    Poisson.Compensated.measurable_markedDensity hm T
  unfold Poisson.Compensated.markedEnergy
  rw [← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
    ← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top, ← lintegral_add_left (hd.const_mul 2)]
  refine lintegral_mono fun ω => ?_
  rw [← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
    ← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
    ← lintegral_add_left ((Poisson.Compensated.measurable_markSlice hm ω).const_mul 2)]
  refine lintegral_mono fun s => ?_
  have he : Measurable fun e => (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
    (measurable_nnnorm.comp ((hm.comp (measurable_prodMk_left (x := ω))).comp
      (measurable_prodMk_left (x := s)))).coe_nnreal_ennreal.pow_const 2
  rw [← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
    ← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top, ← lintegral_add_left (he.const_mul 2)]
  refine lintegral_mono fun e => ?_
  calc (‖φ₁ ω s e + φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 + (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2) :=
        Brownian.Ito.sq_nnnorm_add_le_two_mul _ _
    _ = 2 * (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 := mul_add _ _ _

/-- **The squared triangle inequality for the second moment** of a family of random variables:
`𝔼|x + y|² ≤ 2 𝔼|x|² + 2 𝔼|y|²`, for almost everywhere measurable `x`. -/
theorem lintegral_esq_add_le {ι : Type*} [Fintype ι] {x : ι → Ω → ℝ}
    (hx : ∀ i, AEMeasurable (x i) P) (y : ι → Ω → ℝ) :
    ∫⁻ ω, esq (fun i => x i ω + y i ω) ∂P
      ≤ 2 * ∫⁻ ω, esq (fun i => x i ω) ∂P + 2 * ∫⁻ ω, esq (fun i => y i ω) ∂P := by
  have hm : AEMeasurable (fun ω => esq (fun i => x i ω)) P :=
    Finset.aemeasurable_fun_sum _ fun i _ => ((hx i).nnnorm.coe_nnreal_ennreal).pow_const 2
  rw [← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
    ← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top, ← lintegral_add_left' (hm.const_mul 2)]
  refine lintegral_mono fun ω => ?_
  simp only [esq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  calc (‖x i ω + y i ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖x i ω‖₊ : ℝ≥0∞) ^ 2 + (‖y i ω‖₊ : ℝ≥0∞) ^ 2) :=
        Brownian.Ito.sq_nnnorm_add_le_two_mul _ _
    _ = 2 * (‖x i ω‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖y i ω‖₊ : ℝ≥0∞) ^ 2 := mul_add _ _ _

variable [SigmaFinite ν] {n m d : ℕ}

/-- **The squared triangle inequality for the data size**:
`dataSize(x + y) ≤ 2 dataSize(x) + 2 dataSize(y)`, for data `x` whose initial datum and
terminal forcing are almost everywhere measurable and whose other forcings are jointly
measurable. -/
theorem dataSize_add_le {ξ₁ ξ₂ : Fin n → Ω → ℝ} {qb₁ qb₂ : Fin n → Ω → ℝ → ℝ}
    {qσ₁ qσ₂ : Fin n → ℝ → Ω → Fin d → ℝ} {qh₁ qh₂ : Fin n → ℝ → Ω → E → ℝ}
    {qf₁ qf₂ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ : Fin m → Ω → ℝ}
    (hξ : ∀ i, AEMeasurable (ξ₁ i) P) (hb : ∀ i, Measurable (Function.uncurry (qb₁ i)))
    (hσ : ∀ i j, Measurable (Function.uncurry fun ω s => qσ₁ i s ω j))
    (hh : ∀ i, Measurable fun p : Ω × ℝ × E => qh₁ i p.2.1 p.1 p.2.2)
    (hf : ∀ k, Measurable (Function.uncurry (qf₁ k))) (hg : ∀ k, AEMeasurable (qg₁ k) P) :
    dataSize P ν T (fun i ω => ξ₁ i ω + ξ₂ i ω) (fun i ω s => qb₁ i ω s + qb₂ i ω s)
        (fun i s ω j => qσ₁ i s ω j + qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e + qh₂ i s ω e)
        (fun k ω s => qf₁ k ω s + qf₂ k ω s) (fun k ω => qg₁ k ω + qg₂ k ω)
      ≤ 2 * dataSize P ν T ξ₁ qb₁ qσ₁ qh₁ qf₁ qg₁ + 2 * dataSize P ν T ξ₂ qb₂ qσ₂ qh₂ qf₂ qg₂ := by
  have h3 : ∑ i, Brownian.Ito.energy P T (fun ω s => qb₁ i ω s + qb₂ i ω s)
      ≤ 2 * ∑ i, Brownian.Ito.energy P T (qb₁ i) + 2 * ∑ i, Brownian.Ito.energy P T (qb₂ i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => energy_add_le (hb i) (qb₂ i)
  have h4 : ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ₁ i s ω j + qσ₂ i s ω j)
      ≤ 2 * ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ₁ i s ω j)
        + 2 * ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => qσ₂ i s ω j) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      energy_add_le (H₁ := fun ω s => qσ₁ i s ω j) (hσ i j) _
  have h5 : ∑ i, Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => qh₁ i s ω e + qh₂ i s ω e)
      ≤ 2 * ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh₁ i s ω e)
        + 2 * ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => qh₂ i s ω e) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ =>
      markedEnergy_add_le (φ₁ := fun ω s e => qh₁ i s ω e) (hh i) _
  have h6 : ∑ k, Brownian.Ito.energy P T (fun ω s => qf₁ k ω s + qf₂ k ω s)
      ≤ 2 * ∑ k, Brownian.Ito.energy P T (qf₁ k) + 2 * ∑ k, Brownian.Ito.energy P T (qf₂ k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => energy_add_le (hf k) (qf₂ k)
  unfold dataSize
  refine (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (lintegral_esq_add_le hξ ξ₂) (lintegral_esq_add_le hg qg₂)) h3) h4) h5) h6).trans_eq ?_
  ring

/-- **The triangle inequality for the data size of differences**:
`dataSize(x − z) ≤ 2 dataSize(x − y) + 2 dataSize(y − z)`, for data `x, y` whose initial data and
terminal forcings are almost everywhere measurable and whose other forcings are jointly
measurable. -/
theorem dataSize_sub_le {ξ₁ ξ₂ ξ₃ : Fin n → Ω → ℝ} {qb₁ qb₂ qb₃ : Fin n → Ω → ℝ → ℝ}
    {qσ₁ qσ₂ qσ₃ : Fin n → ℝ → Ω → Fin d → ℝ} {qh₁ qh₂ qh₃ : Fin n → ℝ → Ω → E → ℝ}
    {qf₁ qf₂ qf₃ : Fin m → Ω → ℝ → ℝ} {qg₁ qg₂ qg₃ : Fin m → Ω → ℝ}
    (hξ₁ : ∀ i, AEMeasurable (ξ₁ i) P) (hξ₂ : ∀ i, AEMeasurable (ξ₂ i) P)
    (hb₁ : ∀ i, Measurable (Function.uncurry (qb₁ i)))
    (hb₂ : ∀ i, Measurable (Function.uncurry (qb₂ i)))
    (hσ₁ : ∀ i j, Measurable (Function.uncurry fun ω s => qσ₁ i s ω j))
    (hσ₂ : ∀ i j, Measurable (Function.uncurry fun ω s => qσ₂ i s ω j))
    (hh₁ : ∀ i, Measurable fun p : Ω × ℝ × E => qh₁ i p.2.1 p.1 p.2.2)
    (hh₂ : ∀ i, Measurable fun p : Ω × ℝ × E => qh₂ i p.2.1 p.1 p.2.2)
    (hf₁ : ∀ k, Measurable (Function.uncurry (qf₁ k)))
    (hf₂ : ∀ k, Measurable (Function.uncurry (qf₂ k)))
    (hg₁ : ∀ k, AEMeasurable (qg₁ k) P) (hg₂ : ∀ k, AEMeasurable (qg₂ k) P) :
    dataSize P ν T (fun i ω => ξ₁ i ω - ξ₃ i ω) (fun i ω s => qb₁ i ω s - qb₃ i ω s)
        (fun i s ω j => qσ₁ i s ω j - qσ₃ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₃ i s ω e)
        (fun k ω s => qf₁ k ω s - qf₃ k ω s) (fun k ω => qg₁ k ω - qg₃ k ω)
      ≤ 2 * dataSize P ν T (fun i ω => ξ₁ i ω - ξ₂ i ω) (fun i ω s => qb₁ i ω s - qb₂ i ω s)
          (fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j) (fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
          (fun k ω s => qf₁ k ω s - qf₂ k ω s) (fun k ω => qg₁ k ω - qg₂ k ω)
        + 2 * dataSize P ν T (fun i ω => ξ₂ i ω - ξ₃ i ω) (fun i ω s => qb₂ i ω s - qb₃ i ω s)
          (fun i s ω j => qσ₂ i s ω j - qσ₃ i s ω j) (fun i s ω e => qh₂ i s ω e - qh₃ i s ω e)
          (fun k ω s => qf₂ k ω s - qf₃ k ω s) (fun k ω => qg₂ k ω - qg₃ k ω) := by
  have h := dataSize_add_le (P := P) (ν := ν) (T := T)
    (ξ₁ := fun i ω => ξ₁ i ω - ξ₂ i ω) (ξ₂ := fun i ω => ξ₂ i ω - ξ₃ i ω)
    (qb₁ := fun i ω s => qb₁ i ω s - qb₂ i ω s) (qb₂ := fun i ω s => qb₂ i ω s - qb₃ i ω s)
    (qσ₁ := fun i s ω j => qσ₁ i s ω j - qσ₂ i s ω j)
    (qσ₂ := fun i s ω j => qσ₂ i s ω j - qσ₃ i s ω j)
    (qh₁ := fun i s ω e => qh₁ i s ω e - qh₂ i s ω e)
    (qh₂ := fun i s ω e => qh₂ i s ω e - qh₃ i s ω e)
    (qf₁ := fun k ω s => qf₁ k ω s - qf₂ k ω s) (qf₂ := fun k ω s => qf₂ k ω s - qf₃ k ω s)
    (qg₁ := fun k ω => qg₁ k ω - qg₂ k ω) (qg₂ := fun k ω => qg₂ k ω - qg₃ k ω)
    (fun i => (hξ₁ i).sub (hξ₂ i)) (fun i => (hb₁ i).sub (hb₂ i))
    (fun i j => (hσ₁ i j).sub (hσ₂ i j)) (fun i => (hh₁ i).sub (hh₂ i))
    (fun k => (hf₁ k).sub (hf₂ k)) (fun k => (hg₁ k).sub (hg₂ k))
  simpa only [sub_add_sub_cancel] using h

end Triangle

end MVFBSDEJ.WellPosedness.Stability
