/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Stability.WeightedWindow
import Dissertation.WellPosedness.System.BackwardYoung

/-!
# The Young bound inserted in the weighted backward identity

Step 4 of the proof of Lemma 4.3 of the well-posedness paper inserts the Young bound (4.25) of
the driver pairing in the weighted identity (4.24) for `e^{κt} |δY_t|²`. For the difference system
with interior Lipschitz constant `K ≥ 0`, `λ ∈ [0, 1]`, `ε ∈ (0, 1]`, `κ ∈ ℝ` and `t ∈ [0, T]`,
with `C = 2K + 3`,

`e^{κt} 𝔼|δY_t|² + 𝔼 ∫_t^T e^{κs} ((κ − C/ε) |δY_s|² + (1 − ε) (|δZ_s|²_F + ‖δU_s‖²)) ds
  ≤ e^{κT} 𝔼|λ δg + q^g|² + (C/ε) 𝔼 ∫_t^T e^{κs} (|δX_s|² + |q^f_s|²) ds`,

all integrands being integrable for `P ⊗ ds` on `[t, T]`. The Young bound holds at almost every
time in expectation; at almost every time its sides are finite real numbers, and against the
weight `e^{κs}` it integrates over `[t, T]` by Fubini's theorem. For `ε < 1` and `κ > C/ε` the
`δY`-integral on the left is nonnegative and `1 ≤ e^{κs} ≤ e^{κT}` on `[0, T]`, so

`𝔼|δY_t|² + 𝔼 ∫_t^T (|δZ_s|²_F + ‖δU_s‖²) ds
  ≤ (e^{κT} max(1, C/ε) / (1 − ε)) (𝔼|λ δg + q^g|² + 𝔼 ∫_t^T (|δX_s|² + |q^f_s|²) ds)`.

## Main statements

* `integrable_exp_mul_window` — a continuous weight of time keeps integrability on `Ω × [t, T]`.
* `PairDiff.integrable_window` — the integrands of the backward estimate on `Ω × [t, T]`.
* `PairDiff.integral_weighted_young_le` — the Young bound integrated against `e^{κs}`.
* `PairDiff.weighted_window_le` — the Young bound inserted in the weighted identity.
* `PairDiff.window_le` — the backward estimate at every time.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.Stability

open LevyStochCalc.BSDEJ.Solves LevyStochCalc Dissertation.WellPosedness.BrownianPoisson

universe u v w

section Window

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]

omit [SFinite P] in
/-- **A weight of time keeps integrability on a window.** For `f` integrable for `P ⊗ ds` on
`[t, T]`, `e^{κs} f(ω, s)` is integrable there. -/
theorem integrable_exp_mul_window {f : Ω × ℝ → ℝ} (κ : ℝ) {t T : ℝ}
    (hf : Integrable f (P.prod (volume.restrict (Set.Icc t T)))) :
    Integrable (fun q : Ω × ℝ => Real.exp (κ * q.2) * f q)
      (P.prod (volume.restrict (Set.Icc t T))) := by
  have hc : ContinuousOn (fun s : ℝ => Real.exp (κ * s)) (Set.Icc t T) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact hf.bdd_mul (hc.aestronglyMeasurable measurableSet_Icc).comp_snd
    ((Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)).mono
      fun q hq => hC q.2 hq)

/-- Almost everywhere for `P ⊗ ds`, read time first. -/
theorem ae_ae_swap_of_ae_prod {μ : Measure ℝ} [SFinite μ] {p : Ω × ℝ → Prop}
    (h : ∀ᵐ q ∂(P.prod μ), p q) : ∀ᵐ s ∂μ, ∀ᵐ ω ∂P, p (ω, s) :=
  Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := μ) (ν := P)).quasiMeasurePreserving.ae h)

end Window

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d n m : ℕ}

namespace PairDiff

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T lam K KT α β₁ β₂ : ℝ}
  {G : Matrix (Fin m) (Fin n) ℝ} {ξ₀ : Fin n → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}
  {b : Fin n → Ω → ℝ → ℝ} {σ : Fin n → ℝ → Ω → Fin d → ℝ} {h : Fin n → ℝ → Ω → E → ℝ}
  {f : Fin m → Ω → ℝ → ℝ} {g : Fin m → Ω → ℝ}
  {qb : Fin n → Ω → ℝ → ℝ} {qσ : Fin n → ℝ → Ω → Fin d → ℝ} {qh : Fin n → ℝ → Ω → E → ℝ}
  {qf : Fin m → Ω → ℝ → ℝ} {qg : Fin m → Ω → ℝ}

/-- **The integrands of the weighted backward estimate on the window.** For the difference system
over a filtration with a cross witness, with forcing `q^f` of finite energy, the functions
`|δY|²`, `|δZ|²_F + ‖δU‖²`, `|δX|² + |q^f|²` and `⟨δY, λ δf + q^f⟩` are integrable for `P ⊗ ds`
on `[t, T]` for every `t ∈ [0, T]`. -/
theorem integrable_window (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U b σ h f g
    qb qσ qh qf qg) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    (hqf : ∀ k, Brownian.Ito.energy P T (qf k) ≠ ⊤) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Integrable (fun q : Ω × ℝ => ∑ k, Y k q.2 q.1 ^ 2) (P.prod (volume.restrict (Set.Icc t T)))
      ∧ Integrable (fun q : Ω × ℝ => ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν))
        (P.prod (volume.restrict (Set.Icc t T)))
      ∧ Integrable (fun q : Ω × ℝ => ∑ i, X i q.2 q.1 ^ 2 + ∑ k, qf k q.1 q.2 ^ 2)
        (P.prod (volume.restrict (Set.Icc t T)))
      ∧ Integrable (fun q : Ω × ℝ => ∑ k, Y k q.2 q.1 * (lam * f k q.1 q.2 + qf k q.1 q.2))
        (P.prod (volume.restrict (Set.Icc t T))) := by
  have hw : ∀ {F : Ω × ℝ → ℝ}, Integrable F (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) →
      Integrable F (P.prod (volume.restrict (Set.Icc t T))) := fun hF =>
    (integral_window_split ht hF).2.1
  have hYm : ∀ k, Measurable (Function.uncurry fun ω s => Y k s ω) := fun k =>
    (hD.bwd k).measurable_uncurry.comp measurable_swap
  have hXm : ∀ i, Measurable (Function.uncurry fun ω s => X i s ω) := fun i =>
    ((hD.fwd i).linearBSDEJ hT.le).measurable_uncurry.comp measurable_swap
  have hY : ∀ k, Integrable (fun q : Ω × ℝ => Y k q.2 q.1 * Y k q.2 q.1)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := fun k =>
    integrable_mul_prod (hYm k) (hYm k) ((hD.bwd k).energy_lt_top 𝒲 hT)
      ((hD.bwd k).energy_lt_top 𝒲 hT)
  have hZ : ∀ k j, Integrable (fun q : Ω × ℝ => Z k q.2 q.1 j * Z k q.2 q.1 j)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := fun k j =>
    integrable_mul_prod ((hD.bwd k).Z_meas j) ((hD.bwd k).Z_meas j) ((hD.bwd k).Z_sq j).lt_top
      ((hD.bwd k).Z_sq j).lt_top
  have hU : ∀ k, Integrable (fun q : Ω × ℝ => ∫ e, U k q.2 q.1 e * U k q.2 q.1 e ∂ν)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := fun k =>
    integrable_integral_mul_marked (φ := fun ω s e => U k s ω e) (ψ := fun ω s e => U k s ω e)
      (hD.bwd k).U_meas (hD.bwd k).U_meas (hD.bwd k).U_sq.lt_top (hD.bwd k).U_sq.lt_top
  have hX : ∀ i, Integrable (fun q : Ω × ℝ => X i q.2 q.1 * X i q.2 q.1)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := fun i =>
    integrable_mul_prod (hXm i) (hXm i) ((hD.fwd i).energy_lt_top 𝒲 hT)
      ((hD.fwd i).energy_lt_top 𝒲 hT)
  have hq : ∀ k, Integrable (fun q : Ω × ℝ => qf k q.1 q.2 * qf k q.1 q.2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := fun k =>
    integrable_mul_prod (hD.qf_meas k) (hD.qf_meas k) (hqf k).lt_top (hqf k).lt_top
  have hYφ : ∀ k, Integrable (fun q : Ω × ℝ => Y k q.2 q.1 * (lam * f k q.1 q.2 + qf k q.1 q.2))
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := fun k =>
    integrable_mul_prod (f := fun ω s => Y k s ω) (hYm k) (hD.bwd k).φ_meas
      ((hD.bwd k).energy_lt_top 𝒲 hT) (hD.bwd k).φ_sq.lt_top
  refine ⟨hw ?_, hw ?_, hw ?_, hw (integrable_finsetSum Finset.univ fun k _ => hYφ k)⟩
  · exact (integrable_finsetSum Finset.univ fun k _ => hY k).congr
      (Eventually.of_forall fun q => by simp only [sq])
  · refine (integrable_finsetSum Finset.univ fun k _ =>
      (integrable_finsetSum Finset.univ fun j _ => hZ k j).add (hU k)).congr
      (Eventually.of_forall fun q => ?_)
    simp only [Pi.add_apply, sq]
  · refine ((integrable_finsetSum Finset.univ fun i _ => hX i).add
      (integrable_finsetSum Finset.univ fun k _ => hq k)).congr (Eventually.of_forall fun q => ?_)
    simp only [Pi.add_apply, sq]

/-- **The Young bound integrated against a weight of time.** For the difference system over a
filtration with a cross witness, with interior Lipschitz constant `K ≥ 0`, `λ ∈ [0, 1]`, forcing
`q^f` of finite energy, `ε ∈ (0, 1]`, `κ ∈ ℝ` and `t ∈ [0, T]`, with `C = 2K + 3`,

`2 𝔼 ∫_t^T e^{κs} ⟨δY_s, λ δf_s + q^f_s⟩ ds ≤ (C/ε) 𝔼 ∫_t^T e^{κs} |δY_s|² ds
  + ε 𝔼 ∫_t^T e^{κs} (|δZ_s|²_F + ‖δU_s‖²) ds + (C/ε) 𝔼 ∫_t^T e^{κs} (|δX_s|² + |q^f_s|²) ds`. -/
theorem integral_weighted_young_le (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U
    b σ h f g qb qσ qh qf qg) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (hK : 0 ≤ K)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hqf : ∀ k, Brownian.Ito.energy P T (qf k) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (κ : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    2 * ∫ q, Real.exp (κ * q.2) * ∑ k, Y k q.2 q.1 * (lam * f k q.1 q.2 + qf k q.1 q.2)
        ∂(P.prod (volume.restrict (Set.Icc t T)))
      ≤ (2 * K + 3) / ε * ∫ q, Real.exp (κ * q.2) * ∑ k, Y k q.2 q.1 ^ 2
          ∂(P.prod (volume.restrict (Set.Icc t T)))
        + ε * ∫ q, Real.exp (κ * q.2)
          * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν)
          ∂(P.prod (volume.restrict (Set.Icc t T)))
        + (2 * K + 3) / ε * ∫ q, Real.exp (κ * q.2)
          * (∑ i, X i q.2 q.1 ^ 2 + ∑ k, qf k q.1 q.2 ^ 2)
          ∂(P.prod (volume.restrict (Set.Icc t T))) := by
  obtain ⟨hy, hz, hx, hp⟩ := hD.integrable_window 𝒲 hT hqf ht
  set μ := P.prod (volume.restrict (Set.Icc t T)) with hμ
  set c := (2 * K + 3) / ε with hcdef
  have hc : 0 ≤ c := by positivity
  have hy' := integrable_exp_mul_window κ hy
  have hz' := integrable_exp_mul_window κ hz
  have hx' := integrable_exp_mul_window κ hx
  have hp' := integrable_exp_mul_window κ hp
  have hR : Integrable (fun q : Ω × ℝ => c * (Real.exp (κ * q.2) * ∑ k, Y k q.2 q.1 ^ 2)
      + ε * (Real.exp (κ * q.2) * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν))
      + c * (Real.exp (κ * q.2) * (∑ i, X i q.2 q.1 ^ 2 + ∑ k, qf k q.1 q.2 ^ 2))) μ :=
    ((hy'.const_mul c).add (hz'.const_mul ε)).add (hx'.const_mul c)
  have eR : ∫ q, (c * (Real.exp (κ * q.2) * ∑ k, Y k q.2 q.1 ^ 2)
      + ε * (Real.exp (κ * q.2) * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν))
      + c * (Real.exp (κ * q.2) * (∑ i, X i q.2 q.1 ^ 2 + ∑ k, qf k q.1 q.2 ^ 2))) ∂μ
      = c * ∫ q, Real.exp (κ * q.2) * ∑ k, Y k q.2 q.1 ^ 2 ∂μ
        + ε * ∫ q, Real.exp (κ * q.2)
          * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν) ∂μ
        + c * ∫ q, Real.exp (κ * q.2) * (∑ i, X i q.2 q.1 ^ 2 + ∑ k, qf k q.1 q.2 ^ 2) ∂μ := by
    have h12 : Integrable (fun q : Ω × ℝ => c * (Real.exp (κ * q.2) * ∑ k, Y k q.2 q.1 ^ 2)
        + ε * (Real.exp (κ * q.2)
          * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν))) μ :=
      (hy'.const_mul c).add (hz'.const_mul ε)
    rw [integral_add h12 (hx'.const_mul c), integral_add (hy'.const_mul c) (hz'.const_mul ε),
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [← eR, ← integral_const_mul, integral_prod_symm _ (hp'.const_mul 2),
    integral_prod_symm _ hR]
  refine integral_mono_ae (hp'.const_mul 2).integral_prod_right hR.integral_prod_right ?_
  -- the Young bound at almost every time of `[t, T]`
  have hsub : Set.Icc t T ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc ht.1 le_rfl
  have hY := ae_restrict_of_ae_restrict_of_subset hsub
    (hD.ae_backwardYoung_le hK hlam0 hlam1 hε hε1)
  have hUm : ∀ k, ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Integrable (fun e => U k q.2 q.1 e * U k q.2 q.1 e) ν := fun k =>
    ae_integrable_mul_marked (φ := fun ω s e => U k s ω e) (ψ := fun ω s e => U k s ω e)
      (hD.bwd k).U_meas (hD.bwd k).U_meas (hD.bwd k).U_sq.lt_top (hD.bwd k).U_sq.lt_top
  have hU := ae_restrict_of_ae_restrict_of_subset hsub
    (ae_ae_swap_of_ae_prod (ae_all_iff.mpr hUm))
  filter_upwards [hY, hU, hy.prod_left_ae, hz.prod_left_ae, hx.prod_left_ae] with s hs hUs hys
    hzs hxs
  -- the expectations at `s` as real numbers
  have e1 : ∫⁻ ω, esq (fun k => Y k s ω) ∂P
      = ENNReal.ofReal (∫ ω, ∑ k, Y k s ω ^ 2 ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hys
      (Eventually.of_forall fun ω => by positivity)]
    exact lintegral_congr fun ω => esq_eq_ofReal_sum_sq _
  have e2 : ∫⁻ ω, (∑ k, esq (Z k s ω) + ∑ k, ∫⁻ e, (‖U k s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂P
      = ENNReal.ofReal (∫ ω, ∑ k, (∑ j, Z k s ω j ^ 2 + ∫ e, U k s ω e ^ 2 ∂ν) ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hzs (Eventually.of_forall fun ω =>
      Finset.sum_nonneg fun k _ => add_nonneg (by positivity)
        (integral_nonneg fun e => sq_nonneg _))]
    refine lintegral_congr_ae ?_
    filter_upwards [hUs] with ω hω
    rw [ENNReal.ofReal_sum_of_nonneg fun k _ => add_nonneg (by positivity)
      (integral_nonneg fun e => sq_nonneg _), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_add (by positivity) (integral_nonneg fun e => sq_nonneg _),
      esq_eq_ofReal_sum_sq]
    congr 1
    rw [ofReal_integral_eq_lintegral_ofReal ((hω k).congr (Eventually.of_forall fun e =>
      (sq (U k s ω e)).symm)) (Eventually.of_forall fun e => sq_nonneg _)]
    exact lintegral_congr fun e => by rw [sq_nnnorm_eq_ofReal, sq]
  have e3 : ∫⁻ ω, (esq (fun i => X i s ω) + esq (fun k => qf k ω s)) ∂P
      = ENNReal.ofReal (∫ ω, (∑ i, X i s ω ^ 2 + ∑ k, qf k ω s ^ 2) ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hxs
      (Eventually.of_forall fun ω => by positivity)]
    exact lintegral_congr fun ω => by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), esq_eq_ofReal_sum_sq,
        esq_eq_ofReal_sum_sq]
  have hy0 : 0 ≤ ∫ ω, ∑ k, Y k s ω ^ 2 ∂P := integral_nonneg fun ω => by positivity
  have hz0 : 0 ≤ ∫ ω, ∑ k, (∑ j, Z k s ω j ^ 2 + ∫ e, U k s ω e ^ 2 ∂ν) ∂P :=
    integral_nonneg fun ω => Finset.sum_nonneg fun k _ => add_nonneg (by positivity)
      (integral_nonneg fun e => sq_nonneg _)
  have hx0 : 0 ≤ ∫ ω, (∑ i, X i s ω ^ 2 + ∑ k, qf k ω s ^ 2) ∂P :=
    integral_nonneg fun ω => by positivity
  rw [e1, e2, e3, ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hε.le,
    ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hs
  -- the weighted bound at `s`
  have hl : ∫ ω, 2 * (Real.exp (κ * s) * ∑ k, Y k s ω * (lam * f k ω s + qf k ω s)) ∂P
      = Real.exp (κ * s) * (2 * ∫ ω, ∑ k, Y k s ω * (lam * f k ω s + qf k ω s) ∂P) := by
    rw [integral_const_mul, integral_const_mul]
    ring
  have hr : ∫ ω, (c * (Real.exp (κ * s) * ∑ k, Y k s ω ^ 2)
      + ε * (Real.exp (κ * s) * ∑ k, (∑ j, Z k s ω j ^ 2 + ∫ e, U k s ω e ^ 2 ∂ν))
      + c * (Real.exp (κ * s) * (∑ i, X i s ω ^ 2 + ∑ k, qf k ω s ^ 2))) ∂P
      = Real.exp (κ * s) * (c * ∫ ω, ∑ k, Y k s ω ^ 2 ∂P
        + ε * ∫ ω, ∑ k, (∑ j, Z k s ω j ^ 2 + ∫ e, U k s ω e ^ 2 ∂ν) ∂P
        + c * ∫ ω, (∑ i, X i s ω ^ 2 + ∑ k, qf k ω s ^ 2) ∂P) := by
    have i1 : Integrable (fun ω => c * (Real.exp (κ * s) * ∑ k, Y k s ω ^ 2)) P :=
      (hys.const_mul _).const_mul c
    have i2 : Integrable (fun ω => ε * (Real.exp (κ * s)
        * ∑ k, (∑ j, Z k s ω j ^ 2 + ∫ e, U k s ω e ^ 2 ∂ν))) P :=
      (hzs.const_mul _).const_mul ε
    have i3 : Integrable (fun ω => c * (Real.exp (κ * s)
        * (∑ i, X i s ω ^ 2 + ∑ k, qf k ω s ^ 2))) P :=
      (hxs.const_mul _).const_mul c
    have i12 : Integrable (fun ω => c * (Real.exp (κ * s) * ∑ k, Y k s ω ^ 2)
        + ε * (Real.exp (κ * s) * ∑ k, (∑ j, Z k s ω j ^ 2 + ∫ e, U k s ω e ^ 2 ∂ν))) P :=
      i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2]
    simp only [integral_const_mul]
    ring
  rw [hl, hr]
  exact mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le

/-- **The Young bound inserted in the weighted backward identity.** For the difference system
over a filtration with a cross witness, with interior Lipschitz constant `K ≥ 0`, `λ ∈ [0, 1]`,
forcing `q^f` of finite energy, `ε ∈ (0, 1]`, `κ ∈ ℝ` and `t ∈ [0, T]`, with `C = 2K + 3`, the
functions `|δY_t|²` and `|λ δg + q^g|²` are integrable, the functions
`e^{κs} ((κ − C/ε) |δY_s|² + (1 − ε) (|δZ_s|²_F + ‖δU_s‖²))` and `e^{κs} (|δX_s|² + |q^f_s|²)` are
integrable for `P ⊗ ds` on `[t, T]`, and

`e^{κt} 𝔼|δY_t|² + 𝔼 ∫_t^T e^{κs} ((κ − C/ε) |δY_s|² + (1 − ε) (|δZ_s|²_F + ‖δU_s‖²)) ds
  ≤ e^{κT} 𝔼|λ δg + q^g|² + (C/ε) 𝔼 ∫_t^T e^{κs} (|δX_s|² + |q^f_s|²) ds`. -/
theorem weighted_window_le (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U
    b σ h f g qb qσ qh qf qg) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (hK : 0 ≤ K)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hqf : ∀ k, Brownian.Ito.energy P T (qf k) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (κ : ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Integrable (fun ω => ∑ k, Y k t ω ^ 2) P
      ∧ Integrable (fun ω => ∑ k, (lam * g k ω + qg k ω) ^ 2) P
      ∧ Integrable (fun q : Ω × ℝ => Real.exp (κ * q.2)
          * ((κ - (2 * K + 3) / ε) * ∑ k, Y k q.2 q.1 ^ 2
            + (1 - ε) * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν)))
        (P.prod (volume.restrict (Set.Icc t T)))
      ∧ Integrable (fun q : Ω × ℝ => Real.exp (κ * q.2)
          * (∑ i, X i q.2 q.1 ^ 2 + ∑ k, qf k q.1 q.2 ^ 2))
        (P.prod (volume.restrict (Set.Icc t T)))
      ∧ Real.exp (κ * t) * ∫ ω, ∑ k, Y k t ω ^ 2 ∂P
          + ∫ q, Real.exp (κ * q.2) * ((κ - (2 * K + 3) / ε) * ∑ k, Y k q.2 q.1 ^ 2
            + (1 - ε) * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν))
            ∂(P.prod (volume.restrict (Set.Icc t T)))
        ≤ Real.exp (κ * T) * ∫ ω, ∑ k, (lam * g k ω + qg k ω) ^ 2 ∂P
          + (2 * K + 3) / ε * ∫ q, Real.exp (κ * q.2)
            * (∑ i, X i q.2 q.1 ^ 2 + ∑ k, qf k q.1 q.2 ^ 2)
            ∂(P.prod (volume.restrict (Set.Icc t T))) := by
  obtain ⟨hy, hz, hx, -⟩ := hD.integrable_window 𝒲 hT hqf ht
  set μ := P.prod (volume.restrict (Set.Icc t T)) with hμ
  set c := (2 * K + 3) / ε with hcdef
  have hy' := integrable_exp_mul_window κ hy
  have hz' := integrable_exp_mul_window κ hz
  have hx' := integrable_exp_mul_window κ hx
  have hF := hD.integral_weighted_young_le 𝒲 hT hK hlam0 hlam1 hqf hε hε1 κ ht
  have W := fun k => (hD.bwd k).exp_mul_window_eq 𝒲 hT κ ht
  have hYt : ∀ k, MemLp (Y k t) 2 P := fun k =>
    ((hD.bwd k).linearFSDEJ (ξ₀ := Y k 0) EventuallyEq.rfl hT.le).memLp_apply ht
  have hξ : ∀ k, MemLp (fun ω => lam * g k ω + qg k ω) 2 P := fun k => (hD.bwd k).ξ_sq
  have hD1 : Integrable (fun q : Ω × ℝ => (κ - c) * (Real.exp (κ * q.2) * ∑ k, Y k q.2 q.1 ^ 2)
      + (1 - ε) * (Real.exp (κ * q.2)
        * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν))) μ :=
    (hy'.const_mul (κ - c)).add (hz'.const_mul (1 - ε))
  refine ⟨integrable_finsetSum Finset.univ fun k _ => (hYt k).integrable_sq,
    integrable_finsetSum Finset.univ fun k _ => (hξ k).integrable_sq,
    hD1.congr (Eventually.of_forall fun q => by ring), hx', ?_⟩
  -- the weighted identity, summed over the coordinates
  have hk := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin m))) rfl fun k _ => (W k).2.2
  have eA : ∑ k, ∫ ω, Y k t ω ^ 2 ∂P = ∫ ω, ∑ k, Y k t ω ^ 2 ∂P :=
    (integral_finsetSum _ fun k _ => (hYt k).integrable_sq).symm
  have eC : ∑ k, ∫ ω, (lam * g k ω + qg k ω) ^ 2 ∂P
      = ∫ ω, ∑ k, (lam * g k ω + qg k ω) ^ 2 ∂P :=
    (integral_finsetSum _ fun k _ => (hξ k).integrable_sq).symm
  have hyκ : Integrable (fun q : Ω × ℝ => κ * (Real.exp (κ * q.2) * ∑ k, Y k q.2 q.1 ^ 2)) μ :=
    hy'.const_mul κ
  have eB : ∑ k, ∫ q, Real.exp (κ * q.2) * (κ * Y k q.2 q.1 ^ 2 + ∑ j, Z k q.2 q.1 j ^ 2
        + ∫ e, U k q.2 q.1 e ^ 2 ∂ν) ∂μ
      = κ * ∫ q, Real.exp (κ * q.2) * ∑ k, Y k q.2 q.1 ^ 2 ∂μ
        + ∫ q, Real.exp (κ * q.2)
          * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν) ∂μ := by
    rw [← integral_finsetSum _ fun k _ => (W k).1, ← integral_const_mul, ← integral_add hyκ hz']
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have eD : ∑ k, ∫ q, Real.exp (κ * q.2) * (Y k q.2 q.1 * (lam * f k q.1 q.2 + qf k q.1 q.2)) ∂μ
      = ∫ q, Real.exp (κ * q.2) * ∑ k, Y k q.2 q.1 * (lam * f k q.1 q.2 + qf k q.1 q.2) ∂μ := by
    rw [← integral_finsetSum _ fun k _ => (W k).2.1]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [Finset.mul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, eA, eB, eC, eD] at hk
  -- the integral of the inserted display
  have eI : ∫ q, Real.exp (κ * q.2) * ((κ - c) * ∑ k, Y k q.2 q.1 ^ 2
        + (1 - ε) * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν)) ∂μ
      = (κ - c) * ∫ q, Real.exp (κ * q.2) * ∑ k, Y k q.2 q.1 ^ 2 ∂μ
        + (1 - ε) * ∫ q, Real.exp (κ * q.2)
          * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν) ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hy'.const_mul (κ - c))
      (hz'.const_mul (1 - ε))]
    exact integral_congr_ae (Eventually.of_forall fun q => by ring)
  rw [eI]
  linarith


/-- **The backward estimate at every time.** For the difference system over a filtration with a
cross witness, with interior Lipschitz constant `K ≥ 0`, `λ ∈ [0, 1]`, forcing `q^f` of finite
energy, `ε ∈ (0, 1)`, `κ > C/ε` with `C = 2K + 3`, and `t ∈ [0, T]`, the functions
`|δZ_s|²_F + ‖δU_s‖²` and `|δX_s|² + |q^f_s|²` are integrable for `P ⊗ ds` on `[t, T]`, and

`𝔼|δY_t|² + 𝔼 ∫_t^T (|δZ_s|²_F + ‖δU_s‖²) ds
  ≤ (e^{κT} max(1, C/ε) / (1 − ε)) (𝔼|λ δg + q^g|² + 𝔼 ∫_t^T (|δX_s|² + |q^f_s|²) ds)`. -/
theorem window_le (hD : PairDiff D ℱ hℱW hℱN T lam K KT α β₁ β₂ G ξ₀ X Y Z U
    b σ h f g qb qσ qh qf qg) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (hK : 0 ≤ K)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hqf : ∀ k, Brownian.Ito.energy P T (qf k) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {κ : ℝ} (hκ : (2 * K + 3) / ε < κ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Integrable (fun q : Ω × ℝ => ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν))
        (P.prod (volume.restrict (Set.Icc t T)))
      ∧ Integrable (fun q : Ω × ℝ => ∑ i, X i q.2 q.1 ^ 2 + ∑ k, qf k q.1 q.2 ^ 2)
        (P.prod (volume.restrict (Set.Icc t T)))
      ∧ ∫ ω, ∑ k, Y k t ω ^ 2 ∂P
          + ∫ q, ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν)
            ∂(P.prod (volume.restrict (Set.Icc t T)))
        ≤ Real.exp (κ * T) * max 1 ((2 * K + 3) / ε) / (1 - ε)
          * (∫ ω, ∑ k, (lam * g k ω + qg k ω) ^ 2 ∂P
            + ∫ q, (∑ i, X i q.2 q.1 ^ 2 + ∑ k, qf k q.1 q.2 ^ 2)
              ∂(P.prod (volume.restrict (Set.Icc t T)))) := by
  obtain ⟨hy, hz, hx, -⟩ := hD.integrable_window 𝒲 hT hqf ht
  obtain ⟨-, -, -, -, hdisp⟩ := hD.weighted_window_le 𝒲 hT hK hlam0 hlam1 hqf hε hε1.le κ ht
  refine ⟨hz, hx, ?_⟩
  set μ := P.prod (volume.restrict (Set.Icc t T)) with hμ
  set c := (2 * K + 3) / ε with hcdef
  have hc : 0 ≤ c := by positivity
  have hκ0 : 0 < κ := hc.trans_lt hκ
  have hy' := integrable_exp_mul_window κ hy
  have hz' := integrable_exp_mul_window κ hz
  have hx' := integrable_exp_mul_window κ hx
  have eI : ∫ q, Real.exp (κ * q.2) * ((κ - c) * ∑ k, Y k q.2 q.1 ^ 2
        + (1 - ε) * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν)) ∂μ
      = (κ - c) * ∫ q, Real.exp (κ * q.2) * ∑ k, Y k q.2 q.1 ^ 2 ∂μ
        + (1 - ε) * ∫ q, Real.exp (κ * q.2)
          * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν) ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hy'.const_mul (κ - c))
      (hz'.const_mul (1 - ε))]
    exact integral_congr_ae (Eventually.of_forall fun q => by ring)
  rw [eI] at hdisp
  have hzu : ∀ q : Ω × ℝ, 0 ≤ ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν) :=
    fun q => Finset.sum_nonneg fun k _ => add_nonneg (by positivity)
      (integral_nonneg fun e => sq_nonneg _)
  have hmem : ∀ᵐ q ∂μ, q.2 ∈ Set.Icc t T :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc)
  have hA : 0 ≤ ∫ q, Real.exp (κ * q.2) * ∑ k, Y k q.2 q.1 ^ 2 ∂μ :=
    integral_nonneg fun q => by positivity
  have ha : 0 ≤ ∫ ω, ∑ k, Y k t ω ^ 2 ∂P := integral_nonneg fun ω => by positivity
  have hΞ : 0 ≤ ∫ ω, ∑ k, (lam * g k ω + qg k ω) ^ 2 ∂P := integral_nonneg fun ω => by positivity
  have hX0 : 0 ≤ ∫ q, (∑ i, X i q.2 q.1 ^ 2 + ∑ k, qf k q.1 q.2 ^ 2) ∂μ :=
    integral_nonneg fun q => by positivity
  have hB : ∫ q, ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν) ∂μ
      ≤ ∫ q, Real.exp (κ * q.2)
        * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν) ∂μ := by
    refine integral_mono_ae hz hz' (hmem.mono fun q hq => ?_)
    exact le_mul_of_one_le_left (hzu q) (Real.one_le_exp (by nlinarith [hq.1, ht.1]))
  have hX : ∫ q, Real.exp (κ * q.2) * (∑ i, X i q.2 q.1 ^ 2 + ∑ k, qf k q.1 q.2 ^ 2) ∂μ
      ≤ Real.exp (κ * T) * ∫ q, (∑ i, X i q.2 q.1 ^ 2 + ∑ k, qf k q.1 q.2 ^ 2) ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_ae hx' (hx.const_mul _) (hmem.mono fun q hq => ?_)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [hq.2]))
      (by positivity)
  have ht1 : 1 ≤ Real.exp (κ * t) := Real.one_le_exp (by nlinarith [ht.1])
  have hE : 1 ≤ Real.exp (κ * T) := Real.one_le_exp (by nlinarith)
  set a := ∫ ω, ∑ k, Y k t ω ^ 2 ∂P
  set A := ∫ q, Real.exp (κ * q.2) * ∑ k, Y k q.2 q.1 ^ 2 ∂μ
  set B := ∫ q, Real.exp (κ * q.2) * ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν) ∂μ
  set B₀ := ∫ q, ∑ k, (∑ j, Z k q.2 q.1 j ^ 2 + ∫ e, U k q.2 q.1 e ^ 2 ∂ν) ∂μ
  set Ξ := ∫ ω, ∑ k, (lam * g k ω + qg k ω) ^ 2 ∂P
  set X₀ := ∫ q, (∑ i, X i q.2 q.1 ^ 2 + ∑ k, qf k q.1 q.2 ^ 2) ∂μ
  set X₁ := ∫ q, Real.exp (κ * q.2) * (∑ i, X i q.2 q.1 ^ 2 + ∑ k, qf k q.1 q.2 ^ 2) ∂μ
  set E := Real.exp (κ * T)
  set M := max 1 c with hM
  have h1 : a ≤ Real.exp (κ * t) * a := le_mul_of_one_le_left ha ht1
  have h2 : 0 ≤ (κ - c) * A := mul_nonneg (by linarith) hA
  have h3 : (1 - ε) * B₀ ≤ (1 - ε) * B := mul_le_mul_of_nonneg_left hB (by linarith)
  have h4 : c * X₁ ≤ c * (E * X₀) := mul_le_mul_of_nonneg_left hX hc
  have h5 : E * Ξ + c * (E * X₀) ≤ E * M * (Ξ + X₀) := by
    have hm1 : 1 ≤ M := le_max_left _ _
    have hmc : c ≤ M := le_max_right _ _
    have hE0 : 0 ≤ E := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hm1 (mul_nonneg hE0 hΞ),
      mul_le_mul_of_nonneg_left hmc (mul_nonneg hE0 hX0)]
  have h6 : (a + B₀) * (1 - ε) ≤ a + (1 - ε) * B₀ := by nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith


end PairDiff

end Dissertation.WellPosedness.Stability
