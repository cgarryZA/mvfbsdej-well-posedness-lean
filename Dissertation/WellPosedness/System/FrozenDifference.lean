/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.System.FrozenLegs
import Dissertation.WellPosedness.System.Completeness
import Dissertation.WellPosedness.System.BridgeDiff
import Dissertation.WellPosedness.BrownianPoisson.LegIsometry
import Dissertation.WellPosedness.Existence.ForcingAlgebra

/-!
# The forward difference of two frozen steps

In Step 2 of the proof of Lemma 4.2 of the well-posedness paper the difference of two solutions
of the frozen forward equation (4.7) solves the linear forward equation

`δX̄_t = λ ∫_0^t δb_s ds + λ ∫_0^t δσ_s dW_s + λ ∫_0^t ∫_E δh_s(e) Ñ(ds, de)`,

and its running supremum is bounded through those of the three legs. For a solution `X` of the
linear forward equation from `0` with integrands `λ b`, `λ σ`, `λ γ`, on one set of full measure
`X_t = λ (∫_0^t b_s ds + M_t + N_t)` at every `t ∈ [0, T]`, for versions `M`, `N` of the two
stochastic integrals with right-continuous paths, so

`𝔼 sup_{t ≤ T} |X_t|² ≤ 3λ² (𝔼 (∫_0^T |b_s| ds)² + 𝔼 sup_{t ≤ T} |M_t|² + 𝔼 sup_{t ≤ T} |N_t|²)`;

Cauchy–Schwarz gives `𝔼 (∫_0^T |b_s| ds)² ≤ T 𝔼 ∫_0^T |b_s|² ds`, and Doob's `L²` inequality with
the isometries gives `𝔼 sup_{t ≤ T} |M_t|² ≤ 4 𝔼 ∫_0^T |σ_s|²_F ds` and
`𝔼 sup_{t ≤ T} |N_t|² ≤ 4 𝔼 ∫_0^T ‖γ_s‖²_{L²(ν)} ds`.

Along a tuple of `ℍ²_weak` the canonical representative `coeffJump` of the jump coefficient at the
tuple also represents it at the predictable tuple, and the integrals of (1.1) exist with it.

## Main statements

* `ae_forall_Icc_eq_of_ae_rightCont` — two versions with almost surely right-continuous paths
  are indistinguishable on `[0, T]`.
* `esq_driftLeg_le` — `|∫_0^t b_s ds|² ≤ (∫_0^T |b_s| ds)²`.
* `exists_cadlag_multidim_le` — Doob's bound for the multidimensional Itô integral.
* `lintegral_biSup_esq_brownian_le`, `lintegral_biSup_esq_compensated_le` — Doob's bounds for
  vectors of stochastic integrals.
* `lintegral_sq_lintegral_toLp_le` — Cauchy–Schwarz for the drift leg.
* `LinearFSDEJ.congr_jump` — the jump integrand may be changed on a null set.
* `LinearFSDEJ.lintegral_biSup_esq_le_legs` — the bound by the three legs.
* `PaperWeakTuple.paperAdmissible_coeffJump` — the integrals of (1.1) exist with `coeffJump`.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped NNReal ENNReal

namespace Dissertation.WellPosedness.System

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Existence LevyStochCalc.BSDEJ.Solves LevyStochCalc

universe u v w

/-! ### Versions and squared norms -/

/-- **Two versions with almost surely right-continuous paths are indistinguishable.** Two
processes agreeing almost surely at each time of `[0, T]`, almost every path of each
right-continuous on `[0, T)`, agree at every time of `[0, T]` on one set of full measure. -/
theorem ae_forall_Icc_eq_of_ae_rightCont {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {T : ℝ} {Y R : ℝ → Ω → ℝ} (hT : 0 ≤ T) (h : ∀ t ∈ Set.Icc (0 : ℝ) T, Y t =ᵐ[P] R t)
    (hY : ∀ᵐ ω ∂P, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω)))
    (hR : ∀ᵐ ω ∂P, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => R s ω) (𝓝[>] t) (𝓝 (R t ω))) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y t ω = R t ω := by
  have hmem : ∀ q : ℚ, max (0 : ℝ) (min T (q : ℝ)) ∈ Set.Icc (0 : ℝ) T :=
    fun _ => ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ,
      Y (max (0 : ℝ) (min T (q : ℝ))) ω = R (max (0 : ℝ) (min T (q : ℝ))) ω :=
    ae_all_iff.mpr fun q => h _ (hmem q)
  filter_upwards [hrat, h T ⟨hT, le_rfl⟩, hY, hR] with ω hω hωT hYω hRω
  intro t ht
  rcases eq_or_lt_of_le ht.2 with heq | htT
  · rw [heq]
    exact hωT
  have hex : ∀ n : ℕ, ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < min (t + 1 / ((n : ℝ) + 1)) T := by
    intro n
    refine exists_rat_btwn (lt_min ?_ htT)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose q hq1 hq2 using hex
  have hq0 : ∀ n, (0 : ℝ) ≤ (q n : ℝ) := fun n => le_of_lt (lt_of_le_of_lt ht.1 (hq1 n))
  have hqT : ∀ n, (q n : ℝ) ≤ T := fun n => le_of_lt (lt_of_lt_of_le (hq2 n) (min_le_right _ _))
  have hclamp : ∀ n, max (0 : ℝ) (min T (q n : ℝ)) = (q n : ℝ) := fun n => by
    rw [min_eq_right (hqT n), max_eq_right (hq0 n)]
  have htend : Tendsto (fun n : ℕ => (q n : ℝ)) atTop (𝓝 t) := by
    have hz : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hup : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) atTop (𝓝 t) := by
      simpa using (tendsto_const_nhds (x := t)).add hz
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => (hq1 n).le) (fun n => le_of_lt (lt_of_lt_of_le (hq2 n) (min_le_left _ _)))
  have hsw : Tendsto (fun n : ℕ => (q n : ℝ)) atTop (𝓝[>] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htend
      (Eventually.of_forall fun n => hq1 n)
  refine tendsto_nhds_unique (((hYω t ⟨ht.1, htT⟩).comp hsw).congr fun n => ?_)
    ((hRω t ⟨ht.1, htT⟩).comp hsw)
  have hn := hω (q n)
  rwa [hclamp n] at hn

/-- `|a x|² = a² |x|²` for a coordinate vector, in `ℝ≥0∞`. -/
theorem esq_const_mul {ι : Type*} [Fintype ι] (a : ℝ) (x : ι → ℝ) :
    esq (fun i => a * x i) = ENNReal.ofReal (a ^ 2) * esq x := by
  simp only [esq, sq_nnnorm_const_mul, Finset.mul_sum]

/-- `|x + y + z|² ≤ 3 |x|² + 3 |y|² + 3 |z|²` for coordinate vectors, in `ℝ≥0∞`. -/
theorem esq_add_add_le {ι : Type*} [Fintype ι] (x y z : ι → ℝ) :
    esq (fun i => x i + y i + z i) ≤ 3 * esq x + 3 * esq y + 3 * esq z := by
  simp only [esq, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => sq_nnnorm_add_add_le (x i) (y i) (z i)

/-- **The drift leg of a vector of drifts.** At a sample point at which every coordinate of the
drift has an integrable path on `[0, T]`, for `t ∈ [0, T]`,
`|∫_0^t b_s ds|² ≤ (∫_0^T |b_s| ds)²`, with the Euclidean norm of `ℝⁿ`. -/
theorem esq_driftLeg_le {Ω : Type*} {n : ℕ} {b : Fin n → Ω → ℝ → ℝ} {T : ℝ} {ω : Ω}
    (hω : ∀ i, ω ∈ integrablePaths (b i) T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    esq (fun i => driftLeg (b i) T t ω)
      ≤ (∫⁻ s in Set.Icc (0 : ℝ) T,
          ‖(WithLp.toLp 2 fun i => b i ω s : EuclideanSpace ℝ (Fin n))‖ₑ) ^ 2 := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl ht.2
  have hint : ∀ i, Integrable
      (fun s => (WithLp.toLp 2 fun i => b i ω s : EuclideanSpace ℝ (Fin n)) i)
      (volume.restrict (Set.Icc (0 : ℝ) t)) := fun i => by
    exact (hω i).mono_set hsub
  have hv : (WithLp.toLp 2 fun i => ∫ s in Set.Icc (0 : ℝ) t, b i ω s : EuclideanSpace ℝ (Fin n))
      = ∫ s in Set.Icc (0 : ℝ) t, (WithLp.toLp 2 fun i => b i ω s : EuclideanSpace ℝ (Fin n)) := by
    ext i
    rw [eval_integral_piLp hint i]
  have e : (fun i => driftLeg (b i) T t ω) = fun i => ∫ s in Set.Icc (0 : ℝ) t, b i ω s :=
    funext fun i => driftLeg_of_mem (hω i) t
  rw [e, esq_eq_enorm_sq, hv]
  refine pow_le_pow_left' ((enorm_integral_le_lintegral_enorm _).trans ?_) 2
  exact lintegral_mono_set hsub

/-! ### Scaling of the stochastic integrals -/

section Scaling

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- The multidimensional Itô integral depends on its integrand only. -/
theorem multidimStochasticIntegral_congr (W : Brownian.Multidim.MultidimBrownianMotion P d)
    (hℱ : ∀ j : Fin d, Brownian.IsBrownianFiltration (W.W j) ℱ) {Z Z' : ℝ → Ω → (Fin d → ℝ)}
    (h : Z = Z') (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω j)
    (hq : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm' : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z' s ω j))
    (hp' : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z' s ω j)
    (hq' : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z hm hp hq
      = Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z' hm' hp' hq' := by
  subst h
  rfl

/-- The compensated integral depends on its integrand only. -/
theorem compensatedIntegral_congr (N : Poisson.PoissonRandomMeasure P ν)
    (hℱ : Poisson.IsPoissonFiltration N ℱ) {φ φ' : Ω → ℝ → E → ℝ} (h : φ = φ')
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hm' : Measurable fun p : Ω × ℝ × E => φ' p.1 p.2.1 p.2.2)
    (hp' : Probability.MarkedProgressivelyMeasurable ℱ φ')
    (hq' : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ' ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq
      = Poisson.Compensated.stochasticIntegral N ℱ hℱ φ' hm' hp' hq' := by
  subst h
  rfl

/-- **The multidimensional Itô integral of `a Z` is `a ∫ Z dW`**, almost surely at each time. -/
theorem multidimStochasticIntegral_const_mul_ae
    (W : Brownian.Multidim.MultidimBrownianMotion P d)
    (hℱ : ∀ j : Fin d, Brownian.IsBrownianFiltration (W.W j) ℱ) {Z : ℝ → Ω → (Fin d → ℝ)}
    (a : ℝ) (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω j)
    (hq : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm' : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => a * Z s ω j))
    (hp' : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => a * Z s ω j)
    (hq' : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖a * Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ) :
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ
        (fun s ω j => a * Z s ω j) hm' hp' hq' t
      =ᵐ[P] fun ω =>
        a * Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z hm hp hq t ω := by
  have hm'' : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => a * Z s ω j + 0 * Z s ω j) :=
    fun j => by simpa only [zero_mul, add_zero] using hm' j
  have hp'' : ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ fun ω s => a * Z s ω j + 0 * Z s ω j :=
    fun j => by simpa only [zero_mul, add_zero] using hp' j
  have hq'' : ∀ (j : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖a * Z s ω j + 0 * Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun j T hT => by simpa only [zero_mul, add_zero] using hq' j T hT
  have key := multidimStochasticIntegral_linComb_ae W hℱ a 0 hm hm hp hp hq hq hm'' hp'' hq'' t
  rw [multidimStochasticIntegral_congr W hℱ (Z' := fun s ω j => a * Z s ω j)
    (funext fun s => funext fun ω => funext fun j => by ring) hm'' hp'' hq'' hm' hp' hq'] at key
  filter_upwards [key] with ω hω
  rw [hω]
  ring

/-- **The compensated integral of `a φ` is `a ∫∫ φ dÑ`**, almost surely at each time. -/
theorem compensatedIntegral_const_mul_ae (N : Poisson.PoissonRandomMeasure P ν)
    (hℱ : Poisson.IsPoissonFiltration N ℱ) {φ : Ω → ℝ → E → ℝ} (a : ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hm' : Measurable fun p : Ω × ℝ × E => a * φ p.1 p.2.1 p.2.2)
    (hp' : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => a * φ ω s e)
    (hq' : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖a * φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) (t : ℝ) :
    Poisson.Compensated.stochasticIntegral N ℱ hℱ (fun ω s e => a * φ ω s e) hm' hp' hq' t
      =ᵐ[P] fun ω => a * Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hm hp hq t ω := by
  have hm'' : Measurable fun p : Ω × ℝ × E => a * φ p.1 p.2.1 p.2.2 + 0 * φ p.1 p.2.1 p.2.2 := by
    simpa only [zero_mul, add_zero] using hm'
  have hp'' : Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => a * φ ω s e + 0 * φ ω s e := by
    simpa only [zero_mul, add_zero] using hp'
  have hq'' : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖a * φ ω s e + 0 * φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun T hT => by simpa only [zero_mul, add_zero] using hq' T hT
  have key := compensatedIntegral_linComb_ae N hℱ a 0 hm hm hp hp hq hq hm'' hp'' hq'' t
  rw [compensatedIntegral_congr N hℱ (φ' := fun ω s e => a * φ ω s e)
    (funext fun ω => funext fun s => funext fun e => by ring) hm'' hp'' hq'' hm' hp' hq'] at key
  filter_upwards [key] with ω hω
  rw [hω]
  ring

end Scaling

/-! ### Doob's bounds -/

section Doob

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

include hℱN in
/-- **Doob's bound for the multidimensional Itô integral.** Over a filtration carrying the driver
whose null sets lie in its time-`0` field, whose right-continuation is constant before `0` and
which admits a cross witness, `∫ Z dW` has a jointly measurable version with right-continuous
paths and `𝔼 sup_{t ≤ T} |M_t|² ≤ 4 ∑_j 𝔼 ∫_0^T Z_j(s)² ds`. -/
theorem exists_cadlag_multidim_le (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    {Z : ℝ → Ω → (Fin d → ℝ)} (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω j)
    (hq : ∀ (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ M : ℝ → Ω → ℝ, Measurable (Function.uncurry M)
      ∧ (∀ t : ℝ, M t =ᵐ[P]
        Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW Z hm hp hq t)
      ∧ (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)))
      ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
        ≤ 4 * ∑ j : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω j) := by
  classical
  obtain ⟨M, -, hme, hae, hcad, hmart, -, -⟩ :=
    exists_cadlag_vectorIntegral_supBound D.W ℱ hℱW Z hm hp hq hℱ0 hnull T hT.le
  have hγq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖(fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ)) ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun _ _ => by simp
  have hL : Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN M (fun _ => 0) (fun _ _ => 0) Z
      (fun _ _ _ => 0) :=
    { measurable_path := hme
      σ_meas := hm
      σ_prog := hp
      σ_sq := hq
      γ_meas := measurable_const
      γ_prog := Poisson.Compensated.markedProgressivelyMeasurable_zero ℱ
      γ_sq := hγq
      decomposition := fun t ht => by
        filter_upwards [hae t, Poisson.Compensated.stochasticIntegral_ae_zero_of_vanishing D.N hℱN
          (fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ)) measurable_const
          (Poisson.Compensated.markedProgressivelyMeasurable_zero ℱ) hγq ht
          (fun _ _ _ _ => rfl)] with ω h1 h2
        rw [h1, h2]
        simp }
  have hbq : ∀ T' : ℝ, 0 < T' → ∫⁻ _ω, ∫⁻ _s in Set.Icc (0 : ℝ) T',
      (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun _ _ => by simp
  have hiso := Ito.SecondMoment.integral_mul_self_eq_of_isItoLevyProcess hL 𝒲
    stronglyMeasurable_const (memLp_const 0) measurable_const
    (Probability.progressivelyMeasurable_zero ℱ) hbq hT
  have hMT : MemLp (M T) 2 P :=
    Ito.SecondMoment.memLp_two_of_isItoLevyProcess hL (memLp_const 0) measurable_const hbq hT.le
  simp only [mul_zero, integral_zero, add_zero, zero_add, nnnorm_zero, ENNReal.coe_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, lintegral_const, zero_mul,
    ENNReal.toReal_zero] at hiso
  rw [Ito.SecondMoment.integral_mul_self_eq_toReal hMT] at hiso
  have hσf : ∀ j ∈ Finset.univ, Brownian.Ito.energy P T (fun ω s => Z s ω j) ≠ ⊤ :=
    fun j _ => (hq j T hT).ne
  have hlin : ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∑ j : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω j) := by
    rw [← ENNReal.toReal_eq_toReal_iff'
      (Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two hMT).ne (ENNReal.sum_ne_top.mpr hσf),
      ENNReal.toReal_sum hσf]
    exact hiso
  refine ⟨M, hme, hae, fun ω t => (hcad ω t).1, ?_⟩
  rw [← hlin]
  exact BSDEJ.SupBound.lintegral_biSup_sq_le_of_martingale hmart hT.le
    (Eventually.of_forall fun ω t => (hcad ω t).1)

include hℱN in
/-- **Doob's bound for a vector of multidimensional Itô integrals.** For every version `M` of
`(∫ σ_i dW)_i` almost every path of which is right-continuous on `[0, T)`,
`𝔼 sup_{t ≤ T} |M_t|² ≤ 4 ∑_{i, j} 𝔼 ∫_0^T σ_{ij}(s)² ds`. -/
theorem lintegral_biSup_esq_brownian_le {n : ℕ} (𝒲 : D.CrossWitness ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    {σ : Fin n → ℝ → Ω → (Fin d → ℝ)}
    (hσm : ∀ i j, Measurable (Function.uncurry fun ω s => σ i s ω j))
    (hσp : ∀ i j, Probability.ProgressivelyMeasurable ℱ fun ω s => σ i s ω j)
    (hσq : ∀ i j, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖σ i s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (M : Fin n → ℝ → Ω → ℝ)
    (hMv : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, M i t =ᵐ[P]
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW (σ i) (hσm i)
        (hσp i) (hσq i) t)
    (hMc : ∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Ico (0 : ℝ) T,
      Tendsto (fun s => M i s ω) (𝓝[>] t) (𝓝 (M i t ω))) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => M i t ω)) ∂P
      ≤ 4 * ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => σ i s ω j) := by
  choose MW hMWm hMWae hMWc hMWle using fun i =>
    exists_cadlag_multidim_le (hℱN := hℱN) 𝒲 hℱ0 hnull hT (hσm i) (hσp i) (hσq i)
  have hind : ∀ᵐ ω ∂P, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, M i t ω = MW i t ω :=
    ae_all_iff.mpr fun i => ae_forall_Icc_eq_of_ae_rightCont hT.le
      (fun t ht => (hMv i t ht).trans (hMWae i t).symm) (hMc i)
      (ae_of_all _ fun ω t _ => hMWc i ω t)
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => M i t ω)) ∂P
      = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => MW i t ω)) ∂P :=
        lintegral_congr_ae (hind.mono fun ω hω =>
          iSup_congr fun t => iSup_congr fun ht => by simp only [hω _ t ht])
    _ ≤ ∑ i, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖MW i t ω‖₊ : ℝ≥0∞) ^ 2) ∂P :=
        lintegral_biSup_esq_le hT.le
          (fun i t => (hMWm i).comp (measurable_const.prodMk measurable_id)) hMWc
    _ ≤ ∑ i, 4 * ∑ j, Brownian.Ito.energy P T (fun ω s => σ i s ω j) :=
        Finset.sum_le_sum fun i _ => hMWle i
    _ = 4 * ∑ i, ∑ j, Brownian.Ito.energy P T (fun ω s => σ i s ω j) := by
        rw [Finset.mul_sum]

/-- **Doob's bound for a vector of compensated integrals.**
`𝔼 sup_{t ≤ T} |∫_0^t ∫_E γ_s(e) Ñ(ds, de)|² ≤ 4 ∑_i 𝔼 ∫_0^T ∫_E γ_i(s, e)² ν(de) ds`. -/
theorem lintegral_biSup_esq_compensated_le {n : ℕ}
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    {γ : Fin n → ℝ → Ω → E → ℝ}
    (hγm : ∀ i, Measurable fun p : Ω × ℝ × E => γ i p.2.1 p.1 p.2.2)
    (hγp : ∀ i, Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => γ i s ω e)
    (hγq : ∀ i, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖γ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i =>
        Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω s e => γ i s ω e) (hγm i)
          (hγp i) (hγq i) t ω)) ∂P
      ≤ 4 * ∑ i, Poisson.Compensated.markedEnergy P ν T (fun ω s e => γ i s ω e) := by
  choose MN _ hMNm hMNae hMNc hMNmart _ _ using fun i =>
    exists_cadlag_compensatedIntegral_supBound D.N ℱ hℱN (fun ω s e => γ i s ω e) (hγm i)
      (hγp i) (hγq i) hℱ0 hnull T hT.le
  have hind : ∀ᵐ ω ∂P, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω s e => γ i s ω e) (hγm i)
        (hγp i) (hγq i) t ω = MN i t ω :=
    ae_all_iff.mpr fun i => ae_forall_Icc_eq_of_ae_rightCont hT.le
      (fun t _ => (hMNae i t).symm)
      ((Poisson.Compensated.stochasticIntegral_cadlag D.N ℱ hℱN _ (hγm i) (hγp i)
        (hγq i)).mono fun ω hω t _ => (hω t).1)
      (ae_of_all _ fun ω t _ => (hMNc i ω t).1)
  have hDoob : ∀ i, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖MN i t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
      ≤ 4 * Poisson.Compensated.markedEnergy P ν T (fun ω s e => γ i s ω e) := fun i => by
    have hT' : ∫⁻ ω, (‖MN i T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        = Poisson.Compensated.markedEnergy P ν T (fun ω s e => γ i s ω e) :=
      (lintegral_congr_ae ((hMNae i T).mono fun ω hω => by rw [hω])).trans
        (Poisson.Compensated.isometry_stochasticIntegral D.N ℱ hℱN _ (hγm i) (hγp i)
          (hγq i) T hT)
    rw [← hT']
    exact BSDEJ.SupBound.lintegral_biSup_sq_le_of_martingale (hMNmart i) hT.le
      (Eventually.of_forall fun ω t => (hMNc i ω t).1)
  calc _ = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => MN i t ω)) ∂P :=
        lintegral_congr_ae (hind.mono fun ω hω =>
          iSup_congr fun t => iSup_congr fun ht => by simp only [hω _ t ht])
    _ ≤ ∑ i, ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖MN i t ω‖₊ : ℝ≥0∞) ^ 2) ∂P :=
        lintegral_biSup_esq_le hT.le
          (fun i t => (hMNm i).comp (measurable_const.prodMk measurable_id))
          fun i ω t => (hMNc i ω t).1
    _ ≤ ∑ i, 4 * Poisson.Compensated.markedEnergy P ν T (fun ω s e => γ i s ω e) :=
        Finset.sum_le_sum fun i _ => hDoob i
    _ = _ := by rw [Finset.mul_sum]

end Doob

/-- **Cauchy–Schwarz for the drift leg.** For jointly measurable drifts,
`𝔼 (∫_0^T |b_s| ds)² ≤ T ∑_i 𝔼 ∫_0^T b_i(s)² ds`, with the Euclidean norm of `ℝⁿ`. -/
theorem lintegral_sq_lintegral_toLp_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ i, Measurable (Function.uncurry (b i))) (T : ℝ) :
    ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
        ‖(WithLp.toLp 2 fun i => b i ω s : EuclideanSpace ℝ (Fin n))‖ₑ) ^ 2 ∂P
      ≤ ENNReal.ofReal T * ∑ i, Brownian.Ito.energy P T (b i) := by
  have hsl : ∀ i ω, Measurable fun s => b i ω s := fun i ω =>
    (hbm i).comp (measurable_const.prodMk measurable_id)
  calc ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
        ‖(WithLp.toLp 2 fun i => b i ω s : EuclideanSpace ℝ (Fin n))‖ₑ) ^ 2 ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal T * ∫⁻ s in Set.Icc (0 : ℝ) T,
          ‖(WithLp.toLp 2 fun i => b i ω s : EuclideanSpace ℝ (Fin n))‖ₑ ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => BSDEJ.SupBound.sq_lintegral_le_ofReal_mul_lintegral_sq T
          (measurable_toLp_of_forall fun i => hsl i ω).enorm.aemeasurable
    _ = ∫⁻ ω, ENNReal.ofReal T * ∑ i, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖b i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [← lintegral_finsetSum _ fun i _ => (hsl i ω).nnnorm.coe_nnreal_ennreal.pow_const 2]
        congr 1
        refine lintegral_congr fun s => ?_
        rw [← esq_eq_enorm_sq]
        rfl
    _ = ENNReal.ofReal T * ∑ i, Brownian.Ito.energy P T (b i) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finsetSum _ fun i _ => ?_]
        · rfl
        · exact ((hbm i).nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'

/-! ### The linear forward equation -/

section Forward

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ}

/-- **The jump integrand of the linear forward equation may be changed on a null set**: a
solution is also a solution with a jump integrand meeting the conditions of the compensated
integral and agreeing with the original one almost everywhere for the marked energy measure. -/
theorem _root_.Dissertation.WellPosedness.Stability.LinearFSDEJ.congr_jump {ξ₀ : Ω → ℝ}
    {b : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ} {σ : ℝ → Ω → (Fin d → ℝ)} {γ γ' : ℝ → Ω → E → ℝ}
    (h : LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ)
    (hm : Measurable fun p : Ω × ℝ × E => γ' p.2.1 p.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => γ' s ω e)
    (hv : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → γ' s ω e = 0)
    (hq : Poisson.Compensated.markedEnergy P ν T (fun ω s e => γ' s ω e) ≠ ⊤)
    (hae : ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
      γ q.2.1 q.1 q.2.2 = γ' q.2.1 q.1 q.2.2) :
    LinearFSDEJ D ℱ hℱW hℱN T ξ₀ b X σ γ' :=
  { h with
    γ_meas := hm
    γ_prog := hp
    γ_vanish := hv
    γ_sq := hq
    eqn := fun t ht => by
      have h0 := markedEnergy_sub_eq_zero_of_ae_eq (φ₁ := fun ω s e => γ s ω e)
        (φ₂ := fun ω s e => γ' s ω e) h.γ_meas hm hae
      filter_upwards [h.eqn t ht, compensatedIntegral_congr_of_markedEnergy D.N hℱN
        (φ₁ := fun ω s e => γ s ω e) (φ₂ := fun ω s e => γ' s ω e) h.γ_meas h.γ_prog
        (marked_sq_int_global_of_vanishing h.γ_vanish h.γ_sq) hm hp
        (marked_sq_int_global_of_vanishing hv hq) h0 ht.2] with ω e1 e2
      rw [e1, e2] }

/-- **The forward difference by its three legs.** Let each coordinate `X_i` solve the linear
forward equation from `0` with drift `λ b_i`, diffusion `λ σ_i` and jump integrand `λ γ_i`, with
`b_i` jointly measurable, vanishing off `[0, T]` and of finite energy. For every version `M` of
`(∫ σ_i dW)_i` almost every path of which is right-continuous on `[0, T)`,
`𝔼 sup_{t ≤ T} |X_t|² ≤ 3λ² (𝔼 (∫_0^T |b_s| ds)² + 𝔼 sup_{t ≤ T} |M_t|²
  + 𝔼 sup_{t ≤ T} |∫_0^t ∫_E γ_s(e) Ñ(ds, de)|²)`. -/
theorem _root_.Dissertation.WellPosedness.Stability.LinearFSDEJ.lintegral_biSup_esq_le_legs
    {n : ℕ} (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (lam : ℝ) {X : Fin n → ℝ → Ω → ℝ} {b : Fin n → Ω → ℝ → ℝ}
    {σ : Fin n → ℝ → Ω → (Fin d → ℝ)} {γ : Fin n → ℝ → Ω → E → ℝ}
    (hbm : ∀ i, Measurable (Function.uncurry (b i)))
    (hbv : ∀ i ω s, s ∉ Set.Icc (0 : ℝ) T → b i ω s = 0)
    (hbq : ∀ i, Brownian.Ito.energy P T (b i) ≠ ⊤)
    (hσm : ∀ i j, Measurable (Function.uncurry fun ω s => σ i s ω j))
    (hσp : ∀ i j, Probability.ProgressivelyMeasurable ℱ fun ω s => σ i s ω j)
    (hσq : ∀ i j, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖σ i s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγm : ∀ i, Measurable fun p : Ω × ℝ × E => γ i p.2.1 p.1 p.2.2)
    (hγp : ∀ i, Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => γ i s ω e)
    (hγq : ∀ i, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖γ i s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hX : ∀ i, LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (fun ω s => lam * b i ω s) (X i)
      (fun s ω j => lam * σ i s ω j) (fun s ω e => lam * γ i s ω e))
    (M : Fin n → ℝ → Ω → ℝ)
    (hMv : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, M i t =ᵐ[P]
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hℱW (σ i) (hσm i)
        (hσp i) (hσq i) t)
    (hMc : ∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Ico (0 : ℝ) T,
      Tendsto (fun s => M i s ω) (𝓝[>] t) (𝓝 (M i t ω))) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P
      ≤ ENNReal.ofReal (3 * lam ^ 2)
        * (∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
              ‖(WithLp.toLp 2 fun i => b i ω s : EuclideanSpace ℝ (Fin n))‖ₑ) ^ 2 ∂P
          + ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => M i t ω)) ∂P
          + ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i =>
              Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω s e => γ i s ω e) (hγm i)
                (hγp i) (hγq i) t ω)) ∂P) := by
  classical
  -- versions of the two stochastic legs with right-continuous paths
  choose MW _ hMWm hMWae hMWc _ _ _ using fun i =>
    exists_cadlag_vectorIntegral_supBound D.W ℱ hℱW (σ i) (hσm i) (hσp i) (hσq i) hℱ0 hnull T
      hT.le
  choose MN _ hMNm hMNae hMNc _ _ _ using fun i =>
    exists_cadlag_compensatedIntegral_supBound D.N ℱ hℱN (fun ω s e => γ i s ω e) (hγm i)
      (hγp i) (hγq i) hℱ0 hnull T hT.le
  -- the decomposition, at every time on one set of full measure
  have hid : ∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      X i t ω = lam * (driftLeg (b i) T t ω + MW i t ω + MN i t ω) := fun i => by
    refine ae_forall_Icc_eq_of_rightContinuous hT.le (fun t ht => ?_) (hX i).X_rightCont
      (fun ω t => ?_)
    · filter_upwards [(hX i).eqn t ht,
        multidimStochasticIntegral_const_mul_ae D.W hℱW lam (hσm i) (hσp i) (hσq i)
          (hX i).σ_meas (hX i).σ_prog
          (sq_int_global_of_vanishing (hX i).σ_vanish (hX i).σ_sq) t,
        compensatedIntegral_const_mul_ae D.N hℱN (φ := fun ω s e => γ i s ω e) lam (hγm i)
          (hγp i) (hγq i) (hX i).γ_meas (hX i).γ_prog
          (marked_sq_int_global_of_vanishing (hX i).γ_vanish (hX i).γ_sq) t,
        hMWae i t, hMNae i t, driftLeg_ae_eq (hbm i) (hbq i) t] with ω e1 e2 e3 e4 e5 e6
      rw [e1, e2, e3, e4, e5, e6, integral_const_mul]
      ring
    · have hA : Tendsto (fun s => driftLeg (b i) T s ω) (𝓝[>] t) (𝓝 (driftLeg (b i) T t ω)) :=
        ((continuous_driftLeg (hbv i) ω).tendsto t).mono_left nhdsWithin_le_nhds
      exact ((hA.add (hMWc i ω t).1).add (hMNc i ω t).1).const_mul lam
  -- the pathwise bound
  have hpt : ∀ᵐ ω ∂P, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω))
      ≤ ENNReal.ofReal (3 * lam ^ 2)
        * ((∫⁻ s in Set.Icc (0 : ℝ) T,
              ‖(WithLp.toLp 2 fun i => b i ω s : EuclideanSpace ℝ (Fin n))‖ₑ) ^ 2
          + (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => MW i t ω))
          + (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => MN i t ω))) := by
    filter_upwards [ae_all_iff.mpr hid,
      ae_all_iff.mpr fun i => ae_mem_integrablePaths (hbm i) (hbq i)] with ω hω hg
    refine iSup₂_le fun t ht => ?_
    have e : (fun i => X i t ω)
        = fun i => lam * (driftLeg (b i) T t ω + MW i t ω + MN i t ω) :=
      funext fun i => hω i t ht
    have h3 : ENNReal.ofReal (3 * lam ^ 2) = 3 * ENNReal.ofReal (lam ^ 2) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    rw [e, esq_const_mul]
    calc ENNReal.ofReal (lam ^ 2) * esq (fun i => driftLeg (b i) T t ω + MW i t ω + MN i t ω)
        ≤ ENNReal.ofReal (lam ^ 2) * (3 * esq (fun i => driftLeg (b i) T t ω)
            + 3 * esq (fun i => MW i t ω) + 3 * esq (fun i => MN i t ω)) := by
          gcongr
          exact esq_add_add_le (fun i => driftLeg (b i) T t ω) (fun i => MW i t ω)
            (fun i => MN i t ω)
      _ ≤ ENNReal.ofReal (lam ^ 2) * (3 * (∫⁻ s in Set.Icc (0 : ℝ) T,
              ‖(WithLp.toLp 2 fun i => b i ω s : EuclideanSpace ℝ (Fin n))‖ₑ) ^ 2
            + 3 * (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => MW i t ω))
            + 3 * (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => MN i t ω))) := by
          gcongr
          · exact esq_driftLeg_le hg ht
          · exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => esq (fun i => MW i t ω))
              t ht
          · exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => esq (fun i => MN i t ω))
              t ht
      _ = _ := by
          rw [h3]
          ring
  -- integrate, and pass to the versions of the statement
  have hWm : Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => MW i t ω) :=
    measurable_biSup_esq_of_Ico (fun i t _ => (hMWm i).comp (measurable_const.prodMk
      measurable_id)) fun i ω t _ => (hMWc i ω t).1
  have hNm : Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => MN i t ω) :=
    measurable_biSup_esq_of_Ico (fun i t _ => (hMNm i).comp (measurable_const.prodMk
      measurable_id)) fun i ω t _ => (hMNc i ω t).1
  have hWM : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => MW i t ω)) ∂P
      = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => M i t ω)) ∂P := by
    have hind : ∀ᵐ ω ∂P, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T, MW i t ω = M i t ω :=
      ae_all_iff.mpr fun i => ae_forall_Icc_eq_of_ae_rightCont hT.le
        (fun t ht => (hMWae i t).trans (hMv i t ht).symm)
        (ae_of_all _ fun ω t _ => (hMWc i ω t).1) (hMc i)
    exact lintegral_congr_ae (hind.mono fun ω hω =>
      iSup_congr fun t => iSup_congr fun ht => by simp only [hω _ t ht])
  have hNI : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => MN i t ω)) ∂P
      = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i =>
          Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω s e => γ i s ω e) (hγm i)
            (hγp i) (hγq i) t ω)) ∂P := by
    have hind : ∀ᵐ ω ∂P, ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        MN i t ω = Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (fun ω s e => γ i s ω e)
          (hγm i) (hγp i) (hγq i) t ω :=
      ae_all_iff.mpr fun i => ae_forall_Icc_eq_of_ae_rightCont hT.le
        (fun t _ => hMNae i t) (ae_of_all _ fun ω t _ => (hMNc i ω t).1)
        ((Poisson.Compensated.stochasticIntegral_cadlag D.N ℱ hℱN _ (hγm i) (hγp i)
          (hγq i)).mono fun ω hω t _ => (hω t).1)
    exact lintegral_congr_ae (hind.mono fun ω hω =>
      iSup_congr fun t => iSup_congr fun ht => by simp only [hω _ t ht])
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => X i t ω)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (3 * lam ^ 2)
        * ((∫⁻ s in Set.Icc (0 : ℝ) T,
              ‖(WithLp.toLp 2 fun i => b i ω s : EuclideanSpace ℝ (Fin n))‖ₑ) ^ 2
          + (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => MW i t ω))
          + (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => MN i t ω))) ∂P := lintegral_mono_ae hpt
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ hNm,
          lintegral_add_right _ hWm, hWM, hNI]

end Forward

/-! ### The jump coefficient at the tuple -/

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {T L : ℝ} {C : Coeffs ν n m d} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}

/-- **The integrals of (1.1) along a tuple of `ℍ²_weak` exist with `coeffJump`.** For `T ≥ 0`,
coefficients with the joint measurability (2.3) of `CoeffBorel`, Assumption 2.2 and Assumption 2.3
along the diagonal, and `Θ ∈ ℍ²_weak`, the canonical representative `coeffJump` of
`h(s, Θ_s, ·, μ_s)` also represents `h(s, Θ⁻_s, ·, μ⁻_s)`, and with it the drift, diffusion and
driver processes and the jump integrand are jointly and progressively measurable with finite
energy on `[0, T]`. -/
theorem PaperWeakTuple.paperAdmissible_coeffJump (hΘ : PaperWeakTuple ℱ P ν T X Y Z U)
    (hT : 0 ≤ T) (hC : CoeffBorel T C) (horig : CoeffOrigin T C)
    (hL : DiagonalLipschitz ℱ P T L C) :
    PaperAdmissible ℱ P T C X Y Z U (coeffJump P T C X Y Z U) := by
  obtain ⟨X', Y', hXe, hYe, hΘ', hXe', hYe'⟩ := hΘ.exists_progTuple hT
  have hγ := hC.crossEval hΘ'
  have hcj : coeffJump P T C X' Y' Z U = coeffJump P T C X Y Z U := by
    funext i s ω e
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · exact coeffJump_eq_of_tupleAt_eq hs (tupleAt_eq_of_eqOn hXe hYe hs) i ω e
    · rw [coeffJump_of_notMem hs, coeffJump_of_notMem hs]
  have hdrift := driftProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hdiff := diffusionProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hdriver := driverProc_eq_of_eqOn (P := P) (C := C) (Z := Z) (U := U) hXe hYe
  have hfin : ENNReal.ofReal (20 * L ^ 2) * (∑ i, Brownian.Ito.energy P T (fun ω s => X' i s ω)
      + (∑ k, Brownian.Ito.energy P T (fun ω s => Y' k s ω)
        + ∑ k, ∑ j, Brownian.Ito.energy P T (fun ω s => Z k s ω j)
        + ∑ k, Poisson.Compensated.markedEnergy P ν T (fun ω s e => U k s ω e)))
      + 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, originSq C s ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_,
      ENNReal.mul_ne_top (by norm_num) (lintegral_originSq_lt_top horig).ne⟩
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun i _ => hXe' i,
      ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.sum_ne_top.mpr fun k _ => hYe' k,
        ENNReal.sum_ne_top.mpr fun k _ => ENNReal.sum_ne_top.mpr fun j _ => hΘ.Z_sq k j⟩,
        ENNReal.sum_ne_top.mpr fun k _ => hΘ.U_sq k⟩⟩
  have hbound := hΘ'.coeffEnergy_le hXe' hYe' hγ hL
  rw [hdrift, hdiff, hdriver, hcj] at hbound
  obtain ⟨hBSH, hF⟩ := ENNReal.add_ne_top.mp (ne_top_of_le_ne_top hfin hbound)
  obtain ⟨hBS, hH⟩ := ENNReal.add_ne_top.mp hBSH
  obtain ⟨hB, hS⟩ := ENNReal.add_ne_top.mp hBS
  refine
    { b_meas := by rw [← hdrift]; exact hγ.b_meas
      b_prog := by rw [← hdrift]; exact hγ.b_prog
      b_sq := fun i => ENNReal.sum_ne_top.mp hB i (Finset.mem_univ i)
      σ_meas := by rw [← hdiff]; exact hγ.σ_meas
      σ_prog := by rw [← hdiff]; exact hγ.σ_prog
      σ_sq := fun i j => ENNReal.sum_ne_top.mp (ENNReal.sum_ne_top.mp hS i (Finset.mem_univ i)) j
        (Finset.mem_univ j)
      γ_meas := by rw [← hcj]; exact hγ.h_meas
      γ_prog := by rw [← hcj]; exact hγ.h_prog
      γ_sq := fun i => ENNReal.sum_ne_top.mp hH i (Finset.mem_univ i)
      f_meas := by rw [← hdriver]; exact hγ.f_meas
      f_prog := by rw [← hdriver]; exact hγ.f_prog
      f_sq := fun k => ENNReal.sum_ne_top.mp hF k (Finset.mem_univ k)
      jump_rep := ?_ }
  filter_upwards [hΘ.ae_ae_tupleAt_leftLimProc_eq hT, ae_restrict_mem measurableSet_Icc]
    with s heq hsI
  filter_upwards [heq] with ω hωeq
  rw [hωeq, lawP2_congr heq]
  exact coeffJump_ae_eq hsI ω

end Dissertation.WellPosedness.System
