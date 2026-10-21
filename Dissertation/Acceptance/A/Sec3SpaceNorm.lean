/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3SpaceNorm
import Dissertation.WellPosedness.System.Completeness
import Dissertation.WellPosedness.Existence.PaperAdmissible
import Dissertation.WellPosedness.Existence.CoeffPredictable
import Dissertation.Acceptance.A.Sec3Complete
import LevyStochCalc.Brownian.CadlagVectorIntegral
import LevyStochCalc.Poisson.CompensatedCadlagMod

/-!
# The norm of the solution space and the càdlàg integrals of §3: proofs

## Main statements

* `Dissertation.Acceptance.A.exists_adapted_cadlag_version_Icc` — an everywhere-càdlàg version
  adapted to the right-continuation of a right-continuous filtration is an adapted version whose
  every path is càdlàg on `[0, T]`.
* `Dissertation.Acceptance.A.finset_sum_rpow_half_le` — Minkowski's inequality for square roots
  of finite sums in `[0, ∞]`.
* `Dissertation.Acceptance.A.supSize_const_mul` — `‖c Θ‖²_𝕊 = |c|² ‖Θ‖²_𝕊`.
* `Dissertation.Acceptance.A.sec3_cadlag_versions`, `sec3_HH_norm`.
* `Dissertation.Acceptance.A.sec3_cadlag_versions_hypotheses` — a tuple of `ℍ²` along which
  the integrals of (1.1) exist, with `Z = U = 1_{(0, 1]}` of energy `1`.
* `Dissertation.Acceptance.A.sec3_HH_norm_hypotheses` — two tuples of `ℍ²` with
  `‖·‖²_𝕊 = 4`.
-/

open MeasureTheory ProbabilityTheory Filter WithLp
open scoped Topology ENNReal NNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Spec LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

/-! ### Càdlàg versions of the stochastic integrals -/

/-- A process adapted to the right-continuation of a right-continuous filtration `ℱ`, equal almost
surely to `I` at every time and with every path right-continuous with left limits, is a version
of `I` on `[0, T]`, adapted to `ℱ`, with every path càdlàg on `[0, T]`. -/
theorem exists_adapted_cadlag_version_Icc {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ mΩ} [ℱ.IsRightContinuous] {T : ℝ} {I : ℝ → Ω → ℝ}
    (h : ∃ M : ℝ → Ω → ℝ, Adapted ℱ.rightCont M ∧ (∀ t, M t =ᵐ[P] I t)
      ∧ (∀ ω t, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)))
      ∧ ∀ ω t, ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L)) :
    ∃ M : ℝ → Ω → ℝ, Adapted ℱ M ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, M t =ᵐ[P] I t)
      ∧ (∀ ω, ∀ t ∈ Set.Ico (0 : ℝ) T, Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)))
      ∧ ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L) := by
  obtain ⟨M, hMa, hMe, hMr, hMl⟩ := h
  exact ⟨M, fun t => (hMa t).mono (Filtration.IsRightContinuous.RC (𝓕 := ℱ) t) le_rfl,
    fun t _ => hMe t, fun ω t _ => hMr ω t, fun ω t _ => hMl ω t⟩

/-- §3, the stochastic integrals of (1.1) have càdlàg versions. -/
theorem sec3_cadlag_versions : PaperSpec.A.sec3_cadlag_versions.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ T C X Y Z U γ hΘ hA
  have h0 := hF0_enlJoint D h𝒢₀
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 →
      MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ 0] s := fun _ hs hs0 =>
    measurableSet_enlJoint_of_null D h𝒢₀ hs hs0
  refine ⟨fun i => ?_, fun i => ?_, fun k => ?_, fun k => ?_⟩
  · obtain ⟨M, hMa, -, hMe, hMc, -⟩ :=
      Brownian.Multidim.MultidimBrownianMotion.exists_everywhere_cadlag_vectorIntegral D.W _
        (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) _ (hA.σ_meas i) (hA.σ_prog i)
        (sq_int_global_of_vanishing (fun ω _ hs => diffusionProc_of_notMem hs i ω)
          (hA.σ_sq i)) h0 hnull
    exact exists_adapted_cadlag_version_Icc
      ⟨M, hMa, hMe, fun ω t => (hMc ω t).1, fun ω t => (hMc ω t).2⟩
  · exact exists_adapted_cadlag_version_Icc
      (Poisson.Compensated.exists_everywhere_cadlag_stochasticIntegral D.N _
        (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) _ (hA.γ_meas i) (hA.γ_prog i)
        (marked_sq_int_global_of_vanishing (fun ω _ e hs => jumpProc_of_notMem hs i ω e)
          (hA.γ_sq i)) h0 hnull)
  · obtain ⟨M, hMa, -, hMe, hMc, -⟩ :=
      Brownian.Multidim.MultidimBrownianMotion.exists_everywhere_cadlag_vectorIntegral D.W _
        (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (Z k)
        (fun j => Brownian.Ito.measurable_uncurry_of_predictable (hΘ.Z_pred k j))
        (progressivelyMeasurable_of_predictable_of_vanish (hΘ.Z_pred k) (hΘ.Z_vanish k))
        (sq_int_global_of_vanishing (hΘ.Z_vanish k) (hΘ.Z_sq k)) h0 hnull
    exact exists_adapted_cadlag_version_Icc
      ⟨M, hMa, hMe, fun ω t => (hMc ω t).1, fun ω t => (hMc ω t).2⟩
  · exact exists_adapted_cadlag_version_Icc
      (Poisson.Compensated.exists_everywhere_cadlag_stochasticIntegral D.N _
        (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω' s e => U k s ω' e)
        ((hΘ.U_pred k).mono (Probability.markedPredictableSigma_le _ ν) le_rfl)
        (hΘ.U_pred k).markedProgressivelyMeasurable
        (marked_sq_int_global_of_vanishing (hΘ.U_vanish k) (hΘ.U_sq k)) h0 hnull)

/-! ### The norm of `𝕊` -/

/-- `(x²)^{1/2} = x` in `[0, ∞]`. -/
theorem rpow_half_sq (x : ℝ≥0∞) : (x ^ 2) ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- `(x^{1/2})² = x` in `[0, ∞]`. -/
theorem sq_rpow_half (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- **Minkowski's inequality for square roots of finite sums** in `[0, ∞]`: if
`Q_i^{1/2} ≤ q_i^{1/2} + q'_i^{1/2}` for every `i ∈ s`, then
`(∑ Q_i)^{1/2} ≤ (∑ q_i)^{1/2} + (∑ q'_i)^{1/2}`. -/
theorem finset_sum_rpow_half_le {ι : Type*} (s : Finset ι) {Q q q' : ι → ℝ≥0∞}
    (h : ∀ i ∈ s, Q i ^ (1 / 2 : ℝ) ≤ q i ^ (1 / 2 : ℝ) + q' i ^ (1 / 2 : ℝ)) :
    (∑ i ∈ s, Q i) ^ (1 / 2 : ℝ)
      ≤ (∑ i ∈ s, q i) ^ (1 / 2 : ℝ) + (∑ i ∈ s, q' i) ^ (1 / 2 : ℝ) := by
  have key := ENNReal.Lp_add_le s (fun i => q i ^ (1 / 2 : ℝ)) (fun i => q' i ^ (1 / 2 : ℝ))
    (p := 2) one_le_two
  simp only [sq_rpow_half] at key
  refine le_trans (ENNReal.rpow_le_rpow (Finset.sum_le_sum fun i hi => ?_) (by norm_num)) key
  calc Q i = (Q i ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := (sq_rpow_half _).symm
    _ ≤ _ := ENNReal.rpow_le_rpow (h i hi) (by norm_num)

/-- Minkowski's inequality for the square roots of two-term sums in `[0, ∞]`. -/
theorem add_rpow_half_le {a b a' b' a'' b'' : ℝ≥0∞}
    (ha : a'' ^ (1 / 2 : ℝ) ≤ a ^ (1 / 2 : ℝ) + a' ^ (1 / 2 : ℝ))
    (hb : b'' ^ (1 / 2 : ℝ) ≤ b ^ (1 / 2 : ℝ) + b' ^ (1 / 2 : ℝ)) :
    (a'' + b'') ^ (1 / 2 : ℝ) ≤ (a + b) ^ (1 / 2 : ℝ) + (a' + b') ^ (1 / 2 : ℝ) := by
  have h := finset_sum_rpow_half_le Finset.univ (Q := ![a'', b'']) (q := ![a, b])
    (q' := ![a', b']) (fun i _ => by fin_cases i; exacts [ha, hb])
  simpa [Fin.sum_univ_two] using h

/-- The triangle inequality `|x + y| ≤ |x| + |y|` for the Euclidean norm `(esq x)^{1/2}`. -/
theorem esq_add_rpow_half_le {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    esq (fun i => x i + y i) ^ (1 / 2 : ℝ) ≤ esq x ^ (1 / 2 : ℝ) + esq y ^ (1 / 2 : ℝ) := by
  simp only [esq_eq_enorm_sq, rpow_half_sq]
  exact enorm_add_le (toLp 2 x : EuclideanSpace ℝ ι) (toLp 2 y)

/-- Minkowski's inequality for the `S²`-seminorm `(𝔼 sup_{t ≤ T} |x_t|²)^{1/2}`, for processes
whose running suprema are measurable. -/
theorem lintegral_biSup_esq_add_rpow_half_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} [Fintype ι] {x y : ι → ℝ → Ω → ℝ} {T : ℝ}
    (hx : Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω))
    (hy : Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => y i t ω)) :
    (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω + y i t ω)) ∂P) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂P) ^ (1 / 2 : ℝ)
        + (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => y i t ω)) ∂P) ^ (1 / 2 : ℝ) := by
  have key := ENNReal.lintegral_Lp_add_le (μ := P) (p := 2)
    (f := fun ω => (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ^ (1 / 2 : ℝ))
    (g := fun ω => (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => y i t ω)) ^ (1 / 2 : ℝ))
    (hx.pow_const _).aemeasurable (hy.pow_const _).aemeasurable one_le_two
  simp only [Pi.add_apply, sq_rpow_half] at key
  refine le_trans (ENNReal.rpow_le_rpow (lintegral_mono fun ω => ?_) (by norm_num)) key
  refine iSup₂_le fun t ht => ?_
  calc esq (fun i => x i t ω + y i t ω)
      = (esq (fun i => x i t ω + y i t ω) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := (sq_rpow_half _).symm
    _ ≤ _ := by
      refine ENNReal.rpow_le_rpow ((esq_add_rpow_half_le _ _).trans (add_le_add ?_ ?_))
        (by norm_num)
      · exact ENNReal.rpow_le_rpow
          (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => esq (fun i => x i t ω)) t ht)
          (by norm_num)
      · exact ENNReal.rpow_le_rpow
          (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => esq (fun i => y i t ω)) t ht)
          (by norm_num)

/-- Minkowski's inequality for the square root of the energy of jointly measurable
integrands. -/
theorem energy_add_rpow_half_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H K : Ω → ℝ → ℝ} (hH : Measurable (Function.uncurry H))
    (hK : Measurable (Function.uncurry K)) (T : ℝ) :
    Brownian.Ito.energy P T (fun ω s => H ω s + K ω s) ^ (1 / 2 : ℝ)
      ≤ Brownian.Ito.energy P T H ^ (1 / 2 : ℝ) + Brownian.Ito.energy P T K ^ (1 / 2 : ℝ) := by
  rw [Brownian.Ito.energy_eq_eLpNorm_sq (H := fun ω s => H ω s + K ω s) (hH.add hK) T,
    Brownian.Ito.energy_eq_eLpNorm_sq hH T, Brownian.Ito.energy_eq_eLpNorm_sq hK T]
  simp only [rpow_half_sq]
  exact eLpNorm_add_le (f := fun p : Ω × ℝ => H p.1 p.2) (g := fun p : Ω × ℝ => K p.1 p.2)
    hH.aestronglyMeasurable hK.aestronglyMeasurable one_le_two

/-- Minkowski's inequality for the square root of the marked energy of jointly measurable marked
integrands. -/
theorem markedEnergy_add_rpow_half_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {φ ψ : Ω → ℝ → E → ℝ}
    (hφ : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2) (T : ℝ) :
    Poisson.Compensated.markedEnergy P ν T (fun ω s e => φ ω s e + ψ ω s e) ^ (1 / 2 : ℝ)
      ≤ Poisson.Compensated.markedEnergy P ν T φ ^ (1 / 2 : ℝ)
        + Poisson.Compensated.markedEnergy P ν T ψ ^ (1 / 2 : ℝ) := by
  rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq
      (φ := fun ω s e => φ ω s e + ψ ω s e) (hφ.add hψ) T,
    Poisson.Compensated.markedEnergy_eq_eLpNorm_sq hφ T,
    Poisson.Compensated.markedEnergy_eq_eLpNorm_sq hψ T]
  simp only [rpow_half_sq]
  exact eLpNorm_add_le (f := fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (g := fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    hφ.aestronglyMeasurable hψ.aestronglyMeasurable one_le_two

/-- **`‖c Θ‖²_𝕊 = |c|² ‖Θ‖²_𝕊`**, the scalar multiple taken coordinatewise. -/
theorem supSize_const_mul {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
    (P : Measure Ω) (ν : Measure E) {n m d : ℕ} (T c : ℝ) (X : Fin n → ℝ → Ω → ℝ)
    (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ) :
    supSize P ν T (fun i t ω => c * X i t ω) (fun k t ω => c * Y k t ω)
        (fun k t ω j => c * Z k t ω j) (fun k t ω e => c * U k t ω e)
      = (‖c‖₊ : ℝ≥0∞) ^ 2 * supSize P ν T X Y Z U := by
  set κ : ℝ≥0∞ := (‖c‖₊ : ℝ≥0∞) ^ 2 with hκ
  have hκt : κ ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hesq : ∀ {ι : Type} [Fintype ι] (x : ι → ℝ), esq (fun i => c * x i) = κ * esq x := by
    intro ι _ x
    simp only [esq, nnnorm_mul, ENNReal.coe_mul, mul_pow, Finset.mul_sum, hκ]
  have hsup : ∀ {ι : Type} [Fintype ι] (x : ι → ℝ → Ω → ℝ),
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => c * x i t ω)) ∂P
        = κ * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => x i t ω)) ∂P := by
    intro ι _ x
    simp only [hesq, ← ENNReal.mul_iSup]
    exact lintegral_const_mul' _ _ hκt
  have hen : ∀ H : Ω → ℝ → ℝ,
      Brownian.Ito.energy P T (fun ω s => c * H ω s) = κ * Brownian.Ito.energy P T H := by
    intro H
    simp only [Brownian.Ito.energy, nnnorm_mul, ENNReal.coe_mul, mul_pow, ← hκ,
      lintegral_const_mul' _ _ hκt]
  have hmen : ∀ φ : Ω → ℝ → E → ℝ,
      Poisson.Compensated.markedEnergy P ν T (fun ω s e => c * φ ω s e)
        = κ * Poisson.Compensated.markedEnergy P ν T φ := by
    intro φ
    simp only [Poisson.Compensated.markedEnergy, nnnorm_mul, ENNReal.coe_mul, mul_pow, ← hκ,
      lintegral_const_mul' _ _ hκt]
  simp only [supSize, hsup, hen, hmen, ← Finset.mul_sum, ← mul_add]

/-- §3, `‖·‖_𝕊` satisfies the triangle inequality and is absolutely homogeneous. -/
theorem sec3_HH_norm : PaperSpec.A.sec3_HH_norm.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ T X X' Y Y' Z Z' U U' hΘ hΘ'
  set ℱ := enlJoint 𝒢₀ D h𝒢₀
  refine ⟨?_, fun c => ?_⟩
  · unfold supSize
    refine add_rpow_half_le (add_rpow_half_le (add_rpow_half_le ?_ ?_) ?_) ?_
    · exact lintegral_biSup_esq_add_rpow_half_le
        (measurable_biSup_esq_of_Ico (fun i t ht => (hΘ.X_adapted i t ht).mono (ℱ.le t) le_rfl)
          hΘ.X_rightCont)
        (measurable_biSup_esq_of_Ico (fun i t ht => (hΘ'.X_adapted i t ht).mono (ℱ.le t) le_rfl)
          hΘ'.X_rightCont)
    · exact lintegral_biSup_esq_add_rpow_half_le
        (measurable_biSup_esq_of_Ico (fun k t ht => (hΘ.Y_adapted k t ht).mono (ℱ.le t) le_rfl)
          hΘ.Y_rightCont)
        (measurable_biSup_esq_of_Ico (fun k t ht => (hΘ'.Y_adapted k t ht).mono (ℱ.le t) le_rfl)
          hΘ'.Y_rightCont)
    · exact finset_sum_rpow_half_le _ fun k _ => finset_sum_rpow_half_le _ fun j _ =>
        energy_add_rpow_half_le (Brownian.Ito.measurable_uncurry_of_predictable (hΘ.Z_pred k j))
          (Brownian.Ito.measurable_uncurry_of_predictable (hΘ'.Z_pred k j)) T
    · exact finset_sum_rpow_half_le _ fun k _ => markedEnergy_add_rpow_half_le
        ((hΘ.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl)
        ((hΘ'.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl) T
  · rw [supSize_const_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), rpow_half_sq,
      ← Real.norm_eq_abs, ofReal_norm]
    rfl

/-! ### Instances of the hypotheses -/

/-- **The hypotheses of the càdlàg versions of the integrals of (1.1) can be met with nonzero
integrands.** Over a probability space carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`,
with `𝒢₀ = ⊥`, `n = m = 1` and `T = 1`, the tuple `X = Y = 1`, `Z = U = 1_{(0, 1]}` is a tuple of
`ℍ²` along which the integrals of (1.1) for the system of Example 5.1(i) (`β₁ = β₂ = 1`,
`σ_c = h_c = 0`) exist, and `Z` and `U` have energy `1`. -/
theorem sec3_cadlag_versions_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (_ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)
      (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U : Fin 1 → ℝ → Ω → ℝ → ℝ) (γ : Fin 1 → ℝ → Ω → ℝ → ℝ),
      PaperWeakTuple (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 X Y Z U
      ∧ PaperAdmissibleInt (enlJoint ⊥ D bot_le) P 1
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 1 1 0 0) X Y Z U γ
      ∧ Brownian.Ito.energy P 1 (fun ω s => Z 0 s ω 0) = 1
      ∧ Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1
          (fun ω s e => U 0 s ω e) = 1 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  set ℱ := enlJoint ⊥ D bot_le
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  have hE : Brownian.Ito.energy P 1 (fun (_ : Ω) s => unitWindow s) = 1 := by
    simp [Brownian.Ito.energy, setLIntegral_unitWindow_sq]
  have hEm : Poisson.Compensated.markedEnergy P (Measure.dirac (0 : ℝ)) 1
      (fun (_ : Ω) s (_ : ℝ) => unitWindow s) = 1 := by
    simp [Poisson.Compensated.markedEnergy, setLIntegral_unitWindow_sq]
  have hE1 : Brownian.Ito.energy P 1 (fun (_ : Ω) (_ : ℝ) => (1 : ℝ)) = 1 := by
    simp [Brownian.Ito.energy]
  have hΘ : PaperWeakTuple ℱ P (Measure.dirac (0 : ℝ)) 1 (fun (_ : Fin 1) _ (_ : Ω) => (1 : ℝ))
      (fun (_ : Fin 1) _ (_ : Ω) => (1 : ℝ)) (fun (_ : Fin 1) s (_ : Ω) (_ : Fin 1) => unitWindow s)
      (fun (_ : Fin 1) s (_ : Ω) (_ : ℝ) => unitWindow s) :=
    { X_adapted := fun _ _ _ => measurable_const
      X_rightCont := fun _ _ _ _ => tendsto_const_nhds
      X_leftLim := fun _ => Eventually.of_forall fun _ _ _ => ⟨1, tendsto_const_nhds⟩
      X_sq := fun _ => by rw [hE1]; exact ENNReal.one_ne_top
      Y_adapted := fun _ _ _ => measurable_const
      Y_rightCont := fun _ _ _ _ => tendsto_const_nhds
      Y_leftLim := fun _ => Eventually.of_forall fun _ _ _ => ⟨1, tendsto_const_nhds⟩
      Y_sq := fun _ => by rw [hE1]; exact ENNReal.one_ne_top
      Z_pred := fun _ _ => predictable_unitWindow ℱ
      Z_vanish := fun _ _ _ hs => funext fun _ => unitWindow_of_notMem hs
      Z_sq := fun _ _ => by rw [hE]; exact ENNReal.one_ne_top
      U_pred := fun _ => markedPredictable_unitWindow ℱ (Measure.dirac (0 : ℝ))
      U_vanish := fun _ _ _ _ hs => unitWindow_of_notMem hs
      U_sq := fun _ => by rw [hEm]; exact ENNReal.one_ne_top }
  obtain ⟨hJ, -, -, -, -⟩ :=
    affine_assumptions (ν := Measure.dirac (0 : ℝ)) (ℱ := ℱ) (P := P) (T := 1)
      (σc := 0) (hc := 0) one_pos one_pos (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  obtain ⟨γ, hadm⟩ := hΘ.exists_paperAdmissible zero_le_one (hJ.coeffRegular ℱ P)
    (coeffOrigin_affine 1) (diagonalLipschitz_affine (L := 1) zero_le_one zero_le_one
      (by norm_num))
  exact ⟨Ω, inferInstance, P, inferInstance, D, hind₀, _, _, _, _, γ, hΘ, hadm.toInt, hE, hEm⟩

/-- **The hypotheses of the norm properties of `‖·‖_𝕊` can be met by nonzero tuples.** Over a
probability space carrying a Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥`,
`n = m = 1` and `T = 1`, the tuple `X = Y = 1`, `Z = U = 1_{(0, 1]}`, taken for both `Θ` and
`Θ'`, is a tuple of `ℍ²` with `‖Θ‖²_𝕊 = 4`. -/
theorem sec3_HH_norm_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (X X' : Fin 1 → ℝ → Ω → ℝ) (Y Y' : Fin 1 → ℝ → Ω → ℝ)
      (Z Z' : Fin 1 → ℝ → Ω → Fin 1 → ℝ) (U U' : Fin 1 → ℝ → Ω → ℝ → ℝ),
      PaperWeakTuple (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 X Y Z U
      ∧ PaperWeakTuple (enlJoint ⊥ D bot_le) P (Measure.dirac (0 : ℝ)) 1 X' Y' Z' U'
      ∧ supSize P (Measure.dirac (0 : ℝ)) 1 X Y Z U = 4
      ∧ supSize P (Measure.dirac (0 : ℝ)) 1 X' Y' Z' U' = 4 := by
  obtain ⟨Ω, _, P, _, D, X, Y, Z, U, hw, h4, -⟩ := sec3_HH_complete_hypotheses
  exact ⟨Ω, inferInstance, P, inferInstance, D, X 0, X 0, Y 0, Y 0, Z 0, Z 0, U 0, U 0, hw 0,
    hw 0, h4 0, h4 0⟩

end Dissertation.Acceptance.A
