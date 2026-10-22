/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.PaperSpec.Sec3Rem34
import MVFBSDEJ.WellPosedness.Spec.NotAssumption22
import MVFBSDEJ.WellPosedness.Enlarged.Bot

/-!
# Remark 3.4 of the well-posedness paper: proofs

## Main statements

* `MVFBSDEJ.Acceptance.rem_uniq_initial` — `ξ₀ = X₀` almost surely and `X₀` is square
  integrable by the `S²` bound.
* `MVFBSDEJ.Acceptance.rem_uniq_singular` — the singular-drift system: its assumptions,
  the failure of Assumption 2.2, and the solution `X_t = 2√t − y_T t`, `Y ≡ y_T`, `Z = U = 0` with
  `y_T = 2√T / (1 + T)`, transported from the augmented joint filtration to `enlJoint ⊥ D`.
* `MVFBSDEJ.Acceptance.rem_uniq_hypotheses` — an instance meeting the hypotheses.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace MVFBSDEJ.Acceptance

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.Spec LevyStochCalc LevyStochCalc.BSDEJ.Solves

universe u v w

/-- Remark 3.4, the initial datum. -/
theorem rem_uniq_initial : PaperSpec.rem_uniq_initial.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ T hT C ξ₀ X Y Z U hW hsup i
  obtain ⟨⟨γ, h⟩, -, -⟩ := hW
  obtain ⟨M, hMae, -, hid⟩ := h.fwd i
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hX0 : MemLp (X i 0) 2 P := memLp_of_lintegral_biSup_esq_lt_top hsup h0 i
    ((h.X_adapted i 0 h0).mono ((enlJoint 𝒢₀ D h𝒢₀).le 0) le_rfl).aestronglyMeasurable
  refine hX0.ae_eq ?_
  filter_upwards [hid, hMae 0 h0,
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W _
      (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) _
      (h.σ_meas i) (h.σ_prog i)
      (sq_int_global_of_vanishing (fun ω s hs => diffusionProc_of_notMem hs i ω) (h.σ_sq i))
      le_rfl,
    Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos
      (φ := fun ω s e => jumpProc T γ i s ω e) D.N (isPoissonFiltration_enlJoint D h𝒢₀ hind₀)
      (h.γ_meas i) (h.γ_prog i)
      (marked_sq_int_global_of_vanishing (fun ω s e hs => jumpProc_of_notMem hs i ω e)
        (h.γ_sq i)) le_rfl] with ω hω hM hW hN
  simp only [Pi.zero_apply] at hW hN
  rw [hω 0 h0, hM, hW, hN, Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
    integral_zero_measure]
  ring

/-- `PaperWeakSolutionInt` depends on the filtration only, not on the proofs that it carries the
driver. -/
theorem paperWeakSolutionInt_congr_filtration {Ω : Type u} [MeasurableSpace Ω] {E : Type v}
    [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]
    {n m d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ ℱ' : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : ℱ = ℱ')
    {hW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
    {hN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
    {hW' : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ'}
    {hN' : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ'} {T : ℝ} {C : Coeffs ν n m d}
    {ξ₀ : Fin n → Ω → ℝ} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
    {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}
    (h : PaperWeakSolutionInt D ℱ hW hN T C ξ₀ X Y Z U γ) :
    PaperWeakSolutionInt D ℱ' hW' hN' T C ξ₀ X Y Z U γ := by
  subst hℱ
  exact h

/-- Remark 3.4, the singular drift. -/
theorem rem_uniq_singular : PaperSpec.rem_uniq_singular.{u, v, w} := by
  intro Ω _ E _ ν _ _ d P _ D hind₀ T hT
  set y := singularY T
  have hcont : Continuous fun t : ℝ => 2 * Real.sqrt t - y * t :=
    (continuous_const.mul Real.continuous_sqrt).sub (continuous_const.mul continuous_id)
  have hbd : ∀ t ∈ Set.Icc (0 : ℝ) T,
      esq (fun _ : Fin 1 => 2 * Real.sqrt t - y * t)
        ≤ ENNReal.ofReal ((2 * Real.sqrt T + |y| * T) ^ 2) := by
    intro t ht
    have h1 : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt ht.2
    have h2 : |y * t| ≤ |y| * T := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact mul_le_mul_of_nonneg_left ht.2 (abs_nonneg y)
    have h3 : |2 * Real.sqrt t - y * t| ≤ 2 * Real.sqrt T + |y| * T := by
      have := abs_sub (2 * Real.sqrt t) (y * t)
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt t)] at this
      linarith
    simp only [esq, Finset.univ_unique, Finset.sum_singleton]
    rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  have hYbd : ∀ t ∈ Set.Icc (0 : ℝ) T, esq (fun _ : Fin 1 => y) ≤ esq (fun _ : Fin 1 => y) :=
    fun _ _ => le_rfl
  refine ⟨jointBorel_singularCoeffs T, assumption23_singularCoeffs, ?_, assumption25_singularCoeffs,
    fun ξ₀ => not_assumption22_singularCoeffs hT ξ₀,
    fun _ t _ => 2 * Real.sqrt t - y * t, fun _ _ _ => y, 0, 0, ⟨⟨0, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · simp
  · have h := paperWeakSolutionIntAug_singularCoeffs D hT (ν := ν) (d := d)
    have e : (fun i ω => ((fun _ => (0 : EuclideanSpace ℝ (Fin 1))) ω) i)
        = (0 : Fin 1 → Ω → ℝ) := by
      funext i ω
      simp
    rw [e]
    exact paperWeakSolutionInt_congr_filtration (enlJoint_bot D).symm h
  · intro i ω t _
    exact ⟨_, ((hcont.tendsto t).mono_left nhdsWithin_le_nhds)⟩
  · intro k ω t _
    exact ⟨_, tendsto_const_nhds⟩
  · refine lt_of_le_of_lt (lintegral_mono fun ω => iSup₂_le fun t ht => hbd t ht) ?_
    rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top
  · refine lt_of_le_of_lt (lintegral_mono fun ω => iSup₂_le fun t ht => le_rfl) ?_
    rw [lintegral_const, measure_univ, mul_one]
    simp [esq]

/-- **The hypotheses of Remark 3.4 can be met.** Over a probability space carrying a Lévy driver
with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥` independent of it and `T = 1`, the singular-drift
system has, from the initial datum `0`, a tuple of `ℍ²` satisfying (1.1) whose components
have `𝔼 sup_{t ≤ 1} |X_t|² < ∞` and `𝔼 sup_{t ≤ 1} |Y_t|² < ∞`. -/
theorem rem_uniq_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ)))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)
      (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 1 → ℝ → Ω → ℝ) (Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ)
      (U : Fin 1 → ℝ → Ω → ℝ → ℝ),
      PaperSpec.WeakSolution D bot_le hind₀ 1
          (singularCoeffs (ν := Measure.dirac (0 : ℝ)) (d := 1)) (fun _ => 0) X Y Z U
        ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) 1, esq (fun i => X i t ω)) ∂P < ⊤
        ∧ ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) 1, esq (fun k => Y k t ω)) ∂P < ⊤ := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨-, -, -, -, -, X, Y, Z, U, h⟩ :=
    rem_uniq_singular (Measure.dirac (0 : ℝ)) 1 P D hind₀ 1 one_pos
  exact ⟨Ω, inferInstance, P, inferInstance, D, hind₀, X, Y, Z, U, h⟩

end MVFBSDEJ.Acceptance
