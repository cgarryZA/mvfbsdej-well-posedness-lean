/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec5BrownianReduction
import Dissertation.Acceptance.A.Sec2Basics
import Dissertation.Acceptance.A.Sec3
import Dissertation.Acceptance.A.Sec5Brownian
import Dissertation.WellPosedness.Examples.BrownianSolves
import Dissertation.WellPosedness.System.SolvesPathwise

/-!
# Example 5.2 of the well-posedness paper, the reduction to the Brownian forms: proofs

At `ν = 0` the fibres `L²(0; ℝⁿ)` and `L²(0; ℝᵐ)` have a single point, so every jump term of
Assumptions 2.3 and 2.5 vanishes and `W₂` on `P₂(H)` is `W₂` of the laws of `(X, Y, Z)`
(`w2P_projP2`); the tuple `Θ_s` does not depend on `U`; and the compensated Poisson integral
vanishes on `[0, T]` on one set of full measure, being almost surely right-continuous and almost
surely `0` at each time. The filtration of §2 is the Brownian one (`enlJoint_nu_zero_eq`).

## Main statements

* `Dissertation.Acceptance.A.ex_brownian_reduction` — the reduction of Assumptions 2.3 and 2.5,
  of (2.7) and of the solution notions to their Brownian forms.
* `Dissertation.Acceptance.A.ex_brownian_prp` — the Brownian representation property, from the
  representation property of §2 (`sec2_prp`).
* `Dissertation.Acceptance.A.ex_brownian_reduction_hypotheses` — the hypotheses can be met, at a
  system of the branch `m > n` with a solution of (1.1).
* `Dissertation.Acceptance.A.ex_brownian_prp_hypotheses` — the hypotheses can be met.
-/

open MeasureTheory ProbabilityTheory Filter Dissertation.Law
open scoped Topology ENNReal NNReal

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Enlarged
  Dissertation.WellPosedness.Existence Dissertation.WellPosedness.Spec LevyStochCalc
  LevyStochCalc.BSDEJ.Solves

universe u v w

section Assumptions

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] {n m d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {P : Measure Ω} [IsProbabilityMeasure P] {C : Coeffs (0 : Measure E) n m d}

omit [MeasurableSpace.CountablyGenerated E] in
/-- An element of `L²(0; F)` has norm `0`. -/
theorem norm_lp_nu_zero {F : Type*} [NormedAddCommGroup F] (x : Lp F 2 (0 : Measure E)) :
    ‖x‖ = 0 := by
  rw [Subsingleton.elim x 0, norm_zero]

/-- At `ν = 0` the interior bound of Assumption 2.3 at a time is its Brownian form. -/
theorem lipInteriorAt_iff_brownian {t L : ℝ} :
    LipInteriorAt ℱ P t L C ↔ BrownianLipInteriorAt ℱ P t L C := by
  simp only [LipInteriorAt, BrownianLipInteriorAt, norm_lp_nu_zero, add_zero, w2P_projP2]

/-- At `ν = 0` Assumption 2.3 is its Brownian form. -/
theorem assumption23_iff_brownian {T L : ℝ} :
    Assumption23 ℱ P T L C ↔ BrownianAssumption23 ℱ P T L C := by
  have hI : LipInterior ℱ P T L C ↔ BrownianLipInterior ℱ P T L C := by
    simp only [LipInterior, BrownianLipInterior, lipInteriorAt_iff_brownian]
  exact ⟨fun h => ⟨h.nonneg, hI.mp h.interior, h.terminal⟩,
    fun h => ⟨h.1, hI.mpr h.2.1, h.2.2⟩⟩

omit [MeasurableSpace.CountablyGenerated E] in
/-- At `ν = 0` the integrand of (2.7) is the one without the jump pairing. -/
theorem pairing27_nu_zero (G : Matrix (Fin m) (Fin n) ℝ) (t : ℝ)
    (θ θ' : TupleH (0 : Measure E) n m d) (μ μ' : P2 (TupleH (0 : Measure E) n m d)) :
    pairing27 G C t θ θ' μ μ' = brownianPairing G C t θ θ' μ μ' := by
  simp [pairing27, brownianPairing]

/-- At `ν = 0` the interior inequality (2.7) at a time is its Brownian form. -/
theorem mono27At_iff_brownian {t β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} :
    Mono27At ℱ P t G β₁ β₂ C ↔ BrownianMonoAt ℱ P t G β₁ β₂ C := by
  simp only [Mono27At, BrownianMonoAt, pairing27_nu_zero, norm_lp_nu_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]

/-- At `ν = 0` Assumption 2.5 is its Brownian form. -/
theorem assumption25_iff_brownian {T α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} :
    Assumption25 ℱ P T G α β₁ β₂ C ↔ BrownianAssumption25 ℱ P T G α β₁ β₂ C := by
  have hI : (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Mono27At ℱ P t G β₁ β₂ C)
      ↔ ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), BrownianMonoAt ℱ P t G β₁ β₂ C := by
    simp only [mono27At_iff_brownian]
  exact ⟨fun h => ⟨h.terminal, hI.mp h.interior, h.constants⟩,
    fun h => ⟨h.1, hI.mpr h.2.1, h.2.2⟩⟩

end Assumptions

section Solutions

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type v} [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

omit [MeasurableSpace Ω] [MeasurableSpace.CountablyGenerated E] in
/-- At `ν = 0` the tuple of the coordinate processes does not depend on the jump integrand. -/
theorem tupleAt_nu_zero (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ)
    (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ) :
    tupleAt (0 : Measure E) X Y Z U = tupleAt (0 : Measure E) X Y Z 0 := by
  funext s ω
  simp only [tupleAt, Prod.mk.injEq, true_and]
  exact Subsingleton.elim _ _

/-- At `ν = 0` the drift process does not depend on the jump integrand. -/
theorem driftProc_nu_zero (T : ℝ) (C : Coeffs (0 : Measure E) n m d) (X : Fin n → ℝ → Ω → ℝ)
    (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ) :
    driftProc P T C X Y Z U = driftProc P T C X Y Z 0 := by
  unfold driftProc
  rw [tupleAt_nu_zero X Y Z U]

/-- At `ν = 0` the diffusion process does not depend on the jump integrand. -/
theorem diffusionProc_nu_zero (T : ℝ) (C : Coeffs (0 : Measure E) n m d)
    (X : Fin n → ℝ → Ω → ℝ) (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ)
    (U : Fin m → ℝ → Ω → E → ℝ) :
    diffusionProc P T C X Y Z U = diffusionProc P T C X Y Z 0 := by
  unfold diffusionProc
  rw [tupleAt_nu_zero X Y Z U]

/-- At `ν = 0` the driver process does not depend on the jump integrand. -/
theorem driverProc_nu_zero (T : ℝ) (C : Coeffs (0 : Measure E) n m d) (X : Fin n → ℝ → Ω → ℝ)
    (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ) :
    driverProc P T C X Y Z U = driverProc P T C X Y Z 0 := by
  unfold driverProc
  rw [tupleAt_nu_zero X Y Z U]

omit [MeasurableSpace.CountablyGenerated E] in
/-- The multidimensional Brownian integral depends on the integrand only. -/
theorem brownianIntegral_congr (W : Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, Brownian.IsBrownianFiltration (W.W j) ℱ) {σ σ' : ℝ → Ω → Fin d → ℝ}
    (h : σ = σ') (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ s ω j))
    (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => σ s ω j)
    (hq : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm' : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ' s ω j))
    (hp' : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => σ' s ω j)
    (hq' : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖σ' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW σ hm hp hq
      = Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW σ' hm' hp' hq' := by
  subst h
  rfl

omit [MeasurableSpace.CountablyGenerated E] in
/-- **At `ν = 0` the compensated Poisson integral vanishes on `[0, T]` on one set of full
measure.** -/
theorem ae_forall_Icc_poissonIntegral_nu_zero
    (N : Poisson.PoissonRandomMeasure.{u, v, w} P (0 : Measure E))
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : Poisson.IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ) (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (h_prog : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂(0 : Measure E) ∂volume ∂P < ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Poisson.Compensated.stochasticIntegral N ℱ hℱ φ h_meas h_prog h_sq t ω = 0 := by
  rcases le_or_gt 0 T with hT | hT
  · have h := ae_forall_Icc_eq_of_ae_rightContinuous (B := fun _ _ => (0 : ℝ)) hT
      (fun t _ => stochasticIntegral_nu_zero N ℱ hℱ φ h_meas h_prog h_sq t)
      (by
        filter_upwards [Poisson.Compensated.stochasticIntegral_cadlag N ℱ hℱ φ h_meas h_prog
          h_sq] with ω hω t
        exact (hω t).1)
      (ae_of_all _ fun _ _ => tendsto_const_nhds)
    exact h
  · exact ae_of_all _ fun _ t ht => absurd (ht.1.trans ht.2) (not_le.mpr hT)

omit [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] in
/-- The zero jump integrand cut to the horizon is zero. -/
theorem jumpProc_zero (T : ℝ) : jumpProc T (0 : Fin n → ℝ → Ω → E → ℝ) = 0 := by
  funext i s ω e
  simp [jumpProc]

variable {D : Driver.LevyDriver.{u, v, w} P d (0 : Measure E)}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {C : Coeffs (0 : Measure E) n m d}
  {ξ₀ : Fin n → Ω → ℝ} {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ}
  {Z : Fin m → ℝ → Ω → Fin d → ℝ} {U : Fin m → ℝ → Ω → E → ℝ}

/-- **At `ν = 0` a solution of (1.1) in `ℍ_weak` is a solution of the Brownian system in
`ℍ_weak` with a jump integrand that is `0` in `L²(dt ⊗ dP ⊗ ν)`**, over any filtration carrying
the driver. -/
theorem paperWeakSolutionInt_iff_brownian :
    (∃ γ, PaperWeakSolutionInt D ℱ hℱW hℱN T C ξ₀ X Y Z U γ) ↔
      (∀ k, Probability.MarkedPredictable ℱ (0 : Measure E) (fun ω s e => U k s ω e)
        ∧ (∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U k s ω e = 0)
        ∧ Poisson.Compensated.markedEnergy P (0 : Measure E) T (fun ω s e => U k s ω e) = 0)
      ∧ BrownianPaperWeakSolution D.W ℱ hℱW T C ξ₀ X Y Z := by
  have hb := driftProc_nu_zero (P := P) T C X Y Z U
  have hσ := diffusionProc_nu_zero (P := P) T C X Y Z U
  have hf := driverProc_nu_zero (P := P) T C X Y Z U
  constructor
  · rintro ⟨γ, h⟩
    refine ⟨fun k => ⟨h.U_pred k, h.U_vanish k, markedEnergy_nu_zero T _⟩, ?_⟩
    exact
    { X_adapted := h.X_adapted
      X_rightCont := h.X_rightCont
      X_leftLim := h.X_leftLim
      X_sq := h.X_sq
      Y_adapted := h.Y_adapted
      Y_rightCont := h.Y_rightCont
      Y_leftLim := h.Y_leftLim
      Y_sq := h.Y_sq
      Z_pred := h.Z_pred
      Z_vanish := h.Z_vanish
      Z_sq := h.Z_sq
      b_meas := by rw [← hb]; exact h.b_meas
      b_prog := by rw [← hb]; exact h.b_prog
      b_int := by rw [← hb]; exact h.b_int
      σ_meas := by rw [← hσ]; exact h.σ_meas
      σ_prog := by rw [← hσ]; exact h.σ_prog
      σ_sq := by rw [← hσ]; exact h.σ_sq
      f_meas := by rw [← hf]; exact h.f_meas
      f_prog := by rw [← hf]; exact h.f_prog
      f_int := by rw [← hf]; exact h.f_int
      XT_sq := h.XT_sq
      fwd := fun i => by
        obtain ⟨M, hM, hreg, heq⟩ := h.fwd i
        refine ⟨M, fun t ht => ?_, hreg, ?_⟩
        · filter_upwards [hM t ht] with ω hω
          rw [hω]
          exact congrFun (congrFun (brownianIntegral_congr D.W ℱ hℱW (congrFun hσ i) _ _ _ _ _ _)
            t) ω
        · have hN := ae_forall_Icc_poissonIntegral_nu_zero D.N ℱ hℱN
            (fun ω' s e => jumpProc T γ i s ω' e) (h.γ_meas i) (h.γ_prog i)
            (marked_sq_int_global_of_vanishing (fun ω s e hs => jumpProc_of_notMem hs i ω e)
              (h.γ_sq i)) T
          filter_upwards [heq, hN] with ω h1 h2 t ht
          rw [h1 t ht, h2 t ht, add_zero, hb]
      bwd := fun k => by
        obtain ⟨M, hM, hreg, heq⟩ := h.bwd k
        refine ⟨M, hM, hreg, ?_⟩
        have hN := ae_forall_Icc_poissonIntegral_nu_zero D.N ℱ hℱN (fun ω' s e => U k s ω' e)
          ((h.U_pred k).mono (Probability.markedPredictableSigma_le ℱ (0 : Measure E)) le_rfl)
          (h.U_pred k).markedProgressivelyMeasurable
          (marked_sq_int_global_of_vanishing (h.U_vanish k) (h.U_sq k)) T
        filter_upwards [heq, hN] with ω h1 h2 t ht
        rw [h1 t ht, h2 t ht, h2 T ⟨ht.1.trans ht.2, le_rfl⟩, sub_self, sub_zero, hf] }
  · rintro ⟨hU, h⟩
    have hγm : ∀ i, Measurable fun p : Ω × ℝ × E =>
        jumpProc T (0 : Fin n → ℝ → Ω → E → ℝ) i p.2.1 p.1 p.2.2 := fun i => by
      rw [jumpProc_zero]
      exact measurable_const
    have hγp : ∀ i, Probability.MarkedProgressivelyMeasurable ℱ fun ω s e =>
        jumpProc T (0 : Fin n → ℝ → Ω → E → ℝ) i s ω e := fun i => by
      rw [jumpProc_zero]
      exact Poisson.Compensated.markedProgressivelyMeasurable_zero ℱ
    have hγq : ∀ i, Poisson.Compensated.markedEnergy P (0 : Measure E) T
        (fun ω s e => jumpProc T (0 : Fin n → ℝ → Ω → E → ℝ) i s ω e) ≠ ⊤ := fun i => by
      rw [markedEnergy_nu_zero]
      exact ENNReal.zero_ne_top
    refine ⟨0, ?_⟩
    exact
    { X_adapted := h.X_adapted
      X_rightCont := h.X_rightCont
      X_leftLim := h.X_leftLim
      X_sq := h.X_sq
      Y_adapted := h.Y_adapted
      Y_rightCont := h.Y_rightCont
      Y_leftLim := h.Y_leftLim
      Y_sq := h.Y_sq
      Z_pred := h.Z_pred
      Z_vanish := h.Z_vanish
      Z_sq := h.Z_sq
      U_pred := fun k => (hU k).1
      U_vanish := fun k => (hU k).2.1
      U_sq := fun k => by rw [(hU k).2.2]; exact ENNReal.zero_ne_top
      b_meas := by rw [hb]; exact h.b_meas
      b_prog := by rw [hb]; exact h.b_prog
      b_int := by rw [hb]; exact h.b_int
      σ_meas := by rw [hσ]; exact h.σ_meas
      σ_prog := by rw [hσ]; exact h.σ_prog
      σ_sq := by rw [hσ]; exact h.σ_sq
      γ_meas := hγm
      γ_prog := hγp
      γ_sq := hγq
      f_meas := by rw [hf]; exact h.f_meas
      f_prog := by rw [hf]; exact h.f_prog
      f_int := by rw [hf]; exact h.f_int
      jump_rep := ae_of_all _ fun _ => ae_of_all _ fun _ => by
        rw [Filter.EventuallyEq, ae_zero]
        exact Filter.eventually_bot
      XT_sq := h.XT_sq
      fwd := fun i => by
        obtain ⟨M, hM, hreg, heq⟩ := h.fwd i
        refine ⟨M, fun t ht => ?_, hreg, ?_⟩
        · filter_upwards [hM t ht] with ω hω
          rw [hω]
          exact congrFun (congrFun
            (brownianIntegral_congr D.W ℱ hℱW (congrFun hσ i).symm _ _ _ _ _ _) t) ω
        · have hN := ae_forall_Icc_poissonIntegral_nu_zero D.N ℱ hℱN
            (fun ω' s e => jumpProc T (0 : Fin n → ℝ → Ω → E → ℝ) i s ω' e) (hγm i) (hγp i)
            (marked_sq_int_global_of_vanishing (fun ω s e hs => jumpProc_of_notMem hs i ω e)
              (hγq i)) T
          filter_upwards [heq, hN] with ω h1 h2 t ht
          rw [h2 t ht, add_zero, hb]
          exact h1 t ht
      bwd := fun k => by
        obtain ⟨M, hM, hreg, heq⟩ := h.bwd k
        refine ⟨M, hM, hreg, ?_⟩
        have hN := ae_forall_Icc_poissonIntegral_nu_zero D.N ℱ hℱN (fun ω' s e => U k s ω' e)
          (((hU k).1).mono (Probability.markedPredictableSigma_le ℱ (0 : Measure E)) le_rfl)
          ((hU k).1).markedProgressivelyMeasurable
          (marked_sq_int_global_of_vanishing (hU k).2.1
            (by rw [(hU k).2.2]; exact ENNReal.zero_ne_top)) T
        filter_upwards [heq, hN] with ω h1 h2 t ht
        rw [h2 t ht, h2 T ⟨ht.1.trans ht.2, le_rfl⟩, sub_self, sub_zero, hf]
        exact h1 t ht }

/-- The Brownian system in `ℍ_weak` over equal filtrations. -/
theorem brownianPaperWeakSolution_congr {W : Brownian.Multidim.MultidimBrownianMotion P d}
    {ℱ₁ ℱ₂ : Filtration ℝ ‹MeasurableSpace Ω›} (h : ℱ₁ = ℱ₂)
    (h₁ : ∀ j : Fin d, Brownian.IsBrownianFiltration (W.W j) ℱ₁)
    (h₂ : ∀ j : Fin d, Brownian.IsBrownianFiltration (W.W j) ℱ₂) :
    BrownianPaperWeakSolution W ℱ₁ h₁ T C ξ₀ X Y Z
      ↔ BrownianPaperWeakSolution W ℱ₂ h₂ T C ξ₀ X Y Z := by
  subst h
  rfl

end Solutions

/-- Example 5.2, the reduction of the assumptions and the solution notions. -/
theorem ex_brownian_reduction : PaperSpec.A.ex_brownian_reduction.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ _ d P _ D h𝒢₀ hind₀ n m T C
  have hF := enlJoint_nu_zero_eq 𝒢₀ D h𝒢₀
  have hMP : ∀ U : Fin m → ℝ → Ω → E → ℝ, ∀ k,
      Probability.MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) (0 : Measure E)
          (fun ω s e => U k s ω e)
        ↔ Probability.MarkedPredictable (enlBrownian 𝒢₀ D.W h𝒢₀) (0 : Measure E)
          (fun ω s e => U k s ω e) := fun U k => by
    rw [hF]
  have hweak : ∀ (ξ₀ : Ω → EuclideanSpace ℝ (Fin n)) (X : Fin n → ℝ → Ω → ℝ)
      (Y : Fin m → ℝ → Ω → ℝ) (Z : Fin m → ℝ → Ω → Fin d → ℝ) (U : Fin m → ℝ → Ω → E → ℝ),
      PaperSpec.A.WeakSolution D h𝒢₀ hind₀ T C ξ₀ X Y Z U
        ↔ (∀ k, Probability.MarkedPredictable (enlBrownian 𝒢₀ D.W h𝒢₀) (0 : Measure E)
              (fun ω s e => U k s ω e)
            ∧ (∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U k s ω e = 0)
            ∧ Poisson.Compensated.markedEnergy P (0 : Measure E) T (fun ω s e => U k s ω e) = 0)
          ∧ PaperSpec.A.BrownianWeakSolution D.W h𝒢₀
            (isBrownianFiltration_enlBrownian D h𝒢₀ hind₀) T C ξ₀ X Y Z := by
    intro ξ₀ X Y Z U
    have hcore := paperWeakSolutionInt_iff_brownian (D := D)
      (hℱW := isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
      (hℱN := isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (T := T) (C := C)
      (ξ₀ := fun i ω => ξ₀ ω i) (X := X) (Y := Y) (Z := Z) (U := U)
    have hB := brownianPaperWeakSolution_congr (W := D.W) (T := T) (C := C)
      (ξ₀ := fun i ω => ξ₀ ω i) (X := X) (Y := Y) (Z := Z) hF
      (isBrownianFiltration_enlJoint D h𝒢₀ hind₀) (isBrownianFiltration_enlBrownian D h𝒢₀ hind₀)
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨hU, hBr⟩ := hcore.mp h1
      exact ⟨fun k => ⟨(hMP U k).mp (hU k).1, (hU k).2⟩, hB.mp hBr, h2, h3⟩
    · rintro ⟨hU, hBr, h2, h3⟩
      exact ⟨hcore.mpr ⟨fun k => ⟨(hMP U k).mpr (hU k).1, (hU k).2⟩, hB.mpr hBr⟩, h2, h3⟩
  refine ⟨fun L => ?_, fun t L => ?_, fun t G β₁ β₂ => ?_, fun G α β₁ β₂ => ?_,
    fun ξ₀ X Y Z U => ?_, hweak⟩
  · rw [hF]
    exact assumption23_iff_brownian
  · rw [hF]
    exact lipInteriorAt_iff_brownian
  · rw [hF]
    exact mono27At_iff_brownian
  · rw [hF]
    exact assumption25_iff_brownian
  · constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨hU, hBr⟩ := (hweak ξ₀ X Y Z U).mp h1
      exact ⟨hU, hBr, h2, h3⟩
    · rintro ⟨hU, hBr, h2, h3⟩
      exact ⟨(hweak ξ₀ X Y Z U).mpr ⟨hU, hBr⟩, h2, h3⟩

/-- **The hypotheses of the reduction of Example 5.2 can be met, at a system with a solution.**
There is a probability space carrying a Lévy driver with `d = 1` and the intensity `ν = 0` on
`ℝ`, with `𝒢₀ = ⊥` independent of it; and there, for `n = 1`, `m = 2`, `T = 1` and the initial
datum `0`, a coefficient system and a solution of (1.1) in `ℍ` (the linear generator of the
branch `m > n`, with Theorem 3.5). -/
theorem ex_brownian_reduction_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (0 : Measure ℝ))
      (hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P)
      (C : Coeffs (0 : Measure ℝ) 1 2 1) (X : Fin 1 → ℝ → Ω → ℝ) (Y : Fin 2 → ℝ → Ω → ℝ)
      (Z : Fin 2 → ℝ → Ω → Fin 1 → ℝ) (U : Fin 2 → ℝ → Ω → ℝ → ℝ),
      PaperSpec.A.Solution D bot_le hind₀ 1 C (fun _ => 0) X Y Z U := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (0 : Measure ℝ)
  have hind₀ : Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P := indep_bot_left _
  obtain ⟨G, C, L, α, β₁, β₂, hJ, h22, h23, hG, h25, -⟩ := ex_brownian_rank_gt ⊥ 1 P D bot_le
    hind₀ 1 2 one_pos one_lt_two one_pos 1 one_pos (fun _ => 0) stronglyMeasurable_const
    (memLp_const _)
  obtain ⟨X, Y, Z, U, h⟩ := (thm_cwp ⊥ (0 : Measure ℝ) 1 2 1 P D bot_le hind₀ one_pos two_pos
    one_pos 1 one_pos L α β₁ β₂ G C (fun _ => 0) hJ h22 h23 hG h25).1
  exact ⟨Ω, inferInstance, P, inferInstance, D, hind₀, C, X, Y, Z, U, h⟩

section Representation

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {E : Type v} [MeasurableSpace E] {d : ℕ}

/-- The multidimensional Brownian integral over equal filtrations. -/
theorem brownianIntegral_congr_filtration (W : Brownian.Multidim.MultidimBrownianMotion P d)
    {ℱ₁ ℱ₂ : Filtration ℝ mΩ} (h : ℱ₁ = ℱ₂)
    (h₁ : ∀ j : Fin d, Brownian.IsBrownianFiltration (W.W j) ℱ₁)
    (h₂ : ∀ j : Fin d, Brownian.IsBrownianFiltration (W.W j) ℱ₂) (Z : ℝ → Ω → Fin d → ℝ)
    (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ₁ fun ω s => Z s ω j)
    (hp' : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ₂ fun ω s => Z s ω j)
    (hq : ∀ (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ₁ h₁ Z hm hp hq
      = Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ₂ h₂ Z hm hp' hq := by
  subst h
  rfl

variable (D : Driver.LevyDriver.{u, v, w} P d (0 : Measure E)) (h𝒢₀ : 𝒢₀ ≤ mΩ)
  (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) {T : ℝ} {M : ℝ → Ω → ℝ} {Z : ℝ → Ω → Fin d → ℝ}

/-- **At `ν = 0` a representation of §2 is a Brownian one.** -/
theorem brownian_of_representsMart {U : ℝ → Ω → E → ℝ}
    (h : PaperSpec.A.RepresentsMart D h𝒢₀ hind₀ T M Z U) :
    PaperSpec.A.RepresentsMartBrownian D.W h𝒢₀
      (isBrownianFiltration_enlBrownian D h𝒢₀ hind₀) T M Z := by
  have hF := enlJoint_nu_zero_eq 𝒢₀ D h𝒢₀
  obtain ⟨hZ, hZv, hZe, hU, hUv, hUe, hrep⟩ := h
  have hZB : ∀ j, Probability.Predictable (enlBrownian 𝒢₀ D.W h𝒢₀) fun ω s => Z s ω j :=
    fun j => hF ▸ hZ j
  refine ⟨hZB, hZv, hZe, fun t ht => ?_⟩
  filter_upwards [hrep t ht, stochasticIntegral_nu_zero D.N (enlJoint 𝒢₀ D h𝒢₀)
    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun ω s e => U s ω e)
    (hU.mono (Probability.markedPredictableSigma_le _ (0 : Measure E)) le_rfl)
    hU.markedProgressivelyMeasurable (marked_sq_int_global_of_vanishing hUv hUe) t]
    with ω h1 h2
  rw [h1, h2, Pi.zero_apply, add_zero, brownianIntegral_congr_filtration D.W hF]

/-- **At `ν = 0` a Brownian representation is a representation of §2** with the jump integrand
`0`. -/
theorem representsMart_of_brownian
    (h : PaperSpec.A.RepresentsMartBrownian D.W h𝒢₀
      (isBrownianFiltration_enlBrownian D h𝒢₀ hind₀) T M Z) :
    PaperSpec.A.RepresentsMart D h𝒢₀ hind₀ T M Z (fun _ _ _ => 0) := by
  have hF := enlJoint_nu_zero_eq 𝒢₀ D h𝒢₀
  obtain ⟨hZB, hZv, hZe, hrep⟩ := h
  have hZ : ∀ j, Probability.Predictable (enlJoint 𝒢₀ D h𝒢₀) fun ω s => Z s ω j :=
    fun j => hF.symm ▸ hZB j
  have hU : Probability.MarkedPredictable (enlJoint 𝒢₀ D h𝒢₀) (0 : Measure E)
      fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ) := measurable_const
  have hUe : Poisson.Compensated.markedEnergy P (0 : Measure E) T
      (fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ)) ≠ ⊤ := by
    rw [markedEnergy_nu_zero]
    exact ENNReal.zero_ne_top
  refine ⟨hZ, hZv, hZe, hU, fun _ _ _ _ => rfl, hUe, fun t ht => ?_⟩
  filter_upwards [hrep t ht, stochasticIntegral_nu_zero D.N (enlJoint 𝒢₀ D h𝒢₀)
    (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) (fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ))
    (hU.mono (Probability.markedPredictableSigma_le _ (0 : Measure E)) le_rfl)
    hU.markedProgressivelyMeasurable
    (marked_sq_int_global_of_vanishing (T := T) (fun _ _ _ _ => rfl) hUe) t] with ω h1 h2
  rw [h1, h2, Pi.zero_apply, add_zero, brownianIntegral_congr_filtration D.W hF]

end Representation

/-- Example 5.2, the representation property. -/
theorem ex_brownian_prp : PaperSpec.A.ex_brownian_prp.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ _ d P _ D h𝒢₀ hind₀ hd T hT M hM hM2
  have hMJ : Martingale M (enlJoint 𝒢₀ D h𝒢₀) P := by
    rw [enlJoint_nu_zero_eq 𝒢₀ D h𝒢₀]
    exact hM
  obtain ⟨⟨Z, U, hrep⟩, huniq⟩ := sec2_prp 𝒢₀ (0 : Measure E) d P D h𝒢₀ hind₀ hd T hT M hMJ hM2
  exact ⟨⟨Z, brownian_of_representsMart D h𝒢₀ hind₀ hrep⟩, fun Z₁ Z₂ h₁ h₂ =>
    (huniq Z₁ Z₂ (fun _ _ _ => 0) (fun _ _ _ => 0) (representsMart_of_brownian D h𝒢₀ hind₀ h₁)
      (representsMart_of_brownian D h𝒢₀ hind₀ h₂)).1⟩

/-- **The hypotheses of the representation property of Example 5.2 can be met.** There is a
probability space carrying a Lévy driver with `d = 1` and the intensity `ν = 0` on `ℝ`, with
`𝒢₀ = ⊥` independent of it; `T = 1`; and the martingale `0` of the Brownian filtration, square
integrable at every time. -/
theorem ex_brownian_prp_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (0 : Measure ℝ)),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P ∧ 0 < (1 : ℕ) ∧ (0 : ℝ) < 1
      ∧ Martingale (0 : ℝ → Ω → ℝ) (enlBrownian ⊥ D.W bot_le) P
      ∧ ∀ t, MemLp ((0 : ℝ → Ω → ℝ) t) 2 P := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (0 : Measure ℝ)
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, one_pos, one_pos,
    martingale_zero _ _ _, fun _ => MemLp.zero⟩

end Dissertation.Acceptance.A
