/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Examples.Dealer.Active

/-!
# Example 5.5: the solution depends on the interaction strength

If one tuple solves the exposure-sensitive dealer system at two strengths `ε ≠ ε'`, its forward
equations at the two strengths differ only in the jump integrand, so the second moment of the
difference of the two forward solutions is the marked energy of the difference of the jump
integrands, and vanishes: the jump coefficients agree at the predictable tuple, and the
crowding correction vanishes there for `dt ⊗ dP`.

## Main statements

* `PaperSolution.dealer_crowd_eq_zero_of_two` — a tuple solving at two strengths has vanishing
  crowding correction.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped RealInnerProductSpace ENNReal NNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.BrownianPoisson LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {T β₁ β₂ ε ε' : ℝ} {σc : EuclideanSpace ℝ (Fin 1 × Fin 1)}
  {hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {ξ₀ : Fin 1 → Ω → ℝ}
  {X : Fin 1 → ℝ → Ω → ℝ} {Y : Fin 1 → ℝ → Ω → ℝ} {Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ}
  {U : Fin 1 → ℝ → Ω → E → ℝ} {γ₁ γ₂ : Fin 1 → ℝ → Ω → E → ℝ}

/-- **A tuple solving the dealer system at two strengths has vanishing crowding correction.**
Over a filtration with a cross witness and for `T > 0`, if `(X, Y, Z, U)` solves the
exposure-sensitive dealer system in the sense of the paper at the strengths `ε ≠ ε'`, then at
almost every `s ∈ [0, T]` the crowding correction `A_{μ⁻_s}(U_s)` at the predictable tuple
vanishes almost surely. -/
theorem PaperSolution.dealer_crowd_eq_zero_of_two
    (h₁ : PaperSolution D ℱ hℱW hℱN T (dealerExpCoeffs β₁ β₂ σc hc hx ε) ξ₀ X Y Z U γ₁)
    (h₂ : PaperSolution D ℱ hℱW hℱN T (dealerExpCoeffs β₁ β₂ σc hc hx ε') ξ₀ X Y Z U γ₂)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (hεε : ε ≠ ε') :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      crowdOp (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
        (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2 = 0 := by
  obtain ⟨X₁, Y₁, hXX₁, hYY₁, hS₁⟩ := h₁.exists_solves hT.le
  obtain ⟨X₂, Y₂, hXX₂, hYY₂, hS₂⟩ := h₂.exists_solves hT.le
  have hf₁ := System.Solves.linearFSDEJ hS₁ 0
  have hf₂ := System.Solves.linearFSDEJ hS₂ 0
  -- along the horizon the two tuples agree
  have htup : ∀ s ∈ Set.Icc (0 : ℝ) T,
      tupleAt ν X₂ Y₂ Z U s = tupleAt ν X₁ Y₁ Z U s := by
    intro s hs
    funext ω
    have e1 : (fun i => X₂ i s ω) = fun i => X₁ i s ω := funext fun i => by
      rw [congrFun (hXX₂ i s hs) ω, congrFun (hXX₁ i s hs) ω]
    have e2 : (fun k => Y₂ k s ω) = fun k => Y₁ k s ω := funext fun k => by
      rw [congrFun (hYY₂ k s hs) ω, congrFun (hYY₁ k s hs) ω]
    simp only [tupleAt, e1, e2]
  have hr : ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      2 * (X₂ 0 q.2 q.1 - (fun _ => (1 : ℝ)) q.2 * X₁ 0 q.2 q.1)
          * (driftProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε') X₂ Y₂ Z U 0 q.1 q.2
            - (fun _ => (0 : ℝ)) q.2 * X₁ 0 q.2 q.1
            - (fun _ => (1 : ℝ)) q.2
              * driftProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X₁ Y₁ Z U 0 q.1 q.2)
        + ∑ j, (diffusionProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε') X₂ Y₂ Z U 0 q.2 q.1 j
            - (fun _ => (1 : ℝ)) q.2
              * diffusionProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X₁ Y₁ Z U 0 q.2 q.1 j) ^ 2
        + ∫ e, (jumpProc T γ₂ 0 q.2 q.1 e - (fun _ => (1 : ℝ)) q.2 * jumpProc T γ₁ 0 q.2 q.1 e)
          ^ 2 ∂ν
        = ∫ e, (jumpProc T γ₂ 0 q.2 q.1 e - jumpProc T γ₁ 0 q.2 q.1 e) ^ 2 ∂ν := by
    filter_upwards [LinearFSDEJ.ae_snd_mem_Icc (P := P) T] with q hq
    have hX : X₂ 0 q.2 q.1 = X₁ 0 q.2 q.1 := by
      rw [congrFun (hXX₂ 0 q.2 hq) q.1, congrFun (hXX₁ 0 q.2 hq) q.1]
    have hσ : ∀ j, diffusionProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε') X₂ Y₂ Z U 0 q.2 q.1 j
        = diffusionProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X₁ Y₁ Z U 0 q.2 q.1 j := by
      intro j
      simp only [diffusionProc, Set.indicator_of_mem hq, htup q.2 hq]
      rfl
    simp only [hX, hσ, one_mul, sub_self, mul_zero, zero_mul, Finset.sum_const_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  have hnonneg : 0 ≤ᵐ[P.prod (volume.restrict (Set.Icc (0 : ℝ) T))] fun q : Ω × ℝ =>
      2 * (X₂ 0 q.2 q.1 - (fun _ => (1 : ℝ)) q.2 * X₁ 0 q.2 q.1)
          * (driftProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε') X₂ Y₂ Z U 0 q.1 q.2
            - (fun _ => (0 : ℝ)) q.2 * X₁ 0 q.2 q.1
            - (fun _ => (1 : ℝ)) q.2
              * driftProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X₁ Y₁ Z U 0 q.1 q.2)
        + ∑ j, (diffusionProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε') X₂ Y₂ Z U 0 q.2 q.1 j
            - (fun _ => (1 : ℝ)) q.2
              * diffusionProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X₁ Y₁ Z U 0 q.2 q.1 j) ^ 2
        + ∫ e, (jumpProc T γ₂ 0 q.2 q.1 e - (fun _ => (1 : ℝ)) q.2 * jumpProc T γ₁ 0 q.2 q.1 e)
          ^ 2 ∂ν := by
    filter_upwards [hr] with q hq
    rw [Pi.zero_apply, hq]
    exact integral_nonneg fun _ => sq_nonneg _
  have hT0 : ∫ ω, (X₂ 0 T ω - (fun _ => (1 : ℝ)) T * X₁ 0 T ω) ^ 2 ∂P = 0 := by
    refine (integral_congr_ae (Eventually.of_forall fun ω => ?_)).trans (integral_zero _ _)
    simp only [congrFun (hXX₂ 0 T ⟨hT.le, le_rfl⟩) ω, congrFun (hXX₁ 0 T ⟨hT.le, le_rfl⟩) ω,
      one_mul, sub_self]
    norm_num
  obtain ⟨-, hI⟩ := LinearFSDEJ.residual_eq_zero_of_nonneg hf₁ hf₂ 𝒲 hT
    (p := fun _ => 1) (p' := fun _ => 0) continuousOn_const
    (fun x _ => hasDerivAt_const x 1) continuousOn_const hT0 hnonneg
  obtain ⟨hint, -⟩ := LinearFSDEJ.integral_residual_sq_eq hf₁ hf₂ 𝒲 hT
    (p := fun _ => 1) (p' := fun _ => 0) continuousOn_const
    (fun x _ => hasDerivAt_const x 1) continuousOn_const ⟨hT.le, le_rfl⟩
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hI
  have hγ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      ∫ e, (jumpProc T γ₂ 0 s ω e - jumpProc T γ₁ 0 s ω e) ^ 2 ∂ν = 0 := by
    refine ae_ae_of_ae_prod_Icc (P := P) (p := fun q : Ω × ℝ =>
      ∫ e, (jumpProc T γ₂ 0 q.2 q.1 e - jumpProc T γ₁ 0 q.2 q.1 e) ^ 2 ∂ν = 0) ?_
    filter_upwards [hzero, hr] with q h1 h2
    rw [← h2]
    exact h1
  have hm₁ := ae_ae_memLp_of_markedEnergy_ne_top hf₁.γ_meas hf₁.γ_sq
  have hm₂ := ae_ae_memLp_of_markedEnergy_ne_top hf₂.γ_meas hf₂.γ_sq
  filter_upwards [hγ, hm₁, hm₂, h₁.jump_rep, h₂.jump_rep, ae_restrict_mem measurableSet_Icc]
    with s hs hs₁ hs₂ hr₁ hr₂ hsI
  filter_upwards [hs, hs₁, hs₂, hr₁, hr₂] with ω hω hω₁ hω₂ hω₃ hω₄
  -- the two jump integrands agree, so the two jump coefficients do
  have hint' : Integrable (fun e => (jumpProc T γ₂ 0 s ω e - jumpProc T γ₁ 0 s ω e) ^ 2) ν :=
    (hω₂.sub hω₁).integrable_sq
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint').mp hω
  have hheq : (dealerExpCoeffs β₁ β₂ σc hc hx ε).h s
      (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
      (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s))
      = (dealerExpCoeffs β₁ β₂ σc hc hx ε').h s
      (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω)
      (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)) := by
    refine Lp.ext ?_
    filter_upwards [hω₃, hω₄, hae] with e e1 e2 e3
    rw [← e1, ← e2]
    have : (jumpProc T γ₂ 0 s ω e - jumpProc T γ₁ 0 s ω e) ^ 2 = 0 := e3
    have h0 := pow_eq_zero_iff two_ne_zero |>.mp this
    simp only [jumpProc, Set.indicator_of_mem hsI] at h0
    refine PiLp.ext fun i => ?_
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [PiLp.toLp_apply]
    linarith
  rw [dealerExpCoeffs_h, dealerExpCoeffs_h] at hheq
  have hsm : (ε' - ε) • crowdOp
      (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
      (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2 = 0 := by
    rw [sub_smul]
    linear_combination (norm := module) hheq
  exact (smul_eq_zero.mp hsm).resolve_left (sub_ne_zero.mpr hεε.symm)

end MVFBSDEJ.WellPosedness.Existence
