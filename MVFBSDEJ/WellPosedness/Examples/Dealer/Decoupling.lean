/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Examples.Dealer.Exposure
import MVFBSDEJ.WellPosedness.Stability.MomentAt

/-!
# Example 5.5: decoupling residuals of the dealer market

For a solution `(X, Y, Z, U)` of the exposure-sensitive dealer system
`dealerExpCoeffs β₁ β₂ σ_c h_c h_x ε` (with `n = m = d = 1`) and a weight `p` of class `C¹` with
`p(T) = 1`, the second moment of the decoupling residual `Y_t − p(t) X_t` is absolutely continuous
with rate

`r = 2 (Y − p X)(−β₂ X − ⟨h_x, U⟩ − p' X + β₁ p Y) + (Z − p (σ_c − β₁ Z))² + ∫_E (U − p γ)² dν`,

`γ` the representative of the jump coefficient. When `r ≥ 0`, the residual vanishes and so does
`r`, for `dP ⊗ ds` on `[0, T]`.

## Main statements

* `driftProc_dealerExp`, `diffusionProc_dealerExp`, `driverProc_dealerExp`,
  `terminalVal_dealerExp` — the coefficient processes of the dealer system along a tuple.
* `Solves.dealer_residual_eq_zero` — the residual and its rate vanish when the rate is
  nonnegative.
-/

open MeasureTheory Filter MVFBSDEJ.Law
open scoped RealInnerProductSpace ENNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.BrownianPoisson LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ} {β₁ β₂ ε : ℝ} {σc : EuclideanSpace ℝ (Fin 1 × Fin 1)}
  {hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν}
  {X : Fin 1 → ℝ → Ω → ℝ} {Y : Fin 1 → ℝ → Ω → ℝ} {Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ}
  {U : Fin 1 → ℝ → Ω → E → ℝ}

/-! ### The coefficient processes along a tuple -/

/-- The drift process of the dealer system on `[0, T]` is `−β₁ Y`. -/
theorem driftProc_dealerExp {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ω : Ω) :
    driftProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X Y Z U 0 ω s = -(β₁ * Y 0 s ω) := by
  simp [driftProc, Set.indicator_of_mem hs, dealerExpCoeffs, dealerCoeffs, Coeffs.perturb,
    affineCoeffs, crowdPert, exposurePert, tupleAt]

/-- The diffusion process of the dealer system on `[0, T]` is `σ_c − β₁ Z`. -/
theorem diffusionProc_dealerExp {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ω : Ω) :
    diffusionProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X Y Z U 0 s ω 0
      = σc (0, 0) - β₁ * Z 0 s ω 0 := by
  simp [diffusionProc, Set.indicator_of_mem hs, dealerExpCoeffs, dealerCoeffs, Coeffs.perturb,
    affineCoeffs, crowdPert, exposurePert, tupleAt]

/-- The driver process of the dealer system on `[0, T]` is `β₂ X + ⟨h_x, U⟩_{L²(ν)}`. -/
theorem driverProc_dealerExp {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T)
    (ω : Ω) :
    driverProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X Y Z U 0 ω s
      = β₂ * X 0 s ω + ⟪hx, uLift ν (fun e k => U k s ω e)⟫ := by
  simp [driverProc, Set.indicator_of_mem hs, dealerExpCoeffs, dealerCoeffs, Coeffs.perturb,
    affineCoeffs, crowdPert, exposurePert, tupleAt]

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The terminal value of the dealer system is `X_T`. -/
theorem terminalVal_dealerExp (ω : Ω) :
    terminalVal P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X 0 ω = X 0 T ω := by
  simp [terminalVal, dealerExpCoeffs, dealerCoeffs, Coeffs.perturb, affineCoeffs]

/-! ### The decoupling residual -/

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {ξ₀ : Fin 1 → Ω → ℝ}
  {γ : Fin 1 → ℝ → Ω → E → ℝ}

/-- **The decoupling residual of the dealer system vanishes when its rate is nonnegative.** For
a solution of the dealer system over a filtration with a cross witness, `T > 0`, and a weight `p`
continuous on `[0, T]` with a derivative `p'` on `(0, T)` continuous on `[0, T]` and `p(T) = 1`:
if the rate
`r = 2 (Y − p X)(−(β₂ X + ⟨h_x, U⟩) − p' X + p β₁ Y) + (Z − p (σ_c − β₁ Z))² + ∫_E (U − p γ)² dν`
is nonnegative for `dP ⊗ ds` on `[0, T]`, then `𝔼[(Y_t − p(t) X_t)²] = 0` at every `t ∈ [0, T]`,
and `r` is integrable and vanishes for `dP ⊗ ds` on `[0, T]`. -/
theorem Solves.dealer_residual_eq_zero
    (h : Solves D ℱ hℱW hℱN T (dealerExpCoeffs β₁ β₂ σc hc hx ε) ξ₀ X Y Z U γ)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) {p p' : ℝ → ℝ}
    (hpc : ContinuousOn p (Set.Icc (0 : ℝ) T))
    (hp : ∀ x ∈ Set.Ioo (0 : ℝ) T, HasDerivAt p (p' x) x)
    (hp' : ContinuousOn p' (Set.Icc (0 : ℝ) T)) (hpT : p T = 1)
    (hr : ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      0 ≤ 2 * (Y 0 q.2 q.1 - p q.2 * X 0 q.2 q.1)
          * (-(β₂ * X 0 q.2 q.1 + ⟪hx, uLift ν (fun e k => U k q.2 q.1 e)⟫)
            - p' q.2 * X 0 q.2 q.1 + p q.2 * (β₁ * Y 0 q.2 q.1))
        + (Z 0 q.2 q.1 0 - p q.2 * (σc (0, 0) - β₁ * Z 0 q.2 q.1 0)) ^ 2
        + ∫ e, (U 0 q.2 q.1 e - p q.2 * γ 0 q.2 q.1 e) ^ 2 ∂ν) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∫ ω, (Y 0 t ω - p t * X 0 t ω) ^ 2 ∂P = 0)
      ∧ Integrable (fun q : Ω × ℝ => 2 * (Y 0 q.2 q.1 - p q.2 * X 0 q.2 q.1)
          * (-(β₂ * X 0 q.2 q.1 + ⟪hx, uLift ν (fun e k => U k q.2 q.1 e)⟫)
            - p' q.2 * X 0 q.2 q.1 + p q.2 * (β₁ * Y 0 q.2 q.1))
        + (Z 0 q.2 q.1 0 - p q.2 * (σc (0, 0) - β₁ * Z 0 q.2 q.1 0)) ^ 2
        + ∫ e, (U 0 q.2 q.1 e - p q.2 * γ 0 q.2 q.1 e) ^ 2 ∂ν)
          (P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      ∧ ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
        2 * (Y 0 q.2 q.1 - p q.2 * X 0 q.2 q.1)
            * (-(β₂ * X 0 q.2 q.1 + ⟪hx, uLift ν (fun e k => U k q.2 q.1 e)⟫)
              - p' q.2 * X 0 q.2 q.1 + p q.2 * (β₁ * Y 0 q.2 q.1))
          + (Z 0 q.2 q.1 0 - p q.2 * (σc (0, 0) - β₁ * Z 0 q.2 q.1 0)) ^ 2
          + ∫ e, (U 0 q.2 q.1 e - p q.2 * γ 0 q.2 q.1 e) ^ 2 ∂ν = 0 := by
  have hX := h.linearFSDEJ 0
  have hYb := h.linearBSDEJ 0
  have hY := hYb.linearFSDEJ (ξ₀ := Y 0 0) (ae_eq_refl _) hT.le
  set R : Ω × ℝ → ℝ := fun q => 2 * (Y 0 q.2 q.1 - p q.2 * X 0 q.2 q.1)
      * (-(β₂ * X 0 q.2 q.1 + ⟪hx, uLift ν (fun e k => U k q.2 q.1 e)⟫)
        - p' q.2 * X 0 q.2 q.1 + p q.2 * (β₁ * Y 0 q.2 q.1))
    + (Z 0 q.2 q.1 0 - p q.2 * (σc (0, 0) - β₁ * Z 0 q.2 q.1 0)) ^ 2
    + ∫ e, (U 0 q.2 q.1 e - p q.2 * γ 0 q.2 q.1 e) ^ 2 ∂ν with hRdef
  -- the generic rate is `R` for `dP ⊗ ds` on `[0, T]`
  have hRe : ∀ᵐ q ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      2 * (Y 0 q.2 q.1 - p q.2 * X 0 q.2 q.1)
          * (-(driverProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X Y Z U 0 q.1 q.2)
            - p' q.2 * X 0 q.2 q.1
            - p q.2 * driftProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X Y Z U 0 q.1 q.2)
        + ∑ j, (Z 0 q.2 q.1 j
          - p q.2 * diffusionProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X Y Z U 0 q.2 q.1 j) ^ 2
        + ∫ e, (U 0 q.2 q.1 e - p q.2 * jumpProc T γ 0 q.2 q.1 e) ^ 2 ∂ν = R q := by
    filter_upwards [LinearFSDEJ.ae_snd_mem_Icc (P := P) T] with q hq
    rw [driverProc_dealerExp hq, driftProc_dealerExp hq, Fin.sum_univ_one,
      diffusionProc_dealerExp hq, hRdef]
    simp only [jumpProc, Set.indicator_of_mem hq]
    ring
  obtain ⟨hint, -⟩ := LinearFSDEJ.integral_residual_sq_eq hX hY 𝒲 hT hpc hp hp'
    ⟨hT.le, le_rfl⟩
  have hT0 : ∫ ω, (Y 0 T ω - p T * X 0 T ω) ^ 2 ∂P = 0 := by
    have hYT := hYb.eqn T ⟨hT.le, le_rfl⟩
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [hYT] with ω hω
    rw [hω, Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
      integral_zero_measure, terminalVal_dealerExp, hpT]
    simp
  obtain ⟨hF, hI⟩ := LinearFSDEJ.residual_eq_zero_of_nonneg hX hY 𝒲 hT hpc hp hp' hT0
    (by filter_upwards [hRe, hr] with q h1 h2; rw [h1]; exact h2)
  have hRint : Integrable R (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    hint.congr hRe
  rw [integral_congr_ae hRe] at hI
  exact ⟨hF, hRint, (integral_eq_zero_iff_of_nonneg_ae hr hRint).mp hI⟩


/-- **The decoupling residual of the dealer system vanishes when its rate is nonnegative**, the
rate nonnegative at almost every time, almost surely: `Solves.dealer_residual_eq_zero` with the
almost-everywhere statements read at almost every `s ∈ [0, T]`, almost surely. -/
theorem Solves.dealer_residual_eq_zero'
    (h : Solves D ℱ hℱW hℱN T (dealerExpCoeffs β₁ β₂ σc hc hx ε) ξ₀ X Y Z U γ)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) {p p' : ℝ → ℝ}
    (hpc : ContinuousOn p (Set.Icc (0 : ℝ) T))
    (hp : ∀ x ∈ Set.Ioo (0 : ℝ) T, HasDerivAt p (p' x) x)
    (hp' : ContinuousOn p' (Set.Icc (0 : ℝ) T)) (hpT : p T = 1)
    (hr : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      0 ≤ 2 * (Y 0 s ω - p s * X 0 s ω)
          * (-(β₂ * X 0 s ω + ⟪hx, uLift ν (fun e k => U k s ω e)⟫)
            - p' s * X 0 s ω + p s * (β₁ * Y 0 s ω))
        + (Z 0 s ω 0 - p s * (σc (0, 0) - β₁ * Z 0 s ω 0)) ^ 2
        + ∫ e, (U 0 s ω e - p s * γ 0 s ω e) ^ 2 ∂ν) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∫ ω, (Y 0 t ω - p t * X 0 t ω) ^ 2 ∂P = 0)
      ∧ ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
        2 * (Y 0 s ω - p s * X 0 s ω)
            * (-(β₂ * X 0 s ω + ⟪hx, uLift ν (fun e k => U k s ω e)⟫)
              - p' s * X 0 s ω + p s * (β₁ * Y 0 s ω))
          + (Z 0 s ω 0 - p s * (σc (0, 0) - β₁ * Z 0 s ω 0)) ^ 2
          + ∫ e, (U 0 s ω e - p s * γ 0 s ω e) ^ 2 ∂ν = 0 := by
  have hX := System.Solves.linearFSDEJ h 0
  have hYb := System.Solves.linearBSDEJ h 0
  have hY := hYb.linearFSDEJ (ξ₀ := Y 0 0) (ae_eq_refl _) hT.le
  have hRe : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ ω,
      2 * (Y 0 s ω - p s * X 0 s ω)
          * (-(driverProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X Y Z U 0 ω s)
            - p' s * X 0 s ω - p s * driftProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X Y Z U 0 ω s)
        + ∑ j, (Z 0 s ω j
          - p s * diffusionProc P T (dealerExpCoeffs β₁ β₂ σc hc hx ε) X Y Z U 0 s ω j) ^ 2
        + ∫ e, (U 0 s ω e - p s * jumpProc T γ 0 s ω e) ^ 2 ∂ν
      = 2 * (Y 0 s ω - p s * X 0 s ω)
          * (-(β₂ * X 0 s ω + ⟪hx, uLift ν (fun e k => U k s ω e)⟫)
            - p' s * X 0 s ω + p s * (β₁ * Y 0 s ω))
        + (Z 0 s ω 0 - p s * (σc (0, 0) - β₁ * Z 0 s ω 0)) ^ 2
        + ∫ e, (U 0 s ω e - p s * γ 0 s ω e) ^ 2 ∂ν := by
    intro s hs ω
    rw [driverProc_dealerExp hs, driftProc_dealerExp hs, Fin.sum_univ_one,
      diffusionProc_dealerExp hs]
    simp only [jumpProc, Set.indicator_of_mem hs]
    ring
  have hT0 : ∫ ω, (Y 0 T ω - p T * X 0 T ω) ^ 2 ∂P = 0 := by
    have hYT := hYb.eqn T ⟨hT.le, le_rfl⟩
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [hYT] with ω hω
    rw [hω, Set.Icc_self, Measure.restrict_singleton, measure_singleton, zero_smul,
      integral_zero_measure, terminalVal_dealerExp, hpT]
    simp
  obtain ⟨hF, hR⟩ := LinearFSDEJ.residual_eq_zero_of_ae_ae_nonneg hX hY 𝒲 hT hpc hp hp' hT0
    (by
      filter_upwards [hr, ae_restrict_mem measurableSet_Icc] with s hs hsI
      filter_upwards [hs] with ω hω
      rw [hRe s hsI ω]
      exact hω)
  refine ⟨hF, ?_⟩
  filter_upwards [hR, ae_restrict_mem measurableSet_Icc] with s hs hsI
  filter_upwards [hs] with ω hω
  rw [← hRe s hsI ω]
  exact hω


end MVFBSDEJ.WellPosedness.Existence
