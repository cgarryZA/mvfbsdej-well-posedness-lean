/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.Dealer.ExposureActivity
import Dissertation.WellPosedness.System.SolutionCongr

/-!
# Example 5.5: the interaction is active

On the dealer mark space with `c_{±1} = (2 − ϱ)/2`, `ϱ < 2`, let `activeDealerCoeffs c hϱ ε` be the
exposure-sensitive dealer system of Example 5.5 with `β₁ = 1`, `β₂ = ½`, `σ_c = 1`,
`h_c(ς, q) = ς q` and `h_x(ς, q) = q`, at interaction strength `ε`. Let `T > 0` and let
`(X, Y, Z, U)` be a solution of it in the sense of the paper over `enlJoint 𝒢₀ D h𝒢₀`, with
initial datum `0`. Write `Θ⁻_s = (X_{s−}, Y_{s−}, Z_s, U_s)` for the predictable tuple,
`μ⁻_s = lawP2 P Θ⁻_s` for its law (the Dirac mass at the origin if `Θ⁻_s` is not square
integrable), `μ⁻_s^U` for the `U`-marginal of `μ⁻_s`, and `A_{μ⁻_s^U}(U_s)` for the crowding
correction along the solution.

* **The correction does not vanish `ds ⊗ dP`-almost everywhere, whatever `ε`.** Otherwise the
  jump coefficients at `ε` and at `0` agree along `Θ⁻`, so the tuple also solves the system at
  `ε = 0`; by uniqueness at `ε = 0` its jump channel is `U⁰_s = ½ (h_c + h_x X⁰_s)` almost
  everywhere, `X⁰` the solution of the exposure equation. At a time `s ∈ (0, T]` at which
  `U_s = U⁰_s` almost surely and the correction vanishes almost surely, this contradicts the
  activity of the crowding correction along `U⁰_s`.
* **Hence, for `ε ≠ 0`, `𝔼 ∫_0^T ‖ε A_{μ⁻_s^U}(U_s)‖²_{L²(ν)} ds > 0`**, both as an extended
  integral and as a Bochner integral. The integrand is bounded by `ε²`, since `‖∇V‖ ≤ 1`, and it
  is measurable in `(ω, s)` up to a null set: `U_s(ω)` is jointly measurable, `s ↦ μ⁻_s` agrees
  at almost every time with the law flow of a jointly measurable extension of the tuple, Borel
  for the 2-Wasserstein distance, and `(θ, μ) ↦ A_{μ^U}(u)` is continuous.
* **The solution depends on `ε`.** If the tuple solved the system at two strengths `ε ≠ ε'`,
  with representatives `γ` and `γ'` of the jump coefficients, subtracting the forward identities
  at `T` would leave `∫_0^T ∫_E (γ − γ')(s, e) Ñ(ds, de) = 0`, and the isometry of the
  compensated Poisson integral would give `γ = γ'` almost everywhere; the representations of the
  jump coefficients would then give `ε A_{μ⁻_s^U}(U_s) = ε' A_{μ⁻_s^U}(U_s)` along `Θ⁻`, so the
  correction would vanish `ds ⊗ dP`-almost everywhere.

The two general steps hold for every solution in the sense of the paper: the measurability of the
crowding correction along `Θ⁻`, for systems on `H = ℝⁿ × ℝⁿ × ℝ^{n×d} × L²(ν; ℝⁿ)`, and the
uniqueness of the jump integrand of a tuple solving two systems with the same drift and diffusion.

## Main statements

* `uLift_eq_of_ae_eq` — a representative of `v ∈ L²(ν; ℝ^ι)` has class `v`.
* `dealerExpCoeffs_b_eq`, `dealerExpCoeffs_σ_eq` — the drift and the diffusion of the
  exposure-sensitive dealer system do not depend on `ε`.
* `PaperSolution.aemeasurable_crowdOp_leftLim` — `(ω, s) ↦ A_{μ⁻_s^U}(U_s(ω))` is almost
  everywhere measurable on `Ω × [0, T]`.
* `PaperSolution.jumpProc_ae_eq_of_b_eq_of_σ_eq` — a tuple solving two systems with the same drift
  and diffusion has almost everywhere equal jump integrands.
* `not_ae_ae_crowdOp_activeDealer_eq_zero` — along every solution, at every strength, the crowding
  correction does not vanish `ds ⊗ dP`-almost everywhere.
* `lintegral_enorm_smul_crowdOp_activeDealer_pos`,
  `integral_norm_smul_crowdOp_activeDealer_sq_pos` — `𝔼 ∫_0^T ‖ε A_{μ⁻_s^U}(U_s)‖² ds > 0` for
  `ε ≠ 0`.
* `not_paperSolutionEnl_activeDealer_of_ne` — no tuple solves the system at two strengths.
-/

open MeasureTheory Filter ProbabilityTheory Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.BrownianPoisson Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.System Dissertation.WellPosedness.Enlarged LevyStochCalc
  LevyStochCalc.BSDEJ.Solves

universe u v w

/-! ### Classes in `L²(ν)` and the dealer coefficients -/

section Coefficients

variable {E : Type v} [MeasurableSpace E] {ν : Measure E}

/-- **A representative of an element of `L²(ν; ℝ^ι)` has that element as its class**: if
`e ↦ u(e)` represents `v ∈ L²(ν; ℝ^ι)`, then `uLift ν u = v`. -/
theorem uLift_eq_of_ae_eq {ι : Type*} [Fintype ι] {u : E → ι → ℝ}
    {v : Lp (EuclideanSpace ℝ ι) 2 ν}
    (h : (fun e => (WithLp.toLp 2 (u e) : EuclideanSpace ℝ ι)) =ᵐ[ν] v) : uLift ν u = v := by
  rw [uLift_of_memLp ((Lp.memLp v).ae_eq h.symm), MemLp.toLp_congr _ (Lp.memLp v) h,
    Lp.toLp_coeFn]

variable {n d : ℕ} {β₁ β₂ ε ε' : ℝ} {σc : EuclideanSpace ℝ (Fin n × Fin d)}
  {hc : Lp (EuclideanSpace ℝ (Fin n)) 2 ν} {hx : Lp ℝ 2 ν}

/-- **The drift of the exposure-sensitive dealer system does not depend on `ε`.** -/
theorem dealerExpCoeffs_b_eq :
    (dealerExpCoeffs β₁ β₂ σc hc hx ε').b = (dealerExpCoeffs β₁ β₂ σc hc hx ε).b := by
  funext t θ μ
  simp only [dealerExpCoeffs, dealerCoeffs, Coeffs.perturb, crowdPert, exposurePert]

/-- **The diffusion of the exposure-sensitive dealer system does not depend on `ε`.** -/
theorem dealerExpCoeffs_σ_eq :
    (dealerExpCoeffs β₁ β₂ σc hc hx ε').σ = (dealerExpCoeffs β₁ β₂ σc hc hx ε).σ := by
  funext t θ μ
  simp only [dealerExpCoeffs, dealerCoeffs, Coeffs.perturb, crowdPert, exposurePert]

end Coefficients

/-! ### Solutions in the sense of the paper -/

section Solutions

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n d : ℕ} {P : Measure Ω}
  [IsProbabilityMeasure P] {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {T : ℝ} {C : Coeffs ν n n d}
  {ξ₀ : Fin n → Ω → ℝ} {X Y : Fin n → ℝ → Ω → ℝ} {Z : Fin n → ℝ → Ω → Fin d → ℝ}
  {U γ : Fin n → ℝ → Ω → E → ℝ}

/-- **The crowding correction along the predictable tuple of a solution is measurable.** For a
solution `(X, Y, Z, U)` of (1.1) in the sense of the paper and `T ≥ 0`, the map
`(ω, s) ↦ A_{μ⁻_s^U}(U_s(ω))` is almost everywhere measurable for `dP ⊗ ds` on `Ω × [0, T]`, with
`Θ⁻_s = (X_{s−}, Y_{s−}, Z_s, U_s)`, `μ⁻_s = lawP2 P Θ⁻_s` and `μ⁻_s^U` its `U`-marginal. -/
theorem _root_.Dissertation.WellPosedness.System.PaperSolution.aemeasurable_crowdOp_leftLim
    (h : PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ) (hT : 0 ≤ T) :
    AEMeasurable (fun p : Ω × ℝ =>
      crowdOp (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U p.2)).margU.law
        (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U p.2 p.1).2.2.2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  obtain ⟨X', hXe, hXa, hXr⟩ := exists_adapted_rightCont_extension hT h.X_adapted h.X_rightCont
  obtain ⟨Y', hYe, hYa, hYr⟩ := exists_adapted_rightCont_extension hT h.Y_adapted h.Y_rightCont
  have hΘ : Measurable (Function.uncurry fun ω s => tupleAt ν X' Y' Z U s ω) :=
    measurable_uncurry_tupleAt
      (fun i => (Probability.measurable_uncurry_of_rightContinuous (hXa i) (hXr i)).comp
        measurable_swap)
      (fun k => (Probability.measurable_uncurry_of_rightContinuous (hYa k) (hYr k)).comp
        measurable_swap)
      (fun k j => Brownian.Ito.measurable_uncurry_of_predictable (h.Z_pred k j))
      (fun k => (h.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl)
  have hρ : AEMeasurable (fun s =>
      (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).toP2WH)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    refine (measurable_lawP2_flow (P := P) hΘ).toP2WH.aemeasurable.congr ?_
    filter_upwards [h.ae_ae_tupleAt_leftLimProc_eq hT, ae_restrict_mem measurableSet_Icc]
      with s hs hsI
    rw [lawP2_congr hs, tupleAt_eq_of_eqOn hXe hYe hsI]
  exact (continuous_crowdOp_margU (ν := ν) (n := n) (d := d)).measurable.comp_aemeasurable
    (hΘ.aemeasurable.prodMk hρ.comp_snd)

/-- **The jump integrand of a solution is determined by the tuple, the drift and the diffusion.**
Let `C, C'` have the same drift and diffusion, `T > 0`, and let `(X, Y, Z, U)` be a solution of
(1.1) in the sense of the paper with coefficients `C` and representative `γ`, and with coefficients
`C'` and representative `γ'`, from the same initial datum. Subtracting the forward identities at
`T` leaves `∫_0^T ∫_E (γ − γ')(s, e) Ñ(ds, de) = 0`, and by the isometry of the compensated
Poisson integral `γ = γ'` almost everywhere on `Ω × [0, T] × E`, coordinatewise. -/
theorem _root_.Dissertation.WellPosedness.System.PaperSolution.jumpProc_ae_eq_of_b_eq_of_σ_eq
    {C' : Coeffs ν n n d} {γ' : Fin n → ℝ → Ω → E → ℝ} (hb : C'.b = C.b) (hσ : C'.σ = C.σ)
    (hT : 0 < T) (h : PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ)
    (h' : PaperSolution D ℱ hℱW hℱN T C' ξ₀ X Y Z U γ') (i : Fin n) :
    ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
      jumpProc T γ i q.2.1 q.1 q.2.2 = jumpProc T γ' i q.2.1 q.1 q.2.2 := by
  obtain ⟨b, σ, hC, f, g⟩ := C
  obtain ⟨b', σ', hC', f', g'⟩ := C'
  obtain rfl : b' = b := hb
  obtain rfl : σ' = σ := hσ
  have hTm : T ∈ Set.Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  obtain ⟨M, hM, -, hid⟩ := h.fwd i
  obtain ⟨M', hM', -, hid'⟩ := h'.fwd i
  have hq := marked_sq_int_global_of_vanishing (fun ω s e hs => jumpProc_of_notMem hs i ω e)
    (h.γ_sq i)
  have hq' := marked_sq_int_global_of_vanishing (fun ω s e hs => jumpProc_of_notMem hs i ω e)
    (h'.γ_sq i)
  have hI : ∀ᵐ ω ∂P, Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
        (fun ω' s e => jumpProc T γ i s ω' e) (h.γ_meas i) (h.γ_prog i) hq T ω
      = Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
        (fun ω' s e => jumpProc T γ' i s ω' e) (h'.γ_meas i) (h'.γ_prog i) hq' T ω := by
    filter_upwards [hid, hid', hM T hTm, hM' T hTm] with ω h1 h2 h3 h4
    have key := (h1 T hTm).symm.trans (h2 T hTm)
    rw [h3, h4] at key
    exact add_left_cancel key
  have hE : Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => jumpProc T γ i s ω e - jumpProc T γ' i s ω e) = 0 := by
    refine (Poisson.Compensated.itoIsometry_diff_compensated D.N ℱ hℱN _ _ (h.γ_meas i)
      (h'.γ_meas i) (h.γ_prog i) (h'.γ_prog i) hq hq' T hT).symm.trans ?_
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hI] with ω hω
    simp [hω]
  exact ae_eq_of_markedEnergy_sub_eq_zero (h.γ_meas i) (h'.γ_meas i) hE

end Solutions

/-! ### The interaction is active -/

section Interaction

variable {c : Bool → ℝ} {ϱ : ℝ} {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {T ε : ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (dealerMarks c ϱ)}
  {h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›} {hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P}
  {X Y : Fin 1 → ℝ → Ω → ℝ} {Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ}
  {U γ : Fin 1 → ℝ → Ω → DealerMark → ℝ}

/-- **Along every solution the crowding correction does not vanish `ds ⊗ dP`-almost
everywhere.** With `c_{±1} = (2 − ϱ)/2`, `ϱ < 2` and `T > 0`, let `(X, Y, Z, U)` be a solution
of (1.1) in the sense of the paper over `enlJoint 𝒢₀ D h𝒢₀` for `activeDealerCoeffs c hϱ ε`, at
any interaction strength `ε`, with initial datum `0`. Then `A_{μ⁻_s^U}(U_s) = 0` does not hold
almost surely for almost every `s ∈ [0, T]`, with `Θ⁻_s = (X_{s−}, Y_{s−}, Z_s, U_s)`,
`μ⁻_s = lawP2 P Θ⁻_s` and `μ⁻_s^U` its `U`-marginal. -/
theorem not_ae_ae_crowdOp_activeDealer_eq_zero (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2)
    (hT : 0 < T) (h : PaperSolutionEnl D h𝒢₀ hind₀ T (activeDealerCoeffs c hϱ ε) 0 X Y Z U γ) :
    ¬ ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      crowdOp
        (lawP2 P (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
        (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2 = 0 := by
  intro hA
  have hA' : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      ε • crowdOp
        (lawP2 P (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
        (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2 = 0 :=
    hA.mono fun _ hs => hs.mono fun _ hω => by rw [hω, smul_zero]
  have h0 : PaperSolutionEnl D h𝒢₀ hind₀ T (activeDealerCoeffs c hϱ 0) 0 X Y Z U γ :=
    (paperSolution_dealerExp_iff hA').mp h
  obtain ⟨X₀, hX₀⟩ := exists_linearFSDEJ_exposure_enlJoint D h𝒢₀ hind₀ hϱ hc hT
  obtain ⟨-, -, -, hU⟩ :=
    paperWeakSolutionInt_activeDealer_eq D h𝒢₀ hind₀ hϱ hc hT hX₀ (h0.toWeakInt hT.le)
  have hUs := ae_ae_uLift_eq_of_ae_eq hU
  have hIoc : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Ioc (0 : ℝ) T := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := T)).mem_iff]
      with s hs hsI
    exact Set.Ioo_subset_Ioc_self (hs.mpr hsI)
  haveI : (ae (volume.restrict (Set.Icc (0 : ℝ) T))).NeBot := by
    refine ae_neBot.mpr ?_
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc, ENNReal.ofReal_eq_zero, not_le]
    linarith
  obtain ⟨s, hs, hAs, hUs'⟩ := (hIoc.and (hA.and hUs)).exists
  refine not_ae_crowdOp_margU_eq_zero_of_ae_eq_exposureJump hϱ hc hX₀
    (crossWitnessEnl D h𝒢₀ hind₀) hT hs ?_ hAs
  filter_upwards [hUs'] with ω hω
  rw [hω]
  simp only [tupleAt]
  congr 1
  funext e k
  rw [Subsingleton.elim k 0]

/-- **Example 5.5: the interaction is active, as an extended integral.** Under the hypotheses of
`not_ae_ae_crowdOp_activeDealer_eq_zero`, for `ε ≠ 0`,
`𝔼 ∫_0^T ‖ε A_{μ⁻_s^U}(U_s)‖²_{L²(ν)} ds > 0`. -/
theorem lintegral_enorm_smul_crowdOp_activeDealer_pos (hϱ : ϱ < 2)
    (hc : ∀ b, c b = (2 - ϱ) / 2) (hT : 0 < T) (hε : ε ≠ 0)
    (h : PaperSolutionEnl D h𝒢₀ hind₀ T (activeDealerCoeffs c hϱ ε) 0 X Y Z U γ) :
    0 < ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
      ‖ε • crowdOp
        (lawP2 P (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
        (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2‖ₑ ^ 2) ∂P := by
  have hF : AEMeasurable (fun p : Ω × ℝ => ‖ε • crowdOp
        (lawP2 P (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U p.2)).margU.law
        (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U p.2 p.1).2.2.2‖ₑ ^ 2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    ((PaperSolution.aemeasurable_crowdOp_leftLim h hT.le).const_smul ε).enorm.pow_const 2
  rw [pos_iff_ne_zero, ← lintegral_prod _ hF, Ne, lintegral_eq_zero_iff' hF]
  intro h0
  refine not_ae_ae_crowdOp_activeDealer_eq_zero hϱ hc hT h ?_
  have h1 := (Measure.measurePreserving_swap (μ := volume.restrict (Set.Icc (0 : ℝ) T))
    (ν := P)).quasiMeasurePreserving.ae h0
  filter_upwards [Measure.ae_ae_of_ae_prod h1] with s hs
  filter_upwards [hs] with ω hω
  simpa [hε] using hω

/-- **Example 5.5: the interaction is active.** Under the hypotheses of
`not_ae_ae_crowdOp_activeDealer_eq_zero`, for `ε ≠ 0`,
`𝔼 ∫_0^T ‖ε A_{μ⁻_s^U}(U_s)‖²_{L²(ν)} ds > 0`, as a Bochner integral: the inner integral is over
`s ∈ [0, T]`, the outer one the expectation. -/
theorem integral_norm_smul_crowdOp_activeDealer_sq_pos (hϱ : ϱ < 2)
    (hc : ∀ b, c b = (2 - ϱ) / 2) (hT : 0 < T) (hε : ε ≠ 0)
    (h : PaperSolutionEnl D h𝒢₀ hind₀ T (activeDealerCoeffs c hϱ ε) 0 X Y Z U γ) :
    0 < ∫ ω, (∫ s in Set.Icc (0 : ℝ) T,
      ‖ε • crowdOp
        (lawP2 P (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
        (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2‖ ^ 2) ∂P := by
  have hAm := PaperSolution.aemeasurable_crowdOp_leftLim h hT.le
  have hF : AEMeasurable (fun p : Ω × ℝ => ‖ε • crowdOp
        (lawP2 P (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U p.2)).margU.law
        (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U p.2 p.1).2.2.2‖ₑ ^ 2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := (hAm.const_smul ε).enorm.pow_const 2
  have hf : AEStronglyMeasurable (fun p : Ω × ℝ => ‖ε • crowdOp
        (lawP2 P (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U p.2)).margU.law
        (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U p.2 p.1).2.2.2‖ ^ 2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    ((hAm.const_smul ε).norm.pow_const 2).aestronglyMeasurable
  have hK : ∫⁻ _ in Set.Icc (0 : ℝ) T, ‖ε‖ₑ ^ 2 < ⊤ :=
    setLIntegral_Icc_lt_top_of_le (ENNReal.pow_ne_top enorm_ne_top) (fun _ => le_rfl) T
  have hL : ∀ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      ‖ε • crowdOp
        (lawP2 P (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
        (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2‖ₑ ^ 2
      ≤ ∫⁻ _ in Set.Icc (0 : ℝ) T, ‖ε‖ₑ ^ 2 := fun ω => lintegral_mono fun s => by
    gcongr
    refine enorm_smul_le.trans (mul_le_of_le_one_right' ?_)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.mpr (norm_crowdOp_le_one _ _)
  have hinner : ∀ᵐ ω ∂P, ∫ s in Set.Icc (0 : ℝ) T,
      ‖ε • crowdOp
        (lawP2 P (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
        (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2‖ ^ 2
      = (∫⁻ s in Set.Icc (0 : ℝ) T,
        ‖ε • crowdOp
          (lawP2 P (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
          (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2‖ₑ
            ^ 2).toReal := by
    filter_upwards [hf.prodMk_left] with ω hω
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) hω]
    congr 1
    refine lintegral_congr fun s => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [integral_congr_ae hinner,
    integral_toReal hF.lintegral_prod_right' (ae_of_all _ fun ω => (hL ω).trans_lt hK)]
  refine ENNReal.toReal_pos (lintegral_enorm_smul_crowdOp_activeDealer_pos hϱ hc hT hε h).ne' ?_
  refine ((lintegral_mono hL).trans_lt ?_).ne
  rw [lintegral_const, measure_univ, mul_one]
  exact hK

/-- **Example 5.5: the solution depends on the interaction strength.** With `c_{±1} = (2 − ϱ)/2`,
`ϱ < 2`, `T > 0` and `ε ≠ ε'`, no tuple `(X, Y, Z, U)` is a solution of (1.1) in the sense of
the paper over `enlJoint 𝒢₀ D h𝒢₀` with initial datum `0` both for `activeDealerCoeffs c hϱ ε`,
with a representative `γ` of the jump coefficient, and for `activeDealerCoeffs c hϱ ε'`, with a
representative `γ'`. -/
theorem not_paperSolutionEnl_activeDealer_of_ne (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2)
    (hT : 0 < T) {ε' : ℝ} (hne : ε ≠ ε') {γ' : Fin 1 → ℝ → Ω → DealerMark → ℝ}
    (h : PaperSolutionEnl D h𝒢₀ hind₀ T (activeDealerCoeffs c hϱ ε) 0 X Y Z U γ) :
    ¬ PaperSolutionEnl D h𝒢₀ hind₀ T (activeDealerCoeffs c hϱ ε') 0 X Y Z U γ' := by
  intro h'
  have hUs := ae_ae_uLift_eq_of_ae_eq (U := jumpProc T γ 0) (U' := jumpProc T γ' 0)
    (PaperSolution.jumpProc_ae_eq_of_b_eq_of_σ_eq dealerExpCoeffs_b_eq dealerExpCoeffs_σ_eq hT h
      h' 0)
  refine not_ae_ae_crowdOp_activeDealer_eq_zero hϱ hc hT h ?_
  filter_upwards [h.jump_rep, h'.jump_rep, hUs, ae_restrict_mem measurableSet_Icc]
    with s hs hs' hsU hsI
  filter_upwards [hs, hs', hsU] with ω hω hω' hωU
  have hj : ∀ g : Fin 1 → ℝ → Ω → DealerMark → ℝ,
      (fun e (i : Fin 1) => g i s ω e) = fun e _ => jumpProc T g 0 s ω e := by
    intro g
    funext e i
    rw [Subsingleton.elim i 0]
    simp only [jumpProc, Set.indicator_of_mem hsI]
  have e4 := (uLift_eq_of_ae_eq hω).symm.trans
    ((hj γ ▸ hj γ' ▸ hωU).trans (uLift_eq_of_ae_eq hω'))
  rw [dealerExpCoeffs_h_eq_sub, dealerExpCoeffs_h_eq_sub (ε := ε'), sub_right_inj] at e4
  have h5 : (ε - ε') • crowdOp
      (lawP2 P (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
      (tupleAt (dealerMarks c ϱ) (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2 = 0 := by
    rw [sub_smul, e4, sub_self]
  exact (smul_eq_zero.mp h5).resolve_left (sub_ne_zero.mpr hne)

end Interaction

end Dissertation.WellPosedness.Existence
