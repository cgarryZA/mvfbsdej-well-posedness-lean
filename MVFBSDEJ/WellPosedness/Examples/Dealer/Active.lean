/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Examples.Dealer.ZeroSolution
import MVFBSDEJ.WellPosedness.Examples.Dealer.Symm

/-!
# Example 5.5: the interaction is active

In the specialisation of the dealer market at zero interaction, the jump channel
`U⁰_t = ½ (h_c + h_x X⁰_{t−})` of the solution has `𝔼‖U⁰_t − 𝔼 U⁰_t‖² = 𝔼 X⁰_t² / 4 > 0` at
every `t ∈ (0, T]`, so its law is not a Dirac mass, and by the symmetrised pairing the crowding
correction `A_{Law(U⁰_t)}(U⁰_t)` is nonzero with positive probability.

For a solution at interaction strength `ε > 0`, `𝔼 ∫_0^T ‖ε A_{Law(U_t)}(U_t)‖² dt > 0`: otherwise
the correction vanishes for `dt ⊗ dP`, the solution solves the system at `ε = 0`, its forward
component solves the linear equation and its jump channel is that of `Θ⁰` at almost every time,
where the correction is nonzero with positive probability.

## Main definitions

* `dealerU0` — the jump channel `½ (h_c + h_x X_{t−})` at a fixed time.

## Main statements

* `DealerLinear.dealerU0_moments` — the variance of `U⁰_t` and its law.
* `DealerLinear.crowd_ne_zero` — the crowding correction along `Θ⁰` is nonzero with positive
  probability.
* `lintegral_crowd_eq_zero_iff` — the energy of the crowding correction vanishes iff the
  correction vanishes at almost every time, almost surely.
* `PaperSolution.dealer_active` — in the specialisation, the interaction is active: for `ε ≠ 0`
  every solution from `0` has `𝔼 ∫_0^T ‖ε A_{Law(U_t)}(U_t)‖² dt > 0`.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law
open scoped RealInnerProductSpace ENNReal NNReal

namespace MVFBSDEJ.WellPosedness.Existence

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Stability
  MVFBSDEJ.WellPosedness.BrownianPoisson LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}

/-- The jump channel `½ (h_c + h_x X_{t−})` of the solution at zero interaction at time `t`. -/
noncomputable def dealerU0 (hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) (X : ℝ → Ω → ℝ) (t : ℝ) :
    Ω → Lp (EuclideanSpace ℝ (Fin 1)) 2 ν :=
  fun ω => (1 / 2 : ℝ) • (hc + leftLimProc (fun _ : Fin 1 => X) 0 t ω • hx)

/-! ### The jump channel at a fixed time -/

section Fixed

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ} {hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν} {ηc ηx : E → ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {X : ℝ → Ω → ℝ}

/-- **The jump channel of `Θ⁰` at a fixed time.** Over a filtration whose null sets lie in its
time-`0` field, whose right-continuation is constant before `0` and which admits a cross witness,
for `T > 0`, `η_c, η_x ∈ L²(ν)` with `∫ η_c² = ∫ η_x² = 1` and `∫ η_c η_x = 0`, `‖h_x‖ = 1` and a
solution `X` of the linear equation with left limits on `(0, T]` along every path: at every
`t ∈ (0, T]`, `U⁰_t = ½ (h_c + h_x X_{t−})` is integrable,
`𝔼‖U⁰_t − 𝔼 U⁰_t‖² = 𝔼 X_t² / 4`, and its law is not a Dirac mass. -/
theorem DealerLinear.dealerU0_moments (h : DealerLinear D ℱ hℱW hℱN T ηc ηx X)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hcm : MemLp ηc 2 ν) (hxm : MemLp ηx 2 ν) (hηc : ∫ e, ηc e ^ 2 ∂ν = 1)
    (hηx : ∫ e, ηx e ^ 2 ∂ν = 1) (hηcx : ∫ e, ηc e * ηx e ∂ν = 0) (hhx : ‖hx‖ = 1)
    (hXl : ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 l))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) T) :
    AEMeasurable (dealerU0 hc hx X t) P ∧ Integrable (dealerU0 hc hx X t) P
      ∧ ∫ ω, ‖dealerU0 hc hx X t ω - ∫ ω', dealerU0 hc hx X t ω' ∂P‖ ^ 2 ∂P
        = (∫ ω, X t ω ^ 2 ∂P) / 4
      ∧ ¬ ∃ u, P.map (dealerU0 hc hx X t) = Measure.dirac u := by
  obtain ⟨hL, hL1, hL2⟩ := h.leftLim_moments 𝒲 hℱ0 hnull hT hcm hxm hηc hηx hηcx hXl ht
  set L := leftLimProc (fun _ : Fin 1 => X) 0 t with hLdef
  have hv := h.integral_sq_eq 𝒲 hT hcm hxm hηc hηx hηcx t (Set.Ioc_subset_Icc_self ht)
  have hcont : Continuous fun a : ℝ =>
      ((1 / 2 : ℝ) • (hc + a • hx) : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) := by
    fun_prop
  have hUm : AEMeasurable (dealerU0 hc hx X t) P :=
    hcont.measurable.comp_aemeasurable hL.aestronglyMeasurable.aemeasurable
  have hLi : Integrable L P := hL.integrable one_le_two
  have hUi' : Integrable (fun ω => hc + L ω • hx) P := (integrable_const hc).add (hLi.smul_const hx)
  have hUi : Integrable (dealerU0 hc hx X t) P := hUi'.smul (1 / 2 : ℝ)
  have hmean : ∫ ω, dealerU0 hc hx X t ω ∂P = (1 / 2 : ℝ) • hc := by
    simp only [dealerU0]
    rw [integral_smul, integral_add (integrable_const hc) (hLi.smul_const hx), integral_const,
      probReal_univ, one_smul, integral_smul_const, hL1, zero_smul, add_zero]
  have hvar : ∫ ω, ‖dealerU0 hc hx X t ω - ∫ ω', dealerU0 hc hx X t ω' ∂P‖ ^ 2 ∂P
      = (∫ ω, X t ω ^ 2 ∂P) / 4 := by
    have e : ∀ ω, ‖dealerU0 hc hx X t ω - ∫ ω', dealerU0 hc hx X t ω' ∂P‖ ^ 2
        = 1 / 4 * L ω ^ 2 := fun ω => by
      rw [hmean]
      have : dealerU0 hc hx X t ω - (1 / 2 : ℝ) • hc = (1 / 2 * L ω) • hx := by
        simp only [dealerU0, ← hLdef]
        module
      rw [this, norm_smul, hhx, mul_one, Real.norm_eq_abs, sq_abs, mul_pow]
      ring
    simp_rw [e]
    rw [integral_const_mul, hL2, hv]
    ring
  refine ⟨hUm, hUi, hvar, ?_⟩
  rintro ⟨u, hu⟩
  have hae : ∀ᵐ ω ∂P, dealerU0 hc hx X t ω = u := by
    have h1 : ∀ᵐ y ∂(P.map (dealerU0 hc hx X t)), y = u := by
      rw [hu, ae_dirac_eq]
      exact Filter.eventually_pure.mpr rfl
    exact ae_of_ae_map hUm h1
  have h0 : ∫ ω, ‖dealerU0 hc hx X t ω - ∫ ω', dealerU0 hc hx X t ω' ∂P‖ ^ 2 ∂P = 0 := by
    have hc' : ∫ ω', dealerU0 hc hx X t ω' ∂P = u := by
      rw [integral_congr_ae hae, integral_const, probReal_univ, one_smul]
    rw [hc']
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [hae] with ω hω
    simp [hω]
  rw [hvar, hv] at h0
  have hpos : 0 < 1 - Real.exp (-(7 / 4) * t) := by
    have : Real.exp (-(7 / 4) * t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [ht.1])
    linarith
  nlinarith

/-- **The crowding correction along `Θ⁰` is nonzero with positive probability.** In the setting
of `DealerLinear.dealerU0_moments`, at every `t ∈ (0, T]`,
`P{A_{Law(U⁰_t)}(U⁰_t) ≠ 0} > 0`. -/
theorem DealerLinear.crowd_ne_zero (h : DealerLinear D ℱ hℱW hℱN T ηc ηx X)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hcm : MemLp ηc 2 ν) (hxm : MemLp ηx 2 ν) (hηc : ∫ e, ηc e ^ 2 ∂ν = 1)
    (hηx : ∫ e, ηx e ^ 2 ∂ν = 1) (hηcx : ∫ e, ηc e * ηx e ∂ν = 0) (hhx : ‖hx‖ = 1)
    (hXl : ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 l))
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) T) :
    0 < P {ω | crowdOp (P.map (dealerU0 hc hx X t)) (dealerU0 hc hx X t ω) ≠ 0} := by
  obtain ⟨hUm, hUi, -, hD⟩ :=
    h.dealerU0_moments 𝒲 hℱ0 hnull hT hcm hxm hηc hηx hηcx hhx hXl ht
  set U0 := dealerU0 hc hx X t with hU0
  set Λ := P.map U0 with hΛ
  haveI : IsProbabilityMeasure Λ := Measure.isProbabilityMeasure_map hUm
  have hΛi : Integrable (fun u => ‖u‖) Λ :=
    (integrable_map_measure continuous_norm.aestronglyMeasurable hUm).mpr hUi.norm
  have hpos := crowdPairing_pos Λ hΛi hD
  rw [hΛ, integral_map hUm (((continuous_crowdOp _).inner continuous_id).aestronglyMeasurable)]
    at hpos
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  have hae : ∀ᵐ ω ∂P, crowdOp (P.map U0) (U0 ω) = 0 := by
    have := measure_eq_zero_iff_ae_notMem.mp h0
    filter_upwards [this] with ω hω
    simpa using hω
  have : ∫ ω, ⟪crowdOp (P.map U0) (U0 ω), U0 ω⟫ ∂P = 0 := by
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [hae] with ω hω
    rw [hω, inner_zero_left]
  linarith

end Fixed

/-! ### The energy of the crowding correction -/

section Energy

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

omit [CompleteSpace F] in
/-- **The energy of the crowding correction vanishes iff the correction vanishes.** For a jointly
measurable `V : Ω → ℝ → F` and laws `λ_s` equal to `Law(V_s)` at almost every `s ∈ [0, T]`,
`∫_Ω ∫_0^T ‖ε A_{λ_s}(V_s)‖² ds dP = 0` iff `ε A_{λ_s}(V_s) = 0` almost surely at almost every
`s ∈ [0, T]`. -/
theorem lintegral_crowd_eq_zero_iff {V : Ω → ℝ → F} (hV : Measurable (Function.uncurry V))
    {Λ : ℝ → Measure F}
    (hΛ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Λ s = P.map fun ω => V ω s) (ε : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ‖ε • crowdOp (Λ s) (V ω s)‖ₑ ^ 2 ∂volume ∂P = 0
      ↔ ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
        ε • crowdOp (Λ s) (V ω s) = 0 := by
  have hVs : ∀ s, Measurable fun ω => V ω s := fun s =>
    hV.comp (measurable_id.prodMk measurable_const)
  -- the correction against the exact laws, through the sample space
  set G : Ω × ℝ → F := fun p => ε • ∫ ω', crowdGrad (V p.1 p.2 - V ω' p.2) ∂P with hG
  have hGm : StronglyMeasurable G := by
    have hk : StronglyMeasurable fun q : (Ω × ℝ) × Ω => crowdGrad (V q.1.1 q.1.2 - V q.2 q.1.2) :=
      (continuous_crowdGrad.measurable.comp ((hV.comp measurable_fst).sub
        (hV.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))).stronglyMeasurable
    exact hk.integral_prod_right'.const_smul ε
  have hGeq : ∀ ω s, G (ω, s) = ε • crowdOp (P.map fun ω => V ω s) (V ω s) := fun ω s => by
    simp only [hG, crowdOp_map (hVs s).aemeasurable]
  have hGm' : Measurable fun p : Ω × ℝ => ‖G p‖ₑ ^ 2 := hGm.measurable.enorm.pow_const 2
  have hcongr : ∀ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ‖ε • crowdOp (Λ s) (V ω s)‖ₑ ^ 2
      = ∫⁻ s in Set.Icc (0 : ℝ) T, ‖G (ω, s)‖ₑ ^ 2 := fun ω => by
    refine lintegral_congr_ae ?_
    filter_upwards [hΛ] with s hs
    rw [hGeq, hs]
  simp_rw [hcongr]
  rw [lintegral_lintegral_swap (f := fun ω s => ‖G (ω, s)‖ₑ ^ 2) hGm'.aemeasurable,
    lintegral_eq_zero_iff
      (Measurable.lintegral_prod_left (f := fun x y => ‖G (x, y)‖ₑ ^ 2) hGm')]
  constructor
  · intro h0
    filter_upwards [h0, hΛ] with s hs hΛs
    have hs' : ∫⁻ ω, ‖G (ω, s)‖ₑ ^ 2 ∂P = 0 := hs
    rw [lintegral_eq_zero_iff (f := fun ω => ‖G (ω, s)‖ₑ ^ 2)
      (hGm'.comp (measurable_id.prodMk measurable_const))] at hs'
    filter_upwards [hs'] with ω hω
    have : ‖G (ω, s)‖ₑ ^ 2 = 0 := hω
    rw [hΛs, ← hGeq]
    simpa using this
  · intro h0
    filter_upwards [h0, hΛ] with s hs hΛs
    change ∫⁻ ω, ‖G (ω, s)‖ₑ ^ 2 ∂P = 0
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hs] with ω hω
    rw [hGeq, ← hΛs, hω]
    simp

end Energy

/-! ### The predictable tuple of a solution in the sense of the paper -/

section Paper

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {n m d : ℕ} {T : ℝ} {C : Coeffs ν n m d}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {ξ₀ : Fin n → Ω → ℝ}
  {X : Fin n → ℝ → Ω → ℝ} {Y : Fin m → ℝ → Ω → ℝ} {Z : Fin m → ℝ → Ω → Fin d → ℝ}
  {U : Fin m → ℝ → Ω → E → ℝ} {γ : Fin n → ℝ → Ω → E → ℝ}

/-- The jump channel of a solution in the sense of the paper is jointly measurable as a process
with values in `L²(ν; ℝᵐ)`. -/
theorem PaperSolution.measurable_uncurry_uLift (h : PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ) :
    Measurable (Function.uncurry fun ω s => uLift ν (fun e k => U k s ω e)) := by
  refine System.measurable_uLift (u := fun (q : Ω × ℝ) e k => U k q.2 q.1 e) ?_
  refine measurable_pi_lambda _ fun k => ?_
  exact ((h.U_pred k).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl).comp
    MeasurableEquiv.prodAssoc.measurable

/-- **The predictable tuple of a solution with left limits along every path.** For a solution in
the sense of the paper over a filtration whose null sets lie in its time-`0` field, whose
right-continuation is constant before `0` and which admits a cross witness, with `T > 0` and
left limits on `(0, T]` along every path of `X` and `Y`: at almost every `s ∈ [0, T]` the
`U`-marginal of the law of the predictable tuple is the law of `U_s`. -/
theorem PaperSolution.ae_margU_law_eq_map (h : PaperSolution D ℱ hℱW hℱN T C ξ₀ X Y Z U γ)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hXl : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 l))
    (hYl : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l)) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
        = P.map fun ω => uLift ν (fun e k => U k s ω e) := by
  obtain ⟨X', Y', hXX, hYY, hS⟩ := h.exists_solves hT.le
  have hpred : ∀ s ∈ Set.Ioc (0 : ℝ) T, ∀ ω,
      tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω
        = tupleAt ν (leftLimProc X') (leftLimProc Y') Z U s ω := by
    intro s hs ω
    have hx : (fun i => leftLimProc X i s ω) = fun i => leftLimProc X' i s ω := funext fun i =>
      (leftLim_eq_of_eqOn (fun t ht => congrFun (hXX i t ht) ω) (hXl i ω) hs).symm
    have hy : (fun k => leftLimProc Y k s ω) = fun k => leftLimProc Y' k s ω := funext fun k =>
      (leftLim_eq_of_eqOn (fun t ht => congrFun (hYY k t ht) ω) (hYl k ω) hs).symm
    simp only [tupleAt, hx, hy]
  filter_upwards [SolvesForced.ae_ae_tupleAt_leftLimProc_eq hS hT.le,
    SolvesForced.ae_memLp_tupleAt hS 𝒲 hℱ0 hnull hT, ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with s hs hm hsI hs0
  have hsI' : s ∈ Set.Ioc (0 : ℝ) T := ⟨lt_of_le_of_ne hsI.1 (Ne.symm hs0), hsI.2⟩
  rw [show tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s
    = tupleAt ν (leftLimProc X') (leftLimProc Y') Z U s from funext (hpred s hsI'),
    lawP2_congr hs, margU_lawP2 hm, lawP2_law hm.snd.snd.snd]
  rfl

end Paper

/-! ### The interaction is active -/

section Active

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {T ε : ℝ} {σc : EuclideanSpace ℝ (Fin 1 × Fin 1)}
  {hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν} {ηc ηx : E → ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : Fin 1 → ℝ → Ω → ℝ} {Y : Fin 1 → ℝ → Ω → ℝ} {Z : Fin 1 → ℝ → Ω → Fin 1 → ℝ}
  {U : Fin 1 → ℝ → Ω → E → ℝ} {γ : Fin 1 → ℝ → Ω → E → ℝ}

/-- **Example 5.5: the interaction is active.** In the specialisation (`β₁ = 1`, `β₂ = 1/2`,
`σ_c(0, 0) = 1`, `‖h_x‖ = 1`, `⟨h_x, h_c⟩ = 0`, measurable `η_c, η_x ∈ L²(ν)` representing
`h_c, h_x` with `∫ η_c² = ∫ η_x² = 1` and `∫ η_c η_x = 0`), over a filtration whose null sets lie
in its time-`0` field, whose right-continuation is constant before `0` and which admits a cross
witness, for `T > 0` and `ε ≠ 0`: every solution from `0` in the sense of the paper with left
limits on `(0, T]` along every path has `𝔼 ∫_0^T ‖ε A_{Law(U_t)}(U_t)‖² dt > 0`, the law and
the curve taken at the predictable tuple. -/
theorem PaperSolution.dealer_active
    (hPS : PaperSolution D ℱ hℱW hℱN T (dealerExpCoeffs 1 (1 / 2) σc hc hx ε) 0 X Y Z U γ)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hσ : σc (0, 0) = 1) (hhx : ‖hx‖ = 1) (hxc : ⟪hx, hc⟫ = 0) (hηcm : Measurable ηc)
    (hηxm : Measurable ηx) (hcm : MemLp ηc 2 ν) (hxm : MemLp ηx 2 ν)
    (hcr : ∀ᵐ e ∂ν, hc e = EuclideanSpace.single 0 (ηc e))
    (hxr : ∀ᵐ e ∂ν, hx e = EuclideanSpace.single 0 (ηx e)) (hηc : ∫ e, ηc e ^ 2 ∂ν = 1)
    (hηx : ∫ e, ηx e ^ 2 ∂ν = 1) (hηcx : ∫ e, ηc e * ηx e ∂ν = 0) (hε : ε ≠ 0)
    (hXl : ∀ i ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X i s ω) (𝓝[<] t) (𝓝 l))
    (hYl : ∀ k ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => Y k s ω) (𝓝[<] t) (𝓝 l)) :
    0 < ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      ‖ε • crowdOp (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
        (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2‖ₑ ^ 2 ∂volume ∂P := by
  set Λ : ℝ → Measure (Lp (EuclideanSpace ℝ (Fin 1)) 2 ν) := fun s =>
    (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law with hΛdef
  have hΛ := PaperSolution.ae_margU_law_eq_map hPS 𝒲 hℱ0 hnull hT hXl hYl
  have hiff := lintegral_crowd_eq_zero_iff (P := P) (T := T)
    (PaperSolution.measurable_uncurry_uLift hPS) hΛ ε
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  have hzero := hiff.mp h0
  -- the correction vanishes, so the solution solves the system at `ε = 0`
  have hPS0 : PaperSolution D ℱ hℱW hℱN T (dealerExpCoeffs 1 (1 / 2) σc hc hx 0) 0 X Y Z U γ := by
    refine PaperSolution.congr_h (C := dealerExpCoeffs 1 (1 / 2) σc hc hx ε) rfl rfl rfl rfl hPS ?_
    filter_upwards [hzero] with s hs
    filter_upwards [hs] with ω hω
    rw [dealerExpCoeffs_h, dealerExpCoeffs_h, zero_smul, sub_zero]
    have hω' : ε • crowdOp (lawP2 P (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s)).margU.law
        (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U s ω).2.2.2 = 0 := hω
    rw [hω', sub_zero]
  obtain ⟨X', Y', hXX, -, hS⟩ := hPS0.exists_solves hT.le
  have hX'l : ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
      Tendsto (fun s => X' 0 s ω) (𝓝[<] t) (𝓝 l) := by
    intro ω t ht
    obtain ⟨l, hl⟩ := hXl 0 ω t ht
    refine ⟨l, hl.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT ht.1] with r hr
    exact (congrFun (hXX 0 r ⟨hr.1.le, hr.2.le.trans ht.2⟩) ω).symm
  have hlin := Solves.dealerLinear hS 𝒲 hT hσ hhx hxc hηcm hηxm hcm hxm hcr hxr hX'l
  obtain ⟨-, -, hU0⟩ := Solves.dealer_zero_residual hS 𝒲 hT hσ hhx hxc
  have hl := hlin.ae_ae_leftLimProc_eq hT.le
  -- along almost every time the jump channel is that of `Θ⁰`
  have hV : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (fun ω => uLift ν (fun e k => U k s ω e)) =ᵐ[P] dealerU0 hc hx (X' 0) s := by
    filter_upwards [hU0, hl] with s hs hls
    filter_upwards [hs, hls] with ω h1 h2
    rw [h1, dealerU0, h2]
  have hbad : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      P {ω | crowdOp (P.map (dealerU0 hc hx (X' 0) s)) (dealerU0 hc hx (X' 0) s ω) ≠ 0} = 0 := by
    filter_upwards [hzero, hΛ, hV] with s hs hΛs hVs
    refine measure_eq_zero_iff_ae_notMem.mpr ?_
    filter_upwards [hs, hVs] with ω hω hωV
    have hω' : ε • crowdOp (Λ s) (uLift ν (fun e k => U k s ω e)) = 0 := hω
    have hΛs' : Λ s = P.map fun ω => uLift ν (fun e k => U k s ω e) := hΛs
    rw [hΛs', Measure.map_congr hVs, hωV] at hω'
    simpa [hε] using hω'
  haveI : (ae (volume.restrict (Set.Icc (0 : ℝ) T))).NeBot := by
    refine ae_neBot.mpr fun h' => ?_
    have := congrArg (fun μ : Measure ℝ => μ Set.univ) h'
    simp only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc,
      Measure.coe_zero, Pi.zero_apply, sub_zero] at this
    exact (ENNReal.ofReal_pos.mpr hT).ne' this
  obtain ⟨s, hs, hsI, hs0⟩ := (hbad.and ((ae_restrict_mem measurableSet_Icc).and
    (ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))))).exists
  have hsI' : s ∈ Set.Ioc (0 : ℝ) T := ⟨lt_of_le_of_ne hsI.1 (Ne.symm hs0), hsI.2⟩
  have hpos := hlin.crowd_ne_zero (hc := hc) 𝒲 hℱ0 hnull hT hcm hxm hηc hηx hηcx hhx hX'l hsI'
  exact hpos.ne' hs

end Active

end MVFBSDEJ.WellPosedness.Existence
