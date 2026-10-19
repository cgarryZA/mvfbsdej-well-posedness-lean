/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Examples.Dealer.LinearMoments
import Dissertation.WellPosedness.Stability.LinearCongr
import LevyStochCalc.Ito.JumpCoefficientPredictableZeroExt

/-!
# Example 5.5: the solution at zero interaction and the linear equation

In the specialisation `β₁ = 1`, `β₂ = 1/2`, `σ_c = 1`, `ε = 0` of the exposure-sensitive dealer
system, with `h_c, h_x` represented by `η_c, η_x`, `‖h_x‖ = 1` and `⟨h_x, h_c⟩ = 0`:

* for a solution `X⁰` of the linear equation with left limits on `(0, T]` along every path, the
  tuple `Θ⁰ = (X⁰, X⁰, ½, ½ (h_c + h_x X⁰_{t−}))` solves the system: along it `σ = ½`, `h = U⁰`
  and `f = ½ X⁰ + ½ X⁰_{−}`, which is `X⁰` at almost every time;
* conversely the forward component of every solution solves the linear equation, its backward
  component being `X`, `Z = ½` and `U = ½ (h_c + h_x X)` (`Solves.dealer_zero_residual`).

## Main definitions

* `dealerZeroZ`, `dealerZeroU` — the integrands of `Θ⁰`.

## Main statements

* `markedPredictable_dealerZeroU` — `U⁰` is marked predictable.
* `uLift_half_add` — the class of `½ (η_c + η_x a)` is `½ (h_c + a h_x)`.
* `DealerLinear.solves`, `DealerLinear.paperSolution` — `Θ⁰` solves the system.
* `Solves.dealerLinear` — the forward component of a solution solves the linear equation.
-/

open MeasureTheory Filter Topology Dissertation.Law
open scoped RealInnerProductSpace ENNReal NNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Stability
  Dissertation.WellPosedness.BrownianPoisson LevyStochCalc

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {ν : Measure E}

/-! ### The integrands of `Θ⁰` -/

/-- The diffusion integrand `Z⁰ = ½` of the solution at zero interaction, on `[0, T]`. -/
noncomputable def dealerZeroZ (T : ℝ) : Fin 1 → ℝ → Ω → Fin 1 → ℝ :=
  fun _ s _ _ => (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) s

/-- The jump integrand `U⁰_s(e) = ½ (η_c(e) + η_x(e) X_{s−})` of the solution at zero
interaction, on `(0, T]`. -/
noncomputable def dealerZeroU (T : ℝ) (ηc ηx : E → ℝ) (X : ℝ → Ω → ℝ) :
    Fin 1 → ℝ → Ω → E → ℝ :=
  fun _ s ω e => (Set.Ioc (0 : ℝ) T).indicator
    (fun s => 1 / 2 * (ηc e + ηx e * leftLimProc (fun _ : Fin 1 => X) 0 s ω)) s

omit [MeasurableSpace Ω] in
/-- A deterministic measurable process is progressively measurable. -/
theorem progressivelyMeasurable_of_measurable_time {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
    {g : ℝ → ℝ} (hg : Measurable g) :
    Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) s => g s := fun _ =>
  (hg.stronglyMeasurable.comp_measurable measurable_snd).indicator
    (measurableSet_preimage measurable_snd measurableSet_Iic)

/-- **The jump integrand of `Θ⁰` is marked predictable** when `X` is adapted with left limits on
`(0, T]` along every path and `η_c, η_x` are measurable. -/
theorem markedPredictable_dealerZeroU [SigmaFinite ν] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {T : ℝ} {ηc ηx : E → ℝ} (hηc : Measurable ηc) (hηx : Measurable ηx) {X : ℝ → Ω → ℝ}
    (hXa : MeasureTheory.Adapted ℱ X)
    (hXl : ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 l)) :
    Probability.MarkedPredictable ℱ ν fun ω s e => dealerZeroU T ηc ηx X 0 s ω e := by
  set Xp : ℝ → Ω → Fin 1 → ℝ := fun t ω _ => X (min t T) ω with hXp
  have hXpa : ∀ t : ℝ, Measurable[ℱ t] (Xp t) := fun t =>
    (@measurable_pi_iff Ω (Fin 1) (fun _ => ℝ) (ℱ t) inferInstance (Xp t)).mpr fun _ =>
      (hXa (min t T)).mono (ℱ.mono (min_le_left t T)) le_rfl
  -- the frozen path has the left limits of `X` on `(0, T]`, and is constant after `T`
  have hXpl : ∀ ω t, t ∈ Set.Ioc (0 : ℝ) T → ∀ l, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 l) →
      Tendsto (fun s => Xp s ω) (𝓝[<] t) (𝓝 fun _ => l) := by
    intro ω t ht l hl
    refine tendsto_pi_nhds.mpr fun _ => hl.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : s < t)
    simp only [hXp, min_eq_left (hs.le.trans ht.2)]
  have hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ j : Fin 1,
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L) := by
    intro ω t ht j
    rcases le_or_gt t T with htT | htT
    · obtain ⟨l, hl⟩ := hXl ω t ⟨ht, htT⟩
      exact ⟨l, (tendsto_pi_nhds.mp (hXpl ω t ⟨ht, htT⟩ l hl)) j⟩
    · refine ⟨X T ω, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [Ioo_mem_nhdsLT htT] with s hs
      simp only [hXp, min_eq_right hs.1.le]
  set F : ℝ → (Fin 1 → ℝ) → E → ℝ := fun s x e =>
    (Set.Ioc (0 : ℝ) T).indicator (fun _ => 1 / 2 * (ηc e + ηx e * x 0)) s with hF
  have hFm : Measurable fun q : ℝ × (Fin 1 → ℝ) × E => F q.1 q.2.1 q.2.2 := by
    have e : (fun q : ℝ × (Fin 1 → ℝ) × E => F q.1 q.2.1 q.2.2)
        = (Prod.fst ⁻¹' Set.Ioc (0 : ℝ) T).indicator
          fun q : ℝ × (Fin 1 → ℝ) × E => 1 / 2 * (ηc q.2.2 + ηx q.2.2 * q.2.1 0) := by
      funext q
      simp only [hF, Set.indicator, Set.mem_preimage]
    rw [e]
    refine Measurable.indicator ?_ (measurable_fst measurableSet_Ioc)
    exact measurable_const.mul ((hηc.comp (measurable_snd.comp measurable_snd)).add
      ((hηx.comp (measurable_snd.comp measurable_snd)).mul
        ((measurable_pi_apply 0).comp (measurable_fst.comp measurable_snd))))
  have h := Ito.JumpSplitting.markedPredictable_zeroExtPos_comp_leftLimPathAt (ν := ν) Xp ℱ hXpa
    hleft hFm
  convert h using 1
  funext ω s e
  rcases le_or_gt s 0 with hs | hs
  · rw [Ito.JumpFormula.zeroExtPos_of_nonpos _ ω hs e]
    exact Set.indicator_of_notMem (fun h => absurd h.1 (not_lt.mpr hs)) _
  rw [Ito.JumpFormula.zeroExtPos_of_pos _ ω hs e]
  simp only [dealerZeroU, hF]
  by_cases hsT : s ∈ Set.Ioc (0 : ℝ) T
  · rw [Set.indicator_of_mem hsT, Set.indicator_of_mem hsT]
    obtain ⟨l, hl⟩ := hXl ω s hsT
    rw [Ito.JumpSplitting.leftLimPathAt, leftLim_eq_of_tendsto (hXpl ω s hsT l hl), leftLimProc,
      leftLim_eq_of_tendsto hl]
  · rw [Set.indicator_of_notMem hsT, Set.indicator_of_notMem hsT]

/-- **The class of the curve `½ (η_c + η_x a)`** is `½ (h_c + a h_x)` when `η_c, η_x ∈ L²(ν)`
represent `h_c, h_x`. -/
theorem uLift_half_add {ηc ηx : E → ℝ} (hcm : MemLp ηc 2 ν) (hxm : MemLp ηx 2 ν)
    {hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν}
    (hcr : ∀ᵐ e ∂ν, hc e = EuclideanSpace.single 0 (ηc e))
    (hxr : ∀ᵐ e ∂ν, hx e = EuclideanSpace.single 0 (ηx e)) (a : ℝ) :
    uLift ν (fun e (_ : Fin 1) => 1 / 2 * (ηc e + ηx e * a)) = (1 / 2 : ℝ) • (hc + a • hx) := by
  have hm := memLp_toLp_of_forall (u := fun e (_ : Fin 1) => 1 / 2 * (ηc e + ηx e * a))
    fun _ => (hcm.add (hxm.mul_const a)).const_mul (1 / 2)
  refine Lp.ext ?_
  rw [uLift_of_memLp hm]
  filter_upwards [hm.coeFn_toLp, Lp.coeFn_smul (1 / 2 : ℝ) (hc + a • hx), Lp.coeFn_add hc (a • hx),
    Lp.coeFn_smul a hx, hcr, hxr] with e h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.smul_apply, h3, Pi.add_apply, h4, Pi.smul_apply, h5, h6]
  refine PiLp.ext fun k => ?_
  obtain rfl : k = 0 := Subsingleton.elim _ _
  simp [PiLp.single_apply]
  ring

omit [MeasurableSpace Ω] in
/-- A curve with square-integrable coordinates represents its class. -/
theorem coeFn_uLift {ι : Type*} [Fintype ι] {u : E → ι → ℝ} (hu : ∀ k, MemLp (fun e => u e k) 2 ν) :
    (fun e => (WithLp.toLp 2 (u e) : EuclideanSpace ℝ ι)) =ᵐ[ν] uLift ν u := by
  have hm := memLp_toLp_of_forall hu
  rw [uLift_of_memLp hm]
  exact hm.coeFn_toLp.symm

/-- A progressive process cut to `[0, T]` is progressive. -/
theorem progressivelyMeasurable_indicator_Icc {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {H : Ω → ℝ → ℝ} (hH : Probability.ProgressivelyMeasurable ℱ H) (T : ℝ) :
    Probability.ProgressivelyMeasurable ℱ
      fun ω s => (Set.Icc (0 : ℝ) T).indicator (fun s => H ω s) s := by
  have e : (fun ω s => (Set.Icc (0 : ℝ) T).indicator (fun s => H ω s) s)
      = fun ω s => H ω s * (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 : ℝ)) s := by
    funext ω s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, mul_one]
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, mul_zero]
  rw [e]
  exact hH.mul (progressivelyMeasurable_of_measurable_time
    (measurable_const.indicator measurableSet_Icc))

/-- A jointly measurable process cut to `[0, T]` is jointly measurable. -/
theorem measurable_indicator_Icc {H : Ω → ℝ → ℝ} (hH : Measurable (Function.uncurry H))
    (T : ℝ) :
    Measurable (Function.uncurry fun ω s => (Set.Icc (0 : ℝ) T).indicator (fun s => H ω s) s) := by
  have e : (Function.uncurry fun ω s => (Set.Icc (0 : ℝ) T).indicator (fun s => H ω s) s)
      = (Prod.snd ⁻¹' Set.Icc (0 : ℝ) T).indicator (Function.uncurry H) := by
    funext p
    simp only [Function.uncurry, Set.indicator, Set.mem_preimage]
  rw [e]
  exact hH.indicator (measurable_snd measurableSet_Icc)

/-! ### `Θ⁰` solves the system -/

section Solves

variable [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ} {σc : EuclideanSpace ℝ (Fin 1 × Fin 1)}
  {hc hx : Lp (EuclideanSpace ℝ (Fin 1)) 2 ν} {ηc ηx : E → ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P 1 ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {X : ℝ → Ω → ℝ}

/-- **`Θ⁰` solves the system.** For `T > 0`, `σ_c(0, 0) = 1`, `‖h_x‖ = 1`, `⟨h_x, h_c⟩ = 0` and
`η_c, η_x ∈ L²(ν)` representing `h_c, h_x`, if `X` solves the linear equation then
`Θ⁰ = (X, X, Z⁰, U⁰)` solves the dealer system `dealerExpCoeffs 1 (1/2) σ_c h_c h_x 0` from `0`,
with `U⁰` as representative of its jump coefficient. -/
theorem DealerLinear.solves (h : DealerLinear D ℱ hℱW hℱN T ηc ηx X) (hT : 0 < T)
    (hσ : σc (0, 0) = 1) (hhx : ‖hx‖ = 1) (hxc : ⟪hx, hc⟫ = 0) (hcm : MemLp ηc 2 ν)
    (hxm : MemLp ηx 2 ν) (hcr : ∀ᵐ e ∂ν, hc e = EuclideanSpace.single 0 (ηc e))
    (hxr : ∀ᵐ e ∂ν, hx e = EuclideanSpace.single 0 (ηx e)) :
    Solves D ℱ hℱW hℱN T (dealerExpCoeffs 1 (1 / 2) σc hc hx 0) 0 (fun _ => X) (fun _ => X)
      (dealerZeroZ T) (dealerZeroU T ηc ηx X) (dealerZeroU T ηc ηx X) := by
  set C := dealerExpCoeffs (ν := ν) 1 (1 / 2) σc hc hx 0 with hC
  set Z := dealerZeroZ (Ω := Ω) T with hZ
  set U := dealerZeroU T ηc ηx X with hU
  -- the class of the jump channel
  have hUs : ∀ s ∈ Set.Ioc (0 : ℝ) T, ∀ ω, uLift ν (fun e k => U k s ω e)
      = (1 / 2 : ℝ) • (hc + leftLimProc (fun _ : Fin 1 => X) 0 s ω • hx) := by
    intro s hs ω
    simp only [hU, dealerZeroU, Set.indicator_of_mem hs]
    exact uLift_half_add hcm hxm hcr hxr _
  have hUm : ∀ s ∈ Set.Ioc (0 : ℝ) T, ∀ ω k, MemLp (fun e => U k s ω e) 2 ν := by
    intro s hs ω k
    simp only [hU, dealerZeroU, Set.indicator_of_mem hs]
    exact (hcm.add (hxm.mul_const _)).const_mul _
  -- the forward equation
  have hb : driftProc P T C (fun _ => X) (fun _ => X) Z U 0
      = fun ω s => (Set.Icc (0 : ℝ) T).indicator (fun s => -X s ω) s := by
    funext ω s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · rw [hC, driftProc_dealerExp hs, Set.indicator_of_mem hs]
      ring
    · rw [driftProc_of_notMem hs, Set.indicator_of_notMem hs]
  have hσ' : diffusionProc P T C (fun _ => X) (fun _ => X) Z U 0
      = fun s _ _ => (Set.Icc (0 : ℝ) T).indicator (fun _ => (1 / 2 : ℝ)) s := by
    funext s ω j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · rw [hC, diffusionProc_dealerExp hs, Set.indicator_of_mem hs, hσ]
      simp only [hZ, dealerZeroZ, Set.indicator_of_mem hs]
      norm_num
    · rw [diffusionProc_of_notMem hs, Set.indicator_of_notMem hs]
      rfl
  have hγ : jumpProc T U 0 = fun s ω e => (Set.Ioc (0 : ℝ) T).indicator
      (fun s => 1 / 2 * (ηc e + ηx e * leftLimProc (fun _ : Fin 1 => X) 0 s ω)) s := by
    funext s ω e
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · simp only [jumpProc, Set.indicator_of_mem hs, hU, dealerZeroU]
    · simp only [jumpProc, Set.indicator_of_notMem hs]
      exact (Set.indicator_of_notMem (fun h' => hs (Set.Ioc_subset_Icc_self h')) _).symm
  have hfwd : LinearFSDEJ D ℱ hℱW hℱN T ((0 : Fin 1 → Ω → ℝ) 0)
      (driftProc P T C (fun _ => X) (fun _ => X) Z U 0) X
      (diffusionProc P T C (fun _ => X) (fun _ => X) Z U 0) (jumpProc T U 0) :=
    LinearFSDEJ.of_eq h rfl hb.symm rfl hσ'.symm hγ.symm
  -- the backward equation
  have hbX : LinearBSDEJ D ℱ hℱW hℱN T (X T)
      (fun ω s => -(Set.Icc (0 : ℝ) T).indicator (fun s => -X s ω) s) X (Z 0) (U 0) :=
    h.linearBSDEJ hT.le
  have hΘ : ProgTuple ℱ P ν T (fun _ : Fin 1 => X) (fun _ : Fin 1 => X) Z U :=
    ProgTuple.of_legs (fun _ => hfwd) (fun _ => hbX)
  obtain ⟨γ', hCE⟩ := (coeffBorelW2_dealerExp (β₁ := 1) (β₂ := 1 / 2) (σc := σc) (hc := hc)
    (hx := hx) (ε := 0) T).toCoeffBorel.coeffRegular ℱ P _ _ _ _ hΘ
  have hl := h.ae_ae_leftLimProc_eq hT.le
  have hI : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Ioo (0 : ℝ) T := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := T)).mem_iff] with s hs hsI
    exact hs.mpr hsI
  have hbwd : LinearBSDEJ D ℱ hℱW hℱN T (terminalVal P T C (fun _ => X) 0)
      (driverProc P T C (fun _ => X) (fun _ => X) Z U 0) X (Z 0) (U 0) := by
    refine hbX.congr (Eventually.of_forall fun ω => ?_) (hCE.f_meas 0) (hCE.f_prog 0)
      (fun ω s hs => driverProc_of_notMem hs 0 ω) ?_
    · rw [hC, terminalVal_dealerExp]
    · refine energy_eq_zero_of_ae_ae (hbX.φ_meas.sub (hCE.f_meas 0)) ?_
      filter_upwards [hI, hl] with s hs hls
      filter_upwards [hls] with ω hω
      have hIcc : s ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self hs
      rw [hC, driverProc_dealerExp hIcc, hUs s (Set.Ioo_subset_Ioc_self hs) ω, hω,
        Set.indicator_of_mem hIcc, inner_smul_right, inner_add_right, inner_smul_right, hxc,
        real_inner_self_eq_norm_sq, hhx]
      ring
  refine Solves.of_linear ?_ (fun i => ?_) (fun k => ?_)
  · filter_upwards [hI, hl] with s hs hls
    filter_upwards [hls] with ω hω
    have hIoc : s ∈ Set.Ioc (0 : ℝ) T := Set.Ioo_subset_Ioc_self hs
    have hh : C.h s (tupleAt ν (fun _ : Fin 1 => X) (fun _ : Fin 1 => X) Z U s ω)
        (lawP2 P (tupleAt ν (fun _ : Fin 1 => X) (fun _ : Fin 1 => X) Z U s))
        = uLift ν (fun e k => U k s ω e) := by
      rw [hC, dealerExpCoeffs_h]
      change hc - (1 : ℝ) • uLift ν (fun e k => U k s ω e)
        - (0 : ℝ) • crowdOp _ (uLift ν (fun e k => U k s ω e)) + X s ω • hx = _
      rw [hUs s hIoc ω, hω]
      module
    rw [hh]
    exact coeFn_uLift (u := fun e k => U k s ω e) (hUm s hIoc ω)
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    exact hfwd
  · obtain rfl : k = 0 := Subsingleton.elim _ _
    exact hbwd

/-- **`Θ⁰` is a solution in the sense of the paper.** In the setting of `DealerLinear.solves`,
over a filtration whose null sets lie in its time-`0` field, whose right-continuation is constant
before `0` and which admits a cross witness, for measurable `η_c, η_x` and `X` with left limits on
`(0, T]` along every path, `Θ⁰` is a solution of the dealer system in the sense of the paper. -/
theorem DealerLinear.paperSolution (h : DealerLinear D ℱ hℱW hℱN T ηc ηx X)
    (𝒲 : D.CrossWitness ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (hT : 0 < T)
    (hσ : σc (0, 0) = 1) (hhx : ‖hx‖ = 1) (hxc : ⟪hx, hc⟫ = 0) (hηc : Measurable ηc)
    (hηx : Measurable ηx) (hcm : MemLp ηc 2 ν) (hxm : MemLp ηx 2 ν)
    (hcr : ∀ᵐ e ∂ν, hc e = EuclideanSpace.single 0 (ηc e))
    (hxr : ∀ᵐ e ∂ν, hx e = EuclideanSpace.single 0 (ηx e))
    (hXl : ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 l)) :
    PaperSolution D ℱ hℱW hℱN T (dealerExpCoeffs 1 (1 / 2) σc hc hx 0) 0 (fun _ => X)
      (fun _ => X) (dealerZeroZ T) (dealerZeroU T ηc ηx X) (dealerZeroU T ηc ηx X) :=
  (h.solves hT hσ hhx hxc hcm hxm hcr hxr).paperSolution
    (fun _ _ => predictable_of_measurable_time (measurable_const.indicator measurableSet_Icc))
    (fun _ => markedPredictable_dealerZeroU hηc hηx h.X_adapted hXl) 𝒲 hℱ0 hnull hT

/-- **The forward component of a solution at zero interaction solves the linear equation.** For a
solution of the dealer system `dealerExpCoeffs 1 (1/2) σ_c h_c h_x 0` from `0` over a filtration
with a cross witness, `T > 0`, `σ_c(0, 0) = 1`, `‖h_x‖ = 1`, `⟨h_x, h_c⟩ = 0`, measurable
`η_c, η_x ∈ L²(ν)` representing `h_c, h_x`, and `X` with left limits on `(0, T]` along every path,
`X` solves the linear equation. -/
theorem Solves.dealerLinear {Xs : Fin 1 → ℝ → Ω → ℝ} {Y : Fin 1 → ℝ → Ω → ℝ}
    {Zs : Fin 1 → ℝ → Ω → Fin 1 → ℝ} {Us : Fin 1 → ℝ → Ω → E → ℝ} {γ : Fin 1 → ℝ → Ω → E → ℝ}
    (h : Solves D ℱ hℱW hℱN T (dealerExpCoeffs 1 (1 / 2) σc hc hx 0) 0 Xs Y Zs Us γ)
    (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) (hσ : σc (0, 0) = 1) (hhx : ‖hx‖ = 1)
    (hxc : ⟪hx, hc⟫ = 0) (hηc : Measurable ηc) (hηx : Measurable ηx) (hcm : MemLp ηc 2 ν)
    (hxm : MemLp ηx 2 ν) (hcr : ∀ᵐ e ∂ν, hc e = EuclideanSpace.single 0 (ηc e))
    (hxr : ∀ᵐ e ∂ν, hx e = EuclideanSpace.single 0 (ηx e))
    (hXl : ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) T, ∃ l : ℝ,
      Tendsto (fun s => Xs 0 s ω) (𝓝[<] t) (𝓝 l)) :
    DealerLinear D ℱ hℱW hℱN T ηc ηx (Xs 0) := by
  have hX := System.Solves.linearFSDEJ h 0
  obtain ⟨hYX, hZ, hU⟩ := Solves.dealer_zero_residual h 𝒲 hT hσ hhx hxc
  have hl := hX.ae_ae_leftLimProc_eq hT.le
  have hI : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Ioo (0 : ℝ) T := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := T)).mem_iff] with s hs hsI
    exact hs.mpr hsI
  have hUp := markedPredictable_dealerZeroU (ν := ν) (T := T) hηc hηx hX.X_adapted hXl
  have hXm := hX.measurable_uncurry_swap
  have hXm' := measurable_indicator_Icc (H := fun ω s => -Xs 0 s ω) hXm.neg T
  refine hX.congr hXm'
    (progressivelyMeasurable_indicator_Icc (continuous_neg.comp_progressivelyMeasurable neg_zero
      (Probability.progressivelyMeasurable_of_rightContinuous hX.X_adapted hX.X_rightCont)) T)
    (fun ω s hs => Set.indicator_of_notMem hs _)
    (fun _ => (measurable_const.indicator measurableSet_Icc).comp measurable_snd)
    (fun _ => progressivelyMeasurable_of_measurable_time
      (measurable_const.indicator measurableSet_Icc))
    (fun ω s hs => funext fun _ => Set.indicator_of_notMem hs _)
    (hUp.mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl)
    hUp.markedProgressivelyMeasurable
    (fun ω s e hs => Set.indicator_of_notMem (fun h' => hs (Set.Ioc_subset_Icc_self h')) _)
    ?_ (fun j => ?_) ?_
  · refine energy_eq_zero_of_ae_ae (hX.b_meas.sub hXm') ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    filter_upwards [hYX s hs] with ω hω
    rw [driftProc_dealerExp hs, Set.indicator_of_mem hs, hω]
    ring
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    refine energy_eq_zero_of_ae_ae ((hX.σ_meas 0).sub
      ((measurable_const.indicator measurableSet_Icc).comp measurable_snd)) ?_
    filter_upwards [hZ, ae_restrict_mem measurableSet_Icc] with s hs hsI
    filter_upwards [hs] with ω hω
    rw [diffusionProc_dealerExp hsI, Set.indicator_of_mem hsI, hσ, hω]
    norm_num
  · refine markedEnergy_eq_zero_of_ae_ae (hX.γ_meas.sub
      (hUp.mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl)) ?_
    filter_upwards [hI, hl, hU, h.jump_rep] with s hs hls hUs hrep
    filter_upwards [hls, hUs, hrep] with ω hω hωU hωr
    have hIcc : s ∈ Set.Icc (0 : ℝ) T := Set.Ioo_subset_Icc_self hs
    have hIoc : s ∈ Set.Ioc (0 : ℝ) T := Set.Ioo_subset_Ioc_self hs
    have hh : (dealerExpCoeffs 1 (1 / 2) σc hc hx 0).h s (tupleAt ν Xs Y Zs Us s ω)
        (lawP2 P (tupleAt ν Xs Y Zs Us s))
        = uLift ν (fun e (_ : Fin 1) => 1 / 2 * (ηc e + ηx e * Xs 0 s ω)) := by
      rw [dealerExpCoeffs_h, uLift_half_add hcm hxm hcr hxr]
      change hc - (1 : ℝ) • uLift ν (fun e k => Us k s ω e)
        - (0 : ℝ) • crowdOp _ (uLift ν (fun e k => Us k s ω e)) + Xs 0 s ω • hx = _
      rw [hωU]
      module
    rw [hh] at hωr
    have hrep' := coeFn_uLift (ν := ν) (u := fun e (_ : Fin 1) => 1 / 2 * (ηc e + ηx e * Xs 0 s ω))
      fun _ => (hcm.add (hxm.mul_const _)).const_mul _
    filter_upwards [hωr, hrep'] with e he1 he2
    have he := congrArg (fun x : EuclideanSpace ℝ (Fin 1) => x 0) (he1.trans he2.symm)
    simp only [PiLp.toLp_apply] at he
    simp only [jumpProc, Set.indicator_of_mem hIcc, dealerZeroU, Set.indicator_of_mem hIoc]
    rw [he]
    change 1 / 2 * (ηc e + ηx e * Xs 0 s ω)
      - 1 / 2 * (ηc e + ηx e * leftLimProc (fun _ : Fin 1 => Xs 0) 0 s ω) = 0
    rw [hω]
    ring

end Solves

end Dissertation.WellPosedness.Existence
