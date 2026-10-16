/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.CrowdActivity
import Dissertation.WellPosedness.Examples.Dealer.ExposureExplicit
import Dissertation.WellPosedness.Examples.Dealer.ExposureMoments

/-!
# Example 5.5: the crowding correction is active along the explicit solution at `ε = 0`

Let `X⁰` solve the exposure equation of Example 5.5 of the well-posedness paper on the dealer
mark space with `c_{±1} = (2 − ϱ)/2`, `ϱ < 2`, over a filtration carrying the driver which
admits a cross witness, and let `U⁰_t = ½ (h_c + h_x X⁰_t) ∈ L²(ν; ℝ¹)` be the jump channel of the
explicit solution at `ε = 0`. With `w = ½ h_x e₀`,

`U⁰_t = ½ h_c + X⁰_t w`,   `⟨h_x, U⁰_t⟩_{L²(ν)} = ½ X⁰_t e₀`,

so `U⁰_t` is square integrable, and it is almost surely constant only if `X⁰_t` is. Since
`𝔼 X⁰_t = 0` and `𝔼 |X⁰_t|² = (2/7) (1 − e^{−7t/4}) > 0` for `t ∈ (0, T]`, `X⁰_t` is not almost
surely constant, so `Law(U⁰_t)` is not a Dirac mass, and by the symmetrisation of the crowding
pairing

`A_{Law(U⁰_t)}(U⁰_t) ≠ 0` with positive probability, for every `t ∈ (0, T]`.

The same holds for every random element of `L²(ν; ℝ¹)` almost surely equal to `U⁰_t`, and for the
`U`-marginal of the law of every tuple whose jump channel is almost surely `U⁰_t`: off `L²` that
law is the Dirac mass at the origin, where `A_{δ₀}(u) = ∇V(u)` vanishes only at `u = 0`, while
`‖U⁰_t‖² = ¼ (1 + |X⁰_t|²) > 0`.

## Main statements

* `uLift_exposureJump_eq_add_smul` — `U⁰_t = ½ h_c + X⁰_t w`.
* `memLp_uLift_exposureJump`, `uLift_exposureJump_ne_zero` — `U⁰_t` is square integrable and
  nowhere zero.
* `not_ae_crowdOp_eq_zero_of_ae_eq_exposureJump` — for `t ∈ (0, T]` and `U =ᵐ U⁰_t`,
  `A_{Law U}(U)` does not vanish almost surely.
* `not_ae_crowdOp_margU_eq_zero_of_ae_eq_exposureJump` — the same for the `U`-marginal of the law
  of every tuple with jump channel `U⁰_t`.
* `ae_ae_uLift_eq_of_ae_eq` — marked integrands equal almost everywhere on `Ω × [0, T] × E`
  have, at almost every time, almost surely equal classes in `L²(ν)`.
* `integral_norm_sub_integral_uLift_exposureJump_sq` —
  `𝔼 ‖U⁰_t − 𝔼 U⁰_t‖²_{L²(ν)} = (1/14) (1 − e^{−7t/4})`.
-/

open MeasureTheory Filter ProbabilityTheory Dissertation.Law
open scoped ENNReal

namespace Dissertation.WellPosedness.Existence

open Dissertation.WellPosedness.Stability Dissertation.WellPosedness.System LevyStochCalc

universe u w

variable {c : Bool → ℝ} {ϱ : ℝ}

/-- The vector `x e₀ ∈ ℝ¹` is `x` times `e₀ = (1)`. -/
theorem toLp_const_eq_smul (x : ℝ) :
    (WithLp.toLp 2 fun _ : Fin 1 => x : EuclideanSpace ℝ (Fin 1))
      = x • (WithLp.toLp 2 fun _ : Fin 1 => (1 : ℝ) : EuclideanSpace ℝ (Fin 1)) := by
  ext i
  simp

/-- **The jump channel is affine in the state**: on `[0, T]`,
`U⁰_t = ½ h_c + X_t w` with `w = ½ h_x e₀`. -/
theorem uLift_exposureJump_eq_add_smul {Ω : Type u} {T : ℝ} (hϱ : ϱ < 2) (X : ℝ → Ω → ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (ω : Ω) :
    uLift (dealerMarks c ϱ) (fun e (_ : Fin 1) => exposureJump T X t ω e)
      = (1 / 2 : ℝ) • dealerJump c hϱ + X t ω • ((1 / 2 : ℝ) • exposureOp (dealerSize c hϱ)
        (WithLp.toLp 2 fun _ : Fin 1 => (1 : ℝ))) := by
  rw [uLift_exposureJump hϱ X ht ω, toLp_const_eq_smul, map_smul, smul_add, smul_comm]

/-! ### From almost everywhere equality to equality of the jump channels -/

/-- **Almost everywhere equal marked integrands have almost surely equal classes at almost every
time**: if `U = U'` almost everywhere on `Ω × [0, T] × E` for `P ⊗ ds ⊗ ν`, then for almost every
`s ∈ [0, T]` the classes of `U_s(ω, ·)` and `U'_s(ω, ·)` in `L²(ν)` agree almost surely. -/
theorem ae_ae_uLift_eq_of_ae_eq {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
    {T : ℝ} {U U' : ℝ → Ω → E → ℝ}
    (h : ∀ᵐ q ∂(Poisson.Compensated.markedEnergyMeasure P ν T),
      U q.2.1 q.1 q.2.2 = U' q.2.1 q.1 q.2.2) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      uLift ν (fun e (_ : Fin 1) => U s ω e) = uLift ν (fun e (_ : Fin 1) => U' s ω e) := by
  have hmp : MeasurePreserving
      ((MeasurableEquiv.prodAssoc : (Ω × ℝ) × E ≃ᵐ Ω × ℝ × E) ∘ Prod.map Prod.swap id)
      (((volume.restrict (Set.Icc (0 : ℝ) T)).prod P).prod ν)
      (Poisson.Compensated.markedEnergyMeasure P ν T) :=
    (measurePreserving_prodAssoc P (volume.restrict (Set.Icc (0 : ℝ) T)) ν).comp
      (Measure.measurePreserving_swap.prod (MeasurePreserving.id ν))
  have h1 := hmp.quasiMeasurePreserving.ae h
  have h3 := Measure.ae_ae_of_ae_prod (Measure.ae_ae_of_ae_prod h1)
  filter_upwards [h3] with s hs
  filter_upwards [hs] with ω hω
  exact uLift_congr_ae (hω.mono fun e he => funext fun _ => he)

section Activity

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, 0, w} P 1 (dealerMarks c ϱ)}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ} {X : ℝ → Ω → ℝ}

/-- **The jump channel is square integrable** on `[0, T]`. -/
theorem memLp_uLift_exposureJump (hϱ : ϱ < 2)
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) (hT : 0 < T) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    MemLp (fun ω => uLift (dealerMarks c ϱ) (fun e (_ : Fin 1) => exposureJump T X t ω e)) 2 P := by
  have hmem := memLp_exposure hX hT ht
  have h := (memLp_const ((1 / 2 : ℝ) • dealerJump c hϱ)).add
    (hmem.continuousLinearMap_comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      ((1 / 2 : ℝ) • exposureOp (dealerSize c hϱ) (WithLp.toLp 2 fun _ : Fin 1 => (1 : ℝ)))))
  refine h.ae_eq (Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
  rw [uLift_exposureJump_eq_add_smul hϱ X ht ω]

/-- **The crowding correction does not vanish along the jump channel.** With `c_{±1} = (2 − ϱ)/2`,
`ϱ < 2`, let `X` solve the exposure equation over a filtration carrying the driver which admits
a cross witness, `T > 0` and `t ∈ (0, T]`. For every random element `U` of `L²(ν; ℝ¹)` almost
surely equal to the jump channel `U⁰_t = ½ (h_c + h_x X_t)`,
`A_{Law U}(U) = 0` does not hold almost surely. -/
theorem not_ae_crowdOp_eq_zero_of_ae_eq_exposureJump (hϱ : ϱ < 2) (hc : ∀ b, c b = (2 - ϱ) / 2)
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) T)
    {U : Ω → Lp (EuclideanSpace ℝ (Fin 1)) 2 (dealerMarks c ϱ)}
    (hU : U =ᵐ[P] fun ω => uLift (dealerMarks c ϱ) (fun e (_ : Fin 1) => exposureJump T X t ω e)) :
    ¬ ∀ᵐ ω ∂P, crowdOp (lawP2 P U).law (U ω) = 0 := by
  intro h
  have htI : t ∈ Set.Icc (0 : ℝ) T := Set.Ioc_subset_Icc_self ht
  have hUm : MemLp U 2 P := (memLp_uLift_exposureJump hϱ hX hT htI).ae_eq hU.symm
  obtain ⟨u, hu⟩ := exists_ae_eq_const_of_crowdOp_lawP2_eq_zero hUm h
  set κ : ℝ := 2 * exposurePair (dealerSize c hϱ) u 0 with hκ
  have hconst : X t =ᵐ[P] fun _ => κ := by
    filter_upwards [hU, hu] with ω h1 h2
    have h3 := congrArg (exposurePair (dealerSize c hϱ)) (h1.symm.trans h2)
    rw [uLift_exposureJump hϱ X htI ω, exposurePair_half_smul_dealerJump_add hϱ hc] at h3
    have h4 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h3
    simp only [PiLp.smul_apply, smul_eq_mul] at h4
    rw [hκ, ← h4]
    simp only [WithLp.toLp]
    ring
  have hm := integral_exposure_eq_zero hϱ hc hX 𝒲 hT htI
  rw [integral_congr_ae hconst] at hm
  simp only [integral_const, probReal_univ, one_smul] at hm
  have hv := integral_mul_self_exposure_pos hϱ hc hX 𝒲 hT ht
  rw [integral_congr_ae (hconst.mono fun ω hω => by
    simp only [hω] : (fun ω => X t ω * X t ω) =ᵐ[P] fun _ => κ * κ)] at hv
  simp only [integral_const, probReal_univ, one_smul, hm, mul_zero] at hv
  exact lt_irrefl 0 hv

/-- The jump channel does not vanish: on `[0, T]`, `‖U⁰_t‖²_{L²(ν)} = ¼ (1 + |X_t|²) > 0`. -/
theorem uLift_exposureJump_ne_zero {Ω : Type u} {T : ℝ} (hϱ : ϱ < 2)
    (hc : ∀ b, c b = (2 - ϱ) / 2) (X : ℝ → Ω → ℝ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (ω : Ω) :
    uLift (dealerMarks c ϱ) (fun e (_ : Fin 1) => exposureJump T X t ω e) ≠ 0 := by
  intro h0
  have hn := norm_half_smul_dealerJump_add_exposureOp_sq hϱ hc
    (WithLp.toLp 2 fun _ : Fin 1 => X t ω)
  rw [← uLift_exposureJump hϱ X ht ω, h0, norm_zero] at hn
  nlinarith [sq_nonneg ‖(WithLp.toLp 2 fun _ : Fin 1 => X t ω : EuclideanSpace ℝ (Fin 1))‖]

/-- **The crowding correction does not vanish along a tuple with the explicit jump channel.**
Under the hypotheses of `not_ae_crowdOp_eq_zero_of_ae_eq_exposureJump`, for every tuple `Θ` in
`H = ℝ × ℝ × ℝ^{1×1} × L²(ν; ℝ¹)` whose jump channel is almost surely `U⁰_t`,
`A_{μ^U}(U) = 0` does not hold almost surely, with `μ = lawP2 P Θ` the law of `Θ` (the Dirac mass
at the origin if `Θ` is not square integrable), `μ^U` its `U`-marginal and `U` the jump channel
of `Θ`. -/
theorem not_ae_crowdOp_margU_eq_zero_of_ae_eq_exposureJump (hϱ : ϱ < 2)
    (hc : ∀ b, c b = (2 - ϱ) / 2)
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) T) {Θ : Ω → TupleH (dealerMarks c ϱ) 1 1 1}
    (hU : (fun ω => (Θ ω).2.2.2)
      =ᵐ[P] fun ω => uLift (dealerMarks c ϱ) (fun e (_ : Fin 1) => exposureJump T X t ω e)) :
    ¬ ∀ᵐ ω ∂P, crowdOp (lawP2 P Θ).margU.law (Θ ω).2.2.2 = 0 := by
  by_cases hΘ : MemLp Θ 2 P
  · rw [margU_lawP2 hΘ]
    exact not_ae_crowdOp_eq_zero_of_ae_eq_exposureJump hϱ hc hX 𝒲 hT ht hU
  · rw [lawP2_of_not_memLp hΘ, margU_dirac]
    intro h
    obtain ⟨ω, h1, h2⟩ := (h.and hU).exists
    simp only [P2.dirac, crowdOp_dirac, Prod.snd_zero, sub_zero] at h1
    simp only at h2
    rw [h2] at h1
    have h3 := (inner_crowdGrad_self_eq_zero_iff (F := Lp (EuclideanSpace ℝ (Fin 1)) 2
      (dealerMarks c ϱ))).mp (by rw [h1, inner_zero_left])
    exact uLift_exposureJump_ne_zero hϱ hc X (Set.Ioc_subset_Icc_self ht) ω h3

/-- **The variance of the jump channel**: for `t ∈ [0, T]`,
`𝔼 ‖U⁰_t − 𝔼 U⁰_t‖²_{L²(ν)} = ¼ 𝔼 |X_t|² = (1/14) (1 − e^{−7t/4})`, the expectation of `U⁰_t`
being the Bochner integral in `L²(ν; ℝ¹)`. -/
theorem integral_norm_sub_integral_uLift_exposureJump_sq (hϱ : ϱ < 2)
    (hc : ∀ b, c b = (2 - ϱ) / 2)
    (hX : LinearFSDEJ D ℱ hℱW hℱN T (fun _ => 0) (exposureDrift T X) X
      (exposureDiffusion Ω T) (exposureJump T X)) (𝒲 : D.CrossWitness ℱ) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ ω, ‖uLift (dealerMarks c ϱ) (fun e (_ : Fin 1) => exposureJump T X t ω e)
        - ∫ ω', uLift (dealerMarks c ϱ) (fun e (_ : Fin 1) => exposureJump T X t ω' e) ∂P‖ ^ 2 ∂P
      = 1 / 14 * (1 - Real.exp (-(7 / 4) * t)) := by
  set w : Lp (EuclideanSpace ℝ (Fin 1)) 2 (dealerMarks c ϱ) :=
    (1 / 2 : ℝ) • exposureOp (dealerSize c hϱ) (WithLp.toLp 2 fun _ : Fin 1 => (1 : ℝ)) with hwdef
  have hform := uLift_exposureJump_eq_add_smul (c := c) (T := T) hϱ X ht
  have hmem := memLp_exposure hX hT ht
  have hmean : ∫ ω, uLift (dealerMarks c ϱ) (fun e (_ : Fin 1) => exposureJump T X t ω e) ∂P
      = (1 / 2 : ℝ) • dealerJump c hϱ := by
    simp_rw [hform]
    rw [integral_add (integrable_const _) ((hmem.integrable one_le_two).smul_const w),
      integral_smul_const (fun ω => X t ω) w, integral_exposure_eq_zero hϱ hc hX 𝒲 hT ht,
      zero_smul, add_zero]
    simp
  have hw : ‖w‖ ^ 2 = 1 / 4 := by
    rw [hwdef, norm_smul, mul_pow, norm_exposureOp_apply_sq, norm_dealerSize_eq_one hϱ hc,
      norm_sq_euclidean_fin_one]
    norm_num
  have hv := integral_mul_self_exposure_eq (P := P) hϱ hc hX 𝒲 hT ht
  simp_rw [hmean, hform, add_sub_cancel_left]
  rw [← hwdef]
  simp_rw [norm_smul, mul_pow, hw, Real.norm_eq_abs, sq_abs]
  rw [integral_mul_const]
  simp_rw [sq]
  rw [hv]
  ring

end Activity

end Dissertation.WellPosedness.Existence
