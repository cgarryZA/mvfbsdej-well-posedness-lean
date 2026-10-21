/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Enlarged.TimeZero
import Dissertation.WellPosedness.Enlarged.CrossWitness

/-!
# Uniqueness of the representing pair

Let `ℱ` be a filtration carrying a Lévy driver `D = (W, N)` whose Itô integrals against the
Brownian coordinates are orthogonal in `L²` to its compensated integrals, and let `T > 0`. If

`c + ∑ i ∫₀ᵀ Gⁱ dWⁱ + ∫₀ᵀ ∫ K dÑ = c' + ∑ i ∫₀ᵀ G'ⁱ dWⁱ + ∫₀ᵀ ∫ K' dÑ`

almost surely, with `c` and `c'` measurable for `ℱ₀`, then `c = c'` almost surely and the
representing pairs agree:

`𝔼 ∫₀ᵀ |Gⁱ − G'ⁱ|² ds = 0` for every coordinate `i`,   `𝔼 ∫₀ᵀ ‖K − K'‖²_{L²(ν)} ds = 0`.

A joint integral over `[0, T]` conditions to zero given the right-continuous version of `ℱ` at
time `0`. The difference `c − c'` is measurable there and almost surely equal to a difference of
two joint integrals, so it is its own conditional expectation, which vanishes. The two joint
integrals then agree almost surely, so the differences of the coordinate Itô integrals and of the
compensated integrals sum to zero. These differences lie in the ranges of the `d` coordinate
integrals and of the compensated integral, which are pairwise orthogonal in `L²`; the square of
the `L²` norm of the sum is the sum of the squares of their norms, so each difference vanishes,
and by the isometry of differences its square norm is the energy of the difference of the
integrands.

The enlarged filtration `enlJoint 𝒢₀ D h𝒢₀`, for a σ-algebra `𝒢₀` independent of the joint
natural filtration, carries such an orthogonality.

## Main statements

* `add_jointIntegral_unique` — uniqueness of the representing pair over a filtration with a cross
  witness.
* `add_jointIntegral_unique_enlJoint` — uniqueness over the enlarged filtration.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace Dissertation.WellPosedness.Enlarged

open LevyStochCalc LevyStochCalc.Driver LevyStochCalc.Driver.LevyDriver
open LevyStochCalc.Brownian.Ito LevyStochCalc.Poisson.Compensated

universe u v w

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {d : ℕ}

section General

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : MeasureTheory.Filtration ℝ mΩ} {T : ℝ}
  (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
  (hℱN : Poisson.IsPoissonFiltration D.N ℱ)

/-- **Uniqueness of the representing pair.** Let `ℱ` carry the driver with a cross witness and
let `T > 0`. If `c + ∑ i ∫₀ᵀ Gⁱ dWⁱ + ∫₀ᵀ ∫ K dÑ = c' + ∑ i ∫₀ᵀ G'ⁱ dWⁱ + ∫₀ᵀ ∫ K' dÑ` almost
surely, with `c` and `c'` measurable for `ℱ₀`, then `c = c'` almost surely,
`𝔼 ∫₀ᵀ |Gⁱ − G'ⁱ|² ds = 0` for every coordinate `i` and `𝔼 ∫₀ᵀ ‖K − K'‖²_{L²(ν)} ds = 0`. -/
theorem add_jointIntegral_unique (𝒲 : D.CrossWitness ℱ) (hT : 0 < T) {c c' : Ω → ℝ}
    (hc : AEStronglyMeasurable[ℱ 0] c P) (hc' : AEStronglyMeasurable[ℱ 0] c' P)
    {G G' : ∀ _ : Fin d, HorizonIntegrand P ℱ T} {K K' : MarkedHorizonIntegrand P ν ℱ T}
    (h : (fun ω => c ω + jointIntegral hcoord hℱN G K ω)
      =ᵐ[P] fun ω => c' ω + jointIntegral hcoord hℱN G' K' ω) :
    c =ᵐ[P] c'
      ∧ (∀ i, energy P T (fun ω s => (G i).toFun ω s - (G' i).toFun ω s) = 0)
      ∧ markedEnergy P ν T (fun ω s e => K.toFun ω s e - K'.toFun ω s e) = 0 := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hJ2 := memLp_jointIntegral hcoord hℱN G K
  have hJ'2 := memLp_jointIntegral hcoord hℱN G' K'
  -- the values at time `0`
  have hδ : (fun ω => c ω - c' ω)
      =ᵐ[P] jointIntegral hcoord hℱN G' K' - jointIntegral hcoord hℱN G K := by
    filter_upwards [h] with ω hω
    rw [Pi.sub_apply]
    linarith
  have hδint : Integrable (fun ω => c ω - c' ω) P :=
    ((hJ'2.sub hJ2).integrable (by norm_num)).congr hδ.symm
  have hδm : AEStronglyMeasurable[ℱ.rightCont 0] (fun ω => c ω - c' ω) P :=
    (hc.sub hc').mono (ℱ.le_rightCont 0)
  haveI : SigmaFinite (P.trim (ℱ.rightCont.le 0)) := by infer_instance
  have hcond : P[fun ω => c ω - c' ω | ℱ.rightCont 0] =ᵐ[P] 0 := by
    refine (condExp_congr_ae hδ).trans
      ((condExp_sub (hJ'2.integrable (by norm_num)) (hJ2.integrable (by norm_num)) _).trans ?_)
    filter_upwards [(condExp_jointIntegral_rightCont hcoord hℱN G' K' hT.le).trans
        (jointIntegralProcess_zero_ae hcoord hℱN G' K'),
      (condExp_jointIntegral_rightCont hcoord hℱN G K hT.le).trans
        (jointIntegralProcess_zero_ae hcoord hℱN G K)] with ω e1 e2
    rw [Pi.sub_apply, e1, e2, Pi.zero_apply, sub_zero]
  have hcc : c =ᵐ[P] c' := by
    filter_upwards [(condExp_of_aestronglyMeasurable' (ℱ.rightCont.le 0) hδm hδint).symm.trans
      hcond] with ω hω
    exact sub_eq_zero.mp hω
  -- the representing pairs
  have hJJ : ∀ᵐ ω ∂P, jointIntegral hcoord hℱN G K ω - jointIntegral hcoord hℱN G' K' ω = 0 := by
    filter_upwards [h, hcc] with ω e1 e2
    rw [e2] at e1
    linarith
  set V := jointRange hcoord hℱN hT
  have hGL := fun i => HorizonIntegrand.memLp (D.W.W i) (hcoord i) (G i)
  have hG'L := fun i => HorizonIntegrand.memLp (D.W.W i) (hcoord i) (G' i)
  have hKL := MarkedHorizonIntegrand.memLp D.N hℱN K
  have hK'L := MarkedHorizonIntegrand.memLp D.N hℱN K'
  have hmemB : ∀ i : Fin d, (hGL i).toLp _ - (hG'L i).toLp _ ∈ V (some i) := fun i =>
    Submodule.sub_mem _ ⟨G i, MemLp.coeFn_toLp _⟩ ⟨G' i, MemLp.coeFn_toLp _⟩
  have hmemN : hKL.toLp _ - hK'L.toLp _ ∈ V none :=
    Submodule.sub_mem _ ⟨K, MemLp.coeFn_toLp _⟩ ⟨K', MemLp.coeFn_toLp _⟩
  let l : ∀ o : Option (Fin d), V o := fun o => match o with
    | none => ⟨_, hmemN⟩
    | some i => ⟨_, hmemB i⟩
  have hsum : ∑ o, (V o).subtypeₗᵢ (l o) = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun o => (V o).subtypeₗᵢ (l o),
      Lp.coeFn_sub (hKL.toLp _) (hK'L.toLp _), hKL.coeFn_toLp, hK'L.coeFn_toLp,
      eventually_all.2 fun i => Lp.coeFn_sub ((hGL i).toLp _) ((hG'L i).toLp _),
      eventually_all.2 fun i => (hGL i).coeFn_toLp,
      eventually_all.2 fun i => (hG'L i).coeFn_toLp, hJJ] with ω e1 e2 e3 e4 e5 e6 e7 e8
    rw [e1, Fintype.sum_option, Pi.zero_apply, ← e8]
    change ((hKL.toLp _ - hK'L.toLp _ : Lp ℝ 2 P) : Ω → ℝ) ω
        + ∑ i, (((hGL i).toLp _ - (hG'L i).toLp _ : Lp ℝ 2 P) : Ω → ℝ) ω = _
    rw [e2, Pi.sub_apply, e3, e4]
    simp only [e5, Pi.sub_apply, e6, e7, jointIntegral,
      Brownian.Multidim.MultidimBrownianMotion.vectorIntegral, Finset.sum_sub_distrib]
    ring
  have hnorm := (orthogonalFamily_jointRange hcoord hℱN 𝒲 hT).norm_sum l Finset.univ
  rw [hsum, norm_zero, zero_pow two_ne_zero] at hnorm
  have hl : ∀ o, (l o : Lp ℝ 2 P) = 0 := by
    intro o
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun o _ => sq_nonneg ‖l o‖).mp hnorm.symm o
      (Finset.mem_univ o)
    rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h2
    rw [h2]
    rfl
  refine ⟨hcc, fun i => ?_, ?_⟩
  · have h0 : (hGL i).toLp _ = (hG'L i).toLp _ := sub_eq_zero.mp (hl (some i))
    rw [← HorizonIntegrand.lintegral_sq_integral_sub (D.W.W i) (hcoord i) hT (G i) (G' i)]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [(hGL i).coeFn_toLp, (hG'L i).coeFn_toLp] with ω e1 e2
    rw [← e1, ← e2, h0, sub_self, nnnorm_zero, ENNReal.coe_zero, zero_pow two_ne_zero]
  · have h0 : hKL.toLp _ = hK'L.toLp _ := sub_eq_zero.mp (hl none)
    rw [← MarkedHorizonIntegrand.lintegral_sq_integral_sub D.N hℱN hT K K']
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hKL.coeFn_toLp, hK'L.coeFn_toLp] with ω e1 e2
    rw [← e1, ← e2, h0, sub_self, nnnorm_zero, ENNReal.coe_zero, zero_pow two_ne_zero]

end General

/-- **Uniqueness of the representing pair over the enlarged filtration.** For a σ-algebra `𝒢₀`
independent of the joint natural filtration of the driver and `T > 0`, if
`c + ∑ i ∫₀ᵀ Gⁱ dWⁱ + ∫₀ᵀ ∫ K dÑ = c' + ∑ i ∫₀ᵀ G'ⁱ dWⁱ + ∫₀ᵀ ∫ K' dÑ` almost surely, with
integrands admissible for `enlJoint 𝒢₀ D h𝒢₀` and `c`, `c'` measurable for its time-`0` field,
then `c = c'` almost surely, `𝔼 ∫₀ᵀ |Gⁱ − G'ⁱ|² ds = 0` for every coordinate `i` and
`𝔼 ∫₀ᵀ ‖K − K'‖²_{L²(ν)} ds = 0`. -/
theorem add_jointIntegral_unique_enlJoint (D : LevyDriver.{u, v, w} P d ν) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P)
    {T : ℝ} (hT : 0 < T) {c c' : Ω → ℝ} (hc : AEStronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] c P)
    (hc' : AEStronglyMeasurable[enlJoint 𝒢₀ D h𝒢₀ 0] c' P)
    {G G' : ∀ _ : Fin d, HorizonIntegrand P (enlJoint 𝒢₀ D h𝒢₀) T}
    {K K' : MarkedHorizonIntegrand P ν (enlJoint 𝒢₀ D h𝒢₀) T}
    (h : (fun ω => c ω + jointIntegral (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
        (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) G K ω)
      =ᵐ[P] fun ω => c' ω + jointIntegral (isBrownianFiltration_enlJoint D h𝒢₀ hind₀)
        (isPoissonFiltration_enlJoint D h𝒢₀ hind₀) G' K' ω) :
    c =ᵐ[P] c'
      ∧ (∀ i, energy P T (fun ω s => (G i).toFun ω s - (G' i).toFun ω s) = 0)
      ∧ markedEnergy P ν T (fun ω s e => K.toFun ω s e - K'.toFun ω s e) = 0 :=
  add_jointIntegral_unique _ _ (crossWitnessEnl D h𝒢₀ hind₀) hT hc hc' h

end Dissertation.WellPosedness.Enlarged
