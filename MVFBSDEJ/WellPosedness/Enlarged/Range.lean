/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Enlarged.TimeZero

/-!
# The joint range over a filtration with a nontrivial time-zero field

Let `ℱ` be a filtration carrying a Lévy driver `D = (W, N)` with a cross witness. The `L²` ranges
of the coordinate Itô integrals and of the compensated integral over `[0, T]` form a closed
orthogonal family, so a square-integrable weight `Z` measurable before `T` splits as `Z = y + z`
with `y` a joint integral and `z` orthogonal to both ranges. Every joint integral is orthogonal
to every bounded `ℱ₀`-measurable weight, so when `Z` is, the remainder `z` is as well.

The separation hypothesis therefore concerns only the weights orthogonal to every bounded
`ℱ₀`-measurable weight, and not merely those of mean zero: over a filtration whose time-`0`
field is nontrivial, `1_A - P(A)` for a set `A ∈ ℱ₀` of probability strictly between `0` and
`1` has mean zero, is orthogonal to every joint integral, and does not vanish.

## Main statements

* `exists_jointIntegral_of_perp_zero` — if the only square-integrable weight measurable before
  `T` and orthogonal to every bounded `ℱ₀`-measurable weight and to both integral ranges is the
  zero weight, then every square-integrable weight measurable before `T` and orthogonal to every
  bounded `ℱ₀`-measurable weight is a joint integral.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MVFBSDEJ.WellPosedness.Enlarged

open LevyStochCalc LevyStochCalc.Driver LevyStochCalc.Driver.LevyDriver
open LevyStochCalc.Brownian.Ito LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

universe u v w

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyDriver.{u, v, w} P d ν} {ℱ : MeasureTheory.Filtration ℝ mΩ} {T : ℝ}
  (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
  (hℱN : Poisson.IsPoissonFiltration D.N ℱ)

/-- **The representation half of the joint predictable representation property, with a
time-zero field.** If the only square-integrable weight measurable before `T` and orthogonal to
every bounded `ℱ₀`-measurable weight, to every coordinate Itô integral and to every compensated
integral is the zero weight, then every square-integrable weight measurable before `T` and
orthogonal to every bounded `ℱ₀`-measurable weight is a joint integral. -/
theorem exists_jointIntegral_of_perp_zero (𝒲 : LevyDriver.CrossWitness D ℱ) (hT : 0 < T)
    (hsep : ∀ r : Ω → ℝ, MemLp r 2 P → AEStronglyMeasurable[ℱ T] r P →
      (∀ g : Ω → ℝ, StronglyMeasurable[ℱ 0] g → (∃ C, ∀ ω, |g ω| ≤ C) →
        ∫ ω, r ω * g ω ∂P = 0) →
      (∀ (i : Fin d) (G : HorizonIntegrand P ℱ T),
        ∫ ω, r ω * G.integral (D.W.W i) (hcoord i) ω ∂P = 0) →
      (∀ K : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, r ω * K.integral D.N hℱN ω ∂P = 0) →
      r =ᵐ[P] 0)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hZ0 : ∀ g : Ω → ℝ, StronglyMeasurable[ℱ 0] g → (∃ C, ∀ ω, |g ω| ≤ C) →
      ∫ ω, Z ω * g ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) (K : MarkedHorizonIntegrand P ν ℱ T),
      Z =ᵐ[P] jointIntegral hcoord hℱN G K := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set V : Option (Fin d) → Submodule ℝ (Lp ℝ 2 P) := jointRange hcoord hℱN hT with hVdef
  haveI hcl : IsClosed ((⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) :=
    isClosed_iSup_jointRange hcoord hℱN 𝒲 hT
  haveI : CompleteSpace (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) := hcl.completeSpace_coe
  haveI : ∀ i : Option (Fin d), CompleteSpace (V i) := by
    intro i
    match i with
    | some i => exact (isClosed_itoRange (D.W.W i) (hcoord i) hT).completeSpace_coe
    | none => exact (isClosed_compensatedRange D.N hℱN hT).completeSpace_coe
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)).exists_add_mem_mem_orthogonal (hZ2.toLp Z)
  have hproj : ∑ i, (V i).starProjection y = y :=
    (orthogonalFamily_jointRange hcoord hℱN 𝒲 hT).sum_projection_of_mem_iSup y hy
  have hcompB : ∀ i : Fin d, ∃ G : HorizonIntegrand P ℱ T,
      (((V (some i)).starProjection y : Lp ℝ 2 P) : Ω → ℝ)
        =ᵐ[P] G.integral (D.W.W i) (hcoord i) :=
    fun i => (V (some i)).starProjection_apply_mem y
  choose G hG using hcompB
  obtain ⟨K, hK⟩ : ∃ K : MarkedHorizonIntegrand P ν ℱ T,
      (((V none).starProjection y : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] K.integral D.N hℱN :=
    (V none).starProjection_apply_mem y
  have hyfun : (y : Ω → ℝ) =ᵐ[P] jointIntegral hcoord hℱN G K := by
    have hsumfun : ((∑ i, (V i).starProjection y : Lp ℝ 2 P) : Ω → ℝ)
        =ᵐ[P] fun ω => ∑ i : Option (Fin d),
          (((V i).starProjection y : Lp ℝ 2 P) : Ω → ℝ) ω :=
      MeasureTheory.Lp.coeFn_fun_finsetSum _ _
    rw [← hproj]
    filter_upwards [hsumfun, hK, Filter.eventually_all.2 (fun i : Fin d => hG i)]
      with ω e1 e2 e3
    rw [e1, Fintype.sum_option, e2, jointIntegral, vectorIntegral, add_comm]
    exact congrArg (fun x => x + K.integral D.N hℱN ω) (Finset.sum_congr rfl fun i _ => e3 i)
  have hsplit : Z =ᵐ[P] fun ω => jointIntegral hcoord hℱN G K ω + (z : Ω → ℝ) ω := by
    filter_upwards [hZ2.coeFn_toLp, Lp.coeFn_add y z, hyfun] with ω e1 e2 e3
    rw [← e1, hyz, e2, Pi.add_apply, e3]
  have hzmem : MemLp (z : Ω → ℝ) 2 P := Lp.memLp z
  have hzmeas : AEStronglyMeasurable[ℱ T] (z : Ω → ℝ) P := by
    have hd : (z : Ω → ℝ) =ᵐ[P] fun ω => Z ω - jointIntegral hcoord hℱN G K ω := by
      filter_upwards [hsplit] with ω e1
      rw [e1]; ring
    exact (hZm.sub (aestronglyMeasurable_jointIntegral hcoord hℱN G K)).congr hd.symm
  have hyint : Integrable (jointIntegral hcoord hℱN G K) P :=
    (memLp_jointIntegral hcoord hℱN G K).integrable (by norm_num)
  have hzperp0 : ∀ g : Ω → ℝ, StronglyMeasurable[ℱ 0] g → (∃ C, ∀ ω, |g ω| ≤ C) →
      ∫ ω, (z : Ω → ℝ) ω * g ω ∂P = 0 := by
    rintro g hgm ⟨C, hgC⟩
    have hgae : AEStronglyMeasurable g P := (hgm.mono (ℱ.le 0)).aestronglyMeasurable
    have hbd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ C :=
      Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgC ω
    have hZg : Integrable (fun ω => Z ω * g ω) P :=
      (hZ2.integrable (by norm_num)).mul_bdd hgae hbd
    have hJg : Integrable (fun ω => g ω * jointIntegral hcoord hℱN G K ω) P :=
      hyint.bdd_mul hgae hbd
    have hrw : (fun ω => (z : Ω → ℝ) ω * g ω)
        =ᵐ[P] fun ω => Z ω * g ω - g ω * jointIntegral hcoord hℱN G K ω := by
      filter_upwards [hsplit] with ω e1
      rw [e1]; ring
    rw [integral_congr_ae hrw, integral_sub hZg hJg, hZ0 g hgm ⟨C, hgC⟩,
      integral_mul_jointIntegral_eq_zero hcoord hℱN G K hgm hgC, sub_zero]
  have hzperpB : ∀ (i : Fin d) (L : HorizonIntegrand P ℱ T),
      ∫ ω, (z : Ω → ℝ) ω * L.integral (D.W.W i) (hcoord i) ω ∂P = 0 := by
    intro i L
    have hmem : (HorizonIntegrand.memLp (D.W.W i) (hcoord i) L).toLp
        (L.integral (D.W.W i) (hcoord i)) ∈ (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) :=
      Submodule.mem_iSup_of_mem (some i) ⟨L, MemLp.coeFn_toLp _⟩
    have hinner := (Submodule.mem_orthogonal _ z).mp hz _ hmem
    rw [MeasureTheory.L2.inner_def] at hinner
    rw [← hinner]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp
      (HorizonIntegrand.memLp (D.W.W i) (hcoord i) L)] with ω e1
    rw [RCLike.inner_apply, e1]
    simp
  have hzperpN : ∀ L : MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, (z : Ω → ℝ) ω * L.integral D.N hℱN ω ∂P = 0 := by
    intro L
    have hmem : (MarkedHorizonIntegrand.memLp D.N hℱN L).toLp (L.integral D.N hℱN)
        ∈ (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) :=
      Submodule.mem_iSup_of_mem none ⟨L, MemLp.coeFn_toLp _⟩
    have hinner := (Submodule.mem_orthogonal _ z).mp hz _ hmem
    rw [MeasureTheory.L2.inner_def] at hinner
    rw [← hinner]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (MarkedHorizonIntegrand.memLp D.N hℱN L)] with ω e1
    rw [RCLike.inner_apply, e1]
    simp
  have hzzero := hsep (z : Ω → ℝ) hzmem hzmeas hzperp0 hzperpB hzperpN
  refine ⟨G, K, ?_⟩
  filter_upwards [hsplit, hzzero] with ω e1 e2
  rw [e1, e2]
  simp

end MVFBSDEJ.WellPosedness.Enlarged
