/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Integral.Prod
import Dissertation.Law.CrowdGrad
import Dissertation.Law.LawP2

/-!
# The crowding operator vanishes only at Dirac masses

On a real inner product space the crowding gradient `∇V(w) = w / √(1 + ‖w‖²)` satisfies

`⟨∇V(w), w⟩ = ‖w‖² / √(1 + ‖w‖²)`,

which is nonnegative, at most `‖w‖`, and zero only at `w = 0`.

Let `U` be an integrable random element of a separable Hilbert space `F` on a probability space
`(Ω, P)`, with law `λ = Law U`, and `A_λ(u) = ∫ ∇V(u − v) λ(dv)` the crowding operator. On
`(Ω × Ω, P ⊗ P)` the second coordinate carries an independent copy of `U`, and
`A_λ(U(ω)) = ∫ ∇V(U(ω) − U(ω')) P(dω')`, so `𝔼⟨A_λ(U), U⟩` is the integral over `P ⊗ P` of
`k(ω, ω') = ⟨∇V(U(ω) − U(ω')), U(ω)⟩`. The swap `(ω, ω') ↦ (ω', ω)` preserves `P ⊗ P`, and `∇V`
is odd, so with `a = U(ω) − U(ω')`, `k(ω, ω') + k(ω', ω) = ⟨∇V(a), a⟩`, and

`𝔼⟨A_λ(U), U⟩ = ½ ∬ ‖U(ω) − U(ω')‖² / √(1 + ‖U(ω) − U(ω')‖²) P(dω) P(dω')`.

The integrand on the right is nonnegative and vanishes only on the diagonal `U(ω) = U(ω')`. If
the left-hand side vanishes, in particular if `A_λ(U) = 0` almost surely, then `U(ω) = U(ω')` for
`P ⊗ P`-almost every `(ω, ω')`, so `U` is almost surely constant and `λ` is a Dirac mass;
conversely at a Dirac mass `δ_c`, `A_{δ_c}(c) = ∇V(0) = 0`. For a law `λ ∈ P₂(F)`, the identity
random element on `(F, λ)` gives

`∫ ⟨A_λ(u), u⟩ λ(du) = ½ ∬ ‖u − v‖² / √(1 + ‖u − v‖²) λ(du) λ(dv)`,

which is positive unless `λ` is a Dirac mass.

## Main statements

* `inner_crowdGrad_self`, `inner_crowdGrad_self_nonneg`, `inner_crowdGrad_self_le_norm`,
  `inner_crowdGrad_self_eq_zero_iff` — `⟨∇V(w), w⟩ = ‖w‖² / √(1 + ‖w‖²)`, which lies in
  `[0, ‖w‖]` and vanishes only at the origin.
* `integral_inner_crowdOp_self`, `integral_inner_crowdOp_self_nonneg` — `𝔼⟨A_{Law U}(U), U⟩` as
  half the symmetrised double integral; in particular it is nonnegative.
* `integral_inner_crowdOp_self_eq_zero_iff` — it vanishes exactly when `U` is almost surely
  constant.
* `ae_crowdOp_eq_zero_iff` — `A_{Law U}(U) = 0` almost surely exactly when `U` is almost surely
  constant.
* `ae_eq_const_iff_map_eq_dirac` — `U` is almost surely constant exactly when `Law U` is a Dirac
  mass.
* `exists_ae_eq_const_of_crowdOp_lawP2_eq_zero` — the same for a square-integrable `U` and its
  law of finite second moment.
* `integral_inner_crowdOp_law`, `integral_inner_crowdOp_law_eq_zero_iff`,
  `integral_inner_crowdOp_law_pos` — for `λ ∈ P₂(F)`, `∫ ⟨A_λ(u), u⟩ λ(du)` is half the
  symmetrised double integral, and is positive unless `λ` is a Dirac mass.
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace Dissertation.Law

/-! ### The crowding gradient against its argument -/

section Gradient

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The crowding gradient against its argument**: `⟨∇V(w), w⟩ = ‖w‖² / √(1 + ‖w‖²)`. -/
theorem inner_crowdGrad_self (w : F) :
    ⟪crowdGrad w, w⟫ = ‖w‖ ^ 2 / Real.sqrt (1 + ‖w‖ ^ 2) := by
  rw [crowdGrad, real_inner_smul_left, real_inner_self_eq_norm_sq, div_eq_inv_mul]

/-- The crowding gradient against its argument is nonnegative: `⟨∇V(w), w⟩ ≥ 0`. -/
theorem inner_crowdGrad_self_nonneg (w : F) : 0 ≤ ⟪crowdGrad w, w⟫ := by
  rw [inner_crowdGrad_self]
  positivity

/-- The crowding gradient against its argument is at most the norm: `⟨∇V(w), w⟩ ≤ ‖w‖`. -/
theorem inner_crowdGrad_self_le_norm (w : F) : ⟪crowdGrad w, w⟫ ≤ ‖w‖ :=
  (real_inner_le_norm _ _).trans (by nlinarith [norm_crowdGrad_le_one w, norm_nonneg w])

/-- The crowding gradient against its argument vanishes only at the origin:
`⟨∇V(w), w⟩ = 0 ↔ w = 0`. -/
theorem inner_crowdGrad_self_eq_zero_iff {w : F} : ⟪crowdGrad w, w⟫ = 0 ↔ w = 0 := by
  rw [inner_crowdGrad_self, div_eq_zero_iff,
    or_iff_left (Real.sqrt_pos.mpr (by positivity)).ne', pow_eq_zero_iff two_ne_zero,
    norm_eq_zero]

end Gradient

/-! ### The symmetrisation -/

section RandomElement

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → F}

omit [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
/-- For integrable `U`, `(ω, ω') ↦ ⟨∇V(U(ω) − U(ω')), U(ω) − U(ω')⟩` is integrable against
`P ⊗ P`. -/
theorem integrable_inner_crowdGrad_sub_prod (hU : Integrable U P) :
    Integrable (fun z : Ω × Ω => ⟪crowdGrad (U z.1 - U z.2), U z.1 - U z.2⟫) (P.prod P) := by
  have h12 : Integrable (fun z : Ω × Ω => U z.1 - U z.2) (P.prod P) :=
    (hU.comp_fst P).sub (hU.comp_snd P)
  refine Integrable.mono' h12.norm
    ((continuous_crowdGrad.comp_aestronglyMeasurable h12.1).inner h12.1)
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (inner_crowdGrad_self_nonneg _)]
  exact inner_crowdGrad_self_le_norm _

/-- **The crowding pairing of a random element with itself, symmetrised.** For an integrable
random element `U` of `F`,
`𝔼⟨A_{Law U}(U), U⟩ = ½ ∬ ‖U(ω) − U(ω')‖² / √(1 + ‖U(ω) − U(ω')‖²) P(dω) P(dω')`. -/
theorem integral_inner_crowdOp_self (hU : Integrable U P) :
    ∫ ω, ⟪crowdOp (P.map U) (U ω), U ω⟫ ∂P
      = 1 / 2 * ∫ z : Ω × Ω, ‖U z.1 - U z.2‖ ^ 2 / Real.sqrt (1 + ‖U z.1 - U z.2‖ ^ 2)
          ∂(P.prod P) := by
  set k : Ω × Ω → ℝ := fun z => ⟪crowdGrad (U z.1 - U z.2), U z.1⟫ with hk
  have h1 : AEStronglyMeasurable (fun z : Ω × Ω => U z.1) (P.prod P) := hU.1.comp_fst
  have h2 : AEStronglyMeasurable (fun z : Ω × Ω => U z.2) (P.prod P) := hU.1.comp_snd
  have hki : Integrable k (P.prod P) := by
    refine Integrable.mono' (hU.norm.comp_fst P)
      ((continuous_crowdGrad.comp_aestronglyMeasurable (h1.sub h2)).inner h1)
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (by nlinarith [norm_crowdGrad_le_one (U z.1 - U z.2), norm_nonneg (U z.1)])
  have hsec : ∀ ω, ⟪crowdOp (P.map U) (U ω), U ω⟫ = ∫ ω', k (ω, ω') ∂P := fun ω => by
    have hi : Integrable (fun ω' => crowdGrad (U ω - U ω')) P :=
      Integrable.of_bound
        (continuous_crowdGrad.comp_aestronglyMeasurable (aestronglyMeasurable_const.sub hU.1)) 1
        (Eventually.of_forall fun _ => norm_crowdGrad_le_one _)
    rw [crowdOp, integral_map hU.aemeasurable
        (stronglyMeasurable_crowdGrad_sub _).aestronglyMeasurable,
      real_inner_comm, ← integral_inner hi]
    exact integral_congr_ae (Eventually.of_forall fun ω' => real_inner_comm _ _)
  have hprod : ∫ ω, ⟪crowdOp (P.map U) (U ω), U ω⟫ ∂P = ∫ z, k z ∂(P.prod P) := by
    simp_rw [hsec]
    exact (integral_prod k hki).symm
  have hsum : ∀ z : Ω × Ω,
      ‖U z.1 - U z.2‖ ^ 2 / Real.sqrt (1 + ‖U z.1 - U z.2‖ ^ 2) = k z + k z.swap := by
    rintro ⟨ω, ω'⟩
    simp only [hk, Prod.swap_prod_mk]
    rw [← neg_sub (U ω) (U ω'), crowdGrad_neg, inner_neg_left, ← sub_eq_add_neg,
      ← inner_sub_right, inner_crowdGrad_self]
  have hswap : ∫ z, k z.swap ∂(P.prod P) = ∫ z, k z ∂(P.prod P) := integral_prod_swap k
  have hdouble : ∫ z : Ω × Ω, ‖U z.1 - U z.2‖ ^ 2 / Real.sqrt (1 + ‖U z.1 - U z.2‖ ^ 2)
      ∂(P.prod P) = ∫ z, k z ∂(P.prod P) + ∫ z, k z.swap ∂(P.prod P) := by
    have hki' : Integrable (fun z => k z.swap) (P.prod P) := hki.swap
    rw [← integral_add hki hki']
    exact integral_congr_ae (Eventually.of_forall hsum)
  rw [hprod, hdouble, hswap]
  ring

/-- **The crowding pairing of a random element with itself is nonnegative**:
`𝔼⟨A_{Law U}(U), U⟩ ≥ 0` for integrable `U`. -/
theorem integral_inner_crowdOp_self_nonneg (hU : Integrable U P) :
    0 ≤ ∫ ω, ⟪crowdOp (P.map U) (U ω), U ω⟫ ∂P := by
  rw [integral_inner_crowdOp_self hU]
  exact mul_nonneg (by norm_num) (integral_nonneg fun z => by positivity)

/-- **A vanishing crowding pairing forces an almost surely constant random element**: for
integrable `U`, if `𝔼⟨A_{Law U}(U), U⟩ = 0` then `U = c` almost surely for some `c ∈ F`. -/
theorem exists_ae_eq_const_of_integral_inner_crowdOp_self_eq_zero (hU : Integrable U P)
    (h : ∫ ω, ⟪crowdOp (P.map U) (U ω), U ω⟫ ∂P = 0) : ∃ c : F, U =ᵐ[P] fun _ => c := by
  rw [integral_inner_crowdOp_self hU] at h
  have h0 : ∫ z : Ω × Ω, ⟪crowdGrad (U z.1 - U z.2), U z.1 - U z.2⟫ ∂(P.prod P) = 0 := by
    simp_rw [inner_crowdGrad_self]
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => inner_crowdGrad_self_nonneg _)
    (integrable_inner_crowdGrad_sub_prod hU)).mp h0
  have hdiag : ∀ᵐ z ∂(P.prod P), U z.1 = U z.2 :=
    hae.mono fun z hz => sub_eq_zero.mp (inner_crowdGrad_self_eq_zero_iff.mp hz)
  obtain ⟨ω₀, hω₀⟩ := (Measure.ae_ae_of_ae_prod hdiag).exists
  exact ⟨U ω₀, hω₀.mono fun _ hω => hω.symm⟩

/-- At an almost surely constant random element the crowding correction vanishes almost surely:
if `U = c` almost surely then `Law U = δ_c` and `A_{Law U}(U) = ∇V(0) = 0` almost surely. -/
theorem ae_crowdOp_eq_zero_of_ae_eq_const {c : F} (hc : U =ᵐ[P] fun _ => c) :
    ∀ᵐ ω ∂P, crowdOp (P.map U) (U ω) = 0 := by
  have hmap : P.map U = Measure.dirac c := by
    rw [Measure.map_congr hc, Measure.map_const, measure_univ, one_smul]
  filter_upwards [hc] with ω hω
  rw [hmap, crowdOp_dirac, hω, sub_self, crowdGrad_zero]

/-- **The crowding pairing of a random element with itself vanishes exactly at almost surely
constant random elements**: for integrable `U`, `𝔼⟨A_{Law U}(U), U⟩ = 0` if and only if `U = c`
almost surely for some `c ∈ F`. -/
theorem integral_inner_crowdOp_self_eq_zero_iff (hU : Integrable U P) :
    ∫ ω, ⟪crowdOp (P.map U) (U ω), U ω⟫ ∂P = 0 ↔ ∃ c : F, U =ᵐ[P] fun _ => c := by
  refine ⟨exists_ae_eq_const_of_integral_inner_crowdOp_self_eq_zero hU, fun ⟨c, hc⟩ => ?_⟩
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_crowdOp_eq_zero_of_ae_eq_const hc] with ω hω
  rw [hω, inner_zero_left, Pi.zero_apply]

/-- **The crowding correction vanishes almost surely exactly at almost surely constant random
elements**: for integrable `U`, `A_{Law U}(U) = 0` almost surely if and only if `U = c` almost
surely for some `c ∈ F`. -/
theorem ae_crowdOp_eq_zero_iff (hU : Integrable U P) :
    (∀ᵐ ω ∂P, crowdOp (P.map U) (U ω) = 0) ↔ ∃ c : F, U =ᵐ[P] fun _ => c := by
  refine ⟨fun h => exists_ae_eq_const_of_integral_inner_crowdOp_self_eq_zero hU ?_,
    fun ⟨c, hc⟩ => ae_crowdOp_eq_zero_of_ae_eq_const hc⟩
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h] with ω hω
  rw [hω, inner_zero_left, Pi.zero_apply]

omit [InnerProductSpace ℝ F] in
/-- A random element is almost surely constant exactly when its law is a Dirac mass:
`U = c` almost surely if and only if `Law U = δ_c`. -/
theorem ae_eq_const_iff_map_eq_dirac (hU : AEMeasurable U P) (c : F) :
    (U =ᵐ[P] fun _ => c) ↔ P.map U = Measure.dirac c := by
  refine ⟨fun hc => by rw [Measure.map_congr hc, Measure.map_const, measure_univ, one_smul],
    fun hmap => ae_of_ae_map hU (p := fun x => x = c) ?_⟩
  rw [hmap, ae_dirac_eq]
  exact Filter.eventually_pure.mpr rfl

/-- **The crowding correction along a square-integrable random element**: if `U ∈ L²(Ω; F)` and
`A_{Law U}(U) = 0` almost surely, with `Law U` the law of finite second moment, then `U = c`
almost surely for some `c ∈ F`. -/
theorem exists_ae_eq_const_of_crowdOp_lawP2_eq_zero (hU : MemLp U 2 P)
    (h : ∀ᵐ ω ∂P, crowdOp (lawP2 P U).law (U ω) = 0) : ∃ c : F, U =ᵐ[P] fun _ => c := by
  rw [lawP2_law hU] at h
  exact (ae_crowdOp_eq_zero_iff (hU.integrable one_le_two)).mp h

end RandomElement

/-! ### Laws of finite second moment -/

section Law

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [InnerProductSpace ℝ F] [CompleteSpace F] in
/-- The identity is integrable against a law of finite second moment. -/
theorem integrable_id_law (Λ : P2 F) : Integrable (fun u : F => u) Λ.law :=
  (integrable_norm_iff measurable_id.aestronglyMeasurable).mp
    (integrable_norm_of_secondMoment_ne_top Λ.secondMoment_ne_top)

/-- **The crowding pairing of a law of finite second moment, symmetrised.** For `λ ∈ P₂(F)`,
`∫ ⟨A_λ(u), u⟩ λ(du) = ½ ∬ ‖u − v‖² / √(1 + ‖u − v‖²) λ(du) λ(dv)`. -/
theorem integral_inner_crowdOp_law (Λ : P2 F) :
    ∫ u, ⟪crowdOp Λ.law u, u⟫ ∂Λ.law
      = 1 / 2 * ∫ z : F × F, ‖z.1 - z.2‖ ^ 2 / Real.sqrt (1 + ‖z.1 - z.2‖ ^ 2)
          ∂(Λ.law.prod Λ.law) := by
  have h := integral_inner_crowdOp_self (P := Λ.law) (integrable_id_law Λ)
  rwa [Measure.map_id'] at h

/-- **The crowding pairing of a law of finite second moment vanishes exactly at Dirac masses**:
for `λ ∈ P₂(F)`, `∫ ⟨A_λ(u), u⟩ λ(du) = 0` if and only if `λ = δ_a` for some `a ∈ F`. -/
theorem integral_inner_crowdOp_law_eq_zero_iff (Λ : P2 F) :
    ∫ u, ⟪crowdOp Λ.law u, u⟫ ∂Λ.law = 0 ↔ ∃ a : F, Λ.law = Measure.dirac a := by
  have h := integral_inner_crowdOp_self_eq_zero_iff (P := Λ.law) (integrable_id_law Λ)
  rw [Measure.map_id'] at h
  rw [h]
  refine exists_congr fun a => ?_
  have e := ae_eq_const_iff_map_eq_dirac (P := Λ.law) (U := fun u : F => u)
    measurable_id.aemeasurable a
  rwa [Measure.map_id'] at e

/-- **The crowding pairing of a law of finite second moment is positive off the Dirac masses**:
for `λ ∈ P₂(F)` which is not a Dirac mass, `∫ ⟨A_λ(u), u⟩ λ(du) > 0`. -/
theorem integral_inner_crowdOp_law_pos (Λ : P2 F) (h : ∀ a : F, Λ.law ≠ Measure.dirac a) :
    0 < ∫ u, ⟪crowdOp Λ.law u, u⟫ ∂Λ.law := by
  have hnn : 0 ≤ ∫ u, ⟪crowdOp Λ.law u, u⟫ ∂Λ.law := by
    have h' := integral_inner_crowdOp_self_nonneg (P := Λ.law) (integrable_id_law Λ)
    rwa [Measure.map_id'] at h'
  refine hnn.lt_of_ne fun h0 => ?_
  obtain ⟨a, ha⟩ := (integral_inner_crowdOp_law_eq_zero_iff Λ).mp h0.symm
  exact h a ha

end Law

end Dissertation.Law
