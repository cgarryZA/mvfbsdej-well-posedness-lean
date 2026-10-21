/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.CrowdGrad
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The symmetrised crowding pairing

For a probability measure `λ` with finite first moment on a real Hilbert space `F`, the crowding
operator `A_λ(u) = ∫ ∇V(u − v) λ(dv)` satisfies

`∫ ⟨A_λ(u), u⟩ λ(du) = ½ ∬ ‖u − v‖² / √(1 + ‖u − v‖²) λ(du) λ(dv)`:

the product measure `λ ⊗ λ` is invariant under exchanging the two variables and `∇V` is odd, so
the pairing with `u` equals minus the pairing with `v`, and the average of the two is the pairing
of `∇V(u − v)` with `u − v`. The right side is positive unless `λ` is a Dirac mass, since the
integrand vanishes only on the diagonal.

## Main statements

* `inner_crowdGrad_self` — `⟨∇V(w), w⟩ = ‖w‖² / √(1 + ‖w‖²)`.
* `integral_inner_crowdOp_self` — the symmetrised pairing.
* `crowdPairing_pos` — the pairing is positive off the Dirac masses.
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace Dissertation.Law

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
/-- `⟨∇V(w), w⟩ = ‖w‖² / √(1 + ‖w‖²)`. -/
theorem inner_crowdGrad_self (w : F) :
    ⟪crowdGrad w, w⟫ = ‖w‖ ^ 2 / Real.sqrt (1 + ‖w‖ ^ 2) := by
  rw [crowdGrad, real_inner_smul_left, real_inner_self_eq_norm_sq, div_eq_inv_mul]

omit [CompleteSpace F] in
/-- The symmetrised integrand is integrable for `λ ⊗ λ` when `λ` has finite first moment. -/
theorem integrable_sq_div_sqrt_prod (Λ : Measure F) [IsProbabilityMeasure Λ]
    (hΛ : Integrable (fun u : F => ‖u‖) Λ) :
    Integrable (fun z : F × F => ‖z.1 - z.2‖ ^ 2 / Real.sqrt (1 + ‖z.1 - z.2‖ ^ 2))
      (Λ.prod Λ) := by
  refine Integrable.mono' ((hΛ.comp_fst Λ).add (hΛ.comp_snd Λ)) ?_ (Eventually.of_forall
    fun z => ?_)
  · exact (Continuous.div (by fun_prop) (by fun_prop)
      fun z => (Real.sqrt_pos.mpr (by positivity)).ne').aestronglyMeasurable
  · have h1 := norm_crowdGrad (z.1 - z.2)
    have h2 := inner_crowdGrad_self (z.1 - z.2)
    have hb : ‖z.1 - z.2‖ ^ 2 / Real.sqrt (1 + ‖z.1 - z.2‖ ^ 2) ≤ ‖z.1 - z.2‖ := by
      rw [← h2]
      refine (real_inner_le_norm _ _).trans ?_
      calc ‖crowdGrad (z.1 - z.2)‖ * ‖z.1 - z.2‖ ≤ 1 * ‖z.1 - z.2‖ := by
            gcongr
            exact norm_crowdGrad_le_one _
        _ = ‖z.1 - z.2‖ := one_mul _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hb.trans (norm_sub_le _ _)

/-- **The symmetrised crowding pairing.** For a probability measure `λ` with finite first
moment, `∫ ⟨A_λ(u), u⟩ λ(du) = ½ ∬ ‖u − v‖² / √(1 + ‖u − v‖²) λ(dv) λ(du)`. -/
theorem integral_inner_crowdOp_self (Λ : Measure F) [IsProbabilityMeasure Λ]
    (hΛ : Integrable (fun u : F => ‖u‖) Λ) :
    ∫ u, ⟪crowdOp Λ u, u⟫ ∂Λ
      = 1 / 2 * ∫ u, ∫ v, ‖u - v‖ ^ 2 / Real.sqrt (1 + ‖u - v‖ ^ 2) ∂Λ ∂Λ := by
  set k : F × F → ℝ := fun z => ⟪crowdGrad (z.1 - z.2), z.1⟫ with hk
  have hkm : AEStronglyMeasurable k (Λ.prod Λ) :=
    ((continuous_crowdGrad.comp (continuous_fst.sub continuous_snd)).inner
      continuous_fst).aestronglyMeasurable
  have hki : Integrable k (Λ.prod Λ) := by
    refine Integrable.mono' (hΛ.comp_fst Λ) hkm (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖crowdGrad (z.1 - z.2)‖ * ‖z.1‖ ≤ 1 * ‖z.1‖ := by
          gcongr
          exact norm_crowdGrad_le_one _
      _ = ‖z.1‖ := one_mul _
  have hpair : ∀ u, ⟪crowdOp Λ u, u⟫ = ∫ v, k (u, v) ∂Λ := by
    intro u
    rw [crowdOp, real_inner_comm, ← integral_inner (integrable_crowdGrad_sub Λ u)]
    exact integral_congr_ae (Eventually.of_forall fun v => real_inner_comm _ _)
  have hswap : ∫ z, k z ∂(Λ.prod Λ) = ∫ z, k z.swap ∂(Λ.prod Λ) :=
    (integral_prod_swap k).symm
  have hsum : ∀ z : F × F, k z + k z.swap
      = ‖z.1 - z.2‖ ^ 2 / Real.sqrt (1 + ‖z.1 - z.2‖ ^ 2) := by
    intro z
    simp only [hk, Prod.fst_swap, Prod.snd_swap]
    rw [show z.2 - z.1 = -(z.1 - z.2) by abel, crowdGrad_neg, inner_neg_left, ← sub_eq_add_neg,
      ← inner_sub_right, inner_crowdGrad_self]
  have hki' : Integrable (fun z : F × F => k z.swap) (Λ.prod Λ) := hki.swap
  have h2 : 2 * ∫ z, k z ∂(Λ.prod Λ)
      = ∫ z, ‖z.1 - z.2‖ ^ 2 / Real.sqrt (1 + ‖z.1 - z.2‖ ^ 2) ∂(Λ.prod Λ) := by
    rw [two_mul]
    nth_rw 2 [hswap]
    rw [← integral_add hki hki']
    exact integral_congr_ae (Eventually.of_forall hsum)
  calc ∫ u, ⟪crowdOp Λ u, u⟫ ∂Λ = ∫ u, ∫ v, k (u, v) ∂Λ ∂Λ :=
        integral_congr_ae (Eventually.of_forall hpair)
    _ = ∫ z, k z ∂(Λ.prod Λ) := (integral_prod k hki).symm
    _ = 1 / 2 * ∫ z, ‖z.1 - z.2‖ ^ 2 / Real.sqrt (1 + ‖z.1 - z.2‖ ^ 2) ∂(Λ.prod Λ) := by
        rw [← h2]
        ring
    _ = 1 / 2 * ∫ u, ∫ v, ‖u - v‖ ^ 2 / Real.sqrt (1 + ‖u - v‖ ^ 2) ∂Λ ∂Λ := by
        rw [integral_prod _ (integrable_sq_div_sqrt_prod Λ hΛ)]

/-- **The symmetrised crowding pairing is positive off the Dirac masses.** For a probability
measure `λ` with finite first moment which is not a Dirac mass, `∫ ⟨A_λ(u), u⟩ λ(du) > 0`. -/
theorem crowdPairing_pos (Λ : Measure F) [IsProbabilityMeasure Λ]
    (hΛ : Integrable (fun u : F => ‖u‖) Λ) (hD : ¬ ∃ u, Λ = Measure.dirac u) :
    0 < ∫ u, ⟪crowdOp Λ u, u⟫ ∂Λ := by
  rw [integral_inner_crowdOp_self Λ hΛ]
  set g : F × F → ℝ := fun z => ‖z.1 - z.2‖ ^ 2 / Real.sqrt (1 + ‖z.1 - z.2‖ ^ 2) with hg
  have hgi := integrable_sq_div_sqrt_prod Λ hΛ
  have hg0 : 0 ≤ᵐ[Λ.prod Λ] g := Eventually.of_forall fun z => by positivity
  have hI : 0 ≤ ∫ z, g z ∂(Λ.prod Λ) := integral_nonneg_of_ae hg0
  rw [← integral_prod g hgi]
  rcases hI.lt_or_eq with hpos | hzero
  · positivity
  exfalso
  have hae := (integral_eq_zero_iff_of_nonneg_ae hg0 hgi).mp hzero.symm
  have hdiag : ∀ᵐ z ∂(Λ.prod Λ), z.1 = z.2 := by
    filter_upwards [hae] with z hz
    have hz' : ‖z.1 - z.2‖ ^ 2 / Real.sqrt (1 + ‖z.1 - z.2‖ ^ 2) = 0 := hz
    have hs : 0 < Real.sqrt (1 + ‖z.1 - z.2‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
    rw [div_eq_zero_iff, or_iff_left hs.ne'] at hz'
    exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hz'))
  obtain ⟨u₀, hu₀⟩ := (Measure.ae_ae_of_ae_prod hdiag).exists
  refine hD ⟨u₀, ?_⟩
  calc Λ = Λ.map id := Measure.map_id.symm
    _ = Λ.map (fun _ => u₀) := Measure.map_congr (hu₀.mono fun v hv => hv.symm)
    _ = Measure.dirac u₀ := by rw [Measure.map_const, measure_univ, one_smul]

end Dissertation.Law
