/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec2
import Dissertation.WellPosedness.Remarks.Margin

/-!
# Section 2 of the well-posedness paper: proofs of the coupling matrix and Wasserstein bounds

## Main statements

* `Dissertation.Acceptance.A.eq_coupling` — (2.8).
* `Dissertation.Acceptance.A.eq_couplingT` — (2.9).
* `Dissertation.Acceptance.A.eq_lipfun` — (2.10).
* `Dissertation.Acceptance.A.eq_margproj` — (2.11).
* `Dissertation.Acceptance.A.ass_G` — the bounds of Assumption 2.4.
-/

open MeasureTheory Dissertation.Law

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System

universe u v w

/-- The coupling bound (2.8). -/
theorem eq_coupling : PaperSpec.A.eq_coupling.{u, v} := by
  intro Ω _ P _ E _ ν _ _ n m d Θ Θ' hΘ hΘ'
  exact (w2H_lawP2_sq_le hΘ hΘ').trans_eq rfl

/-- The terminal coupling bound (2.9). -/
theorem eq_couplingT : PaperSpec.A.eq_couplingT.{u} := by
  intro Ω _ P _ n X X' hX hX'
  exact w2P_lawP2_sq_le hX hX'

/-- Lipschitz law functionals (2.10). -/
theorem eq_lipfun : PaperSpec.A.eq_lipfun.{v, w} := by
  intro E _ ν _ _ n m d K _ _ _ _ φ L hL hlip μ μ'
  exact norm_integral_sub_le_w2H hL hlip μ μ'

/-- The `U`-marginal projection (2.11). -/
theorem eq_margproj : PaperSpec.A.eq_margproj.{v} := by
  intro E _ ν _ _ n m d μ μ'
  exact w2P_margU_le_w2H μ μ'

/-- The bounds of Assumption 2.4. -/
theorem ass_G : PaperSpec.A.ass_G.{v} := by
  intro m n hm hn G hG
  have hadj : ∀ v : EuclideanSpace ℝ (Fin m),
      ‖ContinuousLinearMap.adjoint (GX G) v‖ ≤ ‖GX G‖ * ‖v‖ := fun v =>
    ((ContinuousLinearMap.adjoint (GX G)).le_opNorm v).trans_eq
      (by rw [LinearIsometryEquiv.norm_map])
  refine ⟨sMin_pos G hG hn.ne' hm.ne', fun v => (GX G).le_opNorm v, hadj,
    fun h => gCoerciveForward_of_rank hG h, fun h => gCoerciveBackward_of_rank hG h,
    fun hinj => ?_⟩
  have hmn : m ≤ n := by
    have := LinearMap.finrank_le_finrank_of_injective (R := ℝ)
      (f := ((ContinuousLinearMap.adjoint (GX G) :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
          EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) hinj
    simpa using this
  have hb := gCoerciveBackward_of_rank hG hmn
  exact ⟨fun d Z => gCoerciveBackward_GZ hb Z, fun ν U => gCoerciveBackward_GU hb U⟩

end Dissertation.Acceptance.A
