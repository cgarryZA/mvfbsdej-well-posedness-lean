/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec5Regimes
import Dissertation.Acceptance.A.Dealer

/-!
# Remark 5.7 of the well-posedness paper: the dealer interaction, proofs

## Main statements

* `Dissertation.Acceptance.A.rem_regimes_corr` — the crowding correction is nonlinear in the
  valuation curve, affine in the law and no function of its mean.
-/

namespace Dissertation.Acceptance.A

universe v

/-- Remark 5.7, the dealer interaction. -/
theorem rem_regimes_corr : PaperSpec.A.rem_regimes_corr.{v} := by
  intro E _ ν _ _ hne
  obtain ⟨h1, h2⟩ := ex_dealer_not_mean_corr ν hne
  exact ⟨(ex_dealer_affine ν).1, h1, h2⟩

end Dissertation.Acceptance.A
