/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.System.DiagonalAt
import MVFBSDEJ.WellPosedness.Remarks.Pointwise

/-!
# Integrability of the interior pairing at a fixed time

Under the joint Borel measurability (2.3) and Assumption 2.3, interior, at a time `r ∈ [0, T]`,
the interior pairing of (2.7) along two diagonal inputs at `r` is integrable.

## Main statements

* `integrable_interiorPairing_of_diagonalLipschitzHAt` — the pairing of (2.7) is integrable.
-/

open MeasureTheory Filter Topology MVFBSDEJ.Law MVFBSDEJ.WellPosedness
  MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence

namespace MVFBSDEJ.WellPosedness

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} {n m d : ℕ}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E]

/-! ### Integrability of the interior pairing -/

section Nodewise

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T L α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ}
  {C : Coeffs ν n m d} {t : ℝ}

/-- **The interior pairing is integrable at a time of Assumption 2.3**: under (2.3) and
Assumption 2.3, interior, at a time `r ∈ [0, T]`, the pairing of (2.7) along two diagonal inputs
at `r` is integrable. -/
theorem integrable_interiorPairing_of_diagonalLipschitzHAt (hB : CoeffBorelW2 T C) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) (hLr : DiagonalLipschitzHAt ℱ P r L C)
    {Θ Θ' : Ω → TupleH ν n m d} (hΘ : StronglyMeasurable[ℱ r] Θ)
    (hΘ' : StronglyMeasurable[ℱ r] Θ') (hΘ2 : MemLp Θ 2 P) (hΘ2' : MemLp Θ' 2 P) :
    Integrable (fun ω => interiorPairing (GX G) (GZ G) (GU G ν)
      (diagDiff C r (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ'))) P := by
  have hB' := hB.toCoeffBorel
  have ha := hΘ2.aestronglyMeasurable
  have ha' := hΘ2'.aestronglyMeasurable
  exact integrable_interiorPairing_of_ae_le (w2H_nonneg _ _) hΘ2 hΘ2'
    (aestronglyMeasurable_interiorPairing_diagDiff G C r _ _ ha ha'
      (aestronglyMeasurable_sub_of_cutoff hB'.b_meas hr ha.aemeasurable ha'.aemeasurable _ _)
      (aestronglyMeasurable_sub_of_cutoff hB'.σ_meas hr ha.aemeasurable ha'.aemeasurable _ _)
      (aestronglyMeasurable_sub_of_cutoff hB'.h_meas hr ha.aemeasurable ha'.aemeasurable _ _)
      (aestronglyMeasurable_sub_of_cutoff hB'.f_meas hr ha.aemeasurable ha'.aemeasurable _ _))
    (hLr Θ Θ' hΘ hΘ' hΘ2 hΘ2')

end Nodewise

end MVFBSDEJ.WellPosedness
