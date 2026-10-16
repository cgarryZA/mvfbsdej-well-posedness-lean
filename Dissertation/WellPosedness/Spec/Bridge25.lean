/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Spec.Bridge23
import Dissertation.WellPosedness.Robustness.Margin
import Dissertation.WellPosedness.System.DiagonalAtIntegrable
/-!
# Assumption 2.5 in the forms the proofs consume

The proofs consume Assumption 2.5 as `DiagonalMonotone`, `TerminalMonotone` and `Constants`, whose
expectations are Bochner integrals, `0` for a function that is not integrable. The printed
assumption presupposes that the expectations of its two pairings exist. It is therefore the
consumed form together with the integrability of the pairings, and it implies the consumed form
with the same constants.

The pairings are integrable under (2.3) and Assumption 2.3: the interior pairing by
`WellPosedness.integrable_interiorPairing_of_diagonalLipschitzHAt`, and the terminal pairing
`⟨δg_T, G δX_T⟩` because `|δg_T| ≤ L (|δX_T| + W₂(ρ, ρ'))` almost surely and `δX_T` is square
integrable. Under those two assumptions the printed Assumption 2.5 and the consumed form are
therefore equivalent.

The integrand of (2.7) as printed, `pairing27`, is the pairing `interiorPairing` of the channel
differences, the adjoints of `GX G`, `GZ G`, `GU G ν` being `GX Gᵀ`, `GZ Gᵀ`, `GU Gᵀ ν`, and the
inner product of `L²(ν)` the integral of the pointwise inner product. For square-integrable
inputs the expectation of the right-hand side of (2.7), `dissipation`, splits into the two
printed expectations.

## Main statements

* `pairing27_eq` — the printed integrand of (2.7) is `interiorPairing`.
* `integral_dissipation_eq` — the expectation of the right-hand side of (2.7) is
  `−β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}] − β₂ 𝔼|G δX|²`.
* `Assumption25.diagonalMonotone`, `Assumption25.terminalMonotone` — Assumption 2.5 gives the
  consumed form with the same constants.
* `integrable_terminalPairing` — under (2.3) and (2.6) the terminal pairing is integrable.
* `Assumption25.of_integrable` — the consumed form with the integrability of the pairings gives
  Assumption 2.5.
* `Assumption25.of_monotone`, `assumption25_iff` — under (2.3) and Assumption 2.3 the consumed
  form gives Assumption 2.5, and the two are equivalent.
-/

open MeasureTheory Filter Dissertation.Law Matrix

namespace Dissertation.WellPosedness.Spec

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-! ### The printed integrand and the right-hand side of (2.7) -/

/-- **The printed integrand of (2.7) is the pairing `interiorPairing`** of the channel
differences, for the coupling operators of `G`. -/
theorem pairing27_eq (G : Matrix (Fin m) (Fin n) ℝ) (C : Coeffs ν n m d) (t : ℝ)
    (θ θ' : TupleH ν n m d) (μ μ' : P2 (TupleH ν n m d)) :
    pairing27 G C t θ θ' μ μ'
      = interiorPairing (GX G) (GZ G) (GU G ν) (diagDiff C t θ θ' μ μ') := by
  have hU : inner ℝ (C.h t θ μ - C.h t θ' μ')
        (ContinuousLinearMap.adjoint (GU G ν) (θ.2.2.2 - θ'.2.2.2))
      = ∫ e, inner ℝ (C.h t θ μ e - C.h t θ' μ' e) (GX Gᵀ (θ.2.2.2 e - θ'.2.2.2 e)) ∂ν := by
    rw [adjoint_GU, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (C.h t θ μ) (C.h t θ' μ'),
      coeFn_GU Gᵀ ν (θ.2.2.2 - θ'.2.2.2), Lp.coeFn_sub θ.2.2.2 θ'.2.2.2] with e h1 h2 h3
    rw [h1, h2, h3, Pi.sub_apply, Pi.sub_apply]
  unfold pairing27 interiorPairing
  simp only [diagDiff]
  rw [adjoint_GX, adjoint_GZ, hU]

/-- **The expectation of the right-hand side of (2.7) splits into the printed expectations**: for
square-integrable `Θ, Θ'`,
`𝔼[dissipation] = −β₁ 𝔼[|Gᵀ δY|² + |Gᵀ δZ|²_F + ‖Gᵀ δU‖²_{L²(ν)}] − β₂ 𝔼|G δX|²`. -/
theorem integral_dissipation_eq {P : Measure Ω} {Θ Θ' : Ω → TupleH ν n m d} (hΘ : MemLp Θ 2 P)
    (hΘ' : MemLp Θ' 2 P) (G : Matrix (Fin m) (Fin n) ℝ) (β₁ β₂ : ℝ) (C : Coeffs ν n m d)
    (t : ℝ) (μ μ' : P2 (TupleH ν n m d)) :
    ∫ ω, dissipation (GX G) (GZ G) (GU G ν) β₁ β₂ (diagDiff C t (Θ ω) (Θ' ω) μ μ') ∂P
      = -β₁ * ∫ ω, (‖GX Gᵀ ((Θ ω).2.1 - (Θ' ω).2.1)‖ ^ 2
          + ‖GZ Gᵀ ((Θ ω).2.2.1 - (Θ' ω).2.2.1)‖ ^ 2
          + ‖GU Gᵀ ν ((Θ ω).2.2.2 - (Θ' ω).2.2.2)‖ ^ 2) ∂P
        - β₂ * ∫ ω, ‖GX G ((Θ ω).1 - (Θ' ω).1)‖ ^ 2 ∂P := by
  have hY := integrable_norm_sq_comp_sub_Y (GX Gᵀ) hΘ hΘ'
  have hZ := integrable_norm_sq_comp_sub_Z (GZ Gᵀ) hΘ hΘ'
  have hU := integrable_norm_sq_comp_sub_U (GU Gᵀ ν) hΘ hΘ'
  have hA := (hY.fun_add hZ).fun_add hU
  have hB : Integrable (fun ω => ‖GX G ((Θ ω).1 - (Θ' ω).1)‖ ^ 2) P :=
    integrable_norm_sq_comp_sub_X (GX G) hΘ hΘ'
  unfold dissipation
  simp only [diagDiff, adjoint_GX, adjoint_GZ, adjoint_GU]
  rw [integral_sub (hA.const_mul _) (hB.const_mul _), integral_const_mul, integral_const_mul]

/-! ### From the printed assumption to the consumed form -/

section Consumed

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T L α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d}

namespace Assumption25

/-- **Assumption 2.5 gives `DiagonalMonotone`** with the same `G, β₁, β₂`. -/
theorem diagonalMonotone (h : Assumption25 ℱ P T G α β₁ β₂ C) :
    DiagonalMonotone ℱ P T G β₁ β₂ C := by
  filter_upwards [h.interior] with t ht Θ Θ' hΘ hΘ' hΘ2 hΘ2'
  have key := (ht (Θ, lawP2 P Θ) (mk_mem_diagonalInputs hΘ hΘ2) (Θ', lawP2 P Θ')
    (mk_mem_diagonalInputs hΘ' hΘ2')).2
  rw [integral_dissipation_eq hΘ2 hΘ2']
  simpa only [pairing27_eq] using key

/-- **Assumption 2.5 gives `TerminalMonotone`** with the same `G, α`. -/
theorem terminalMonotone (h : Assumption25 ℱ P T G α β₁ β₂ C) :
    TerminalMonotone ℱ P T G α C.g :=
  fun ξ ξ' hξ hξ' hξ2 hξ2' => (h.terminal ξ ξ' hξ hξ' hξ2 hξ2').2

end Assumption25

end Consumed

/-! ### From the consumed form to the printed assumption -/

section Printed

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T L α β₁ β₂ : ℝ} {G : Matrix (Fin m) (Fin n) ℝ} {C : Coeffs ν n m d}

/-- **The terminal pairing is integrable under (2.3) and (2.6)**: for `X_T, X'_T` strongly
`ℱ_T`-measurable and square integrable with laws `ρ, ρ'`,
`ω ↦ ⟨g(X_T, ρ) − g(X'_T, ρ'), G (X_T − X'_T)⟩` is integrable. -/
theorem integrable_terminalPairing (hJ : JointBorel T C) (hLT : LipTerminal ℱ P T L C.g)
    {XT XT' : Ω → EuclideanSpace ℝ (Fin n)} (hX : StronglyMeasurable[ℱ T] XT)
    (hX' : StronglyMeasurable[ℱ T] XT') (hX2 : MemLp XT 2 P) (hX2' : MemLp XT' 2 P) :
    Integrable (fun ω => inner ℝ (C.g (XT ω) (lawP2 P XT) - C.g (XT' ω) (lawP2 P XT'))
      (GX G (XT ω - XT' ω))) P := by
  set w := w2P (lawP2 P XT) (lawP2 P XT')
  have hw : 0 ≤ w := w2P_nonneg _ _
  have hgm : ∀ {Y : Ω → EuclideanSpace ℝ (Fin n)}, MemLp Y 2 P → ∀ ρ,
      AEStronglyMeasurable (fun ω => C.g (Y ω) ρ) P := fun hY ρ =>
    ((hJ.measurable_g_section ρ).comp_aemeasurable
      hY.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hδ : MemLp (fun ω => XT ω - XT' ω) 2 P := hX2.sub hX2'
  have hm : AEStronglyMeasurable (fun ω => inner ℝ
      (C.g (XT ω) (lawP2 P XT) - C.g (XT' ω) (lawP2 P XT')) (GX G (XT ω - XT' ω))) P :=
    ((hgm hX2 _).sub (hgm hX2' _)).inner
      ((GX G).continuous.comp_aestronglyMeasurable hδ.aestronglyMeasurable)
  have hi : Integrable (fun ω => |L| * ‖GX G‖ * (‖XT ω - XT' ω‖ ^ 2 + w * ‖XT ω - XT' ω‖)) P :=
    ((hδ.integrable_norm_pow two_ne_zero).fun_add
      ((hδ.integrable one_le_two).norm.const_mul w)).const_mul _
  refine hi.mono' hm ((hLT XT XT' hX hX' hX2 hX2').mono fun ω hω => ?_)
  have hn := norm_nonneg (XT ω - XT' ω)
  have hG := (GX G).le_opNorm (XT ω - XT' ω)
  have hg : ‖C.g (XT ω) (lawP2 P XT) - C.g (XT' ω) (lawP2 P XT')‖
      ≤ |L| * (‖XT ω - XT' ω‖ + w) :=
    hω.trans (mul_le_mul_of_nonneg_right (le_abs_self L) (add_nonneg hn hw))
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  calc ‖C.g (XT ω) (lawP2 P XT) - C.g (XT' ω) (lawP2 P XT')‖ * ‖GX G (XT ω - XT' ω)‖
      ≤ (|L| * (‖XT ω - XT' ω‖ + w)) * (‖GX G‖ * ‖XT ω - XT' ω‖) :=
        mul_le_mul hg hG (norm_nonneg _) (by positivity)
    _ = |L| * ‖GX G‖ * (‖XT ω - XT' ω‖ ^ 2 + w * ‖XT ω - XT' ω‖) := by ring

/-- **The consumed form together with the integrability of the two pairings gives Assumption
2.5**, with the same constants. -/
theorem Assumption25.of_integrable (hconst : Constants n m α β₁ β₂)
    (hM : DiagonalMonotone ℱ P T G β₁ β₂ C) (hMT : TerminalMonotone ℱ P T G α C.g)
    (hint : ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ Θ Θ' : Ω → TupleH ν n m d,
      StronglyMeasurable[ℱ t] Θ → StronglyMeasurable[ℱ t] Θ' → MemLp Θ 2 P → MemLp Θ' 2 P →
      Integrable (fun ω => interiorPairing (GX G) (GZ G) (GU G ν)
        (diagDiff C t (Θ ω) (Θ' ω) (lawP2 P Θ) (lawP2 P Θ'))) P)
    (hintT : ∀ XT XT' : Ω → EuclideanSpace ℝ (Fin n), StronglyMeasurable[ℱ T] XT →
      StronglyMeasurable[ℱ T] XT' → MemLp XT 2 P → MemLp XT' 2 P →
      Integrable (fun ω => inner ℝ (C.g (XT ω) (lawP2 P XT) - C.g (XT' ω) (lawP2 P XT'))
        (GX G (XT ω - XT' ω))) P) :
    Assumption25 ℱ P T G α β₁ β₂ C where
  terminal XT XT' hX hX' hX2 hX2' :=
    ⟨hintT XT XT' hX hX' hX2 hX2', hMT XT XT' hX hX' hX2 hX2'⟩
  interior := by
    filter_upwards [hM, hint] with t hMt hit p hp p' hp'
    obtain ⟨hs, h2, he⟩ := hp
    obtain ⟨hs', h2', he'⟩ := hp'
    rw [he, he']
    refine ⟨by simpa only [pairing27_eq] using hit p.1 p'.1 hs hs' h2 h2', ?_⟩
    rw [← integral_dissipation_eq h2 h2']
    simpa only [pairing27_eq] using hMt p.1 p'.1 hs hs' h2 h2'
  constants := hconst

/-- **Under (2.3) and Assumption 2.3 the consumed form gives Assumption 2.5**, with the same
constants. -/
theorem Assumption25.of_monotone (hJ : JointBorel T C) (h23 : Assumption23 ℱ P T L C)
    (hconst : Constants n m α β₁ β₂) (hM : DiagonalMonotone ℱ P T G β₁ β₂ C)
    (hMT : TerminalMonotone ℱ P T G α C.g) : Assumption25 ℱ P T G α β₁ β₂ C :=
  Assumption25.of_integrable hconst hM hMT
    (by
      filter_upwards [lipInterior_iff_diagonalLipschitzH.mp h23.interior,
        ae_restrict_mem measurableSet_Icc]
        with t hLt htI Θ Θ' hs hs' h2 h2'
      exact WellPosedness.integrable_interiorPairing_of_diagonalLipschitzHAt (G := G)
        (jointBorel_iff.mp hJ).1 htI hLt hs hs' h2 h2')
    fun _ _ hX hX' hX2 hX2' => integrable_terminalPairing hJ h23.terminal hX hX' hX2 hX2'

/-- **Under (2.3) and Assumption 2.3, Assumption 2.5 is its consumed form**: `DiagonalMonotone`,
`TerminalMonotone` and `Constants`, with the same constants. -/
theorem assumption25_iff (hJ : JointBorel T C) (h23 : Assumption23 ℱ P T L C) :
    Assumption25 ℱ P T G α β₁ β₂ C
      ↔ DiagonalMonotone ℱ P T G β₁ β₂ C ∧ TerminalMonotone ℱ P T G α C.g
        ∧ Constants n m α β₁ β₂ :=
  ⟨fun h => ⟨h.diagonalMonotone, h.terminalMonotone, h.constants⟩,
    fun h => Assumption25.of_monotone hJ h23 h.2.2 h.1 h.2.1⟩

end Printed

end Dissertation.WellPosedness.Spec
