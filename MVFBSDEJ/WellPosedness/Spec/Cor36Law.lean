/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import MVFBSDEJ.WellPosedness.Existence.GlobalEnl
import MVFBSDEJ.WellPosedness.Spec.Bridge22
import MVFBSDEJ.WellPosedness.Spec.CorollaryHyps
import MVFBSDEJ.WellPosedness.Robustness.JumpMargin
import MVFBSDEJ.WellPosedness.Examples.FullLawBeyond

/-!
# (3.5), the law-Lipschitz bound of Corollary 3.6

The last paragraph of Corollary 3.6 takes perturbations that are independent of `θ` and satisfy
(3.5),

`|δp_b| + |δp_σ|_F + ‖δp_h‖_{L²(ν)} + |δp_f| ≤ L_p W₂(μ, μ')`

for almost every `t ∈ [0, T]` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`. This file states (3.5) as printed,
`LawLip35`, with the differences compared almost surely as in Assumption 2.3, and identifies it with
`MVFBSDEJ.WellPosedness.System.DiagonalLawLipschitzH` at the same constant. With `n ≥ 1` and
`T > 0`, (3.5) forces `L_p ≥ 0`: at the deterministic inputs `(e₁, 0, 0, 0)` and `0` the right-hand
side is `L_p`.

## Main definitions

* `LawLip35` — (3.5).

## Main statements

* `lawLip35_iff` — (3.5) as printed is `MVFBSDEJ.WellPosedness.System.DiagonalLawLipschitzH`.
* `LawLip35.nonneg` — (3.5) forces `L_p ≥ 0` for `n ≥ 1`, `T > 0`.
-/

open MeasureTheory Filter ProbabilityTheory MVFBSDEJ.Law Matrix
open scoped ENNReal

namespace MVFBSDEJ.WellPosedness.Spec

open MVFBSDEJ.WellPosedness.System MVFBSDEJ.WellPosedness.Existence
  MVFBSDEJ.WellPosedness.Enlarged LevyStochCalc

/-! ### (3.5) -/

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {ν : Measure E}
  [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-- **(3.5)**, the law-Lipschitz bound of the perturbation `p` with the constant `L_p`: for almost
every `t ∈ [0, T]` and all `(Θ, μ), (Θ', μ') ∈ 𝒟_t`, almost surely
`|δp_b| + |δp_σ|_F + ‖δp_h‖_{L²(ν)} + |δp_f| ≤ L_p W₂(μ, μ')`, with `W₂` the 2-Wasserstein
distance on `P₂(H)` of the Hilbert norm of `H`. -/
def LawLip35 (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) [IsProbabilityMeasure P]
    (T Lₚ : ℝ) (p : Coeffs ν n m d) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
    ∀ q ∈ diagonalInputs ν n m d ℱ P t, ∀ q' ∈ diagonalInputs ν n m d ℱ P t, ∀ᵐ ω ∂P,
      ‖p.b t (q.1 ω) q.2 - p.b t (q'.1 ω) q'.2‖ + ‖p.σ t (q.1 ω) q.2 - p.σ t (q'.1 ω) q'.2‖
          + ‖p.h t (q.1 ω) q.2 - p.h t (q'.1 ω) q'.2‖
          + ‖p.f t (q.1 ω) q.2 - p.f t (q'.1 ω) q'.2‖
        ≤ Lₚ * w2H q.2 q'.2

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω} [IsProbabilityMeasure P]
  {T Lₚ : ℝ} {p : Coeffs ν n m d}

/-- **(3.5) as printed is `DiagonalLawLipschitzH`**, with the same constant. -/
theorem lawLip35_iff : LawLip35 ℱ P T Lₚ p ↔ DiagonalLawLipschitzH ℱ P T Lₚ p := by
  refine eventually_congr (Eventually.of_forall fun t => ⟨fun h Θ Θ' hΘ hΘ' hΘ2 hΘ2' =>
    h (Θ, lawP2 P Θ) (mk_mem_diagonalInputs hΘ hΘ2) (Θ', lawP2 P Θ')
      (mk_mem_diagonalInputs hΘ' hΘ2'), fun h q hq q' hq' => ?_⟩)
  obtain ⟨hs, h2, he⟩ := hq
  obtain ⟨hs', h2', he'⟩ := hq'
  rw [he, he']
  exact h _ _ hs hs' h2 h2'

/-- **(3.5) forces `L_p ≥ 0`** for `n ≥ 1` and `T > 0`: at the deterministic inputs
`(e₁, 0, 0, 0)` and `0`, whose laws are at `W₂`-distance `1`, the left-hand side is
nonnegative. -/
theorem LawLip35.nonneg (hn : 0 < n) (hT : 0 < T) (h : LawLip35 ℱ P T Lₚ p) : 0 ≤ Lₚ := by
  haveI : (ae (volume.restrict (Set.Icc (0 : ℝ) T))).NeBot := by
    rw [ae_restrict_neBot, Real.volume_Icc, sub_zero]
    exact ENNReal.ofReal_ne_zero_iff.mpr hT
  obtain ⟨t, ht⟩ := h.exists
  set θ : TupleH ν n m d := (EuclideanSpace.single ⟨0, hn⟩ 1, 0, 0, 0) with hθ
  obtain ⟨ω, hω⟩ := (ht (fun _ => θ, lawP2 P fun _ => θ)
    (mk_mem_diagonalInputs stronglyMeasurable_const (memLp_const θ))
    (fun _ => 0, lawP2 P fun _ => 0)
    (mk_mem_diagonalInputs stronglyMeasurable_const (memLp_const 0))).exists
  simp only [lawP2_const, w2H_dirac_dirac, sub_zero] at hω
  have hW : ‖toL2 θ‖ = 1 := by
    have hsq := norm_toL2_sq θ
    have hc : channelSq θ = 1 := by simp [channelSq, hθ]
    rw [hc] at hsq
    have := norm_nonneg (toL2 θ)
    nlinarith [sq_nonneg (‖toL2 θ‖ - 1), sq_nonneg (‖toL2 θ‖ + 1)]
  rw [hW, mul_one] at hω
  exact le_trans (by positivity) hω

end Law

universe u v w

end MVFBSDEJ.WellPosedness.Spec
