/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.WellPosedness.Spec.Bridge22
import Dissertation.WellPosedness.Spec.Bridge25
import Dissertation.WellPosedness.Remarks.LiMinSystem
import Dissertation.WellPosedness.Robustness.JumpMargin
import Dissertation.WellPosedness.Examples.MeanFieldWP

/-!
# A system failing Assumption 2.5: Example 3.2 of Li and Min

The linear mean-field system of Li and Min, `liMinCoeffs`, with `n = m = d = 1`,

`b = m_Y(μ)`, `σ = 1`, `h = u`, `f = m_X(μ)`, `g(x, ρ) = −𝔟(ρ)`,

satisfies the measurability (2.3), Assumption 2.2 with any deterministic initial datum and
Assumption 2.3 with `L = 2`, and `G = 1` satisfies Assumption 2.4. Its terminal map is Borel
measurable in the law since the barycentre `𝔟` is `1`-Lipschitz on the 2-Wasserstein space
`P₂(ℝ¹)`. Assumption 2.5 fails for every coupling matrix `G = (c) ∈ ℝ^{1×1}` of full rank, so
`c ≠ 0`, and all constants `α, β₁, β₂`, over any filtered probability space and at every horizon
`T > 0`: its interior inequality (2.7) fails at a pair of deterministic inputs, whose laws are
Dirac masses with means their points. For `c > 0` the inputs `(0, 1, 0, 0)` and `0` turn (2.7)
into `c ≤ −β₁ c²`, and for `c < 0` the inputs `(1, 0, 0, 0)` and `0` turn it into `−c ≤ −β₂ c²`;
both fail for `β₁, β₂ ≥ 0`.

This shows a failure of Assumption 2.5 while the other assumptions hold; it says nothing about
whether Assumption 2.5 is necessary for well-posedness.

## Main statements

* `GX_fin_one_apply`, `entry_ne_zero_of_rank_eq_one` — a `1 × 1` coupling matrix.
* `lipschitzWith_barycentre_toP2` — the barycentre is `1`-Lipschitz on `P₂(ℝ¹)`.
* `jointBorel_liMin`, `assumption22_liMin`, `assumption23_liMin` — (2.3), Assumption 2.2 and
  Assumption 2.3 for the system of Li and Min.
* `not_diagonalMonotone_liMin` — (2.7) fails for every `G ≠ 0` and all `β₁, β₂ ≥ 0`.
* `not_assumption25_liMin` — Assumption 2.5 fails for every full-rank `G` and all constants.
* `liMin_fails_assumption25` — the bundle: (2.3), Assumptions 2.2, 2.3 and 2.4 hold, and
  Assumption 2.5 fails.
-/

open MeasureTheory Filter Dissertation.Law Matrix

namespace Dissertation.WellPosedness.Spec

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence

/-! ### A `1 × 1` coupling matrix -/

/-- For a `1 × 1` matrix `G`, `G x = G₀₀ x`. -/
theorem GX_fin_one_apply (G : Matrix (Fin 1) (Fin 1) ℝ) (x : EuclideanSpace ℝ (Fin 1)) :
    GX G x = G 0 0 • x := by
  rw [← WithLp.toLp_ofLp 2 x, GX_toLp]
  refine PiLp.ext fun i => ?_
  fin_cases i
  simp [Matrix.mulVec, dotProduct]

/-- A `1 × 1` matrix of full rank has a nonzero entry. -/
theorem entry_ne_zero_of_rank_eq_one {G : Matrix (Fin 1) (Fin 1) ℝ} (hG : G.rank = min 1 1) :
    G 0 0 ≠ 0 := by
  intro h0
  have hz : G = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    exact h0
  rw [hz, Matrix.rank_zero] at hG
  norm_num at hG

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E]

/-! ### The assumptions that hold -/

/-- The barycentre is `1`-Lipschitz on the 2-Wasserstein space `P₂(ℝ¹)`. -/
theorem lipschitzWith_barycentre_toP2 :
    LipschitzWith 1 fun ρ : P2W (EuclideanSpace ℝ (Fin 1)) => barycentre ρ.toP2 :=
  LipschitzWith.of_dist_le_mul fun ρ ρ' => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm]
    exact norm_barycentre_sub_le _ _

/-- **(2.3) for the system of Li and Min.** -/
theorem jointBorel_liMin (T : ℝ) : JointBorel T (liMinCoeffs ν) :=
  jointBorel_iff.mpr ⟨coeffBorelW2_liMin T,
    ((lipschitzWith_barycentre_toP2.continuous.comp continuous_snd).neg).borel_measurable⟩

variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {P : Measure Ω}
  [IsProbabilityMeasure P] {T : ℝ}

/-- **Assumption 2.2 for the system of Li and Min**, with a deterministic initial datum. -/
theorem assumption22_liMin (x₀ : EuclideanSpace ℝ (Fin 1)) :
    Assumption22 ℱ P T (liMinCoeffs ν) (fun _ => x₀) :=
  ⟨stronglyMeasurable_const, memLp_const x₀, originValues_iff_coeffOrigin.mpr (coeffOrigin_liMin T)⟩

/-- **Assumption 2.3 for the system of Li and Min**, with `L = 2`. -/
theorem assumption23_liMin : Assumption23 ℱ P T 2 (liMinCoeffs ν) :=
  assumption23_iff.mpr ⟨zero_le_two, diagonalLipschitzH_liMin, terminalLipschitz_liMin one_le_two⟩

/-! ### Assumption 2.5 fails -/

/-- **(2.7) fails for the system of Li and Min**, for every `G ≠ 0` in `ℝ^{1×1}` and all
`β₁, β₂ ≥ 0`, at every horizon `T > 0`: it fails at a pair of deterministic inputs. -/
theorem not_diagonalMonotone_liMin (hT : 0 < T) {G : Matrix (Fin 1) (Fin 1) ℝ} (hG : G 0 0 ≠ 0)
    {β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) :
    ¬ DiagonalMonotone ℱ P T G β₁ β₂ (liMinCoeffs ν) := by
  intro hM
  haveI : (ae (volume.restrict (Set.Icc (0 : ℝ) T))).NeBot := by
    rw [ae_restrict_neBot, Real.volume_Icc, sub_zero]
    exact ENNReal.ofReal_ne_zero_iff.mpr hT
  obtain ⟨t, ht⟩ := hM.exists
  set c := G 0 0
  have hGt : ∀ x : EuclideanSpace ℝ (Fin 1), GX Gᵀ x = c • x := fun x => by
    rw [GX_fin_one_apply, transpose_apply]
  set e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with he
  have he1 : ‖e‖ = 1 := by simp [he]
  have key : ∀ θ : TupleH ν 1 1 1,
      interiorPairing (GX G) (GZ G) (GU G ν)
          (diagDiff (liMinCoeffs ν) t θ 0 (P2.dirac θ) (P2.dirac 0))
        ≤ dissipation (GX G) (GZ G) (GU G ν) β₁ β₂
          (diagDiff (liMinCoeffs ν) t θ 0 (P2.dirac θ) (P2.dirac 0)) := fun θ => by
    have h := ht (fun _ => θ) (fun _ => 0) stronglyMeasurable_const stronglyMeasurable_const
      (memLp_const _) (memLp_const _)
    simpa only [integral_const, probReal_univ, one_smul, lawP2_const] using h
  rcases hG.lt_or_gt with hneg | hpos
  · have h := key ((e, 0, 0, 0) : TupleH ν 1 1 1)
    simp only [interiorPairing, dissipation, diagDiff, liMinCoeffs, tupleMean_dirac,
      adjoint_GX, hGt, GX_fin_one_apply, Prod.fst_zero, Prod.snd_zero, sub_zero, sub_self,
      map_zero, inner_zero_left, inner_zero_right, norm_zero, inner_neg_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, he1] at h
    nlinarith [sq_nonneg c, mul_nonneg hβ₂ (sq_nonneg c), Real.norm_eq_abs c, sq_abs c]
  · have h := key ((0, e, 0, 0) : TupleH ν 1 1 1)
    simp only [interiorPairing, dissipation, diagDiff, liMinCoeffs, tupleMean_dirac,
      adjoint_GX, hGt, GX_fin_one_apply, Prod.fst_zero, Prod.snd_zero, sub_zero, sub_self,
      map_zero, inner_zero_left, inner_zero_right, norm_zero, inner_neg_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, he1] at h
    nlinarith [sq_nonneg c, mul_nonneg hβ₁ (sq_nonneg c), Real.norm_eq_abs c, sq_abs c]

/-- **Assumption 2.5 fails for the system of Li and Min**, for every coupling matrix
`G ∈ ℝ^{1×1}` of full rank and all constants `α, β₁, β₂`, over any filtered probability space
and at every horizon `T > 0`. -/
theorem not_assumption25_liMin (hT : 0 < T) {G : Matrix (Fin 1) (Fin 1) ℝ}
    (hG : G.rank = min 1 1) (α β₁ β₂ : ℝ) :
    ¬ Assumption25 ℱ P T G α β₁ β₂ (liMinCoeffs ν) := fun h =>
  not_diagonalMonotone_liMin hT (entry_ne_zero_of_rank_eq_one hG) h.constants.β₁_nonneg
    h.constants.β₂_nonneg h.diagonalMonotone

/-- **The system of Li and Min fails Assumption 2.5 while the other assumptions hold.** Over any
filtered probability space and at every horizon `T > 0`, with any deterministic initial datum
`x₀`: (2.3), Assumption 2.2 and Assumption 2.3 with `L = 2` hold; `G = 1` satisfies
Assumption 2.4; and for every coupling matrix `G ∈ ℝ^{1×1}` of full rank and all constants
`α, β₁, β₂`, Assumption 2.5 fails. -/
theorem liMin_fails_assumption25 (hT : 0 < T) (x₀ : EuclideanSpace ℝ (Fin 1)) :
    JointBorel T (liMinCoeffs ν)
      ∧ Assumption22 ℱ P T (liMinCoeffs ν) (fun _ => x₀)
      ∧ Assumption23 ℱ P T 2 (liMinCoeffs ν)
      ∧ (1 : Matrix (Fin 1) (Fin 1) ℝ).rank = min 1 1
      ∧ ∀ G : Matrix (Fin 1) (Fin 1) ℝ, G.rank = min 1 1 →
          ∀ α β₁ β₂ : ℝ, ¬ Assumption25 ℱ P T G α β₁ β₂ (liMinCoeffs ν) :=
  ⟨jointBorel_liMin T, assumption22_liMin x₀, assumption23_liMin, rank_one_eq_min,
    fun _ hG α β₁ β₂ => not_assumption25_liMin hT hG α β₁ β₂⟩

end Dissertation.WellPosedness.Spec
