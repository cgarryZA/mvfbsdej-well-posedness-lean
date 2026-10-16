/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3Margin
import Dissertation.WellPosedness.Robustness.JumpMargin
import Dissertation.Acceptance.A.Witness
import LevyStochCalc.Driver.Existence

/-!
# The paragraph after Corollary 3.6 of the well-posedness paper: proofs

## Main statements

* `Dissertation.Acceptance.A.cor_margin_channels` — a margin in (2.13) makes every channel
  strictly dissipative.
* `Dissertation.Acceptance.A.cor_margin_additive` — an additive jump coefficient supplies no
  margin when `ν ≠ 0`.
* `Dissertation.Acceptance.A.cor_margin_finite` — finitely many functionals of `u` supply no
  margin on an infinite-dimensional `L²(ν)`.
* `Dissertation.Acceptance.A.cor_margin_findim` — on a finite-dimensional `L²(ν)` they carry one.
* `Dissertation.Acceptance.A.not_finiteDimensional_Lp_volume` — `L²(Lebesgue; ℝ¹)` is infinite
  dimensional.
* `Dissertation.Acceptance.A.cor_margin_additive_hypotheses`, `cor_margin_finite_hypotheses`,
  `cor_margin_findim_hypotheses` — instances meeting the hypotheses.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Matrix

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Enlarged Dissertation.WellPosedness.Spec Dissertation.Law

universe u v w

/-- The paragraph after Corollary 3.6, every channel. -/
theorem cor_margin_channels : PaperSpec.A.cor_margin_channels.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ _ T β₁ β₂ c G C h
  filter_upwards [h] with t ht p hp p' hp'
  obtain ⟨-, hle⟩ := ht p hp p' hp'
  refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_, fun heq => ?_⟩
  · have e1 : ∀ ω, pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2
        = inner ℝ (-(C.f t (p.1 ω) p.2 - C.f t (p'.1 ω) p'.2))
            (GX G ((p.1 ω).1 - (p'.1 ω).1)) := fun ω => by
      obtain ⟨h2, h3, h4⟩ := heq ω
      simp [pairing27, h2, h3, h4]
    have e2 : ∀ ω, ‖GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)‖ ^ 2
        + ‖GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)‖ ^ 2
        + ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2 = 0 := fun ω => by
      obtain ⟨h2, h3, h4⟩ := heq ω
      simp [h2, h3, h4]
    have e3 : ∀ ω, ‖(p.1 ω).2.1 - (p'.1 ω).2.1‖ ^ 2 + ‖(p.1 ω).2.2.1 - (p'.1 ω).2.2.1‖ ^ 2
        + ‖(p.1 ω).2.2.2 - (p'.1 ω).2.2.2‖ ^ 2 + ‖(p.1 ω).1 - (p'.1 ω).1‖ ^ 2
        = ‖(p.1 ω).1 - (p'.1 ω).1‖ ^ 2 := fun ω => by
      obtain ⟨h2, h3, h4⟩ := heq ω
      simp [h2, h3, h4]
    rw [integral_congr_ae (ae_of_all _ e1), integral_congr_ae (ae_of_all _ e2),
      integral_congr_ae (ae_of_all _ e3), integral_zero, mul_zero] at hle
    linarith
  · have e1 : ∀ ω, pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2
        = inner ℝ (C.b t (p.1 ω) p.2 - C.b t (p'.1 ω) p'.2)
            (GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)) := fun ω => by
      obtain ⟨h1, h3, h4⟩ := heq ω
      simp [pairing27, h1, h3, h4]
    have e2 : ∀ ω, ‖GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)‖ ^ 2
        + ‖GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)‖ ^ 2
        + ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2
        = ‖GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)‖ ^ 2 := fun ω => by
      obtain ⟨h1, h3, h4⟩ := heq ω
      simp [h3, h4]
    have e3 : ∀ ω, ‖GX G ((p.1 ω).1 - (p'.1 ω).1)‖ ^ 2 = 0 := fun ω => by
      obtain ⟨h1, h3, h4⟩ := heq ω
      simp [h1]
    have e4 : ∀ ω, ‖(p.1 ω).2.1 - (p'.1 ω).2.1‖ ^ 2 + ‖(p.1 ω).2.2.1 - (p'.1 ω).2.2.1‖ ^ 2
        + ‖(p.1 ω).2.2.2 - (p'.1 ω).2.2.2‖ ^ 2 + ‖(p.1 ω).1 - (p'.1 ω).1‖ ^ 2
        = ‖(p.1 ω).2.1 - (p'.1 ω).2.1‖ ^ 2 := fun ω => by
      obtain ⟨h1, h3, h4⟩ := heq ω
      simp [h1, h3, h4]
    rw [integral_congr_ae (ae_of_all _ e1), integral_congr_ae (ae_of_all _ e2),
      integral_congr_ae (ae_of_all _ e3), integral_congr_ae (ae_of_all _ e4), integral_zero,
      mul_zero, sub_zero] at hle
    exact hle
  · have e1 : ∀ ω, pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2
        = inner ℝ (C.σ t (p.1 ω) p.2 - C.σ t (p'.1 ω) p'.2)
            (GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)) := fun ω => by
      obtain ⟨h1, h2, h4⟩ := heq ω
      simp [pairing27, h1, h2, h4]
    have e2 : ∀ ω, ‖GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)‖ ^ 2
        + ‖GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)‖ ^ 2
        + ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2
        = ‖GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)‖ ^ 2 := fun ω => by
      obtain ⟨h1, h2, h4⟩ := heq ω
      simp [h2, h4]
    have e3 : ∀ ω, ‖GX G ((p.1 ω).1 - (p'.1 ω).1)‖ ^ 2 = 0 := fun ω => by
      obtain ⟨h1, h2, h4⟩ := heq ω
      simp [h1]
    have e4 : ∀ ω, ‖(p.1 ω).2.1 - (p'.1 ω).2.1‖ ^ 2 + ‖(p.1 ω).2.2.1 - (p'.1 ω).2.2.1‖ ^ 2
        + ‖(p.1 ω).2.2.2 - (p'.1 ω).2.2.2‖ ^ 2 + ‖(p.1 ω).1 - (p'.1 ω).1‖ ^ 2
        = ‖(p.1 ω).2.2.1 - (p'.1 ω).2.2.1‖ ^ 2 := fun ω => by
      obtain ⟨h1, h2, h4⟩ := heq ω
      simp [h1, h2, h4]
    rw [integral_congr_ae (ae_of_all _ e1), integral_congr_ae (ae_of_all _ e2),
      integral_congr_ae (ae_of_all _ e3), integral_congr_ae (ae_of_all _ e4), integral_zero,
      mul_zero, sub_zero] at hle
    exact hle
  · have e1 : ∀ ω, pairing27 G C t (p.1 ω) (p'.1 ω) p.2 p'.2
        = ∫ e, inner ℝ (C.h t (p.1 ω) p.2 e - C.h t (p'.1 ω) p'.2 e)
            (GX Gᵀ ((p.1 ω).2.2.2 e - (p'.1 ω).2.2.2 e)) ∂ν := fun ω => by
      obtain ⟨h1, h2, h3⟩ := heq ω
      simp only [pairing27, h1, h2, h3, sub_self, map_zero, inner_zero_right, zero_add]
    have e2 : ∀ ω, ‖GX Gᵀ ((p.1 ω).2.1 - (p'.1 ω).2.1)‖ ^ 2
        + ‖GZ Gᵀ ((p.1 ω).2.2.1 - (p'.1 ω).2.2.1)‖ ^ 2
        + ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2
        = ‖GU Gᵀ ν ((p.1 ω).2.2.2 - (p'.1 ω).2.2.2)‖ ^ 2 := fun ω => by
      obtain ⟨-, h2, h3⟩ := heq ω
      simp [h2, h3]
    have e3 : ∀ ω, ‖GX G ((p.1 ω).1 - (p'.1 ω).1)‖ ^ 2 = 0 := fun ω => by
      obtain ⟨h1, -, -⟩ := heq ω
      simp [h1]
    have e4 : ∀ ω, ‖(p.1 ω).2.1 - (p'.1 ω).2.1‖ ^ 2 + ‖(p.1 ω).2.2.1 - (p'.1 ω).2.2.1‖ ^ 2
        + ‖(p.1 ω).2.2.2 - (p'.1 ω).2.2.2‖ ^ 2 + ‖(p.1 ω).1 - (p'.1 ω).1‖ ^ 2
        = ‖(p.1 ω).2.2.2 - (p'.1 ω).2.2.2‖ ^ 2 := fun ω => by
      obtain ⟨h1, h2, h3⟩ := heq ω
      simp [h1, h2, h3]
    rw [integral_congr_ae (ae_of_all _ e1), integral_congr_ae (ae_of_all _ e2),
      integral_congr_ae (ae_of_all _ e3), integral_congr_ae (ae_of_all _ e4), integral_zero,
      mul_zero, sub_zero] at hle
    exact hle

/-- The paragraph after Corollary 3.6, the additive jump coefficient. -/
theorem cor_margin_additive : PaperSpec.A.cor_margin_additive.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ _ hm T hT hν β₁ β₂ c G C hβ₁ hc hadd h
  exact not_diagonalMonotoneMargin_of_additive hT hc hβ₁ hν hm hadd h.diagonalMonotoneMargin

/-- The paragraph after Corollary 3.6, finitely many functionals. -/
theorem cor_margin_finite : PaperSpec.A.cor_margin_finite.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ _ T hT hinf β₁ β₂ c G C k ℓ hβ₁ hc hfac h
  exact not_diagonalMonotoneMargin_of_not_finiteDimensional hinf hT hc hβ₁ ℓ hfac
    h.diagonalMonotoneMargin

/-- The paragraph after Corollary 3.6, the finite-dimensional case. -/
theorem cor_margin_findim : PaperSpec.A.cor_margin_findim.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n d P _ D h𝒢₀ _ hn T hT hfin β₁ β₂ c hβ₁ hβ₂ hc σc hcL
  let b := Module.finBasis ℝ (Lp (EuclideanSpace ℝ (Fin n)) 2 ν)
  refine ⟨_, b.equivFun.toLinearMap, b.equivFun.injective, fun t θ θ' μ μ' h => ?_, ?_⟩
  · have e : θ.2.2.2 = θ'.2.2.2 := b.equivFun.injective h
    simp only [affineCoeffs, e]
  · exact (margin213_iff hc (by linarith) (by linarith)).mpr
      (diagonalMonotoneMargin_affine β₁ β₂ c)

/-- `L²(Lebesgue; ℝ¹)` is infinite dimensional: the indicators of the intervals `[k, k + 1)`,
`k ∈ ℕ`, are nonzero and pairwise orthogonal. -/
theorem not_finiteDimensional_Lp_volume :
    ¬ FiniteDimensional ℝ (Lp (EuclideanSpace ℝ (Fin 1)) 2 (volume : Measure ℝ)) := by
  intro hfin
  have hS : ∀ k : ℕ, MeasurableSet (Set.Ico (k : ℝ) (k + 1)) := fun _ => measurableSet_Ico
  have hSf : ∀ k : ℕ, volume (Set.Ico (k : ℝ) (k + 1)) ≠ ⊤ := fun _ => by simp
  let f : ℕ → Lp (EuclideanSpace ℝ (Fin 1)) 2 (volume : Measure ℝ) :=
    fun k => indicatorConstLp 2 (hS k) (hSf k) (EuclideanSpace.single 0 1)
  have hli : LinearIndependent ℝ f := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun k h0 => ?_) (fun i j hij => ?_)
    · have hn := congrArg norm h0
      rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_zero] at hn
      simp at hn
    · have hd : Disjoint (Set.Ico (i : ℝ) (i + 1)) (Set.Ico (j : ℝ) (j + 1)) := by
        rw [Set.Ico_disjoint_Ico]
        rcases Nat.lt_or_gt_of_ne hij with h | h
        · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
          exact (min_le_left _ _).trans (this.trans (le_max_right _ _))
        · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
          exact (min_le_right _ _).trans (this.trans (le_max_left _ _))
      simp only [f]
      rw [L2.inner_indicatorConstLp_indicatorConstLp (hS i) (hS j) (hSf i) (hSf j),
        Set.disjoint_iff_inter_eq_empty.mp hd]
      simp
  exact Module.Finite.not_linearIndependent_of_infinite f hli

/-- The indicator `φ = 1_{[0, 1]} e₁ ∈ L²(Lebesgue; ℝ¹)`. -/
noncomputable def unitIndicator : Lp (EuclideanSpace ℝ (Fin 1)) 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (measurableSet_Icc (a := (0 : ℝ)) (b := 1)) (by simp)
    (EuclideanSpace.single 0 1)

/-- The tuple space at Lebesgue measure on `ℝ` and `n = m = d = 1` has measurable singletons
(the product instance, beyond the default instance-search size for the fourfold product). -/
instance measurableSingletonClass_tupleH_volume :
    MeasurableSingletonClass (TupleH (volume : Measure ℝ) 1 1 1) :=
  @Prod.instMeasurableSingletonClass _ _ _ _ _ (@Prod.instMeasurableSingletonClass _ _ _ _ _
    inferInstance)

/-- Rank-one jump feedback on `ℍ` with `n = m = d = 1` and `ν` Lebesgue measure on `ℝ`:
`b = σ = f = g = 0` and `h(t, θ, μ) = −⟨φ, u⟩ φ`, with `φ = unitIndicator`. -/
noncomputable def rankOneCoeffs : Coeffs (volume : Measure ℝ) 1 1 1 where
  b _ _ _ := 0
  σ _ _ _ := 0
  h _ θ _ := -(inner ℝ unitIndicator θ.2.2.2) • unitIndicator
  f _ _ _ := 0
  g _ _ := 0

/-- **The hypotheses of `cor_margin_finite` can be met.** Over a probability space carrying a Lévy
driver with `d = 1` and `ν` Lebesgue measure on `ℝ`, with `𝒢₀ = ⊥` independent of it,
`L²(ν; ℝ¹)` is infinite dimensional, and the jump coefficient of `rankOneCoeffs` depends on `u`
only through the single functional `ℓ u = ⟨φ, u⟩`. -/
theorem cor_margin_finite_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (volume : Measure ℝ)),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P
      ∧ ¬ FiniteDimensional ℝ (Lp (EuclideanSpace ℝ (Fin 1)) 2 (volume : Measure ℝ))
      ∧ ∃ ℓ : Lp (EuclideanSpace ℝ (Fin 1)) 2 (volume : Measure ℝ) →ₗ[ℝ] (Fin 1 → ℝ),
        ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin 1)) (y : EuclideanSpace ℝ (Fin 1))
          (z : EuclideanSpace ℝ (Fin 1 × Fin 1))
          (u u' : Lp (EuclideanSpace ℝ (Fin 1)) 2 (volume : Measure ℝ)),
          ℓ u = ℓ u' → rankOneCoeffs.h t (x, y, z, u)
              (P2.dirac ((x, y, z, u) : TupleH (volume : Measure ℝ) 1 1 1))
            = rankOneCoeffs.h t (x, y, z, u')
              (P2.dirac ((x, y, z, u') : TupleH (volume : Measure ℝ) 1 1 1)) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (volume : Measure ℝ)
  refine ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _,
    not_finiteDimensional_Lp_volume,
    LinearMap.pi fun _ => (innerSL ℝ unitIndicator).toLinearMap, fun t x y z u u' h => ?_⟩
  have h0 := congrFun h 0
  simp only [LinearMap.pi_apply, ContinuousLinearMap.coe_coe, innerSL_apply_apply] at h0
  simp only [rankOneCoeffs, h0]

/-- **The hypotheses of `cor_margin_additive` can be met.** Over a probability space carrying a
Lévy driver with `d = 1` and `ν = δ₀ ≠ 0` on `ℝ`, with `𝒢₀ = ⊥` independent of it, the jump
coefficient of Example 5.1(i) with `n = 1`, `β₁ = 0`, `β₂ = 1`, `σ_c = 0`, `h_c = 0` depends
on `t` and `x` only. -/
theorem cor_margin_additive_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ))),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P
      ∧ Measure.dirac (0 : ℝ) ≠ 0
      ∧ ∀ (t : ℝ) (θ θ' : TupleH (Measure.dirac (0 : ℝ)) 1 1 1)
          (μ μ' : P2 (TupleH (Measure.dirac (0 : ℝ)) 1 1 1)), θ.1 = θ'.1 →
          (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 0 1 0 0).h t θ μ
            = (affineCoeffs (ν := Measure.dirac (0 : ℝ)) (n := 1) (d := 1) 0 1 0 0).h t θ' μ' := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _, Measure.dirac_ne_zero,
    fun t θ θ' μ μ' _ => by simp [affineCoeffs]⟩

/-- **The hypotheses of `cor_margin_findim` can be met.** Over a probability space carrying a
Lévy driver with `d = 1` and `ν = δ₀` on `ℝ`, with `𝒢₀ = ⊥` independent of it, `L²(ν; ℝ¹)` is
finite dimensional. -/
theorem cor_margin_findim_hypotheses :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyStochCalc.Driver.LevyDriver P 1 (Measure.dirac (0 : ℝ))),
      Indep (⊥ : MeasurableSpace Ω) (⨆ t, D.filtration t) P
      ∧ FiniteDimensional ℝ (Lp (EuclideanSpace ℝ (Fin 1)) 2 (Measure.dirac (0 : ℝ))) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (0 : ℝ))
  obtain ⟨ℓ, hℓ⟩ := exists_injective_functional_dirac (0 : ℝ)
  exact ⟨Ω, inferInstance, P, inferInstance, D, indep_bot_left _,
    FiniteDimensional.of_injective ℓ hℓ⟩

end Dissertation.Acceptance.A
