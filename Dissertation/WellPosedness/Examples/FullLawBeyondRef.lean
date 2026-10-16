/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.AffineSegments
import Dissertation.Law.RadialProfile
import Dissertation.WellPosedness.Examples.FullLaw
import Dissertation.WellPosedness.Examples.FullLawBeyond

/-!
# Example 5.4: the law statistics with an arbitrary reference law

The law statistics of Example 5.4 of the well-posedness paper are not expectation functionals for
any reference law, not only for Dirac masses (`FullLawBeyond.lean`).

* The radial statistic `μ ↦ 𝔮(W₂(μ, μ₀))` of the full tuple law, `W₂` for the Hilbert norm of
  `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)` and `n > 0`, is not affine along mixtures for a bounded
  profile `𝔮` not constant on `[0, ∞)`; the mixtures `(1 − t) μ₀ + t δ_{R v}` along a unit vector
  `v` of the `X`-channel realise every distance to `μ₀`
  (`not_affineAlongMixtures_of_radialProfile`).
* The same holds for the radial statistic `μ ↦ 𝔮̃(W₂(μ^U, Λ₀))` of the `U`-marginal when
  `L²(ν; ℝᵐ)` is not reduced to `0`, along the mixtures of the image of `Λ₀` under
  `u ↦ (0, 0, 0, u)` with Dirac masses in that channel.
* If the cylindrical statistic `μ ↦ Q((∫ φ_j dμ^U)_j)` is an expectation functional, then `Q` is
  affine along the segments of the attained range of the feature vector, a convex set, so it
  agrees there with an affine function (`exists_affine_eq_of_affine_segments`).

## Main definitions

* `embedU` — the embedding `u ↦ (0, 0, 0, u)` of the jump channel into the tuple space.

## Main statements

* `radial_not_affine_ref`, `radialU_not_affine_ref` — the two radial statistics are not affine
  along mixtures, for any reference law.
* `exists_affine_cylindrical_of_eq_integral` — a cylindrical statistic that is an expectation
  functional has an outer function affine on the attained range.
-/

open MeasureTheory Dissertation.Law

namespace Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

/-- **The radial statistic of the full law, for any reference law, is not affine along
mixtures**: for `n > 0`, a reference law `μ₀ ∈ P₂(H)` and a bounded profile `𝔮` not constant on
`[0, ∞)`, the law functional `μ ↦ 𝔮(W₂(μ, μ₀))`, `W₂` for the Hilbert norm of `H`, is not affine
along mixtures. -/
theorem radial_not_affine_ref (hn : 0 < n) (μ₀ : P2 (TupleH ν n m d)) {q : ℝ → ℝ} {B : ℝ}
    (hB : ∀ r, |q r| ≤ B) (hne : ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ q a ≠ q b) :
    ¬ AffineAlongMixtures fun μ : P2 (TupleH ν n m d) => q (w2H μ μ₀) := by
  set v : TupleH ν n m d := (EuclideanSpace.single ⟨0, hn⟩ 1, 0, 0, 0) with hv
  have hv0 : v ≠ 0 := by
    intro h
    have := congrArg (fun θ : TupleH ν n m d => θ.1 ⟨0, hn⟩) h
    simp [hv] at this
  have hself : w2H μ₀ μ₀ = 0 := (P2WH.dist_toP2WH μ₀ μ₀).symm.trans (dist_self _)
  have hlip : ∀ x y : P2 (TupleH ν n m d), |w2H x μ₀ - w2H y μ₀| ≤ w2H x y := fun x y => by
    have := abs_dist_sub_le x.toP2WH y.toP2WH μ₀.toP2WH
    simpa only [P2WH.dist_toP2WH] using this
  refine not_affineAlongMixtures_of_radialProfile (D := fun μ => w2H μ μ₀) μ₀ v hB hne
    (fun μ => rfl) hself (K := 2 * ‖v‖) (fun t ht a b => ?_)
    (M := 2 * Real.sqrt (secondMoment μ₀.law).toReal) (fun t ht => ?_)
    (c := ‖v‖) (norm_pos_iff.mpr hv0) (C := w2P μ₀ (P2.dirac 0)) (fun t ht R hR => ?_)
  · refine (hlip _ _).trans ((w2H_le_two_mul_w2P _ _).trans ?_)
    have h := w2P_mix_dirac_mix_dirac_le t ht μ₀ (a • v) (b • v)
    rw [← sub_smul, norm_smul, Real.norm_eq_abs] at h
    have e : 2 * ‖v‖ * Real.sqrt t * |a - b| = 2 * (Real.sqrt t * (|a - b| * ‖v‖)) := by ring
    rw [e]
    linarith
  · rw [zero_smul]
    refine (w2H_le_two_mul_w2P _ _).trans ?_
    have h := w2P_mix_dirac_self_le t ht μ₀
    linarith
  · have h1 := w2P_le_w2H (P2.mix t ht μ₀ (P2.dirac (R • v))) μ₀
    have h2 := w2P_triangle (P2.mix t ht μ₀ (P2.dirac (R • v))) μ₀ (P2.dirac 0)
    have h3 := sqrt_mul_norm_le_w2P_mix_dirac t ht μ₀ (R • v)
    rw [norm_smul, Real.norm_of_nonneg hR] at h3
    have e : ‖v‖ * Real.sqrt t * R = Real.sqrt t * (R * ‖v‖) := by ring
    rw [e]
    linarith

/-- The embedding `u ↦ (0, 0, 0, u)` of the jump channel into the tuple space. -/
noncomputable def embedU (u : Lp (EuclideanSpace ℝ (Fin m)) 2 ν) : TupleH ν n m d :=
  (0, 0, 0, u)

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The embedding of the jump channel into the tuple space is measurable. -/
theorem measurable_embedU :
    Measurable (embedU : Lp (EuclideanSpace ℝ (Fin m)) 2 ν → TupleH ν n m d) :=
  measurable_const.prodMk (measurable_const.prodMk (measurable_const.prodMk measurable_id))

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The embedding of the jump channel into the tuple space does not increase the norm. -/
theorem norm_embedU_le (u : Lp (EuclideanSpace ℝ (Fin m)) 2 ν) :
    ‖(embedU u : TupleH ν n m d)‖ ≤ ‖u‖ := by
  simp [embedU, Prod.norm_def]

/-- **The radial statistic of the `U`-marginal, for any reference law, is not affine along
mixtures**: when `L²(ν; ℝᵐ)` contains some `u₀ ≠ 0`, for a reference law `Λ₀ ∈ P₂(L²(ν; ℝᵐ))` and a
bounded profile `𝔮̃` not constant on `[0, ∞)`, the law functional `μ ↦ 𝔮̃(W₂(μ^U, Λ₀))` is not
affine along mixtures. -/
theorem radialU_not_affine_ref {u₀ : Lp (EuclideanSpace ℝ (Fin m)) 2 ν} (hu₀ : u₀ ≠ 0)
    (Λ₀ : P2 (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)) {q : ℝ → ℝ} {B : ℝ}
    (hB : ∀ r, |q r| ≤ B) (hne : ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ q a ≠ q b) :
    ¬ AffineAlongMixtures fun μ : P2 (TupleH ν n m d) => q (w2P μ.margU Λ₀) := by
  set μ₀ : P2 (TupleH ν n m d) := Λ₀.map measurable_embedU norm_embedU_le with hμ₀
  have hmarg : μ₀.margU = Λ₀ := by
    refine P2.ext_law ?_
    rw [margU_law]
    change (Λ₀.law.map embedU).map projUH = Λ₀.law
    rw [Measure.map_map measurable_projUH measurable_embedU]
    exact Measure.map_id
  set v : TupleH ν n m d := embedU u₀ with hv
  have hp : ∀ R : ℝ, (R • v).2.2.2 = R • u₀ := fun R => rfl
  refine not_affineAlongMixtures_of_radialProfile (D := fun μ => w2P μ.margU Λ₀) μ₀ v hB hne
    (fun μ => rfl) (by rw [hmarg, w2P_self]) (K := ‖v‖) (fun t ht a b => ?_)
    (M := Real.sqrt (secondMoment μ₀.law).toReal) (fun t ht => ?_)
    (c := ‖u₀‖) (norm_pos_iff.mpr hu₀) (C := w2P Λ₀ (P2.dirac 0)) (fun t ht R hR => ?_)
  · refine (abs_w2P_sub_w2P_le _ _ _).trans ((w2P_margU_le _ _).trans ?_)
    have h := w2P_mix_dirac_mix_dirac_le t ht μ₀ (a • v) (b • v)
    rw [← sub_smul, norm_smul, Real.norm_eq_abs] at h
    have e : ‖v‖ * Real.sqrt t * |a - b| = Real.sqrt t * (|a - b| * ‖v‖) := by ring
    rw [e]
    exact h
  · rw [zero_smul, ← hmarg]
    exact (w2P_margU_le _ _).trans (w2P_mix_dirac_self_le t ht μ₀)
  · rw [margU_mix, margU_dirac, hp]
    have h2 := w2P_triangle (P2.mix t ht μ₀.margU (P2.dirac (R • u₀))) Λ₀ (P2.dirac 0)
    have h3 := sqrt_mul_norm_le_w2P_mix_dirac t ht μ₀.margU (R • u₀)
    rw [norm_smul, Real.norm_of_nonneg hR] at h3
    have e : ‖u₀‖ * Real.sqrt t * R = Real.sqrt t * (R * ‖u₀‖) := by ring
    rw [e]
    linarith

/-- **A cylindrical statistic that is an expectation functional is affine on the attained
range**: for Lipschitz features `φ_j : L²(ν; ℝᵐ) → ℝ`, if `Q((∫ φ_j dμ^U)_j) = ∫ φ' dμ` for every
`μ ∈ P₂(H)`, with `φ'` integrable against every law of finite second moment, then
`Q(s) = a + ∑_j c_j s_j` at every attained feature vector `s = (∫ φ_j dμ^U)_j`, for some `a` and
`c`. -/
theorem exists_affine_cylindrical_of_eq_integral {J : ℕ} {Q : EuclideanSpace ℝ (Fin J) → ℝ}
    {φ : Fin J → Lp (EuclideanSpace ℝ (Fin m)) 2 ν → ℝ} {K : Fin J → ℝ}
    (hφ : ∀ j u u', |φ j u - φ j u'| ≤ K j * ‖u - u'‖) {φ' : TupleH ν n m d → ℝ}
    (hφ' : ∀ μ : P2 (TupleH ν n m d), Integrable φ' μ.law)
    (hall : ∀ μ : P2 (TupleH ν n m d),
      Q (WithLp.toLp 2 fun j => ∫ u, φ j u ∂μ.margU.law) = ∫ θ, φ' θ ∂μ.law) :
    ∃ (a : ℝ) (c : Fin J → ℝ), ∀ μ : P2 (TupleH ν n m d),
      Q (WithLp.toLp 2 fun j => ∫ u, φ j u ∂μ.margU.law)
        = a + ∑ j, c j * ∫ u, φ j u ∂μ.margU.law := by
  have hs : ∀ j, StronglyMeasurable (φ j) := fun j => stronglyMeasurable_of_abs_sub_le (hφ j)
  have hint : ∀ (j : Fin J) (Λ : P2 (Lp (EuclideanSpace ℝ (Fin m)) 2 ν)),
      Integrable (φ j) Λ.law := fun j Λ =>
    integrable_of_norm_sub_le (hs j) (K := K j)
      (fun x y => by simpa only [Real.norm_eq_abs] using hφ j x y) Λ.secondMoment_ne_top
  set s : P2 (TupleH ν n m d) → EuclideanSpace ℝ (Fin J) :=
    fun μ => WithLp.toLp 2 fun j => ∫ u, φ j u ∂μ.margU.law with hsdef
  have hsmix : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (μ μ' : P2 (TupleH ν n m d)),
      s (P2.mix t ht μ μ') = (1 - t) • s μ + t • s μ' := by
    intro t ht μ μ'
    refine PiLp.ext fun j => ?_
    simp only [hsdef, margU_mix, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact integral_mix t ht (hint j _) (hint j _)
  have hA : Convex ℝ (Set.range s) := by
    rintro _ ⟨μ, rfl⟩ _ ⟨μ', rfl⟩ a b ha hb hab
    refine ⟨P2.mix b ⟨hb, by linarith⟩ μ μ', ?_⟩
    rw [hsmix, show 1 - b = a by linarith]
  have hQaff : ∀ x ∈ Set.range s, ∀ y ∈ Set.range s, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Q ((1 - t) • x + t • y) = (1 - t) * Q x + t * Q y := by
    rintro _ ⟨μ, rfl⟩ _ ⟨μ', rfl⟩ t ht0 ht1
    rw [← hsmix t ⟨ht0, ht1⟩]
    simp only [hsdef]
    rw [hall, hall, hall]
    exact integral_mix t ⟨ht0, ht1⟩ (hφ' μ) (hφ' μ')
  obtain ⟨a, ℓ, hℓ⟩ := exists_affine_eq_of_affine_segments hA hQaff
  refine ⟨a, fun j => ℓ (EuclideanSpace.single j 1), fun μ => ?_⟩
  have h := hℓ (s μ) ⟨μ, rfl⟩
  simp only [hsdef] at h
  rw [h]
  congr 1
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin J) ℝ).sum_repr
    (WithLp.toLp 2 fun j => ∫ u, φ j u ∂μ.margU.law)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr]

end Dissertation.WellPosedness.System
