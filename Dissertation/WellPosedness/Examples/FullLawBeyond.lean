/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.Law.Mixture
import Dissertation.Law.TupleMarginal

/-!
# Example 5.4: the law statistics are not expectation functionals

An expectation functional `μ ↦ ∫ φ dμ` of the law of the tuple is affine along mixtures. The law
statistics of Example 5.4 are not, in the following precise sense.

* The radial statistic `μ ↦ 𝔮(W₂(μ, δ_c))` of the full tuple law, `W₂` for the Hilbert norm of
  `H = ℝⁿ × ℝᵐ × ℝ^{m×d} × L²(ν; ℝᵐ)` and `n > 0`, is not affine along mixtures when `𝔮` is
  Lipschitz and not constant on `[0, ∞)`: along the mixtures `(1 − t) δ_c + t δ_y` its distance
  is `√t |y − c|_H`.
* The same holds for the radial statistic `μ ↦ 𝔮̃(W₂(μ^U, δ_{u₀}))` of the `U`-marginal when
  `L²(ν; ℝᵐ)` is not reduced to `0`.
* The cylindrical statistic `μ ↦ Q((∫ φ_j dμ^U)_j)` is not affine along mixtures as soon as `Q`
  is not affine along the segment between the feature vectors `(φ_j(u))_j`, `(φ_j(u'))_j` of two
  points of `L²(ν; ℝᵐ)`.

The reference laws are Dirac masses.

## Main statements

* `margU_mix`, `margU_dirac` — the `U`-marginal of a mixture and of a Dirac mass.
* `w2H_dirac_dirac`, `w2H_mix_dirac` — the Hilbert-norm distances of Dirac masses and of their
  mixtures to a Dirac mass.
* `exists_norm_toL2_sub_eq` — for `n > 0` every Hilbert-norm distance is attained.
* `radial_not_affine`, `radialU_not_affine`, `cylindrical_margU_not_affine` — the three law
  statistics are not affine along mixtures.
* `radial_ne_integral`, `radialU_ne_integral`, `cylindrical_margU_ne_integral` — they are no
  expectation functionals.
-/

open MeasureTheory Dissertation.Law

namespace Dissertation.WellPosedness.System

variable {E : Type*} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  [MeasurableSpace.CountablyGenerated E] {n m d : ℕ}

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- The `U`-marginal of a mixture is the mixture of the `U`-marginals. -/
theorem margU_mix (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (μ μ' : P2 (TupleH ν n m d)) :
    (P2.mix t ht μ μ').margU = P2.mix t ht μ.margU μ'.margU := by
  refine P2.ext_law ?_
  rw [margU_law, P2.mix_law, P2.mix_law, Measure.map_add _ _ measurable_projUH, Measure.map_smul,
    Measure.map_smul, margU_law, margU_law]

/-- The `U`-marginal of a Dirac mass is the Dirac mass at the `U`-channel. -/
theorem margU_dirac (θ : TupleH ν n m d) : (P2.dirac θ).margU = P2.dirac θ.2.2.2 :=
  P2.ext_law (Measure.map_dirac' measurable_projUH θ)

/-- The Hilbert-norm distance of two Dirac masses is the Hilbert norm of the difference of their
points. -/
theorem w2H_dirac_dirac (θ θ' : TupleH ν n m d) :
    w2H (P2.dirac θ) (P2.dirac θ') = ‖toL2 (θ - θ')‖ := by
  rw [w2H, P2.dirac, P2.dirac]
  simp only
  rw [Measure.map_dirac' measurable_toL2, Measure.map_dirac' measurable_toL2, toL2_sub]
  exact w2_dirac_dirac (toL2 θ) (toL2 θ')

/-- **The Hilbert-norm distance of `(1 − t) δ_c + t δ_y` to `δ_c` is `√t |y − c|_H`.** -/
theorem w2H_mix_dirac (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (c y : TupleH ν n m d) :
    w2H (P2.mix t ht (P2.dirac c) (P2.dirac y)) (P2.dirac c) = Real.sqrt t * ‖toL2 (y - c)‖ := by
  rw [w2H, P2.mix_law, P2.dirac, P2.dirac]
  simp only
  rw [Measure.map_add _ _ measurable_toL2, Measure.map_smul, Measure.map_smul,
    Measure.map_dirac' measurable_toL2, Measure.map_dirac' measurable_toL2, toL2_sub]
  exact w2_mix_dirac t ht (toL2 c) (toL2 y)

omit [SigmaFinite ν] [MeasurableSpace.CountablyGenerated E] in
/-- For `n > 0` and `s ≥ 0` the tuple space has a point at Hilbert-norm distance `s` from `c`. -/
theorem exists_norm_toL2_sub_eq (hn : 0 < n) (c : TupleH ν n m d) {s : ℝ} (hs : 0 ≤ s) :
    ∃ y : TupleH ν n m d, ‖toL2 (y - c)‖ = s := by
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ 1
  have he : ‖e‖ = 1 := by simp [e]
  refine ⟨c + ((s • e, 0, 0, 0) : TupleH ν n m d), ?_⟩
  rw [add_sub_cancel_left]
  have h := norm_toL2_sq ((s • e, 0, 0, 0) : TupleH ν n m d)
  simp only [channelSq, norm_zero, norm_smul, he, Real.norm_of_nonneg hs] at h
  have h' : ‖toL2 ((s • e, 0, 0, 0) : TupleH ν n m d)‖ ^ 2 = s ^ 2 := by
    rw [h]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) hs two_ne_zero).mp h'

/-- **The radial statistic of the full tuple law is not affine along mixtures.** For `n > 0`,
`c ∈ H` and `𝔮` Lipschitz with `𝔮(a) ≠ 𝔮(b)` for some `a, b ≥ 0`, the law functional
`μ ↦ 𝔮(W₂(μ, δ_c))`, `W₂` for the Hilbert norm of `H`, is not affine along mixtures. -/
theorem radial_not_affine (hn : 0 < n) (c : TupleH ν n m d) {q : ℝ → ℝ} {Lq : ℝ}
    (hq : ∀ r r', |q r - q r'| ≤ Lq * |r - r'|) (hne : ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ q a ≠ q b) :
    ¬ AffineAlongMixtures fun μ : P2 (TupleH ν n m d) => q (w2H μ (P2.dirac c)) := by
  refine not_affineAlongMixtures_of_profile hq hne fun s hs => ?_
  obtain ⟨y, hy⟩ := exists_norm_toL2_sub_eq hn c hs.le
  refine ⟨P2.dirac c, P2.dirac y, by
    rw [w2H_dirac_dirac, sub_self, show toL2 (0 : TupleH ν n m d) = 0 from rfl, norm_zero],
    by rw [w2H_dirac_dirac, hy], fun t ht => by rw [w2H_mix_dirac, hy]⟩

/-- **The radial statistic of the `U`-marginal is not affine along mixtures.** If
`L²(ν; ℝᵐ)` is not reduced to `0`, then for `u₀ ∈ L²(ν; ℝᵐ)` and `𝔮̃` Lipschitz with
`𝔮̃(a) ≠ 𝔮̃(b)` for some `a, b ≥ 0`, the law functional `μ ↦ 𝔮̃(W₂(μ^U, δ_{u₀}))` on `P₂(H)` is
not affine along mixtures. -/
theorem radialU_not_affine (hU : ∃ u : Lp (EuclideanSpace ℝ (Fin m)) 2 ν, u ≠ 0)
    (u₀ : Lp (EuclideanSpace ℝ (Fin m)) 2 ν) {q : ℝ → ℝ} {Lq : ℝ}
    (hq : ∀ r r', |q r - q r'| ≤ Lq * |r - r'|) (hne : ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ q a ≠ q b) :
    ¬ AffineAlongMixtures fun μ : P2 (TupleH ν n m d) => q (w2P μ.margU (P2.dirac u₀)) := by
  obtain ⟨u, hu⟩ := hU
  haveI : Nontrivial (Lp (EuclideanSpace ℝ (Fin m)) 2 ν) := nontrivial_of_ne u 0 hu
  refine not_affineAlongMixtures_of_profile hq hne fun s hs => ?_
  obtain ⟨y, hy⟩ := exists_norm_sub_eq u₀ hs.le
  refine ⟨P2.dirac ((0, 0, 0, u₀) : TupleH ν n m d), P2.dirac ((0, 0, 0, y) : TupleH ν n m d),
    by rw [margU_dirac, w2P_self], by rw [margU_dirac, w2P_dirac_dirac, hy],
    fun t ht => by rw [margU_mix, margU_dirac, margU_dirac, w2P_mix_dirac, hy]⟩

/-- **The cylindrical statistic of the `U`-marginal is not affine along mixtures** when its outer
function is not affine along a segment of feature vectors: if `u, u' ∈ L²(ν; ℝᵐ)`, `t ∈ [0, 1]`
and `Q((1 − t) φ(u) + t φ(u')) ≠ (1 − t) Q(φ(u)) + t Q(φ(u'))` for the feature vectors
`φ(u) = (φ_j(u))_j`, then `μ ↦ Q((∫ φ_j dμ^U)_j)` on `P₂(H)` is not affine along mixtures. -/
theorem cylindrical_margU_not_affine {J : ℕ} {Q : EuclideanSpace ℝ (Fin J) → ℝ}
    {φ : Fin J → Lp (EuclideanSpace ℝ (Fin m)) 2 ν → ℝ} {u u' : Lp (EuclideanSpace ℝ (Fin m)) 2 ν}
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hQ : Q ((1 - t) • featureMap φ u + t • featureMap φ u')
      ≠ (1 - t) * Q (featureMap φ u) + t * Q (featureMap φ u')) :
    ¬ AffineAlongMixtures fun μ : P2 (TupleH ν n m d) => cylindricalFunctional Q φ μ.margU := by
  intro hF
  have key := hF t ht (P2.dirac ((0, 0, 0, u) : TupleH ν n m d))
    (P2.dirac ((0, 0, 0, u') : TupleH ν n m d))
  simp only [margU_mix, margU_dirac, cylindricalFunctional_mix_dirac,
    cylindricalFunctional_dirac] at key
  exact hQ key

/-! ### No expectation functionals -/

/-- **The radial statistic of the full tuple law is no expectation functional**: under the
hypotheses of `radial_not_affine`, for every `φ` integrable against every law of finite second
moment on `H`, `𝔮(W₂(μ, δ_c)) ≠ ∫ φ dμ` for some law `μ`. -/
theorem radial_ne_integral (hn : 0 < n) (c : TupleH ν n m d) {q : ℝ → ℝ} {Lq : ℝ}
    (hq : ∀ r r', |q r - q r'| ≤ Lq * |r - r'|) (hne : ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ q a ≠ q b)
    {φ : TupleH ν n m d → ℝ} (hφ : ∀ μ : P2 (TupleH ν n m d), Integrable φ μ.law) :
    ∃ μ : P2 (TupleH ν n m d), q (w2H μ (P2.dirac c)) ≠ ∫ θ, φ θ ∂μ.law :=
  exists_ne_integral_of_not_affineAlongMixtures (radial_not_affine hn c hq hne) hφ

/-- **The radial statistic of the `U`-marginal is no expectation functional**: under the
hypotheses of `radialU_not_affine`, for every `φ` integrable against every law of finite second
moment on `H`, `𝔮̃(W₂(μ^U, δ_{u₀})) ≠ ∫ φ dμ` for some law `μ`. -/
theorem radialU_ne_integral (hU : ∃ u : Lp (EuclideanSpace ℝ (Fin m)) 2 ν, u ≠ 0)
    (u₀ : Lp (EuclideanSpace ℝ (Fin m)) 2 ν) {q : ℝ → ℝ} {Lq : ℝ}
    (hq : ∀ r r', |q r - q r'| ≤ Lq * |r - r'|) (hne : ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ q a ≠ q b)
    {φ : TupleH ν n m d → ℝ} (hφ : ∀ μ : P2 (TupleH ν n m d), Integrable φ μ.law) :
    ∃ μ : P2 (TupleH ν n m d), q (w2P μ.margU (P2.dirac u₀)) ≠ ∫ θ, φ θ ∂μ.law :=
  exists_ne_integral_of_not_affineAlongMixtures (radialU_not_affine hU u₀ hq hne) hφ

/-- **The cylindrical statistic of the `U`-marginal is no expectation functional**: under the
hypotheses of `cylindrical_margU_not_affine`, for every `φ'` integrable against every law of
finite second moment on `H`, `Q((∫ φ_j dμ^U)_j) ≠ ∫ φ' dμ` for some law `μ`. -/
theorem cylindrical_margU_ne_integral {J : ℕ} {Q : EuclideanSpace ℝ (Fin J) → ℝ}
    {φ : Fin J → Lp (EuclideanSpace ℝ (Fin m)) 2 ν → ℝ} {u u' : Lp (EuclideanSpace ℝ (Fin m)) 2 ν}
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hQ : Q ((1 - t) • featureMap φ u + t • featureMap φ u')
      ≠ (1 - t) * Q (featureMap φ u) + t * Q (featureMap φ u'))
    {φ' : TupleH ν n m d → ℝ} (hφ' : ∀ μ : P2 (TupleH ν n m d), Integrable φ' μ.law) :
    ∃ μ : P2 (TupleH ν n m d), cylindricalFunctional Q φ μ.margU ≠ ∫ θ, φ' θ ∂μ.law :=
  exists_ne_integral_of_not_affineAlongMixtures (cylindrical_margU_not_affine ht hQ) hφ'

end Dissertation.WellPosedness.System
