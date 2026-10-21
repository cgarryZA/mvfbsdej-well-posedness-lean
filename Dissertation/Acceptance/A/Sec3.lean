/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Dissertation.PaperSpec.A.Sec3
import Dissertation.WellPosedness.Spec.Thm35
import Dissertation.WellPosedness.Existence.CadlagVersion
import Dissertation.WellPosedness.Spec.Cor36WellPosed
import Dissertation.Acceptance.A.Solution

/-!
# Section 3 of the well-posedness paper: proofs of the main results

## Main statements

* `Dissertation.Acceptance.A.thm_stab` — Theorem 3.1, with
  `C_stab = aprioriConst T (10 (2L)²) (4 (2L)²) ‖G‖ c_G α β₁ β₂ 1`.
* `Dissertation.Acceptance.A.thm_uniq` — Theorem 3.3.
* `Dissertation.Acceptance.A.thm_cwp` — Theorem 3.5, existence and uniqueness.
* `Dissertation.Acceptance.A.cor_robust`, `cor_robust_wp`, `cor_robust_lip` — Corollary 3.6.
* `Dissertation.Acceptance.A.prop_strict` — Proposition 3.8.
-/

open MeasureTheory ProbabilityTheory

namespace Dissertation.Acceptance.A

open Dissertation.WellPosedness.System Dissertation.WellPosedness.Existence
  Dissertation.WellPosedness.Stability Dissertation.WellPosedness.Spec
  Dissertation.WellPosedness.Enlarged

universe u v w

/-- Theorem 3.1. -/
theorem thm_stab : PaperSpec.A.thm_stab.{u, v, w} := by
  refine ⟨fun T L g c α β₁ β₂ =>
    aprioriConst T (10 * (2 * L) ^ 2) (4 * (2 * L) ^ 2) g c α β₁ β₂ 1, ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L L₂ α β₁ β₂ G C₁ C₂ ξ₁ ξ₂
    hJ₁ h22₁ h23₁ hG h25₁ hJ₂ h22₂ h23₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ hS₁ hS₂
  obtain ⟨⟨γ₁, h₁⟩, -, -⟩ := Solution.paperSolutionEnl hT.le hJ₁ h22₁.origin h23₁ hS₁
  obtain ⟨⟨γ₂, h₂⟩, hX₂l, hY₂l⟩ := Solution.paperSolutionEnl hT.le hJ₂ h22₂.origin h23₂ hS₂
  have key := PaperSolutionEnl.supSize_sub_le_of_assumptions D h𝒢₀ hind₀ hn hm hd hT hJ₁ h22₁
    h23₁ hG h25₁ hJ₂ h22₂ h23₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ γ₁ γ₂ h₁ h₂
  have hj : ∀ i, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => jumpProc T (coeffJump P T C₁ X₂ Y₂ Z₂ U₂) i s ω e - jumpProc T γ₂ i s ω e)
      = LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e =>
        jumpProc T (coeffJump P T C₁ (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e
          - jumpProc T (coeffJump P T C₂ (leftLimProc X₂) (leftLimProc Y₂) Z₂ U₂) i s ω e) :=
    fun i => PaperSolution.markedEnergy_coeffJump_sub_eq_leftLim h₂ hT hX₂l hY₂l
      (jointBorel_iff.mp hJ₁).1.toCoeffBorel (jointBorel_iff.mp hJ₂).1.toCoeffBorel i
  refine key.trans_eq ?_
  simp only [dataSize, hj]

/-- The supremum term of `supSize` vanishes for processes vanishing on `[0, T]` almost surely. -/
theorem lintegral_biSup_esq_eq_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    {T : ℝ} {V : Fin n → ℝ → Ω → ℝ}
    (hV : ∀ i, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, V i t ω = 0) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, esq (fun i => V i t ω)) ∂P = 0 := by
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [ae_all_iff.mpr hV] with ω hω
  refine le_antisymm (iSup₂_le fun t ht => ?_) zero_le
  have h0 : ∀ i, V i t ω = 0 := fun i => hω i t ht
  simp [esq, h0]

/-- Theorem 3.3. -/
theorem thm_uniq : PaperSpec.A.thm_uniq.{u, v, w} := by
  rintro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C hJ h23 hG h25 ξ₀
    X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨γ₁, h₁⟩, -, -⟩ ⟨⟨γ₂, h₂⟩, -, -⟩
  have key := PaperWeakSolutionIntEnl.uniqueness_of_assumptions D h𝒢₀ hind₀ hn hm hd hT hJ h23
    hG h25 _ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ γ₁ γ₂ h₁ h₂
  refine ⟨key, ?_⟩
  obtain ⟨hX, hY, hZ, hU⟩ := key
  have hXs := lintegral_biSup_esq_eq_zero (P := P) (T := T)
    (V := fun i t ω => X₁ i t ω - X₂ i t ω) fun i => (hX i).mono fun ω hω t ht =>
      sub_eq_zero.mpr (hω t ht)
  have hYs := lintegral_biSup_esq_eq_zero (P := P) (T := T)
    (V := fun k t ω => Y₁ k t ω - Y₂ k t ω) fun k => (hY k).mono fun ω hω t ht =>
      sub_eq_zero.mpr (hω t ht)
  simp only [supSize] at hXs hYs ⊢
  rw [hXs, hYs]
  simp [hZ, hU]

/-- Theorem 3.5, existence and uniqueness. -/
theorem thm_cwp : PaperSpec.A.thm_cwp.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n m d P _ D h𝒢₀ hind₀ hn hm hd T hT L α β₁ β₂ G C ξ₀ hJ h22 h23 hG h25
  refine ⟨?_, ?_⟩
  · have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → ∀ t : ℝ,
        MeasurableSet[enlJoint 𝒢₀ D h𝒢₀ t] s := by
      intro s hs h0 t
      have h0' := measurableSet_enlJoint_of_null D h𝒢₀ hs h0
      rcases le_total 0 t with ht | ht
      · exact (enlJoint 𝒢₀ D h𝒢₀).mono ht _ h0'
      · exact enlJoint_le_of_nonpos D h𝒢₀ ht _ h0'
    obtain ⟨X, Y, Z, U, γ, h, -⟩ :=
      exists_paperSolutionEnl_unique_of_assumptions D h𝒢₀ hind₀ hn hm hd hT hJ h22 h23 hG h25
    obtain ⟨X', Y', h', hX', hY', -⟩ :=
      h.exists_cadlag_version hT.le (jointBorel_iff.mp hJ).1.toCoeffBorel hnull
    exact ⟨X', Y', Z, U, solution_of_paperSolutionEnl hT.le h' hX' hY'⟩
  · rintro X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ ⟨⟨⟨γ₁, h₁⟩, -, -⟩, -, -⟩ ⟨⟨⟨γ₂, h₂⟩, -, -⟩, -, -⟩
    exact PaperWeakSolutionIntEnl.uniqueness_of_assumptions D h𝒢₀ hind₀ hn hm hd hT hJ h23 hG
      h25 _ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ γ₁ γ₂ h₁ h₂

/-- Corollary 3.6, the assumptions of the perturbed system. -/
theorem cor_robust : PaperSpec.A.cor_robust.{u, v, w} := by
  intro Ω 𝒢₀ mΩ E _ ν _ _ n d P _ D h𝒢₀ _ hn hd T hT L₀ Lₚ α β₁ β₂ cdiss cpert G C p ξ₀ hJ h22
    h23 hG h25 h213 hcdiss horigp hLp hLp0 h34 _ hJp hc
  obtain ⟨h22', h23', h25', hm', -⟩ :=
    perturb_assumptions_of_assumptions h22 h23 h25 h213 hcdiss hJp horigp hLp hLp0 h34 hc
  exact ⟨h22', ⟨_, h23'⟩, hG, h25', hm'⟩

/-- Corollary 3.6, well-posedness of the perturbed system, with the constant of Theorem 3.1. -/
theorem cor_robust_wp : PaperSpec.A.cor_robust_wp.{u, v, w} := by
  obtain ⟨Cstab, hstab⟩ := thm_stab.{u, v, w}
  refine ⟨Cstab, ?_⟩
  intro Ω 𝒢₀ mΩ E _ ν _ _ n d P _ D h𝒢₀ hind₀ hn hd T hT L₀ Lₚ α β₁ β₂ cdiss cpert G C p ξ₀ hJ
    h22 h23 hG h25 h213 hcdiss horigp hLp hLp0 h34 _ hJp hc
  obtain ⟨h22', h23', h25', -, -⟩ :=
    perturb_assumptions_of_assumptions h22 h23 h25 h213 hcdiss hJp horigp hLp hLp0 h34 hc
  refine ⟨(thm_cwp 𝒢₀ ν n n d P D h𝒢₀ hind₀ hn hn hd T hT _ α β₁ β₂ G _ ξ₀ hJp h22' h23' hG
      h25').1, fun X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ h₁ h₂ => (thm_uniq 𝒢₀ ν n n d P D h𝒢₀ hind₀ hn hn hd T
      hT _ α β₁ β₂ G _ hJp h23' hG h25' ξ₀ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ h₁ h₂).1,
    fun L hL L₂ C₂ ξ₂ hJ₂ h22₂ h23₂ X₁ X₂ Y₁ Y₂ Z₁ Z₂ U₁ U₂ h₁ h₂ => hstab 𝒢₀ ν n n d P D h𝒢₀
      hind₀ hn hn hd T hT L L₂ α β₁ β₂ G _ C₂ ξ₀ ξ₂ hJp h22' hL hG h25' hJ₂ h22₂ h23₂ X₁ X₂ Y₁ Y₂
      Z₁ Z₂ U₁ U₂ h₁ h₂⟩

/-- Corollary 3.6, (3.5) gives (3.4) with `c_pert = ‖G‖ L_p`. -/
theorem cor_robust_lip : PaperSpec.A.cor_robust_lip.{u, v} := by
  intro Ω _ P _ ℱ E _ ν _ _ n d hn T hT Lₚ G p hind h35
  exact pairingBound34_iff.mpr ((lawLip35_iff.mp h35).diagonalPairingBound hind
    (h35.nonneg hn hT) G)

/-- Proposition 3.8. -/
theorem prop_strict : PaperSpec.A.prop_strict.{u, v} := by
  intro E _ ν _ _ d _ β₁ ε hβ₁ hε hεβ₁
  refine ⟨fun t θ θ' μ μ' => norm_clampDrift_sub_le hβ₁.le hε.le t θ θ' μ μ',
    fun P _ t Θ Θ' hΘ hΘ' => ⟨integrable_inner_clampDrift hΘ hΘ' t,
      integral_inner_clampDrift_le hε.le hΘ hΘ' t⟩,
    fun t β hβ => pointwise_monotonicity_fails_on_supports hβ₁ hε t hβ⟩

end Dissertation.Acceptance.A
